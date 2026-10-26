import V185TrunkScan23Chunk0600

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3553587 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 3, 2, 2]
def baseStart_3553587 : Nat := 118140960795 + 3553587 * 2 ^ 59
def prefixEnd_3553587 : Nat := 4983230072969 + 3 ^ 40 * 3553587 * 2
def baseEnd_3553587 : Nat := 1824698178568893308219857

theorem tailTrace_3553587 : CollatzResearch.WordTrace tailWord_3553587 prefixEnd_3553587 1824698178568893308219857 := by
  unfold tailWord_3553587
  simp only [CollatzResearch.WordTrace]
  refine ⟨129609965776968678186587015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86406643851312452124391343 129609965776968678186587015)
  ·
    refine ⟨194414948665453017279880523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129609965776968678186587015 194414948665453017279880523)
    ·
      refine ⟨291622422998179525919820785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194414948665453017279880523 291622422998179525919820785)
      ·
        refine ⟨218716817248634644439865589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291622422998179525919820785 218716817248634644439865589)
        ·
          refine ⟨20504701617059497916237399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218716817248634644439865589 20504701617059497916237399)
          ·
            refine ⟨30757052425589246874356099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20504701617059497916237399 30757052425589246874356099)
            ·
              refine ⟨46135578638383870311534149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30757052425589246874356099 46135578638383870311534149)
              ·
                refine ⟨8650420994696975683412653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46135578638383870311534149 8650420994696975683412653)
                ·
                  refine ⟨3243907873011365881279745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8650420994696975683412653 3243907873011365881279745)
                  ·
                    refine ⟨2432930904758524410959809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3243907873011365881279745 2432930904758524410959809)
                    ·
                      refine ⟨1824698178568893308219857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432930904758524410959809 1824698178568893308219857)
                      ·
                        rfl

theorem cell23_3553587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 2, 2].length) (baseStart_3553587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553587 prefixEnd_3553587 := by exact prefixLift 3553587
  have htrace : WordTrace (prefixWord ++ tailWord_3553587) baseStart_3553587 baseEnd_3553587 := by
    simpa [prefixWord, tailWord_3553587, baseEnd_3553587] using wordTrace_append hprefix tailTrace_3553587
  have hstable : (prefixWord ++ tailWord_3553587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553587).length < 2 ^ (prefixWord ++ tailWord_3553587).sum := by decide
  have hdescent : baseEnd_3553587 < baseStart_3553587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553621 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 3, 2, 2]
def baseStart_3553621 : Nat := 118140960795 + 3553621 * 2 ^ 59
def prefixEnd_3553621 : Nat := 4983230072969 + 3 ^ 40 * 3553621 * 2
def baseEnd_3553621 : Nat := 1824715636911146175194701

theorem tailTrace_3553621 : CollatzResearch.WordTrace tailWord_3553621 prefixEnd_3553621 1824715636911146175194701 := by
  unfold tailWord_3553621
  simp only [CollatzResearch.WordTrace]
  refine ⟨129611205858845501993324717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86407470572563667995549811 129611205858845501993324717)
  ·
    refine ⟨48604202197067063247496769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129611205858845501993324717 48604202197067063247496769)
    ·
      refine ⟨36453151647800297435622577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48604202197067063247496769 36453151647800297435622577)
      ·
        refine ⟨27339863735850223076716933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36453151647800297435622577 27339863735850223076716933)
        ·
          refine ⟨5126224450471916826884425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27339863735850223076716933 5126224450471916826884425)
          ·
            refine ⟨3844668337853937620163319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5126224450471916826884425 3844668337853937620163319)
            ·
              refine ⟨5767002506780906430244979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844668337853937620163319 5767002506780906430244979)
              ·
                refine ⟨8650503760171359645367469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767002506780906430244979 8650503760171359645367469)
                ·
                  refine ⟨3243938910064259867012801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8650503760171359645367469 3243938910064259867012801)
                  ·
                    refine ⟨2432954182548194900259601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3243938910064259867012801 2432954182548194900259601)
                    ·
                      refine ⟨1824715636911146175194701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432954182548194900259601 1824715636911146175194701)
                      ·
                        rfl

theorem cell23_3553621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_3553621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553621 prefixEnd_3553621 := by exact prefixLift 3553621
  have htrace : WordTrace (prefixWord ++ tailWord_3553621) baseStart_3553621 baseEnd_3553621 := by
    simpa [prefixWord, tailWord_3553621, baseEnd_3553621] using wordTrace_append hprefix tailTrace_3553621
  have hstable : (prefixWord ++ tailWord_3553621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553621).length < 2 ^ (prefixWord ++ tailWord_3553621).sum := by decide
  have hdescent : baseEnd_3553621 < baseStart_3553621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553623 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 2, 7]
def baseStart_3553623 : Nat := 118140960795 + 3553623 * 2 ^ 59
def prefixEnd_3553623 : Nat := 4983230072969 + 3 ^ 40 * 3553623 * 2
def baseEnd_3553623 : Nat := 608238887957485055789897

theorem tailTrace_3553623 : CollatzResearch.WordTrace tailWord_3553623 prefixEnd_3553623 608238887957485055789897 := by
  unfold tailWord_3553623
  simp only [CollatzResearch.WordTrace]
  refine ⟨129611278804838256334897523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86407519203225504223265015 129611278804838256334897523)
  ·
    refine ⟨194416918207257384502346285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129611278804838256334897523 194416918207257384502346285)
    ·
      refine ⟨72906344327721519188379857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194416918207257384502346285 72906344327721519188379857)
      ·
        refine ⟨54679758245791139391284893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72906344327721519188379857 54679758245791139391284893)
        ·
          refine ⟨20504909342171677271731835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54679758245791139391284893 20504909342171677271731835)
          ·
            refine ⟨30757364013257515907597753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20504909342171677271731835 30757364013257515907597753)
            ·
              refine ⟨23068023009943136930698315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30757364013257515907597753 23068023009943136930698315)
              ·
                refine ⟨34602034514914705396047473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23068023009943136930698315 34602034514914705396047473)
                ·
                  refine ⟨25951525886186029047035605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34602034514914705396047473 25951525886186029047035605)
                  ·
                    refine ⟨608238887957485055789897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25951525886186029047035605 608238887957485055789897)
                    ·
                      rfl

theorem cell23_3553623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_3553623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553623 prefixEnd_3553623 := by exact prefixLift 3553623
  have htrace : WordTrace (prefixWord ++ tailWord_3553623) baseStart_3553623 baseEnd_3553623 := by
    simpa [prefixWord, tailWord_3553623, baseEnd_3553623] using wordTrace_append hprefix tailTrace_3553623
  have hstable : (prefixWord ++ tailWord_3553623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553623).length < 2 ^ (prefixWord ++ tailWord_3553623).sum := by decide
  have hdescent : baseEnd_3553623 < baseStart_3553623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553643 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 4]
def baseStart_3553643 : Nat := 118140960795 + 3553643 * 2 ^ 59
def prefixEnd_3553643 : Nat := 4983230072969 + 3 ^ 40 * 3553643 * 2
def baseEnd_3553643 : Nat := 1824726933485545089119599

theorem tailTrace_3553643 : CollatzResearch.WordTrace tailWord_3553643 prefixEnd_3553643 1824726933485545089119599 := by
  unfold tailWord_3553643
  simp only [CollatzResearch.WordTrace]
  refine ⟨129612008264765799750625583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86408005509843866500417055 129612008264765799750625583)
  ·
    refine ⟨194418012397148699625938375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129612008264765799750625583 194418012397148699625938375)
    ·
      refine ⟨291627018595723049438907563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194418012397148699625938375 291627018595723049438907563)
      ·
        refine ⟨437440527893584574158361345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291627018595723049438907563 437440527893584574158361345)
        ·
          refine ⟨328080395920188430618771009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437440527893584574158361345 328080395920188430618771009)
          ·
            refine ⟨246060296940141322964078257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328080395920188430618771009 246060296940141322964078257)
            ·
              refine ⟨184545222705105992223058693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246060296940141322964078257 184545222705105992223058693)
              ·
                refine ⟨34602229257207373541823505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184545222705105992223058693 34602229257207373541823505)
                ·
                  refine ⟨25951671942905530156367629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34602229257207373541823505 25951671942905530156367629)
                  ·
                    refine ⟨9731876978589573808637861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25951671942905530156367629 9731876978589573808637861)
                    ·
                      refine ⟨1824726933485545089119599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9731876978589573808637861 1824726933485545089119599)
                      ·
                        rfl

theorem cell23_3553643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 4].length) (baseStart_3553643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553643 prefixEnd_3553643 := by exact prefixLift 3553643
  have htrace : WordTrace (prefixWord ++ tailWord_3553643) baseStart_3553643 baseEnd_3553643 := by
    simpa [prefixWord, tailWord_3553643, baseEnd_3553643] using wordTrace_append hprefix tailTrace_3553643
  have hstable : (prefixWord ++ tailWord_3553643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553643).length < 2 ^ (prefixWord ++ tailWord_3553643).sum := by decide
  have hdescent : baseEnd_3553643 < baseStart_3553643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553647 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 1, 3, 2]
def baseStart_3553647 : Nat := 118140960795 + 3553647 * 2 ^ 59
def prefixEnd_3553647 : Nat := 4983230072969 + 3 ^ 40 * 3553647 * 2
def baseEnd_3553647 : Nat := 1824728987408163073469581

theorem tailTrace_3553647 : CollatzResearch.WordTrace tailWord_3553647 prefixEnd_3553647 1824728987408163073469581 := by
  unfold tailWord_3553647
  simp only [CollatzResearch.WordTrace]
  refine ⟨129612154156751308433771195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86408102771167538955847463 129612154156751308433771195)
  ·
    refine ⟨194418231235126962650656793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129612154156751308433771195 194418231235126962650656793)
    ·
      refine ⟨145813673426345221987992595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194418231235126962650656793 145813673426345221987992595)
      ·
        refine ⟨218720510139517832981988893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145813673426345221987992595 218720510139517832981988893)
        ·
          refine ⟨82020191302319187368245835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218720510139517832981988893 82020191302319187368245835)
          ·
            refine ⟨123030286953478781052368753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82020191302319187368245835 123030286953478781052368753)
            ·
              refine ⟨92272715215109085789276565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123030286953478781052368753 92272715215109085789276565)
              ·
                refine ⟨4325283525708238396372339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92272715215109085789276565 4325283525708238396372339)
                ·
                  refine ⟨6487925288562357594558509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4325283525708238396372339 6487925288562357594558509)
                  ·
                    refine ⟨2432971983210884097959441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6487925288562357594558509 2432971983210884097959441)
                    ·
                      refine ⟨1824728987408163073469581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432971983210884097959441 1824728987408163073469581)
                      ·
                        rfl

theorem cell23_3553647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 3, 2].length) (baseStart_3553647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553647 prefixEnd_3553647 := by exact prefixLift 3553647
  have htrace : WordTrace (prefixWord ++ tailWord_3553647) baseStart_3553647 baseEnd_3553647 := by
    simpa [prefixWord, tailWord_3553647, baseEnd_3553647] using wordTrace_append hprefix tailTrace_3553647
  have hstable : (prefixWord ++ tailWord_3553647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553647).length < 2 ^ (prefixWord ++ tailWord_3553647).sum := by decide
  have hdescent : baseEnd_3553647 < baseStart_3553647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553690 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3553690 : Nat := 118140960795 + 3553690 * 2 ^ 59
def prefixEnd_3553690 : Nat := 4983230072969 + 3 ^ 40 * 3553690 * 2
def baseEnd_3553690 : Nat := 1824751067076306405231883

theorem tailTrace_3553690 : CollatzResearch.WordTrace tailWord_3553690 prefixEnd_3553690 1824751067076306405231883 := by
  unfold tailWord_3553690
  simp only [CollatzResearch.WordTrace]
  refine ⟨32403430623898881694396631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86409148330397017851724349 32403430623898881694396631)
  ·
    refine ⟨48605145935848322541594947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32403430623898881694396631 48605145935848322541594947)
    ·
      refine ⟨72907718903772483812392421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48605145935848322541594947 72907718903772483812392421)
      ·
        refine ⟨13670197294457340714823579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72907718903772483812392421 13670197294457340714823579)
        ·
          refine ⟨20505295941686011072235369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13670197294457340714823579 20505295941686011072235369)
          ·
            refine ⟨15378971956264508304176527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20505295941686011072235369 15378971956264508304176527)
            ·
              refine ⟨23068457934396762456264791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15378971956264508304176527 23068457934396762456264791)
              ·
                refine ⟨34602686901595143684397187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23068457934396762456264791 34602686901595143684397187)
                ·
                  refine ⟨51904030352392715526595781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34602686901595143684397187 51904030352392715526595781)
                  ·
                    refine ⟨9732005691073634161236709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51904030352392715526595781 9732005691073634161236709)
                    ·
                      refine ⟨1824751067076306405231883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9732005691073634161236709 1824751067076306405231883)
                      ·
                        rfl

theorem cell23_3553690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3553690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553690 prefixEnd_3553690 := by exact prefixLift 3553690
  have htrace : WordTrace (prefixWord ++ tailWord_3553690) baseStart_3553690 baseEnd_3553690 := by
    simpa [prefixWord, tailWord_3553690, baseEnd_3553690] using wordTrace_append hprefix tailTrace_3553690
  have hstable : (prefixWord ++ tailWord_3553690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553690).length < 2 ^ (prefixWord ++ tailWord_3553690).sum := by decide
  have hdescent : baseEnd_3553690 < baseStart_3553690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553723 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 7]
def baseStart_3553723 : Nat := 118140960795 + 3553723 * 2 ^ 59
def prefixEnd_3553723 : Nat := 4983230072969 + 3 ^ 40 * 3553723 * 2
def baseEnd_3553723 : Nat := 1824768011937904776119231

theorem tailTrace_3553723 : CollatzResearch.WordTrace tailWord_3553723 prefixEnd_3553723 1824768011937904776119231 := by
  unfold tailWord_3553723
  simp only [CollatzResearch.WordTrace]
  refine ⟨129614926104475973413537823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86409950736317315609025215 129614926104475973413537823)
  ·
    refine ⟨194422389156713960120306735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129614926104475973413537823 194422389156713960120306735)
    ·
      refine ⟨291633583735070940180460103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194422389156713960120306735 291633583735070940180460103)
      ·
        refine ⟨437450375602606410270690155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291633583735070940180460103 437450375602606410270690155)
        ·
          refine ⟨656175563403909615406035233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437450375602606410270690155 656175563403909615406035233)
          ·
            refine ⟨492131672552932211554526425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656175563403909615406035233 492131672552932211554526425)
            ·
              refine ⟨369098754414699158665894819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492131672552932211554526425 369098754414699158665894819)
              ·
                refine ⟨553648131622048737998842229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369098754414699158665894819 553648131622048737998842229)
                ·
                  refine ⟨51904512339567069187391459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 553648131622048737998842229 51904512339567069187391459)
                  ·
                    refine ⟨77856768509350603781087189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51904512339567069187391459 77856768509350603781087189)
                    ·
                      refine ⟨1824768011937904776119231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77856768509350603781087189 1824768011937904776119231)
                      ·
                        rfl

theorem cell23_3553723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_3553723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553723 prefixEnd_3553723 := by exact prefixLift 3553723
  have htrace : WordTrace (prefixWord ++ tailWord_3553723) baseStart_3553723 baseEnd_3553723 := by
    simpa [prefixWord, tailWord_3553723, baseEnd_3553723] using wordTrace_append hprefix tailTrace_3553723
  have hstable : (prefixWord ++ tailWord_3553723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553723).length < 2 ^ (prefixWord ++ tailWord_3553723).sum := by decide
  have hdescent : baseEnd_3553723 < baseStart_3553723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553767 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3553767 : Nat := 118140960795 + 3553767 * 2 ^ 59
def prefixEnd_3553767 : Nat := 4983230072969 + 3 ^ 40 * 3553767 * 2
def baseEnd_3553767 : Nat := 1824790605086702603969029

theorem tailTrace_3553767 : CollatzResearch.WordTrace tailWord_3553767 prefixEnd_3553767 1824790605086702603969029 := by
  unfold tailWord_3553767
  simp only [CollatzResearch.WordTrace]
  refine ⟨129616530916316568928139555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86411020610877712618759703 129616530916316568928139555)
  ·
    refine ⟨194424796374474853392209333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129616530916316568928139555 194424796374474853392209333)
    ·
      refine ⟨18227324660107017505519625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194424796374474853392209333 18227324660107017505519625)
      ·
        refine ⟨13670493495080263129139719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18227324660107017505519625 13670493495080263129139719)
        ·
          refine ⟨20505740242620394693709579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13670493495080263129139719 20505740242620394693709579)
          ·
            refine ⟨30758610363930592040564369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20505740242620394693709579 30758610363930592040564369)
            ·
              refine ⟨23068957772947944030423277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30758610363930592040564369 23068957772947944030423277)
              ·
                refine ⟨8650859164855479011408729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23068957772947944030423277 8650859164855479011408729)
                ·
                  refine ⟨6488144373641609258556547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8650859164855479011408729 6488144373641609258556547)
                  ·
                    refine ⟨9732216560462413887834821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6488144373641609258556547 9732216560462413887834821)
                    ·
                      refine ⟨1824790605086702603969029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9732216560462413887834821 1824790605086702603969029)
                      ·
                        rfl

theorem cell23_3553767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3553767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553767 prefixEnd_3553767 := by exact prefixLift 3553767
  have htrace : WordTrace (prefixWord ++ tailWord_3553767) baseStart_3553767 baseEnd_3553767 := by
    simpa [prefixWord, tailWord_3553767, baseEnd_3553767] using wordTrace_append hprefix tailTrace_3553767
  have hstable : (prefixWord ++ tailWord_3553767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553767).length < 2 ^ (prefixWord ++ tailWord_3553767).sum := by decide
  have hdescent : baseEnd_3553767 < baseStart_3553767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553874 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_3553874 : Nat := 118140960795 + 3553874 * 2 ^ 59
def prefixEnd_3553874 : Nat := 4983230072969 + 3 ^ 40 * 3553874 * 2
def baseEnd_3553874 : Nat := 1824845547516733685331037

theorem tailTrace_3553874 : CollatzResearch.WordTrace tailWord_3553874 prefixEnd_3553874 1824845547516733685331037 := by
  unfold tailWord_3553874
  simp only [CollatzResearch.WordTrace]
  refine ⟨32405108381732231550571169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86413622351285950801523117 32405108381732231550571169)
  ·
    refine ⟨24303831286299173662928377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32405108381732231550571169 24303831286299173662928377)
    ·
      refine ⟨18227873464724380247196283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24303831286299173662928377 18227873464724380247196283)
      ·
        refine ⟨27341810197086570370794425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18227873464724380247196283 27341810197086570370794425)
        ·
          refine ⟨20506357647814927778095819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27341810197086570370794425 20506357647814927778095819)
          ·
            refine ⟨30759536471722391667143729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20506357647814927778095819 30759536471722391667143729)
            ·
              refine ⟨23069652353791793750357797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30759536471722391667143729 23069652353791793750357797)
              ·
                refine ⟨4325559816335961328192087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23069652353791793750357797 4325559816335961328192087)
                ·
                  refine ⟨6488339724503941992288131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4325559816335961328192087 6488339724503941992288131)
                  ·
                    refine ⟨9732509586755912988432197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6488339724503941992288131 9732509586755912988432197)
                    ·
                      refine ⟨1824845547516733685331037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9732509586755912988432197 1824845547516733685331037)
                      ·
                        rfl

theorem cell23_3553874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_3553874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553874 prefixEnd_3553874 := by exact prefixLift 3553874
  have htrace : WordTrace (prefixWord ++ tailWord_3553874) baseStart_3553874 baseEnd_3553874 := by
    simpa [prefixWord, tailWord_3553874, baseEnd_3553874] using wordTrace_append hprefix tailTrace_3553874
  have hstable : (prefixWord ++ tailWord_3553874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553874).length < 2 ^ (prefixWord ++ tailWord_3553874).sum := by decide
  have hdescent : baseEnd_3553874 < baseStart_3553874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553880 : List Nat := [2, 1, 2, 2, 1, 2, 2, 11]
def baseStart_3553880 : Nat := 118140960795 + 3553880 * 2 ^ 59
def prefixEnd_3553880 : Nat := 4983230072969 + 3 ^ 40 * 3553880 * 2
def baseEnd_3553880 : Nat := 67586986237061505994667

theorem tailTrace_3553880 : CollatzResearch.WordTrace tailWord_3553880 prefixEnd_3553880 67586986237061505994667 := by
  unfold tailWord_3553880
  simp only [CollatzResearch.WordTrace]
  refine ⟨64810326182453594613501547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86413768243271459484668729 64810326182453594613501547)
  ·
    refine ⟨97215489273680391920252321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64810326182453594613501547 97215489273680391920252321)
    ·
      refine ⟨72911616955260293940189241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97215489273680391920252321 72911616955260293940189241)
      ·
        refine ⟨54683712716445220455141931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72911616955260293940189241 54683712716445220455141931)
        ·
          refine ⟨82025569074667830682712897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54683712716445220455141931 82025569074667830682712897)
          ·
            refine ⟨61519176806000873012034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82025569074667830682712897 61519176806000873012034673)
            ·
              refine ⟨46139382604500654759026005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61519176806000873012034673 46139382604500654759026005)
              ·
                refine ⟨67586986237061505994667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 46139382604500654759026005 67586986237061505994667)
                ·
                  rfl

theorem cell23_3553880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 11].length) (baseStart_3553880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553880 prefixEnd_3553880 := by exact prefixLift 3553880
  have htrace : WordTrace (prefixWord ++ tailWord_3553880) baseStart_3553880 baseEnd_3553880 := by
    simpa [prefixWord, tailWord_3553880, baseEnd_3553880] using wordTrace_append hprefix tailTrace_3553880
  have hstable : (prefixWord ++ tailWord_3553880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553880).length < 2 ^ (prefixWord ++ tailWord_3553880).sum := by decide
  have hdescent : baseEnd_3553880 < baseStart_3553880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553901 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_3553901 : Nat := 118140960795 + 3553901 * 2 ^ 59
def prefixEnd_3553901 : Nat := 4983230072969 + 3 ^ 40 * 3553901 * 2
def baseEnd_3553901 : Nat := 608286470498135026564471

theorem tailTrace_3553901 : CollatzResearch.WordTrace tailWord_3553901 prefixEnd_3553901 608286470498135026564471 := by
  unfold tailWord_3553901
  simp only [CollatzResearch.WordTrace]
  refine ⟨129621418297831109813517557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86414278865220739875678371 129621418297831109813517557)
  ·
    refine ⟨12152007965421666545017271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129621418297831109813517557 12152007965421666545017271)
    ·
      refine ⟨18228011948132499817525907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12152007965421666545017271 18228011948132499817525907)
      ·
        refine ⟨27342017922198749726288861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18228011948132499817525907 27342017922198749726288861)
        ·
          refine ⟨10253256720824531147358323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27342017922198749726288861 10253256720824531147358323)
          ·
            refine ⟨15379885081236796721037485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10253256720824531147358323 15379885081236796721037485)
            ·
              refine ⟨5767456905463798770389057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15379885081236796721037485 5767456905463798770389057)
              ·
                refine ⟨4325592679097849077791793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5767456905463798770389057 4325592679097849077791793)
                ·
                  refine ⟨3244194509323386808343845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4325592679097849077791793 3244194509323386808343845)
                  ·
                    refine ⟨608286470498135026564471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3244194509323386808343845 608286470498135026564471)
                    ·
                      rfl

theorem cell23_3553901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_3553901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553901 prefixEnd_3553901 := by exact prefixLift 3553901
  have htrace : WordTrace (prefixWord ++ tailWord_3553901) baseStart_3553901 baseEnd_3553901 := by
    simpa [prefixWord, tailWord_3553901, baseEnd_3553901] using wordTrace_append hprefix tailTrace_3553901
  have hstable : (prefixWord ++ tailWord_3553901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553901).length < 2 ^ (prefixWord ++ tailWord_3553901).sum := by decide
  have hdescent : baseEnd_3553901 < baseStart_3553901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553959 : List Nat := [1, 1, 6, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3553959 : Nat := 118140960795 + 3553959 * 2 ^ 59
def prefixEnd_3553959 : Nat := 4983230072969 + 3 ^ 40 * 3553959 * 2
def baseEnd_3553959 : Nat := 1824889193372365852768147

theorem tailTrace_3553959 : CollatzResearch.WordTrace tailWord_3553959 prefixEnd_3553959 1824889193372365852768147 := by
  unfold tailWord_3553959
  simp only [CollatzResearch.WordTrace]
  refine ⟨129623533731620985719128931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86415689154413990479419287 129623533731620985719128931)
  ·
    refine ⟨194435300597431478578693397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129623533731620985719128931 194435300597431478578693397)
    ·
      refine ⟨9114154715504600558376253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 194435300597431478578693397 9114154715504600558376253)
      ·
        refine ⟨3417808018314225209391095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9114154715504600558376253 3417808018314225209391095)
        ·
          refine ⟨5126712027471337814086643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3417808018314225209391095 5126712027471337814086643)
          ·
            refine ⟨7690068041207006721129965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126712027471337814086643 7690068041207006721129965)
            ·
              refine ⟨2883775515452627520423737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7690068041207006721129965 2883775515452627520423737)
              ·
                refine ⟨2162831636589470640317803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2883775515452627520423737 2162831636589470640317803)
                ·
                  refine ⟨3244247454884205960476705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162831636589470640317803 3244247454884205960476705)
                  ·
                    refine ⟨2433185591163154470357529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3244247454884205960476705 2433185591163154470357529)
                    ·
                      refine ⟨1824889193372365852768147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2433185591163154470357529 1824889193372365852768147)
                      ·
                        rfl

theorem cell23_3553959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3553959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553959 prefixEnd_3553959 := by exact prefixLift 3553959
  have htrace : WordTrace (prefixWord ++ tailWord_3553959) baseStart_3553959 baseEnd_3553959 := by
    simpa [prefixWord, tailWord_3553959, baseEnd_3553959] using wordTrace_append hprefix tailTrace_3553959
  have hstable : (prefixWord ++ tailWord_3553959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553959).length < 2 ^ (prefixWord ++ tailWord_3553959).sum := by decide
  have hdescent : baseEnd_3553959 < baseStart_3553959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553975 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 2, 1, 3]
def baseStart_3553975 : Nat := 118140960795 + 3553975 * 2 ^ 59
def prefixEnd_3553975 : Nat := 4983230072969 + 3 ^ 40 * 3553975 * 2
def baseEnd_3553975 : Nat := 1824897409062837790168073

theorem tailTrace_3553975 : CollatzResearch.WordTrace tailWord_3553975 prefixEnd_3553975 1824897409062837790168073 := by
  unfold tailWord_3553975
  simp only [CollatzResearch.WordTrace]
  refine ⟨129624117299563020451711379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86416078199708680301140919 129624117299563020451711379)
  ·
    refine ⟨194436175949344530677567069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129624117299563020451711379 194436175949344530677567069)
    ·
      refine ⟨72913565981004199004087651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194436175949344530677567069 72913565981004199004087651)
      ·
        refine ⟨109370348971506298506131477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72913565981004199004087651 109370348971506298506131477)
        ·
          refine ⟨5126735108039357742474913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109370348971506298506131477 5126735108039357742474913)
          ·
            refine ⟨3845051331029518306856185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5126735108039357742474913 3845051331029518306856185)
            ·
              refine ⟨2883788498272138730142139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3845051331029518306856185 2883788498272138730142139)
              ·
                refine ⟨4325682747408208095213209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2883788498272138730142139 4325682747408208095213209)
                ·
                  refine ⟨3244262060556156071409907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4325682747408208095213209 3244262060556156071409907)
                  ·
                    refine ⟨4866393090834234107114861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3244262060556156071409907 4866393090834234107114861)
                    ·
                      refine ⟨1824897409062837790168073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4866393090834234107114861 1824897409062837790168073)
                      ·
                        rfl

theorem cell23_3553975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_3553975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553975 prefixEnd_3553975 := by exact prefixLift 3553975
  have htrace : WordTrace (prefixWord ++ tailWord_3553975) baseStart_3553975 baseEnd_3553975 := by
    simpa [prefixWord, tailWord_3553975, baseEnd_3553975] using wordTrace_append hprefix tailTrace_3553975
  have hstable : (prefixWord ++ tailWord_3553975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553975).length < 2 ^ (prefixWord ++ tailWord_3553975).sum := by decide
  have hdescent : baseEnd_3553975 < baseStart_3553975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553977 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3553977 : Nat := 118140960795 + 3553977 * 2 ^ 59
def prefixEnd_3553977 : Nat := 4983230072969 + 3 ^ 40 * 3553977 * 2
def baseEnd_3553977 : Nat := 1824898436024146782343063

theorem tailTrace_3553977 : CollatzResearch.WordTrace tailWord_3553977 prefixEnd_3553977 1824898436024146782343063 := by
  unfold tailWord_3553977
  simp only [CollatzResearch.WordTrace]
  refine ⟨129624190245555774793284185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86416126830370516528856123 129624190245555774793284185)
  ·
    refine ⟨97218142684166831094963139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129624190245555774793284185 97218142684166831094963139)
    ·
      refine ⟨145827214026250246642444709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97218142684166831094963139 145827214026250246642444709)
      ·
        refine ⟨27342602629921921245458383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145827214026250246642444709 27342602629921921245458383)
        ·
          refine ⟨41013903944882881868187575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27342602629921921245458383 41013903944882881868187575)
          ·
            refine ⟨61520855917324322802281363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41013903944882881868187575 61520855917324322802281363)
            ·
              refine ⟨92281283875986484203422045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61520855917324322802281363 92281283875986484203422045)
              ·
                refine ⟨34605481453494931576283267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92281283875986484203422045 34605481453494931576283267)
                ·
                  refine ⟨51908222180242397364424901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34605481453494931576283267 51908222180242397364424901)
                  ·
                    refine ⟨9732791658795449505829669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51908222180242397364424901 9732791658795449505829669)
                    ·
                      refine ⟨1824898436024146782343063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9732791658795449505829669 1824898436024146782343063)
                      ·
                        rfl

theorem cell23_3553977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3553977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553977 prefixEnd_3553977 := by exact prefixLift 3553977
  have htrace : WordTrace (prefixWord ++ tailWord_3553977) baseStart_3553977 baseEnd_3553977 := by
    simpa [prefixWord, tailWord_3553977, baseEnd_3553977] using wordTrace_append hprefix tailTrace_3553977
  have hstable : (prefixWord ++ tailWord_3553977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553977).length < 2 ^ (prefixWord ++ tailWord_3553977).sum := by decide
  have hdescent : baseEnd_3553977 < baseStart_3553977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553985 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3553985 : Nat := 118140960795 + 3553985 * 2 ^ 59
def prefixEnd_3553985 : Nat := 4983230072969 + 3 ^ 40 * 3553985 * 2
def baseEnd_3553985 : Nat := 1824902543869382751043027

theorem tailTrace_3553985 : CollatzResearch.WordTrace tailWord_3553985 prefixEnd_3553985 1824902543869382751043027 := by
  unfold tailWord_3553985
  simp only [CollatzResearch.WordTrace]
  refine ⟨129624482029526792159575409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86416321353017861439716939 129624482029526792159575409)
  ·
    refine ⟨97218361522145094119681557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129624482029526792159575409 97218361522145094119681557)
    ·
      refine ⟨4557110696350551286860073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97218361522145094119681557 4557110696350551286860073)
      ·
        refine ⟨3417833022262913465145055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4557110696350551286860073 3417833022262913465145055)
        ·
          refine ⟨5126749533394370197717583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3417833022262913465145055 5126749533394370197717583)
          ·
            refine ⟨7690124300091555296576375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126749533394370197717583 7690124300091555296576375)
            ·
              refine ⟨11535186450137332944864563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690124300091555296576375 11535186450137332944864563)
              ·
                refine ⟨17302779675205999417296845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11535186450137332944864563 17302779675205999417296845)
                ·
                  refine ⟨6488542378202249781486317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17302779675205999417296845 6488542378202249781486317)
                  ·
                    refine ⟨2433203391825843668057369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6488542378202249781486317 2433203391825843668057369)
                    ·
                      refine ⟨1824902543869382751043027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2433203391825843668057369 1824902543869382751043027)
                      ·
                        rfl

theorem cell23_3553985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3553985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553985 prefixEnd_3553985 := by exact prefixLift 3553985
  have htrace : WordTrace (prefixWord ++ tailWord_3553985) baseStart_3553985 baseEnd_3553985 := by
    simpa [prefixWord, tailWord_3553985, baseEnd_3553985] using wordTrace_append hprefix tailTrace_3553985
  have hstable : (prefixWord ++ tailWord_3553985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553985).length < 2 ^ (prefixWord ++ tailWord_3553985).sum := by decide
  have hdescent : baseEnd_3553985 < baseStart_3553985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554021 : List Nat := [1, 3, 1, 4, 1, 3, 1, 4, 5]
def baseStart_3554021 : Nat := 118140960795 + 3554021 * 2 ^ 59
def prefixEnd_3554021 : Nat := 4983230072969 + 3 ^ 40 * 3554021 * 2
def baseEnd_3554021 : Nat := 202769003241438290021429

theorem tailTrace_3554021 : CollatzResearch.WordTrace tailWord_3554021 prefixEnd_3554021 202769003241438290021429 := by
  unfold tailWord_3554021
  simp only [CollatzResearch.WordTrace]
  refine ⟨129625795057396370307885917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86417196704930913538590611 129625795057396370307885917)
  ·
    refine ⟨48609673146523638865457219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129625795057396370307885917 48609673146523638865457219)
    ·
      refine ⟨72914509719785458298185829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48609673146523638865457219 72914509719785458298185829)
      ·
        refine ⟨13671470572459773430909843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72914509719785458298185829 13671470572459773430909843)
        ·
          refine ⟨20507205858689660146364765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13671470572459773430909843 20507205858689660146364765)
          ·
            refine ⟨7690202197008622554886787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20507205858689660146364765 7690202197008622554886787)
            ·
              refine ⟨11535303295512933832330181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690202197008622554886787 11535303295512933832330181)
              ·
                refine ⟨2162869367908675093561909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11535303295512933832330181 2162869367908675093561909)
                ·
                  refine ⟨202769003241438290021429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2162869367908675093561909 202769003241438290021429)
                  ·
                    rfl

theorem cell23_3554021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_3554021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554021 prefixEnd_3554021 := by exact prefixLift 3554021
  have htrace : WordTrace (prefixWord ++ tailWord_3554021) baseStart_3554021 baseEnd_3554021 := by
    simpa [prefixWord, tailWord_3554021, baseEnd_3554021] using wordTrace_append hprefix tailTrace_3554021
  have hstable : (prefixWord ++ tailWord_3554021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554021).length < 2 ^ (prefixWord ++ tailWord_3554021).sum := by decide
  have hdescent : baseEnd_3554021 < baseStart_3554021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554067 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 6]
def baseStart_3554067 : Nat := 118140960795 + 3554067 * 2 ^ 59
def prefixEnd_3554067 : Nat := 4983230072969 + 3 ^ 40 * 3554067 * 2
def baseEnd_3554067 : Nat := 1824944649283051430217649

theorem tailTrace_3554067 : CollatzResearch.WordTrace tailWord_3554067 prefixEnd_3554067 1824944649283051430217649 := by
  unfold tailWord_3554067
  simp only [CollatzResearch.WordTrace]
  refine ⟨129627472815229720164060455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86418315210153146776040303 129627472815229720164060455)
  ·
    refine ⟨194441209222844580246090683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129627472815229720164060455 194441209222844580246090683)
    ·
      refine ⟨291661813834266870369136025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194441209222844580246090683 291661813834266870369136025)
      ·
        refine ⟨218746360375700152776852019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291661813834266870369136025 218746360375700152776852019)
        ·
          refine ⟨328119540563550229165278029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218746360375700152776852019 328119540563550229165278029)
          ·
            refine ⟨123044827711331335936979261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328119540563550229165278029 123044827711331335936979261)
            ·
              refine ⟨46141810391749250976367223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123044827711331335936979261 46141810391749250976367223)
              ·
                refine ⟨69212715587623876464550835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46141810391749250976367223 69212715587623876464550835)
                ·
                  refine ⟨103819073381435814696826253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69212715587623876464550835 103819073381435814696826253)
                  ·
                    refine ⟨38932152518038430511309845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103819073381435814696826253 38932152518038430511309845)
                    ·
                      refine ⟨1824944649283051430217649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38932152518038430511309845 1824944649283051430217649)
                      ·
                        rfl

theorem cell23_3554067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_3554067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554067 prefixEnd_3554067 := by exact prefixLift 3554067
  have htrace : WordTrace (prefixWord ++ tailWord_3554067) baseStart_3554067 baseEnd_3554067 := by
    simpa [prefixWord, tailWord_3554067, baseEnd_3554067] using wordTrace_append hprefix tailTrace_3554067
  have hstable : (prefixWord ++ tailWord_3554067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554067).length < 2 ^ (prefixWord ++ tailWord_3554067).sum := by decide
  have hdescent : baseEnd_3554067 < baseStart_3554067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554081 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 3, 4]
def baseStart_3554081 : Nat := 118140960795 + 3554081 * 2 ^ 59
def prefixEnd_3554081 : Nat := 4983230072969 + 3 ^ 40 * 3554081 * 2
def baseEnd_3554081 : Nat := 608317279337404791814195

theorem tailTrace_3554081 : CollatzResearch.WordTrace tailWord_3554081 prefixEnd_3554081 608317279337404791814195 := by
  unfold tailWord_3554081
  simp only [CollatzResearch.WordTrace]
  refine ⟨129627983437179000555070097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86418655624786000370046731 129627983437179000555070097)
  ·
    refine ⟨97220987577884250416302573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129627983437179000555070097 97220987577884250416302573)
    ·
      refine ⟨36457870341706593906113465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97220987577884250416302573 36457870341706593906113465)
      ·
        refine ⟨27343402756279945429585099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36457870341706593906113465 27343402756279945429585099)
        ·
          refine ⟨41015104134419918144377649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27343402756279945429585099 41015104134419918144377649)
          ·
            refine ⟨30761328100814938608283237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41015104134419918144377649 30761328100814938608283237)
            ·
              refine ⟨5767749018902800989053107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30761328100814938608283237 5767749018902800989053107)
              ·
                refine ⟨8651623528354201483579661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767749018902800989053107 8651623528354201483579661)
                ·
                  refine ⟨3244358823132825556342373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8651623528354201483579661 3244358823132825556342373)
                  ·
                    refine ⟨608317279337404791814195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3244358823132825556342373 608317279337404791814195)
                    ·
                      rfl

theorem cell23_3554081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_3554081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554081 prefixEnd_3554081 := by exact prefixLift 3554081
  have htrace : WordTrace (prefixWord ++ tailWord_3554081) baseStart_3554081 baseEnd_3554081 := by
    simpa [prefixWord, tailWord_3554081, baseEnd_3554081] using wordTrace_append hprefix tailTrace_3554081
  have hstable : (prefixWord ++ tailWord_3554081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554081).length < 2 ^ (prefixWord ++ tailWord_3554081).sum := by decide
  have hdescent : baseEnd_3554081 < baseStart_3554081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554104 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 2, 5, 3]
def baseStart_3554104 : Nat := 118140960795 + 3554104 * 2 ^ 59
def prefixEnd_3554104 : Nat := 4983230072969 + 3 ^ 40 * 3554104 * 2
def baseEnd_3554104 : Nat := 1824963648067267785454979

theorem tailTrace_3554104 : CollatzResearch.WordTrace tailWord_3554104 prefixEnd_3554104 1824963648067267785454979 := by
  unfold tailWord_3554104
  simp only [CollatzResearch.WordTrace]
  refine ⟨64814411158047837741578683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86419214877397116988771577 64814411158047837741578683)
  ·
    refine ⟨97221616737071756612368025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64814411158047837741578683 97221616737071756612368025)
    ·
      refine ⟨72916212552803817459276019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97221616737071756612368025 72916212552803817459276019)
      ·
        refine ⟨109374318829205726188914029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72916212552803817459276019 109374318829205726188914029)
        ·
          refine ⟨41015369560952147320842761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109374318829205726188914029 41015369560952147320842761)
          ·
            refine ⟨30761527170714110490632071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41015369560952147320842761 30761527170714110490632071)
            ·
              refine ⟨46142290756071165735948107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30761527170714110490632071 46142290756071165735948107)
              ·
                refine ⟨69213436134106748603922161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46142290756071165735948107 69213436134106748603922161)
                ·
                  refine ⟨51910077100580061452941621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69213436134106748603922161 51910077100580061452941621)
                  ·
                    refine ⟨4866569728179380761213277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51910077100580061452941621 4866569728179380761213277)
                    ·
                      refine ⟨1824963648067267785454979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4866569728179380761213277 1824963648067267785454979)
                      ·
                        rfl

theorem cell23_3554104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_3554104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554104 prefixEnd_3554104 := by exact prefixLift 3554104
  have htrace : WordTrace (prefixWord ++ tailWord_3554104) baseStart_3554104 baseEnd_3554104 := by
    simpa [prefixWord, tailWord_3554104, baseEnd_3554104] using wordTrace_append hprefix tailTrace_3554104
  have hstable : (prefixWord ++ tailWord_3554104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554104).length < 2 ^ (prefixWord ++ tailWord_3554104).sum := by decide
  have hdescent : baseEnd_3554104 < baseStart_3554104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554125 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3554125 : Nat := 118140960795 + 3554125 * 2 ^ 59
def prefixEnd_3554125 : Nat := 4983230072969 + 3 ^ 40 * 3554125 * 2
def baseEnd_3554125 : Nat := 1824974431161012203292383

theorem tailTrace_3554125 : CollatzResearch.WordTrace tailWord_3554125 prefixEnd_3554125 1824974431161012203292383 := by
  unfold tailWord_3554125
  simp only [CollatzResearch.WordTrace]
  refine ⟨129629588249019596069671829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86419725499346397379781219 129629588249019596069671829)
  ·
    refine ⟨6076386949172793565765867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129629588249019596069671829 6076386949172793565765867)
    ·
      refine ⟨9114580423759190348648801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6076386949172793565765867 9114580423759190348648801)
      ·
        refine ⟨6835935317819392761486601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9114580423759190348648801 6835935317819392761486601)
        ·
          refine ⟨5126951488364544571114951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6835935317819392761486601 5126951488364544571114951)
          ·
            refine ⟨7690427232546816856672427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126951488364544571114951 7690427232546816856672427)
            ·
              refine ⟨11535640848820225285008641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690427232546816856672427 11535640848820225285008641)
              ·
                refine ⟨8651730636615168963756481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11535640848820225285008641 8651730636615168963756481)
                ·
                  refine ⟨6488797977461376722817361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8651730636615168963756481 6488797977461376722817361)
                  ·
                    refine ⟨4866598483096032542113021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6488797977461376722817361 4866598483096032542113021)
                    ·
                      refine ⟨1824974431161012203292383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4866598483096032542113021 1824974431161012203292383)
                      ·
                        rfl

theorem cell23_3554125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3554125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554125 prefixEnd_3554125 := by exact prefixLift 3554125
  have htrace : WordTrace (prefixWord ++ tailWord_3554125) baseStart_3554125 baseEnd_3554125 := by
    simpa [prefixWord, tailWord_3554125, baseEnd_3554125] using wordTrace_append hprefix tailTrace_3554125
  have hstable : (prefixWord ++ tailWord_3554125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554125).length < 2 ^ (prefixWord ++ tailWord_3554125).sum := by decide
  have hdescent : baseEnd_3554125 < baseStart_3554125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554132 : List Nat := [2, 4, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_3554132 : Nat := 118140960795 + 3554132 * 2 ^ 59
def prefixEnd_3554132 : Nat := 4983230072969 + 3 ^ 40 * 3554132 * 2
def baseEnd_3554132 : Nat := 608326008508531225301617

theorem tailTrace_3554132 : CollatzResearch.WordTrace tailWord_3554132 prefixEnd_3554132 608326008508531225301617 := by
  unfold tailWord_3554132
  simp only [CollatzResearch.WordTrace]
  refine ⟨64814921779997118132588325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86419895706662824176784433 64814921779997118132588325)
  ·
    refine ⟨12152797833749459649860311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64814921779997118132588325 12152797833749459649860311)
    ·
      refine ⟨18229196750624189474790467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12152797833749459649860311 18229196750624189474790467)
      ·
        refine ⟨27343795125936284212185701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18229196750624189474790467 27343795125936284212185701)
        ·
          refine ⟨5126961586113053289784819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27343795125936284212185701 5126961586113053289784819)
          ·
            refine ⟨7690442379169579934677229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126961586113053289784819 7690442379169579934677229)
            ·
              refine ⟨2883915892188592475503961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7690442379169579934677229 2883915892188592475503961)
              ·
                refine ⟨2162936919141444356627971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2883915892188592475503961 2162936919141444356627971)
                ·
                  refine ⟨3244405378712166534941957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162936919141444356627971 3244405378712166534941957)
                  ·
                    refine ⟨608326008508531225301617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3244405378712166534941957 608326008508531225301617)
                    ·
                      rfl

theorem cell23_3554132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_3554132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554132 prefixEnd_3554132 := by exact prefixLift 3554132
  have htrace : WordTrace (prefixWord ++ tailWord_3554132) baseStart_3554132 baseEnd_3554132 := by
    simpa [prefixWord, tailWord_3554132, baseEnd_3554132] using wordTrace_append hprefix tailTrace_3554132
  have hstable : (prefixWord ++ tailWord_3554132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554132).length < 2 ^ (prefixWord ++ tailWord_3554132).sum := by decide
  have hdescent : baseEnd_3554132 < baseStart_3554132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554138 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3]
def baseStart_3554138 : Nat := 118140960795 + 3554138 * 2 ^ 59
def prefixEnd_3554138 : Nat := 4983230072969 + 3 ^ 40 * 3554138 * 2
def baseEnd_3554138 : Nat := 1824981106409520652429823

theorem tailTrace_3554138 : CollatzResearch.WordTrace tailWord_3554138 prefixEnd_3554138 1824981106409520652429823 := by
  unfold tailWord_3554138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32407515599493124822473767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86420041598648332859930045 32407515599493124822473767)
  ·
    refine ⟨48611273399239687233710651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32407515599493124822473767 48611273399239687233710651)
    ·
      refine ⟨72916910098859530850565977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48611273399239687233710651 72916910098859530850565977)
      ·
        refine ⟨54687682574144648137924483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72916910098859530850565977 54687682574144648137924483)
        ·
          refine ⟨82031523861216972206886725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54687682574144648137924483 82031523861216972206886725)
          ·
            refine ⟨15380910723978182288791261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82031523861216972206886725 15380910723978182288791261)
            ·
              refine ⟨5767841521491818358296723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15380910723978182288791261 5767841521491818358296723)
              ·
                refine ⟨8651762282237727537445085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767841521491818358296723 8651762282237727537445085)
                ·
                  refine ⟨3244410855839147826541907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8651762282237727537445085 3244410855839147826541907)
                  ·
                    refine ⟨4866616283758721739812861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3244410855839147826541907 4866616283758721739812861)
                    ·
                      refine ⟨1824981106409520652429823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4866616283758721739812861 1824981106409520652429823)
                      ·
                        rfl

theorem cell23_3554138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_3554138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554138 prefixEnd_3554138 := by exact prefixLift 3554138
  have htrace : WordTrace (prefixWord ++ tailWord_3554138) baseStart_3554138 baseEnd_3554138 := by
    simpa [prefixWord, tailWord_3554138, baseEnd_3554138] using wordTrace_append hprefix tailTrace_3554138
  have hstable : (prefixWord ++ tailWord_3554138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554138).length < 2 ^ (prefixWord ++ tailWord_3554138).sum := by decide
  have hdescent : baseEnd_3554138 < baseStart_3554138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554158 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_3554158 : Nat := 118140960795 + 3554158 * 2 ^ 59
def prefixEnd_3554158 : Nat := 4983230072969 + 3 ^ 40 * 3554158 * 2
def baseEnd_3554158 : Nat := 608330458674203524726577

theorem tailTrace_3554158 : CollatzResearch.WordTrace tailWord_3554158 prefixEnd_3554158 608330458674203524726577 := by
  unfold tailWord_3554158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16203848982237505338202891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86420527905266695137082085 16203848982237505338202891)
  ·
    refine ⟨24305773473356258007304337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16203848982237505338202891 24305773473356258007304337)
    ·
      refine ⟨18229330105017193505478253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24305773473356258007304337 18229330105017193505478253)
      ·
        refine ⟨6835998789381447564554345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18229330105017193505478253 6835998789381447564554345)
        ·
          refine ⟨5126999092036085673415759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6835998789381447564554345 5126999092036085673415759)
          ·
            refine ⟨7690498638054128510123639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126999092036085673415759 7690498638054128510123639)
            ·
              refine ⟨11535747957081192765185459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690498638054128510123639 11535747957081192765185459)
              ·
                refine ⟨17303621935621789147778189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11535747957081192765185459 17303621935621789147778189)
                ·
                  refine ⟨6488858225858170930416821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17303621935621789147778189 6488858225858170930416821)
                  ·
                    refine ⟨608330458674203524726577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6488858225858170930416821 608330458674203524726577)
                    ·
                      rfl

theorem cell23_3554158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_3554158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554158 prefixEnd_3554158 := by exact prefixLift 3554158
  have htrace : WordTrace (prefixWord ++ tailWord_3554158) baseStart_3554158 baseEnd_3554158 := by
    simpa [prefixWord, tailWord_3554158, baseEnd_3554158] using wordTrace_append hprefix tailTrace_3554158
  have hstable : (prefixWord ++ tailWord_3554158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554158).length < 2 ^ (prefixWord ++ tailWord_3554158).sum := by decide
  have hdescent : baseEnd_3554158 < baseStart_3554158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554161 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_3554161 : Nat := 118140960795 + 3554161 * 2 ^ 59
def prefixEnd_3554161 : Nat := 4983230072969 + 3 ^ 40 * 3554161 * 2
def baseEnd_3554161 : Nat := 1824992916464574062442217

theorem tailTrace_3554161 : CollatzResearch.WordTrace tailWord_3554161 prefixEnd_3554161 1824992916464574062442217 := by
  unfold tailWord_3554161
  simp only [CollatzResearch.WordTrace]
  refine ⟨129630901276889174217982337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86420600851259449478654891 129630901276889174217982337)
  ·
    refine ⟨97223175957666880663486753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129630901276889174217982337 97223175957666880663486753)
    ·
      refine ⟨72917381968250160497615065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97223175957666880663486753 72917381968250160497615065)
      ·
        refine ⟨54688036476187620373211299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72917381968250160497615065 54688036476187620373211299)
        ·
          refine ⟨82032054714281430559816949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54688036476187620373211299 82032054714281430559816949)
          ·
            refine ⟨7690505129463884114982839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82032054714281430559816949 7690505129463884114982839)
            ·
              refine ⟨11535757694195826172474259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690505129463884114982839 11535757694195826172474259)
              ·
                refine ⟨17303636541293739258711389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11535757694195826172474259 17303636541293739258711389)
                ·
                  refine ⟨6488863702985152222016771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17303636541293739258711389 6488863702985152222016771)
                  ·
                    refine ⟨9733295554477728333025157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6488863702985152222016771 9733295554477728333025157)
                    ·
                      refine ⟨1824992916464574062442217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9733295554477728333025157 1824992916464574062442217)
                      ·
                        rfl

theorem cell23_3554161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_3554161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554161 prefixEnd_3554161 := by exact prefixLift 3554161
  have htrace : WordTrace (prefixWord ++ tailWord_3554161) baseStart_3554161 baseEnd_3554161 := by
    simpa [prefixWord, tailWord_3554161, baseEnd_3554161] using wordTrace_append hprefix tailTrace_3554161
  have hstable : (prefixWord ++ tailWord_3554161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554161).length < 2 ^ (prefixWord ++ tailWord_3554161).sum := by decide
  have hdescent : baseEnd_3554161 < baseStart_3554161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554165 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_3554165 : Nat := 118140960795 + 3554165 * 2 ^ 59
def prefixEnd_3554165 : Nat := 4983230072969 + 3 ^ 40 * 3554165 * 2
def baseEnd_3554165 : Nat := 1824994970387192046792199

theorem tailTrace_3554165 : CollatzResearch.WordTrace tailWord_3554165 prefixEnd_3554165 1824994970387192046792199 := by
  unfold tailWord_3554165
  simp only [CollatzResearch.WordTrace]
  refine ⟨129631047168874682901127949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86420698112583121934085299 129631047168874682901127949)
  ·
    refine ⟨48611642688328006087922981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129631047168874682901127949 48611642688328006087922981)
    ·
      refine ⟨9114683004061501141485559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48611642688328006087922981 9114683004061501141485559)
      ·
        refine ⟨13672024506092251712228339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9114683004061501141485559 13672024506092251712228339)
        ·
          refine ⟨20508036759138377568342509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13672024506092251712228339 20508036759138377568342509)
          ·
            refine ⟨7690513784676891588128441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20508036759138377568342509 7690513784676891588128441)
            ·
              refine ⟨5767885338507668691096331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7690513784676891588128441 5767885338507668691096331)
              ·
                refine ⟨8651828007761503036644497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767885338507668691096331 8651828007761503036644497)
                ·
                  refine ⟨6488871005821127277483373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8651828007761503036644497 6488871005821127277483373)
                  ·
                    refine ⟨2433326627182922729056265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6488871005821127277483373 2433326627182922729056265)
                    ·
                      refine ⟨1824994970387192046792199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2433326627182922729056265 1824994970387192046792199)
                      ·
                        rfl

theorem cell23_3554165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_3554165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554165 prefixEnd_3554165 := by exact prefixLift 3554165
  have htrace : WordTrace (prefixWord ++ tailWord_3554165) baseStart_3554165 baseEnd_3554165 := by
    simpa [prefixWord, tailWord_3554165, baseEnd_3554165] using wordTrace_append hprefix tailTrace_3554165
  have hstable : (prefixWord ++ tailWord_3554165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554165).length < 2 ^ (prefixWord ++ tailWord_3554165).sum := by decide
  have hdescent : baseEnd_3554165 < baseStart_3554165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554181 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 5]
def baseStart_3554181 : Nat := 118140960795 + 3554181 * 2 ^ 59
def prefixEnd_3554181 : Nat := 4983230072969 + 3 ^ 40 * 3554181 * 2
def baseEnd_3554181 : Nat := 1825003186077663984192125

theorem tailTrace_3554181 : CollatzResearch.WordTrace tailWord_3554181 prefixEnd_3554181 1825003186077663984192125 := by
  unfold tailWord_3554181
  simp only [CollatzResearch.WordTrace]
  refine ⟨129631630736816717633710397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86421087157877811755806931 129631630736816717633710397)
  ·
    refine ⟨48611861526306269112641399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129631630736816717633710397 48611861526306269112641399)
    ·
      refine ⟨72917792289459403668962099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48611861526306269112641399 72917792289459403668962099)
      ·
        refine ⟨109376688434189105503443149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72917792289459403668962099 109376688434189105503443149)
        ·
          refine ⟨41016258162820914563791181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109376688434189105503443149 41016258162820914563791181)
          ·
            refine ⟨15381096811057842961421693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41016258162820914563791181 15381096811057842961421693)
            ·
              refine ⟨5767911304146691110533135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15381096811057842961421693 5767911304146691110533135)
              ·
                refine ⟨8651866956220036665799703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767911304146691110533135 8651866956220036665799703)
                ·
                  refine ⟨12977800434330054998699555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8651866956220036665799703 12977800434330054998699555)
                  ·
                    refine ⟨19466700651495082498049333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12977800434330054998699555 19466700651495082498049333)
                    ·
                      refine ⟨1825003186077663984192125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19466700651495082498049333 1825003186077663984192125)
                      ·
                        rfl

theorem cell23_3554181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_3554181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554181 prefixEnd_3554181 := by exact prefixLift 3554181
  have htrace : WordTrace (prefixWord ++ tailWord_3554181) baseStart_3554181 baseEnd_3554181 := by
    simpa [prefixWord, tailWord_3554181, baseEnd_3554181] using wordTrace_append hprefix tailTrace_3554181
  have hstable : (prefixWord ++ tailWord_3554181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554181).length < 2 ^ (prefixWord ++ tailWord_3554181).sum := by decide
  have hdescent : baseEnd_3554181 < baseStart_3554181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554184 : List Nat := [2, 1, 3, 3, 2, 12]
def baseStart_3554184 : Nat := 118140960795 + 3554184 * 2 ^ 59
def prefixEnd_3554184 : Nat := 4983230072969 + 3 ^ 40 * 3554184 * 2
def baseEnd_3554184 : Nat := 7510307516541676841377

theorem tailTrace_3554184 : CollatzResearch.WordTrace tailWord_3554184 prefixEnd_3554184 7510307516541676841377 := by
  unfold tailWord_3554184
  simp only [CollatzResearch.WordTrace]
  refine ⟨64815870077902924573034803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86421160103870566097379737 64815870077902924573034803)
  ·
    refine ⟨97223805116854386859552205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64815870077902924573034803 97223805116854386859552205)
    ·
      refine ⟨36458926918820395072332077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97223805116854386859552205 36458926918820395072332077)
      ·
        refine ⟨13672097594557648152124529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36458926918820395072332077 13672097594557648152124529)
        ·
          refine ⟨10254073195918236114093397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13672097594557648152124529 10254073195918236114093397)
          ·
            refine ⟨7510307516541676841377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10254073195918236114093397 7510307516541676841377)
            ·
              rfl

theorem cell23_3554184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 12].length) (baseStart_3554184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554184 prefixEnd_3554184 := by exact prefixLift 3554184
  have htrace : WordTrace (prefixWord ++ tailWord_3554184) baseStart_3554184 baseEnd_3554184 := by
    simpa [prefixWord, tailWord_3554184, baseEnd_3554184] using wordTrace_append hprefix tailTrace_3554184
  have hstable : (prefixWord ++ tailWord_3554184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554184).length < 2 ^ (prefixWord ++ tailWord_3554184).sum := by decide
  have hdescent : baseEnd_3554184 < baseStart_3554184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554211 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 3]
def baseStart_3554211 : Nat := 118140960795 + 3554211 * 2 ^ 59
def prefixEnd_3554211 : Nat := 4983230072969 + 3 ^ 40 * 3554211 * 2
def baseEnd_3554211 : Nat := 1825018590497298866816987

theorem tailTrace_3554211 : CollatzResearch.WordTrace tailWord_3554211 prefixEnd_3554211 1825018590497298866816987 := by
  unfold tailWord_3554211
  simp only [CollatzResearch.WordTrace]
  refine ⟨129632724926708032757302487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86421816617805355171534991 129632724926708032757302487)
  ·
    refine ⟨194449087390062049135953731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129632724926708032757302487 194449087390062049135953731)
    ·
      refine ⟨291673631085093073703930597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194449087390062049135953731 291673631085093073703930597)
      ·
        refine ⟨54688805828454951319486987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291673631085093073703930597 54688805828454951319486987)
        ·
          refine ⟨82033208742682426979230481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54688805828454951319486987 82033208742682426979230481)
          ·
            refine ⟨61524906557011820234422861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82033208742682426979230481 61524906557011820234422861)
            ·
              refine ⟨23071839958879432587908573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61524906557011820234422861 23071839958879432587908573)
              ·
                refine ⟨8651939984579787220465715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23071839958879432587908573 8651939984579787220465715)
                ·
                  refine ⟨12977909976869680830698573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8651939984579787220465715 12977909976869680830698573)
                  ·
                    refine ⟨4866716241326130311511965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12977909976869680830698573 4866716241326130311511965)
                    ·
                      refine ⟨1825018590497298866816987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4866716241326130311511965 1825018590497298866816987)
                      ·
                        rfl

theorem cell23_3554211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_3554211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554211 prefixEnd_3554211 := by exact prefixLift 3554211
  have htrace : WordTrace (prefixWord ++ tailWord_3554211) baseStart_3554211 baseEnd_3554211 := by
    simpa [prefixWord, tailWord_3554211, baseEnd_3554211] using wordTrace_append hprefix tailTrace_3554211
  have hstable : (prefixWord ++ tailWord_3554211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554211).length < 2 ^ (prefixWord ++ tailWord_3554211).sum := by decide
  have hdescent : baseEnd_3554211 < baseStart_3554211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554262 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3554262 : Nat := 118140960795 + 3554262 * 2 ^ 59
def prefixEnd_3554262 : Nat := 4983230072969 + 3 ^ 40 * 3554262 * 2
def baseEnd_3554262 : Nat := 1825044778010678167279253

theorem tailTrace_3554262 : CollatzResearch.WordTrace tailWord_3554262 prefixEnd_3554262 1825044778010678167279253 := by
  unfold tailWord_3554262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8102161565595204279213065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86423056699682178978272693 8102161565595204279213065)
  ·
    refine ⟨6076621174196403209409799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8102161565595204279213065 6076621174196403209409799)
    ·
      refine ⟨9114931761294604814114699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6076621174196403209409799 9114931761294604814114699)
      ·
        refine ⟨13672397641941907221172049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9114931761294604814114699 13672397641941907221172049)
        ·
          refine ⟨10254298231456430415879037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13672397641941907221172049 10254298231456430415879037)
          ·
            refine ⟨3845361836796161405954639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10254298231456430415879037 3845361836796161405954639)
            ·
              refine ⟨5768042755194242108931959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3845361836796161405954639 5768042755194242108931959)
              ·
                refine ⟨8652064132791363163397939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5768042755194242108931959 8652064132791363163397939)
                ·
                  refine ⟨12978096199187044745096909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8652064132791363163397939 12978096199187044745096909)
                  ·
                    refine ⟨4866786074695141779411341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12978096199187044745096909 4866786074695141779411341)
                    ·
                      refine ⟨1825044778010678167279253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4866786074695141779411341 1825044778010678167279253)
                      ·
                        rfl

theorem cell23_3554262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3554262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554262 prefixEnd_3554262 := by exact prefixLift 3554262
  have htrace : WordTrace (prefixWord ++ tailWord_3554262) baseStart_3554262 baseEnd_3554262 := by
    simpa [prefixWord, tailWord_3554262, baseEnd_3554262] using wordTrace_append hprefix tailTrace_3554262
  have hstable : (prefixWord ++ tailWord_3554262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554262).length < 2 ^ (prefixWord ++ tailWord_3554262).sum := by decide
  have hdescent : baseEnd_3554262 < baseStart_3554262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554338 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3554338 : Nat := 118140960795 + 3554338 * 2 ^ 59
def prefixEnd_3554338 : Nat := 4983230072969 + 3 ^ 40 * 3554338 * 2
def baseEnd_3554338 : Nat := 608361267513473289976301

theorem tailTrace_3554338 : CollatzResearch.WordTrace tailWord_3554338 prefixEnd_3554338 608361267513473289976301 := by
  unfold tailWord_3554338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32409339249311983361793917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86424904664831955631450445 32409339249311983361793917)
  ·
    refine ⟨12153502218491993760672719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32409339249311983361793917 12153502218491993760672719)
    ·
      refine ⟨18230253327737990641009079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12153502218491993760672719 18230253327737990641009079)
      ·
        refine ⟨27345379991606985961513619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18230253327737990641009079 27345379991606985961513619)
        ·
          refine ⟨41018069987410478942270429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27345379991606985961513619 41018069987410478942270429)
          ·
            refine ⟨15381776245278929603351411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41018069987410478942270429 15381776245278929603351411)
            ·
              refine ⟨23072664367918394405027117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15381776245278929603351411 23072664367918394405027117)
              ·
                refine ⟨8652249137969397901885169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23072664367918394405027117 8652249137969397901885169)
                ·
                  refine ⟨6489186853477048426413877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8652249137969397901885169 6489186853477048426413877)
                  ·
                    refine ⟨608361267513473289976301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6489186853477048426413877 608361267513473289976301)
                    ·
                      rfl

theorem cell23_3554338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3554338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554338 prefixEnd_3554338 := by exact prefixLift 3554338
  have htrace : WordTrace (prefixWord ++ tailWord_3554338) baseStart_3554338 baseEnd_3554338 := by
    simpa [prefixWord, tailWord_3554338, baseEnd_3554338] using wordTrace_append hprefix tailTrace_3554338
  have hstable : (prefixWord ++ tailWord_3554338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554338).length < 2 ^ (prefixWord ++ tailWord_3554338).sum := by decide
  have hdescent : baseEnd_3554338 < baseStart_3554338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554368 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 3, 4]
def baseStart_3554368 : Nat := 118140960795 + 3554368 * 2 ^ 59
def prefixEnd_3554368 : Nat := 4983230072969 + 3 ^ 40 * 3554368 * 2
def baseEnd_3554368 : Nat := 608366402320018250851255

theorem tailTrace_3554368 : CollatzResearch.WordTrace tailWord_3554368 prefixEnd_3554368 608366402320018250851255 := by
  unfold tailWord_3554368
  simp only [CollatzResearch.WordTrace]
  refine ⟨64819225593569624285383879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86425634124759499047178505 64819225593569624285383879)
  ·
    refine ⟨97228838390354436428075819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64819225593569624285383879 97228838390354436428075819)
    ·
      refine ⟨145843257585531654642113729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97228838390354436428075819 145843257585531654642113729)
      ·
        refine ⟨109382443189148740981585297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145843257585531654642113729 109382443189148740981585297)
        ·
          refine ⟨82036832391861555736188973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109382443189148740981585297 82036832391861555736188973)
          ·
            refine ⟨30763812146948083401070865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82036832391861555736188973 30763812146948083401070865)
            ·
              refine ⟨23072859110211062550803149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30763812146948083401070865 23072859110211062550803149)
              ·
                refine ⟨8652322166329148456551181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23072859110211062550803149 8652322166329148456551181)
                ·
                  refine ⟨3244620812373430671206693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8652322166329148456551181 3244620812373430671206693)
                  ·
                    refine ⟨608366402320018250851255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3244620812373430671206693 608366402320018250851255)
                    ·
                      rfl

theorem cell23_3554368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3, 4].length) (baseStart_3554368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554368 prefixEnd_3554368 := by exact prefixLift 3554368
  have htrace : WordTrace (prefixWord ++ tailWord_3554368) baseStart_3554368 baseEnd_3554368 := by
    simpa [prefixWord, tailWord_3554368, baseEnd_3554368] using wordTrace_append hprefix tailTrace_3554368
  have hstable : (prefixWord ++ tailWord_3554368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554368).length < 2 ^ (prefixWord ++ tailWord_3554368).sum := by decide
  have hdescent : baseEnd_3554368 < baseStart_3554368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554375 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 2, 4, 2]
def baseStart_3554375 : Nat := 118140960795 + 3554375 * 2 ^ 59
def prefixEnd_3554375 : Nat := 4983230072969 + 3 ^ 40 * 3554375 * 2
def baseEnd_3554375 : Nat := 1825102801324636225166233

theorem tailTrace_3554375 : CollatzResearch.WordTrace tailWord_3554375 prefixEnd_3554375 1825102801324636225166233 := by
  unfold tailWord_3554375
  simp only [CollatzResearch.WordTrace]
  refine ⟨129638706498113888766272579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86425804332075925844181719 129638706498113888766272579)
  ·
    refine ⟨194458059747170833149408869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129638706498113888766272579 194458059747170833149408869)
    ·
      refine ⟨36460886202594531215514163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194458059747170833149408869 36460886202594531215514163)
      ·
        refine ⟨54691329303891796823271245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36460886202594531215514163 54691329303891796823271245)
        ·
          refine ⟨20509248488959423808726717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54691329303891796823271245 20509248488959423808726717)
          ·
            refine ⟨7690968183359783928272519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20509248488959423808726717 7690968183359783928272519)
            ·
              refine ⟨11536452275039675892408779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690968183359783928272519 11536452275039675892408779)
              ·
                refine ⟨17304678412559513838613169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11536452275039675892408779 17304678412559513838613169)
                ·
                  refine ⟨12978508809419635378959877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17304678412559513838613169 12978508809419635378959877)
                  ·
                    refine ⟨2433470401766181633554977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12978508809419635378959877 2433470401766181633554977)
                    ·
                      refine ⟨1825102801324636225166233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2433470401766181633554977 1825102801324636225166233)
                      ·
                        rfl

theorem cell23_3554375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_3554375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554375 prefixEnd_3554375 := by exact prefixLift 3554375
  have htrace : WordTrace (prefixWord ++ tailWord_3554375) baseStart_3554375 baseEnd_3554375 := by
    simpa [prefixWord, tailWord_3554375, baseEnd_3554375] using wordTrace_append hprefix tailTrace_3554375
  have hstable : (prefixWord ++ tailWord_3554375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554375).length < 2 ^ (prefixWord ++ tailWord_3554375).sum := by decide
  have hdescent : baseEnd_3554375 < baseStart_3554375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554378 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_3554378 : Nat := 118140960795 + 3554378 * 2 ^ 59
def prefixEnd_3554378 : Nat := 4983230072969 + 3 ^ 40 * 3554378 * 2
def baseEnd_3554378 : Nat := 1825104341766599713428719

theorem tailTrace_3554378 : CollatzResearch.WordTrace tailWord_3554378 prefixEnd_3554378 1825104341766599713428719 := by
  unfold tailWord_3554378
  simp only [CollatzResearch.WordTrace]
  refine ⟨32409703979275755069657947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86425877278068680185754525 32409703979275755069657947)
  ·
    refine ⟨48614555968913632604486921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32409703979275755069657947 48614555968913632604486921)
    ·
      refine ⟨36460916976685224453365191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48614555968913632604486921 36460916976685224453365191)
      ·
        refine ⟨54691375465027836680047787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36460916976685224453365191 54691375465027836680047787)
        ·
          refine ⟨82037063197541755020071681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54691375465027836680047787 82037063197541755020071681)
          ·
            refine ⟨61527797398156316265053761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82037063197541755020071681 61527797398156316265053761)
            ·
              refine ⟨46145848048617237198790321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61527797398156316265053761 46145848048617237198790321)
              ·
                refine ⟨34609386036462927899092741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46145848048617237198790321 34609386036462927899092741)
                ·
                  refine ⟨6489259881836798981079889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34609386036462927899092741 6489259881836798981079889)
                  ·
                    refine ⟨4866944911377599235809917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6489259881836798981079889 4866944911377599235809917)
                    ·
                      refine ⟨1825104341766599713428719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4866944911377599235809917 1825104341766599713428719)
                      ·
                        rfl

theorem cell23_3554378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_3554378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554378 prefixEnd_3554378 := by exact prefixLift 3554378
  have htrace : WordTrace (prefixWord ++ tailWord_3554378) baseStart_3554378 baseEnd_3554378 := by
    simpa [prefixWord, tailWord_3554378, baseEnd_3554378] using wordTrace_append hprefix tailTrace_3554378
  have hstable : (prefixWord ++ tailWord_3554378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554378).length < 2 ^ (prefixWord ++ tailWord_3554378).sum := by decide
  have hdescent : baseEnd_3554378 < baseStart_3554378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554462 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_3554462 : Nat := 118140960795 + 3554462 * 2 ^ 59
def prefixEnd_3554462 : Nat := 4983230072969 + 3 ^ 40 * 3554462 * 2
def baseEnd_3554462 : Nat := 608382491380525794926111

theorem tailTrace_3554462 : CollatzResearch.WordTrace tailWord_3554462 prefixEnd_3554462 608382491380525794926111 := by
  unfold tailWord_3554462
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205234956099837828086205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86427919765865801749793093 16205234956099837828086205)
  ·
    refine ⟨6076963108537439185532327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16205234956099837828086205 6076963108537439185532327)
    ·
      refine ⟨9115444662806158778298491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6076963108537439185532327 9115444662806158778298491)
      ·
        refine ⟨13673166994209238167447737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9115444662806158778298491 13673166994209238167447737)
        ·
          refine ⟨10254875245656928625585803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13673166994209238167447737 10254875245656928625585803)
          ·
            refine ⟨15382312868485392938378705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10254875245656928625585803 15382312868485392938378705)
            ·
              refine ⟨11536734651364044703784029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15382312868485392938378705 11536734651364044703784029)
              ·
                refine ⟨4326275494261516763919011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11536734651364044703784029 4326275494261516763919011)
                ·
                  refine ⟨6489413241392275145878517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326275494261516763919011 6489413241392275145878517)
                  ·
                    refine ⟨608382491380525794926111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6489413241392275145878517 608382491380525794926111)
                    ·
                      rfl

theorem cell23_3554462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_3554462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554462 prefixEnd_3554462 := by exact prefixLift 3554462
  have htrace : WordTrace (prefixWord ++ tailWord_3554462) baseStart_3554462 baseEnd_3554462 := by
    simpa [prefixWord, tailWord_3554462, baseEnd_3554462] using wordTrace_append hprefix tailTrace_3554462
  have hstable : (prefixWord ++ tailWord_3554462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554462).length < 2 ^ (prefixWord ++ tailWord_3554462).sum := by decide
  have hdescent : baseEnd_3554462 < baseStart_3554462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554465 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3554465 : Nat := 118140960795 + 3554465 * 2 ^ 59
def prefixEnd_3554465 : Nat := 4983230072969 + 3 ^ 40 * 3554465 * 2
def baseEnd_3554465 : Nat := 1825149014583540873040819

theorem tailTrace_3554465 : CollatzResearch.WordTrace tailWord_3554465 prefixEnd_3554465 1825149014583540873040819 := by
  unfold tailWord_3554465
  simp only [CollatzResearch.WordTrace]
  refine ⟨129641989067787834137048849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86427992711858556091365899 129641989067787834137048849)
  ·
    refine ⟨97231491800840875602786637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129641989067787834137048849 97231491800840875602786637)
    ·
      refine ⟨36461809425315328351044989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97231491800840875602786637 36461809425315328351044989)
      ·
        refine ⟨13673178534493248131641871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36461809425315328351044989 13673178534493248131641871)
        ·
          refine ⟨20509767801739872197462807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13673178534493248131641871 20509767801739872197462807)
          ·
            refine ⟨30764651702609808296194211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20509767801739872197462807 30764651702609808296194211)
            ·
              refine ⟨46146977553914712444291317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30764651702609808296194211 46146977553914712444291317)
              ·
                refine ⟨4326279145679504291652311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46146977553914712444291317 4326279145679504291652311)
                ·
                  refine ⟨6489418718519256437478467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326279145679504291652311 6489418718519256437478467)
                  ·
                    refine ⟨9734128077778884656217701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6489418718519256437478467 9734128077778884656217701)
                    ·
                      refine ⟨1825149014583540873040819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9734128077778884656217701 1825149014583540873040819)
                      ·
                        rfl

theorem cell23_3554465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3554465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554465 prefixEnd_3554465 := by exact prefixLift 3554465
  have htrace : WordTrace (prefixWord ++ tailWord_3554465) baseStart_3554465 baseEnd_3554465 := by
    simpa [prefixWord, tailWord_3554465, baseEnd_3554465] using wordTrace_append hprefix tailTrace_3554465
  have hstable : (prefixWord ++ tailWord_3554465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554465).length < 2 ^ (prefixWord ++ tailWord_3554465).sum := by decide
  have hdescent : baseEnd_3554465 < baseStart_3554465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554492 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_3554492 : Nat := 118140960795 + 3554492 * 2 ^ 59
def prefixEnd_3554492 : Nat := 4983230072969 + 3 ^ 40 * 3554492 * 2
def baseEnd_3554492 : Nat := 608387626187070755801065

theorem tailTrace_3554492 : CollatzResearch.WordTrace tailWord_3554492 prefixEnd_3554492 608387626187070755801065 := by
  unfold tailWord_3554492
  simp only [CollatzResearch.WordTrace]
  refine ⟨64821486919345008874140865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86428649225793345165521153 64821486919345008874140865)
  ·
    refine ⟨48616115189508756655605649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64821486919345008874140865 48616115189508756655605649)
    ·
      refine ⟨36462086392131567491704237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48616115189508756655605649 36462086392131567491704237)
      ·
        refine ⟨13673282397049337809389089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36462086392131567491704237 13673282397049337809389089)
        ·
          refine ⟨10254961797787003357041817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13673282397049337809389089 10254961797787003357041817)
          ·
            refine ⟨7691221348340252517781363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10254961797787003357041817 7691221348340252517781363)
            ·
              refine ⟨11536832022510378776672045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7691221348340252517781363 11536832022510378776672045)
              ·
                refine ⟨4326312008441392041252017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11536832022510378776672045 4326312008441392041252017)
                ·
                  refine ⟨3244734006331044030939013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326312008441392041252017 3244734006331044030939013)
                  ·
                    refine ⟨608387626187070755801065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3244734006331044030939013 608387626187070755801065)
                    ·
                      rfl

theorem cell23_3554492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_3554492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554492 prefixEnd_3554492 := by exact prefixLift 3554492
  have htrace : WordTrace (prefixWord ++ tailWord_3554492) baseStart_3554492 baseEnd_3554492 := by
    simpa [prefixWord, tailWord_3554492, baseEnd_3554492] using wordTrace_append hprefix tailTrace_3554492
  have hstable : (prefixWord ++ tailWord_3554492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554492).length < 2 ^ (prefixWord ++ tailWord_3554492).sum := by decide
  have hdescent : baseEnd_3554492 < baseStart_3554492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554509 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3554509 : Nat := 118140960795 + 3554509 * 2 ^ 59
def prefixEnd_3554509 : Nat := 4983230072969 + 3 ^ 40 * 3554509 * 2
def baseEnd_3554509 : Nat := 608390535910779566963539

theorem tailTrace_3554509 : CollatzResearch.WordTrace tailWord_3554509 prefixEnd_3554509 608390535910779566963539 := by
  unfold tailWord_3554509
  simp only [CollatzResearch.WordTrace]
  refine ⟨129643593879628429651650581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86429062586418953101100387 129643593879628429651650581)
  ·
    refine ⟨6077043463107582639921121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129643593879628429651650581 6077043463107582639921121)
    ·
      refine ⟨4557782597330686979940841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6077043463107582639921121 4557782597330686979940841)
      ·
        refine ⟨3418336947998015234955631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4557782597330686979940841 3418336947998015234955631)
        ·
          refine ⟨5127505421997022852433447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3418336947998015234955631 5127505421997022852433447)
          ·
            refine ⟨7691258132995534278650171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5127505421997022852433447 7691258132995534278650171)
            ·
              refine ⟨11536887199493301417975257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7691258132995534278650171 11536887199493301417975257)
              ·
                refine ⟨8652665399619976063481443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11536887199493301417975257 8652665399619976063481443)
                ·
                  refine ⟨12978998099429964095222165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8652665399619976063481443 12978998099429964095222165)
                  ·
                    refine ⟨608390535910779566963539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12978998099429964095222165 608390535910779566963539)
                    ·
                      rfl

theorem cell23_3554509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3554509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554509 prefixEnd_3554509 := by exact prefixLift 3554509
  have htrace : WordTrace (prefixWord ++ tailWord_3554509) baseStart_3554509 baseEnd_3554509 := by
    simpa [prefixWord, tailWord_3554509, baseEnd_3554509] using wordTrace_append hprefix tailTrace_3554509
  have hstable : (prefixWord ++ tailWord_3554509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554509).length < 2 ^ (prefixWord ++ tailWord_3554509).sum := by decide
  have hdescent : baseEnd_3554509 < baseStart_3554509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554516 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3554516 : Nat := 118140960795 + 3554516 * 2 ^ 59
def prefixEnd_3554516 : Nat := 4983230072969 + 3 ^ 40 * 3554516 * 2
def baseEnd_3554516 : Nat := 1825175202096920173503085

theorem tailTrace_3554516 : CollatzResearch.WordTrace tailWord_3554516 prefixEnd_3554516 1825175202096920173503085 := by
  unfold tailWord_3554516
  simp only [CollatzResearch.WordTrace]
  refine ⟨64821924595301534923577701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86429232793735379898103601 64821924595301534923577701)
  ·
    refine ⟨12154110861619037798170819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64821924595301534923577701 12154110861619037798170819)
    ·
      refine ⟨18231166292428556697256229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12154110861619037798170819 18231166292428556697256229)
      ·
        refine ⟨3418343679830354380735543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18231166292428556697256229 3418343679830354380735543)
        ·
          refine ⟨5127515519745531571103315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3418343679830354380735543 5127515519745531571103315)
          ·
            refine ⟨7691273279618297356654973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5127515519745531571103315 7691273279618297356654973)
            ·
              refine ⟨2884227479856861508745615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7691273279618297356654973 2884227479856861508745615)
              ·
                refine ⟨4326341219785292263118423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2884227479856861508745615 4326341219785292263118423)
                ·
                  refine ⟨6489511829677938394677635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326341219785292263118423 6489511829677938394677635)
                  ·
                    refine ⟨9734267744516907592016453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6489511829677938394677635 9734267744516907592016453)
                    ·
                      refine ⟨1825175202096920173503085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9734267744516907592016453 1825175202096920173503085)
                      ·
                        rfl

theorem cell23_3554516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3554516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554516 prefixEnd_3554516 := by exact prefixLift 3554516
  have htrace : WordTrace (prefixWord ++ tailWord_3554516) baseStart_3554516 baseEnd_3554516 := by
    simpa [prefixWord, tailWord_3554516, baseEnd_3554516] using wordTrace_append hprefix tailTrace_3554516
  have hstable : (prefixWord ++ tailWord_3554516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554516).length < 2 ^ (prefixWord ++ tailWord_3554516).sum := by decide
  have hdescent : baseEnd_3554516 < baseStart_3554516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554532 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_3554532 : Nat := 118140960795 + 3554532 * 2 ^ 59
def prefixEnd_3554532 : Nat := 4983230072969 + 3 ^ 40 * 3554532 * 2
def baseEnd_3554532 : Nat := 1825183417787392110903011

theorem tailTrace_3554532 : CollatzResearch.WordTrace tailWord_3554532 prefixEnd_3554532 1825183417787392110903011 := by
  unfold tailWord_3554532
  simp only [CollatzResearch.WordTrace]
  refine ⟨64822216379272552289868925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86429621839030069719825233 64822216379272552289868925)
  ·
    refine ⟨24308331142227207108700847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64822216379272552289868925 24308331142227207108700847)
    ·
      refine ⟨36462496713340810663051271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24308331142227207108700847 36462496713340810663051271)
      ·
        refine ⟨54693745070011215994576907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36462496713340810663051271 54693745070011215994576907)
        ·
          refine ⟨82040617605016823991865361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54693745070011215994576907 82040617605016823991865361)
          ·
            refine ⟨61530463203762617993899021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82040617605016823991865361 61530463203762617993899021)
            ·
              refine ⟨23073923701410981747712133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61530463203762617993899021 23073923701410981747712133)
              ·
                refine ⟨4326360694014559077696025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23073923701410981747712133 4326360694014559077696025)
                ·
                  refine ⟨3244770520510919308272019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326360694014559077696025 3244770520510919308272019)
                  ·
                    refine ⟨4867155780766378962408029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3244770520510919308272019 4867155780766378962408029)
                    ·
                      refine ⟨1825183417787392110903011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4867155780766378962408029 1825183417787392110903011)
                      ·
                        rfl

theorem cell23_3554532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_3554532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554532 prefixEnd_3554532 := by exact prefixLift 3554532
  have htrace : WordTrace (prefixWord ++ tailWord_3554532) baseStart_3554532 baseEnd_3554532 := by
    simpa [prefixWord, tailWord_3554532, baseEnd_3554532] using wordTrace_append hprefix tailTrace_3554532
  have hstable : (prefixWord ++ tailWord_3554532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554532).length < 2 ^ (prefixWord ++ tailWord_3554532).sum := by decide
  have hdescent : baseEnd_3554532 < baseStart_3554532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554542 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_3554542 : Nat := 118140960795 + 3554542 * 2 ^ 59
def prefixEnd_3554542 : Nat := 4983230072969 + 3 ^ 40 * 3554542 * 2
def baseEnd_3554542 : Nat := 1825188552593937071777965

theorem tailTrace_3554542 : CollatzResearch.WordTrace tailWord_3554542 prefixEnd_3554542 1825188552593937071777965 := by
  unfold tailWord_3554542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205599686063609535950235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86429864992339250858401253 16205599686063609535950235)
  ·
    refine ⟨24308399529095414303925353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16205599686063609535950235 24308399529095414303925353)
    ·
      refine ⟨18231299646821560727944015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24308399529095414303925353 18231299646821560727944015)
      ·
        refine ⟨27346949470232341091916023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18231299646821560727944015 27346949470232341091916023)
        ·
          refine ⟨41020424205348511637874035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27346949470232341091916023 41020424205348511637874035)
          ·
            refine ⟨61530636308022767456811053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41020424205348511637874035 61530636308022767456811053)
            ·
              refine ⟨23073988615508537796304145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61530636308022767456811053 23073988615508537796304145)
              ·
                refine ⟨17305491461631403347228109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23073988615508537796304145 17305491461631403347228109)
                ·
                  refine ⟨6489559298111776255210541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17305491461631403347228109 6489559298111776255210541)
                  ·
                    refine ⟨2433584736791916095703953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6489559298111776255210541 2433584736791916095703953)
                    ·
                      refine ⟨1825188552593937071777965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2433584736791916095703953 1825188552593937071777965)
                      ·
                        rfl

theorem cell23_3554542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_3554542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554542 prefixEnd_3554542 := by exact prefixLift 3554542
  have htrace : WordTrace (prefixWord ++ tailWord_3554542) baseStart_3554542 baseEnd_3554542 := by
    simpa [prefixWord, tailWord_3554542, baseEnd_3554542] using wordTrace_append hprefix tailTrace_3554542
  have hstable : (prefixWord ++ tailWord_3554542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554542).length < 2 ^ (prefixWord ++ tailWord_3554542).sum := by decide
  have hdescent : baseEnd_3554542 < baseStart_3554542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554572 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 1, 4, 2]
def baseStart_3554572 : Nat := 118140960795 + 3554572 * 2 ^ 59
def prefixEnd_3554572 : Nat := 4983230072969 + 3 ^ 40 * 3554572 * 2
def baseEnd_3554572 : Nat := 1825203957013571954402827

theorem tailTrace_3554572 : CollatzResearch.WordTrace tailWord_3554572 prefixEnd_3554572 1825203957013571954402827 := by
  unfold tailWord_3554572
  simp only [CollatzResearch.WordTrace]
  refine ⟨64822945839200095705596985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86430594452266794274129313 64822945839200095705596985)
  ·
    refine ⟨48617209379400071779197739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64822945839200095705596985 48617209379400071779197739)
    ·
      refine ⟨72925814069100107668796609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48617209379400071779197739 72925814069100107668796609)
      ·
        refine ⟨54694360551825080751597457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72925814069100107668796609 54694360551825080751597457)
        ·
          refine ⟨41020770413868810563698093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54694360551825080751597457 41020770413868810563698093)
          ·
            refine ⟨15382788905200803961386785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41020770413868810563698093 15382788905200803961386785)
            ·
              refine ⟨11537091678900602971040089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15382788905200803961386785 11537091678900602971040089)
              ·
                refine ⟨8652818759175452228280067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11537091678900602971040089 8652818759175452228280067)
                ·
                  refine ⟨12979228138763178342420101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8652818759175452228280067 12979228138763178342420101)
                  ·
                    refine ⟨2433605276018095939203769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12979228138763178342420101 2433605276018095939203769)
                    ·
                      refine ⟨1825203957013571954402827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2433605276018095939203769 1825203957013571954402827)
                      ·
                        rfl

theorem cell23_3554572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_3554572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554572 prefixEnd_3554572 := by exact prefixLift 3554572
  have htrace : WordTrace (prefixWord ++ tailWord_3554572) baseStart_3554572 baseEnd_3554572 := by
    simpa [prefixWord, tailWord_3554572, baseEnd_3554572] using wordTrace_append hprefix tailTrace_3554572
  have hstable : (prefixWord ++ tailWord_3554572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554572).length < 2 ^ (prefixWord ++ tailWord_3554572).sum := by decide
  have hdescent : baseEnd_3554572 < baseStart_3554572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554595 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 7]
def baseStart_3554595 : Nat := 118140960795 + 3554595 * 2 ^ 59
def prefixEnd_3554595 : Nat := 4983230072969 + 3 ^ 40 * 3554595 * 2
def baseEnd_3554595 : Nat := 202801751896513929379469

theorem tailTrace_3554595 : CollatzResearch.WordTrace tailWord_3554595 prefixEnd_3554595 202801751896513929379469 := by
  unfold tailWord_3554595
  simp only [CollatzResearch.WordTrace]
  refine ⟨129646730557316866339281239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86431153704877910892854159 129646730557316866339281239)
  ·
    refine ⟨194470095835975299508921859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129646730557316866339281239 194470095835975299508921859)
    ·
      refine ⟨291705143753962949263382789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194470095835975299508921859 291705143753962949263382789)
      ·
        refine ⟨54694714453868052986884273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291705143753962949263382789 54694714453868052986884273)
        ·
          refine ⟨41021035840401039740163205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54694714453868052986884273 41021035840401039740163205)
          ·
            refine ⟨7691444220075194951280601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41021035840401039740163205 7691444220075194951280601)
            ·
              refine ⟨5768583165056396213460451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7691444220075194951280601 5768583165056396213460451)
              ·
                refine ⟨8652874747584594320190677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5768583165056396213460451 8652874747584594320190677)
                ·
                  refine ⟨202801751896513929379469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8652874747584594320190677 202801751896513929379469)
                  ·
                    rfl

theorem cell23_3554595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 7].length) (baseStart_3554595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554595 prefixEnd_3554595 := by exact prefixLift 3554595
  have htrace : WordTrace (prefixWord ++ tailWord_3554595) baseStart_3554595 baseEnd_3554595 := by
    simpa [prefixWord, tailWord_3554595, baseEnd_3554595] using wordTrace_append hprefix tailTrace_3554595
  have hstable : (prefixWord ++ tailWord_3554595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554595).length < 2 ^ (prefixWord ++ tailWord_3554595).sum := by decide
  have hdescent : baseEnd_3554595 < baseStart_3554595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554602 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3554602 : Nat := 118140960795 + 3554602 * 2 ^ 59
def prefixEnd_3554602 : Nat := 4983230072969 + 3 ^ 40 * 3554602 * 2
def baseEnd_3554602 : Nat := 1825219361433206837027689

theorem tailTrace_3554602 : CollatzResearch.WordTrace tailWord_3554602 prefixEnd_3554602 1825219361433206837027689 := by
  unfold tailWord_3554602
  simp only [CollatzResearch.WordTrace]
  refine ⟨32411746467072876633696515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86431323912194337689857373 32411746467072876633696515)
  ·
    refine ⟨48617619700609314950544773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32411746467072876633696515 48617619700609314950544773)
    ·
      refine ⟨9115803693864246553227145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48617619700609314950544773 9115803693864246553227145)
      ·
        refine ⟨6836852770398184914920359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9115803693864246553227145 6836852770398184914920359)
        ·
          refine ⟨10255279155597277372380539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6836852770398184914920359 10255279155597277372380539)
          ·
            refine ⟨15382918733395916058570809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10255279155597277372380539 15382918733395916058570809)
            ·
              refine ⟨11537189050046937043928107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15382918733395916058570809 11537189050046937043928107)
              ·
                refine ⟨17305783575070405565892161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11537189050046937043928107 17305783575070405565892161)
                ·
                  refine ⟨12979337681302804174419121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17305783575070405565892161 12979337681302804174419121)
                  ·
                    refine ⟨9734503260977103130814341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12979337681302804174419121 9734503260977103130814341)
                    ·
                      refine ⟨1825219361433206837027689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9734503260977103130814341 1825219361433206837027689)
                      ·
                        rfl

theorem cell23_3554602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3554602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554602 prefixEnd_3554602 := by exact prefixLift 3554602
  have htrace : WordTrace (prefixWord ++ tailWord_3554602) baseStart_3554602 baseEnd_3554602 := by
    simpa [prefixWord, tailWord_3554602, baseEnd_3554602] using wordTrace_append hprefix tailTrace_3554602
  have hstable : (prefixWord ++ tailWord_3554602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554602).length < 2 ^ (prefixWord ++ tailWord_3554602).sum := by decide
  have hdescent : baseEnd_3554602 < baseStart_3554602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554608 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 3, 7]
def baseStart_3554608 : Nat := 118140960795 + 3554608 * 2 ^ 59
def prefixEnd_3554608 : Nat := 4983230072969 + 3 ^ 40 * 3554608 * 2
def baseEnd_3554608 : Nat := 608407480772377937850887

theorem tailTrace_3554608 : CollatzResearch.WordTrace tailWord_3554608 prefixEnd_3554608 608407480772377937850887 := by
  unfold tailWord_3554608
  simp only [CollatzResearch.WordTrace]
  refine ⟨64823602353134884779752239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86431469804179846373002985 64823602353134884779752239)
  ·
    refine ⟨97235403529702327169628359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64823602353134884779752239 97235403529702327169628359)
    ·
      refine ⟨145853105294553490754442539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97235403529702327169628359 145853105294553490754442539)
      ·
        refine ⟨218779657941830236131663809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145853105294553490754442539 218779657941830236131663809)
        ·
          refine ⟨164084743456372677098747857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218779657941830236131663809 164084743456372677098747857)
          ·
            refine ⟨123063557592279507824060893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164084743456372677098747857 123063557592279507824060893)
            ·
              refine ⟨46148834097104815434022835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123063557592279507824060893 46148834097104815434022835)
              ·
                refine ⟨69223251145657223151034253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46148834097104815434022835 69223251145657223151034253)
                ·
                  refine ⟨25958719179621458681637845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69223251145657223151034253 25958719179621458681637845)
                  ·
                    refine ⟨608407480772377937850887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25958719179621458681637845 608407480772377937850887)
                    ·
                      rfl

theorem cell23_3554608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_3554608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554608 prefixEnd_3554608 := by exact prefixLift 3554608
  have htrace : WordTrace (prefixWord ++ tailWord_3554608) baseStart_3554608 baseEnd_3554608 := by
    simpa [prefixWord, tailWord_3554608, baseEnd_3554608] using wordTrace_append hprefix tailTrace_3554608
  have hstable : (prefixWord ++ tailWord_3554608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554608).length < 2 ^ (prefixWord ++ tailWord_3554608).sum := by decide
  have hdescent : baseEnd_3554608 < baseStart_3554608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554665 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 1, 4, 3]
def baseStart_3554665 : Nat := 118140960795 + 3554665 * 2 ^ 59
def prefixEnd_3554665 : Nat := 4983230072969 + 3 ^ 40 * 3554665 * 2
def baseEnd_3554665 : Nat := 1825251710714440090539899

theorem tailTrace_3554665 : CollatzResearch.WordTrace tailWord_3554665 prefixEnd_3554665 1825251710714440090539899 := by
  unfold tailWord_3554665
  simp only [CollatzResearch.WordTrace]
  refine ⟨129649283667063268294329449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86432855778042178862886299 129649283667063268294329449)
  ·
    refine ⟨97236962750297451220747087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129649283667063268294329449 97236962750297451220747087)
    ·
      refine ⟨145855444125446176831120631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97236962750297451220747087 145855444125446176831120631)
      ·
        refine ⟨218783166188169265246680947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145855444125446176831120631 218783166188169265246680947)
        ·
          refine ⟨328174749282253897870021421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218783166188169265246680947 328174749282253897870021421)
          ·
            refine ⟨123065530980845211701258033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328174749282253897870021421 123065530980845211701258033)
            ·
              refine ⟨92299148235633908775943525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123065530980845211701258033 92299148235633908775943525)
              ·
                refine ⟨17306090294181357895489411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92299148235633908775943525 17306090294181357895489411)
                ·
                  refine ⟨25959135441272036843234117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17306090294181357895489411 25959135441272036843234117)
                  ·
                    refine ⟨4867337895238506908106397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25959135441272036843234117 4867337895238506908106397)
                    ·
                      refine ⟨1825251710714440090539899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4867337895238506908106397 1825251710714440090539899)
                      ·
                        rfl

theorem cell23_3554665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4, 3].length) (baseStart_3554665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554665 prefixEnd_3554665 := by exact prefixLift 3554665
  have htrace : WordTrace (prefixWord ++ tailWord_3554665) baseStart_3554665 baseEnd_3554665 := by
    simpa [prefixWord, tailWord_3554665, baseEnd_3554665] using wordTrace_append hprefix tailTrace_3554665
  have hstable : (prefixWord ++ tailWord_3554665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554665).length < 2 ^ (prefixWord ++ tailWord_3554665).sum := by decide
  have hdescent : baseEnd_3554665 < baseStart_3554665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554797 : List Nat := [1, 5, 1, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_3554797 : Nat := 118140960795 + 3554797 * 2 ^ 59
def prefixEnd_3554797 : Nat := 4983230072969 + 3 ^ 40 * 3554797 * 2
def baseEnd_3554797 : Nat := 1825319490160833574089293

theorem tailTrace_3554797 : CollatzResearch.WordTrace tailWord_3554797 prefixEnd_3554797 1825319490160833574089293 := by
  unfold tailWord_3554797
  simp only [CollatzResearch.WordTrace]
  refine ⟨129654098102585054838134645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86436065401723369892089763 129654098102585054838134645)
  ·
    refine ⟨12155071697117348891075123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129654098102585054838134645 12155071697117348891075123)
    ·
      refine ⟨18232607545676023336612685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12155071697117348891075123 18232607545676023336612685)
      ·
        refine ⟨6837227829628508751229757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18232607545676023336612685 6837227829628508751229757)
        ·
          refine ⟨2563960436110690781711159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6837227829628508751229757 2563960436110690781711159)
          ·
            refine ⟨3845940654166036172566739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563960436110690781711159 3845940654166036172566739)
            ·
              refine ⟨5768910981249054258850109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3845940654166036172566739 5768910981249054258850109)
              ·
                refine ⟨2163341617968395347068791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5768910981249054258850109 2163341617968395347068791)
                ·
                  refine ⟨3245012426952593020603187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163341617968395347068791 3245012426952593020603187)
                  ·
                    refine ⟨4867518640428889530904781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3245012426952593020603187 4867518640428889530904781)
                    ·
                      refine ⟨1825319490160833574089293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4867518640428889530904781 1825319490160833574089293)
                      ·
                        rfl

theorem cell23_3554797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_3554797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554797 prefixEnd_3554797 := by exact prefixLift 3554797
  have htrace : WordTrace (prefixWord ++ tailWord_3554797) baseStart_3554797 baseEnd_3554797 := by
    simpa [prefixWord, tailWord_3554797, baseEnd_3554797] using wordTrace_append hprefix tailTrace_3554797
  have hstable : (prefixWord ++ tailWord_3554797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554797).length < 2 ^ (prefixWord ++ tailWord_3554797).sum := by decide
  have hdescent : baseEnd_3554797 < baseStart_3554797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554806 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3554806 : Nat := 118140960795 + 3554806 * 2 ^ 59
def prefixEnd_3554806 : Nat := 4983230072969 + 3 ^ 40 * 3554806 * 2
def baseEnd_3554806 : Nat := 1825324111486724038876751

theorem tailTrace_3554806 : CollatzResearch.WordTrace tailWord_3554806 prefixEnd_3554806 1825324111486724038876751 := by
  unfold tailWord_3554806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8103401647472028085950767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86436284239701632916808181 8103401647472028085950767)
  ·
    refine ⟨12155102471208042128926151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8103401647472028085950767 12155102471208042128926151)
    ·
      refine ⟨18232653706812063193389227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12155102471208042128926151 18232653706812063193389227)
      ·
        refine ⟨27348980560218094790083841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18232653706812063193389227 27348980560218094790083841)
        ·
          refine ⟨20511735420163571092562881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27348980560218094790083841 20511735420163571092562881)
          ·
            refine ⟨15383801565122678319422161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20511735420163571092562881 15383801565122678319422161)
            ·
              refine ⟨11537851173842008739566621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15383801565122678319422161 11537851173842008739566621)
              ·
                refine ⟨4326694190190753277337483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11537851173842008739566621 4326694190190753277337483)
                ·
                  refine ⟨6490041285286129916006225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326694190190753277337483 6490041285286129916006225)
                  ·
                    refine ⟨4867530963964597437004669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6490041285286129916006225 4867530963964597437004669)
                    ·
                      refine ⟨1825324111486724038876751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4867530963964597437004669 1825324111486724038876751)
                      ·
                        rfl

theorem cell23_3554806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3554806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554806 prefixEnd_3554806 := by exact prefixLift 3554806
  have htrace : WordTrace (prefixWord ++ tailWord_3554806) baseStart_3554806 baseEnd_3554806 := by
    simpa [prefixWord, tailWord_3554806, baseEnd_3554806] using wordTrace_append hprefix tailTrace_3554806
  have hstable : (prefixWord ++ tailWord_3554806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554806).length < 2 ^ (prefixWord ++ tailWord_3554806).sum := by decide
  have hdescent : baseEnd_3554806 < baseStart_3554806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554820 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_3554820 : Nat := 118140960795 + 3554820 * 2 ^ 59
def prefixEnd_3554820 : Nat := 4983230072969 + 3 ^ 40 * 3554820 * 2
def baseEnd_3554820 : Nat := 1825331300215886984101687

theorem tailTrace_3554820 : CollatzResearch.WordTrace tailWord_3554820 prefixEnd_3554820 1825331300215886984101687 := by
  unfold tailWord_3554820
  simp only [CollatzResearch.WordTrace]
  refine ⟨64827468490750864883110957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86436624654334486510814609 64827468490750864883110957)
  ·
    refine ⟨24310300684031574331166609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64827468490750864883110957 24310300684031574331166609)
    ·
      refine ⟨18232725513023680748374957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24310300684031574331166609 18232725513023680748374957)
      ·
        refine ⟨6837272067383880280640609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18232725513023680748374957 6837272067383880280640609)
        ·
          refine ⟨5127954050537910210480457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6837272067383880280640609 5127954050537910210480457)
          ·
            refine ⟨3845965537903432657860343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5127954050537910210480457 3845965537903432657860343)
            ·
              refine ⟨5768948306855148986790515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3845965537903432657860343 5768948306855148986790515)
              ·
                refine ⟨8653422460282723480185773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5768948306855148986790515 8653422460282723480185773)
                ·
                  refine ⟨3245033422606021305069665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8653422460282723480185773 3245033422606021305069665)
                  ·
                    refine ⟨2433775066954515978802249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3245033422606021305069665 2433775066954515978802249)
                    ·
                      refine ⟨1825331300215886984101687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2433775066954515978802249 1825331300215886984101687)
                      ·
                        rfl

theorem cell23_3554820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_3554820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554820 prefixEnd_3554820 := by exact prefixLift 3554820
  have htrace : WordTrace (prefixWord ++ tailWord_3554820) baseStart_3554820 baseEnd_3554820 := by
    simpa [prefixWord, tailWord_3554820, baseEnd_3554820] using wordTrace_append hprefix tailTrace_3554820
  have hstable : (prefixWord ++ tailWord_3554820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554820).length < 2 ^ (prefixWord ++ tailWord_3554820).sum := by decide
  have hdescent : baseEnd_3554820 < baseStart_3554820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554830 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_3554830 : Nat := 118140960795 + 3554830 * 2 ^ 59
def prefixEnd_3554830 : Nat := 4983230072969 + 3 ^ 40 * 3554830 * 2
def baseEnd_3554830 : Nat := 608445478340810648325547

theorem tailTrace_3554830 : CollatzResearch.WordTrace tailWord_3554830 prefixEnd_3554830 608445478340810648325547 := by
  unfold tailWord_3554830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16206912713933187684260743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86436867807643667649390629 16206912713933187684260743)
  ·
    refine ⟨24310369070899781526391115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16206912713933187684260743 24310369070899781526391115)
    ·
      refine ⟨36465553606349672289586673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24310369070899781526391115 36465553606349672289586673)
      ·
        refine ⟨27349165204762254217190005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36465553606349672289586673 27349165204762254217190005)
        ·
          refine ⟨2563984237946461332861563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27349165204762254217190005 2563984237946461332861563)
          ·
            refine ⟨3845976356919691999292345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563984237946461332861563 3845976356919691999292345)
            ·
              refine ⟨2884482267689768999469259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3845976356919691999292345 2884482267689768999469259)
              ·
                refine ⟨4326723401534653499203889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2884482267689768999469259 4326723401534653499203889)
                ·
                  refine ⟨3245042551150990124402917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326723401534653499203889 3245042551150990124402917)
                  ·
                    refine ⟨608445478340810648325547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3245042551150990124402917 608445478340810648325547)
                    ·
                      rfl

theorem cell23_3554830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_3554830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554830 prefixEnd_3554830 := by exact prefixLift 3554830
  have htrace : WordTrace (prefixWord ++ tailWord_3554830) baseStart_3554830 baseEnd_3554830 := by
    simpa [prefixWord, tailWord_3554830, baseEnd_3554830] using wordTrace_append hprefix tailTrace_3554830
  have hstable : (prefixWord ++ tailWord_3554830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554830).length < 2 ^ (prefixWord ++ tailWord_3554830).sum := by decide
  have hdescent : baseEnd_3554830 < baseStart_3554830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554870 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3554870 : Nat := 118140960795 + 3554870 * 2 ^ 59
def prefixEnd_3554870 : Nat := 4983230072969 + 3 ^ 40 * 3554870 * 2
def baseEnd_3554870 : Nat := 1825356974248611788476457

theorem tailTrace_3554870 : CollatzResearch.WordTrace tailWord_3554870 prefixEnd_3554870 1825356974248611788476457 := by
  unfold tailWord_3554870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8103547539457536769096379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86437840420880392203694709 8103547539457536769096379)
  ·
    refine ⟨12155321309186305153644569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8103547539457536769096379 12155321309186305153644569)
    ·
      refine ⟨9116490981889728865233427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12155321309186305153644569 9116490981889728865233427)
      ·
        refine ⟨13674736472834593297850141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9116490981889728865233427 13674736472834593297850141)
        ·
          refine ⟨5128026177312972486693803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13674736472834593297850141 5128026177312972486693803)
          ·
            refine ⟨7692039265969458730040705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128026177312972486693803 7692039265969458730040705)
            ·
              refine ⟨5769029449477094047530529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7692039265969458730040705 5769029449477094047530529)
              ·
                refine ⟨4326772087107820535647897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5769029449477094047530529 4326772087107820535647897)
                ·
                  refine ⟨3245079065330865401735923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326772087107820535647897 3245079065330865401735923)
                  ·
                    refine ⟨4867618597996298102603885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3245079065330865401735923 4867618597996298102603885)
                    ·
                      refine ⟨1825356974248611788476457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4867618597996298102603885 1825356974248611788476457)
                      ·
                        rfl

theorem cell23_3554870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3554870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554870 prefixEnd_3554870 := by exact prefixLift 3554870
  have htrace : WordTrace (prefixWord ++ tailWord_3554870) baseStart_3554870 baseEnd_3554870 := by
    simpa [prefixWord, tailWord_3554870, baseEnd_3554870] using wordTrace_append hprefix tailTrace_3554870
  have hstable : (prefixWord ++ tailWord_3554870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554870).length < 2 ^ (prefixWord ++ tailWord_3554870).sum := by decide
  have hdescent : baseEnd_3554870 < baseStart_3554870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554916 : List Nat := [2, 3, 1, 1, 2, 4, 2, 3, 5]
def baseStart_3554916 : Nat := 118140960795 + 3554916 * 2 ^ 59
def prefixEnd_3554916 : Nat := 4983230072969 + 3 ^ 40 * 3554916 * 2
def baseEnd_3554916 : Nat := 202820066039857623166805

theorem tailTrace_3554916 : CollatzResearch.WordTrace tailWord_3554916 prefixEnd_3554916 202820066039857623166805 := by
  unfold tailWord_3554916
  simp only [CollatzResearch.WordTrace]
  refine ⟨64829219194576969080858301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86438958926102625441144401 64829219194576969080858301)
  ·
    refine ⟨24310957197966363405321863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64829219194576969080858301 24310957197966363405321863)
    ·
      refine ⟨36466435796949545107982795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24310957197966363405321863 36466435796949545107982795)
      ·
        refine ⟨54699653695424317661974193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36466435796949545107982795 54699653695424317661974193)
        ·
          refine ⟨41024740271568238246480645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54699653695424317661974193 41024740271568238246480645)
          ·
            refine ⟨7692138800919044671215121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41024740271568238246480645 7692138800919044671215121)
            ·
              refine ⟨5769104100689283503411341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7692138800919044671215121 5769104100689283503411341)
              ·
                refine ⟨2163414037758481313779253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5769104100689283503411341 2163414037758481313779253)
                ·
                  refine ⟨202820066039857623166805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2163414037758481313779253 202820066039857623166805)
                  ·
                    rfl

theorem cell23_3554916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_3554916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554916 prefixEnd_3554916 := by exact prefixLift 3554916
  have htrace : WordTrace (prefixWord ++ tailWord_3554916) baseStart_3554916 baseEnd_3554916 := by
    simpa [prefixWord, tailWord_3554916, baseEnd_3554916] using wordTrace_append hprefix tailTrace_3554916
  have hstable : (prefixWord ++ tailWord_3554916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554916).length < 2 ^ (prefixWord ++ tailWord_3554916).sum := by decide
  have hdescent : baseEnd_3554916 < baseStart_3554916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554989 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 8]
def baseStart_3554989 : Nat := 118140960795 + 3554989 * 2 ^ 59
def prefixEnd_3554989 : Nat := 4983230072969 + 3 ^ 40 * 3554989 * 2
def baseEnd_3554989 : Nat := 202824230938499646987601

theorem tailTrace_3554989 : CollatzResearch.WordTrace tailWord_3554989 prefixEnd_3554989 202824230938499646987601 := by
  unfold tailWord_3554989
  simp only [CollatzResearch.WordTrace]
  refine ⟨129661100917889471629124021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86440733945259647752749347 129661100917889471629124021)
  ·
    refine ⟨12155728211052137965230377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129661100917889471629124021 12155728211052137965230377)
    ·
      refine ⟨9116796158289103473922783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12155728211052137965230377 9116796158289103473922783)
      ·
        refine ⟨13675194237433655210884175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9116796158289103473922783 13675194237433655210884175)
        ·
          refine ⟨20512791356150482816326263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13675194237433655210884175 20512791356150482816326263)
          ·
            refine ⟨30769187034225724224489395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20512791356150482816326263 30769187034225724224489395)
            ·
              refine ⟨46153780551338586336734093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30769187034225724224489395 46153780551338586336734093)
              ·
                refine ⟨17307667706751969876275285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46153780551338586336734093 17307667706751969876275285)
                ·
                  refine ⟨202824230938499646987601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17307667706751969876275285 202824230938499646987601)
                  ·
                    rfl

theorem cell23_3554989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_3554989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554989 prefixEnd_3554989 := by exact prefixLift 3554989
  have htrace : WordTrace (prefixWord ++ tailWord_3554989) baseStart_3554989 baseEnd_3554989 := by
    simpa [prefixWord, tailWord_3554989, baseEnd_3554989] using wordTrace_append hprefix tailTrace_3554989
  have hstable : (prefixWord ++ tailWord_3554989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554989).length < 2 ^ (prefixWord ++ tailWord_3554989).sum := by decide
  have hdescent : baseEnd_3554989 < baseStart_3554989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3554992 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_3554992 : Nat := 118140960795 + 3554992 * 2 ^ 59
def prefixEnd_3554992 : Nat := 4983230072969 + 3 ^ 40 * 3554992 * 2
def baseEnd_3554992 : Nat := 1825419618888460311150895

theorem tailTrace_3554992 : CollatzResearch.WordTrace tailWord_3554992 prefixEnd_3554992 1825419618888460311150895 := by
  unfold tailWord_3554992
  simp only [CollatzResearch.WordTrace]
  refine ⟨64830605168439301570741615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86440806891252402094322153 64830605168439301570741615)
  ·
    refine ⟨97245907752658952356112423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64830605168439301570741615 97245907752658952356112423)
    ·
      refine ⟨145868861628988428534168635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97245907752658952356112423 145868861628988428534168635)
      ·
        refine ⟨218803292443482642801252953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145868861628988428534168635 218803292443482642801252953)
        ·
          refine ⟨164102469332611982100939715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218803292443482642801252953 164102469332611982100939715)
          ·
            refine ⟨246153703998917973151409573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164102469332611982100939715 246153703998917973151409573)
            ·
              refine ⟨46153819499797119965889295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246153703998917973151409573 46153819499797119965889295)
              ·
                refine ⟨69230729249695679948833943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46153819499797119965889295 69230729249695679948833943)
                ·
                  refine ⟨103846093874543519923250915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69230729249695679948833943 103846093874543519923250915)
                  ·
                    refine ⟨155769140811815279884876373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103846093874543519923250915 155769140811815279884876373)
                    ·
                      refine ⟨1825419618888460311150895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 155769140811815279884876373 1825419618888460311150895)
                      ·
                        rfl

theorem cell23_3554992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_3554992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3554992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3554992 prefixEnd_3554992 := by exact prefixLift 3554992
  have htrace : WordTrace (prefixWord ++ tailWord_3554992) baseStart_3554992 baseEnd_3554992 := by
    simpa [prefixWord, tailWord_3554992, baseEnd_3554992] using wordTrace_append hprefix tailTrace_3554992
  have hstable : (prefixWord ++ tailWord_3554992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3554992).length < 2 ^ (prefixWord ++ tailWord_3554992).sum := by decide
  have hdescent : baseEnd_3554992 < baseStart_3554992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3554992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555006 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_3555006 : Nat := 118140960795 + 3555006 * 2 ^ 59
def prefixEnd_3555006 : Nat := 4983230072969 + 3 ^ 40 * 3555006 * 2
def baseEnd_3555006 : Nat := 202825200846402584041759

theorem tailTrace_3555006 : CollatzResearch.WordTrace tailWord_3555006 prefixEnd_3555006 202825200846402584041759 := by
  unfold tailWord_3555006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16207715119853485441561609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86441147305885255688328581 16207715119853485441561609)
  ·
    refine ⟨12155786339890114081171207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16207715119853485441561609 12155786339890114081171207)
    ·
      refine ⟨18233679509835171121756811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12155786339890114081171207 18233679509835171121756811)
      ·
        refine ⟨27350519264752756682635217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18233679509835171121756811 27350519264752756682635217)
        ·
          refine ⟨20512889448564567511976413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27350519264752756682635217 20512889448564567511976413)
          ·
            refine ⟨7692333543211712816991155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20512889448564567511976413 7692333543211712816991155)
            ·
              refine ⟨11538500314817569225486733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692333543211712816991155 11538500314817569225486733)
              ·
                refine ⟨4326937618056588459557525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11538500314817569225486733 4326937618056588459557525)
                ·
                  refine ⟨202825200846402584041759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4326937618056588459557525 202825200846402584041759)
                  ·
                    rfl

theorem cell23_3555006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_3555006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555006 prefixEnd_3555006 := by exact prefixLift 3555006
  have htrace : WordTrace (prefixWord ++ tailWord_3555006) baseStart_3555006 baseEnd_3555006 := by
    simpa [prefixWord, tailWord_3555006, baseEnd_3555006] using wordTrace_append hprefix tailTrace_3555006
  have hstable : (prefixWord ++ tailWord_3555006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555006).length < 2 ^ (prefixWord ++ tailWord_3555006).sum := by decide
  have hdescent : baseEnd_3555006 < baseStart_3555006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555016 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_3555016 : Nat := 118140960795 + 3555016 * 2 ^ 59
def prefixEnd_3555016 : Nat := 4983230072969 + 3 ^ 40 * 3555016 * 2
def baseEnd_3555016 : Nat := 1825431942424168217250785

theorem tailTrace_3555016 : CollatzResearch.WordTrace tailWord_3555016 prefixEnd_3555016 1825431942424168217250785 := by
  unfold tailWord_3555016
  simp only [CollatzResearch.WordTrace]
  refine ⟨64831042844395827620178451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86441390459194436826904601 64831042844395827620178451)
  ·
    refine ⟨97246564266593741430267677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64831042844395827620178451 97246564266593741430267677)
    ·
      refine ⟨36467461599972653036350379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97246564266593741430267677 36467461599972653036350379)
      ·
        refine ⟨54701192399958979554525569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36467461599972653036350379 54701192399958979554525569)
        ·
          refine ⟨41025894299969234665894177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54701192399958979554525569 41025894299969234665894177)
          ·
            refine ⟨30769420724976925999420633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41025894299969234665894177 30769420724976925999420633)
            ·
              refine ⟨23077065543732694499565475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30769420724976925999420633 23077065543732694499565475)
              ·
                refine ⟨34615598315599041749348213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23077065543732694499565475 34615598315599041749348213)
                ·
                  refine ⟨3245212342087410164001395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34615598315599041749348213 3245212342087410164001395)
                  ·
                    refine ⟨4867818513131115246002093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3245212342087410164001395 4867818513131115246002093)
                    ·
                      refine ⟨1825431942424168217250785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4867818513131115246002093 1825431942424168217250785)
                      ·
                        rfl

theorem cell23_3555016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_3555016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555016 prefixEnd_3555016 := by exact prefixLift 3555016
  have htrace : WordTrace (prefixWord ++ tailWord_3555016) baseStart_3555016 baseEnd_3555016 := by
    simpa [prefixWord, tailWord_3555016, baseEnd_3555016] using wordTrace_append hprefix tailTrace_3555016
  have hstable : (prefixWord ++ tailWord_3555016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555016).length < 2 ^ (prefixWord ++ tailWord_3555016).sum := by decide
  have hdescent : baseEnd_3555016 < baseStart_3555016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555059 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 5]
def baseStart_3555059 : Nat := 118140960795 + 3555059 * 2 ^ 59
def prefixEnd_3555059 : Nat := 4983230072969 + 3 ^ 40 * 3555059 * 2
def baseEnd_3555059 : Nat := 1825454022092311549013087

theorem tailTrace_3555059 : CollatzResearch.WordTrace tailWord_3555059 prefixEnd_3555059 1825454022092311549013087 := by
  unfold tailWord_3555059
  simp only [CollatzResearch.WordTrace]
  refine ⟨129663654027635873584172231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86442436018423915722781487 129663654027635873584172231)
  ·
    refine ⟨194495481041453810376258347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129663654027635873584172231 194495481041453810376258347)
    ·
      refine ⟨291743221562180715564387521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194495481041453810376258347 291743221562180715564387521)
      ·
        refine ⟨218807416171635536673290641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291743221562180715564387521 218807416171635536673290641)
        ·
          refine ⟨164105562128726652504967981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218807416171635536673290641 164105562128726652504967981)
          ·
            refine ⟨61539585798272494689362993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164105562128726652504967981 61539585798272494689362993)
            ·
              refine ⟨46154689348704371017022245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61539585798272494689362993 46154689348704371017022245)
              ·
                refine ⟨8654004252882069565691671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46154689348704371017022245 8654004252882069565691671)
                ·
                  refine ⟨12981006379323104348537507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8654004252882069565691671 12981006379323104348537507)
                  ·
                    refine ⟨19471509568984656522806261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12981006379323104348537507 19471509568984656522806261)
                    ·
                      refine ⟨1825454022092311549013087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19471509568984656522806261 1825454022092311549013087)
                      ·
                        rfl

theorem cell23_3555059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_3555059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555059 prefixEnd_3555059 := by exact prefixLift 3555059
  have htrace : WordTrace (prefixWord ++ tailWord_3555059) baseStart_3555059 baseEnd_3555059 := by
    simpa [prefixWord, tailWord_3555059, baseEnd_3555059] using wordTrace_append hprefix tailTrace_3555059
  have hstable : (prefixWord ++ tailWord_3555059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555059).length < 2 ^ (prefixWord ++ tailWord_3555059).sum := by decide
  have hdescent : baseEnd_3555059 < baseStart_3555059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555073 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_3555073 : Nat := 118140960795 + 3555073 * 2 ^ 59
def prefixEnd_3555073 : Nat := 4983230072969 + 3 ^ 40 * 3555073 * 2
def baseEnd_3555073 : Nat := 1825461210821474494238023

theorem tailTrace_3555073 : CollatzResearch.WordTrace tailWord_3555073 prefixEnd_3555073 1825461210821474494238023 := by
  unfold tailWord_3555073
  simp only [CollatzResearch.WordTrace]
  refine ⟨129664164649585153975181873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86442776433056769316787915 129664164649585153975181873)
  ·
    refine ⟨97248123487188865481386405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129664164649585153975181873 97248123487188865481386405)
    ·
      refine ⟨18234023153847912277759951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97248123487188865481386405 18234023153847912277759951)
      ·
        refine ⟨27351034730771868416639927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18234023153847912277759951 27351034730771868416639927)
        ·
          refine ⟨41026552096157802624959891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27351034730771868416639927 41026552096157802624959891)
          ·
            refine ⟨61539828144236703937439837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41026552096157802624959891 61539828144236703937439837)
            ·
              refine ⟨23077435554088763976539939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61539828144236703937439837 23077435554088763976539939)
              ·
                refine ⟨34616153331133145964809909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23077435554088763976539939 34616153331133145964809909)
                ·
                  refine ⟨3245264374793732434200929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34616153331133145964809909 3245264374793732434200929)
                  ·
                    refine ⟨2433948281095299325650697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3245264374793732434200929 2433948281095299325650697)
                    ·
                      refine ⟨1825461210821474494238023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2433948281095299325650697 1825461210821474494238023)
                      ·
                        rfl

theorem cell23_3555073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_3555073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555073 prefixEnd_3555073 := by exact prefixLift 3555073
  have htrace : WordTrace (prefixWord ++ tailWord_3555073) baseStart_3555073 baseEnd_3555073 := by
    simpa [prefixWord, tailWord_3555073, baseEnd_3555073] using wordTrace_append hprefix tailTrace_3555073
  have hstable : (prefixWord ++ tailWord_3555073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555073).length < 2 ^ (prefixWord ++ tailWord_3555073).sum := by decide
  have hdescent : baseEnd_3555073 < baseStart_3555073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555078 : List Nat := [6, 2, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3555078 : Nat := 118140960795 + 3555078 * 2 ^ 59
def prefixEnd_3555078 : Nat := 4983230072969 + 3 ^ 40 * 3555078 * 2
def baseEnd_3555078 : Nat := 608487926074915658225167

theorem tailTrace_3555078 : CollatzResearch.WordTrace tailWord_3555078 prefixEnd_3555078 608487926074915658225167 := by
  unfold tailWord_3555078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052010844205219994659809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86442898009711359886075925 4052010844205219994659809)
  ·
    refine ⟨3039008133153914995994857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4052010844205219994659809 3039008133153914995994857)
    ·
      refine ⟨2279256099865436246996143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3039008133153914995994857 2279256099865436246996143)
      ·
        refine ⟨3418884149798154370494215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279256099865436246996143 3418884149798154370494215)
        ·
          refine ⟨5128326224697231555741323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3418884149798154370494215 5128326224697231555741323)
          ·
            refine ⟨7692489337045847333611985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128326224697231555741323 7692489337045847333611985)
            ·
              refine ⟨5769367002784385500208989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7692489337045847333611985 5769367002784385500208989)
              ·
                refine ⟨2163512626044144562578371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5769367002784385500208989 2163512626044144562578371)
                ·
                  refine ⟨3245268939066216843867557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163512626044144562578371 3245268939066216843867557)
                  ·
                    refine ⟨608487926074915658225167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3245268939066216843867557 608487926074915658225167)
                    ·
                      rfl

theorem cell23_3555078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3555078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555078 prefixEnd_3555078 := by exact prefixLift 3555078
  have htrace : WordTrace (prefixWord ++ tailWord_3555078) baseStart_3555078 baseEnd_3555078 := by
    simpa [prefixWord, tailWord_3555078, baseEnd_3555078] using wordTrace_append hprefix tailTrace_3555078
  have hstable : (prefixWord ++ tailWord_3555078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555078).length < 2 ^ (prefixWord ++ tailWord_3555078).sum := by decide
  have hdescent : baseEnd_3555078 < baseStart_3555078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555086 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3555086 : Nat := 118140960795 + 3555086 * 2 ^ 59
def prefixEnd_3555086 : Nat := 4983230072969 + 3 ^ 40 * 3555086 * 2
def baseEnd_3555086 : Nat := 1825467886069982943375463

theorem tailTrace_3555086 : CollatzResearch.WordTrace tailWord_3555086 prefixEnd_3555086 1825467886069982943375463 := by
  unfold tailWord_3555086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16208079849817257149425639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86443092532358704796936741 16208079849817257149425639)
  ·
    refine ⟨24312119774725885724138459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16208079849817257149425639 24312119774725885724138459)
    ·
      refine ⟨36468179662088828586207689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24312119774725885724138459 36468179662088828586207689)
      ·
        refine ⟨27351134746566621439655767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36468179662088828586207689 27351134746566621439655767)
        ·
          refine ⟨41026702119849932159483651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27351134746566621439655767 41026702119849932159483651)
          ·
            refine ⟨61540053179774898239225477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41026702119849932159483651 61540053179774898239225477)
            ·
              refine ⟨11538759971207793419854777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61540053179774898239225477 11538759971207793419854777)
              ·
                refine ⟨8654069978405845064891083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11538759971207793419854777 8654069978405845064891083)
                ·
                  refine ⟨12981104967608767597336625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8654069978405845064891083 12981104967608767597336625)
                  ·
                    refine ⟨9735828725706575698002469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12981104967608767597336625 9735828725706575698002469)
                    ·
                      refine ⟨1825467886069982943375463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9735828725706575698002469 1825467886069982943375463)
                      ·
                        rfl

theorem cell23_3555086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3555086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555086 prefixEnd_3555086 := by exact prefixLift 3555086
  have htrace : WordTrace (prefixWord ++ tailWord_3555086) baseStart_3555086 baseEnd_3555086 := by
    simpa [prefixWord, tailWord_3555086, baseEnd_3555086] using wordTrace_append hprefix tailTrace_3555086
  have hstable : (prefixWord ++ tailWord_3555086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555086).length < 2 ^ (prefixWord ++ tailWord_3555086).sum := by decide
  have hdescent : baseEnd_3555086 < baseStart_3555086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555090 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3555090 : Nat := 118140960795 + 3555090 * 2 ^ 59
def prefixEnd_3555090 : Nat := 4983230072969 + 3 ^ 40 * 3555090 * 2
def baseEnd_3555090 : Nat := 1825469939992600927725445

theorem tailTrace_3555090 : CollatzResearch.WordTrace tailWord_3555090 prefixEnd_3555090 1825469939992600927725445 := by
  unfold tailWord_3555090
  simp only [CollatzResearch.WordTrace]
  refine ⟨32416196172630891469637681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86443189793682377252367149 32416196172630891469637681)
  ·
    refine ⟨24312147129473168602228261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32416196172630891469637681 24312147129473168602228261)
    ·
      refine ⟨4558527586776219112917799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24312147129473168602228261 4558527586776219112917799)
      ·
        refine ⟨6837791380164328669376699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558527586776219112917799 6837791380164328669376699)
        ·
          refine ⟨10256687070246493004065049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6837791380164328669376699 10256687070246493004065049)
          ·
            refine ⟨7692515302684869753048787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10256687070246493004065049 7692515302684869753048787)
            ·
              refine ⟨11538772954027304629573181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692515302684869753048787 11538772954027304629573181)
              ·
                refine ⟨4327039857760239236089943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11538772954027304629573181 4327039857760239236089943)
                ·
                  refine ⟨6490559786640358854134915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327039857760239236089943 6490559786640358854134915)
                  ·
                    refine ⟨9735839679960538281202373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6490559786640358854134915 9735839679960538281202373)
                    ·
                      refine ⟨1825469939992600927725445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9735839679960538281202373 1825469939992600927725445)
                      ·
                        rfl

theorem cell23_3555090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3555090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555090 prefixEnd_3555090 := by exact prefixLift 3555090
  have htrace : WordTrace (prefixWord ++ tailWord_3555090) baseStart_3555090 baseEnd_3555090 := by
    simpa [prefixWord, tailWord_3555090, baseEnd_3555090] using wordTrace_append hprefix tailTrace_3555090
  have hstable : (prefixWord ++ tailWord_3555090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555090).length < 2 ^ (prefixWord ++ tailWord_3555090).sum := by decide
  have hdescent : baseEnd_3555090 < baseStart_3555090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555093 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_3555093 : Nat := 118140960795 + 3555093 * 2 ^ 59
def prefixEnd_3555093 : Nat := 4983230072969 + 3 ^ 40 * 3555093 * 2
def baseEnd_3555093 : Nat := 1825471480434564415987931

theorem tailTrace_3555093 : CollatzResearch.WordTrace tailWord_3555093 prefixEnd_3555093 1825471480434564415987931 := by
  unfold tailWord_3555093
  simp only [CollatzResearch.WordTrace]
  refine ⟨129664894109512697390909933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86443262739675131593939955 129664894109512697390909933)
  ·
    refine ⟨48624335291067261521591225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129664894109512697390909933 48624335291067261521591225)
    ·
      refine ⟨36468251468300446141193419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48624335291067261521591225 36468251468300446141193419)
      ·
        refine ⟨54702377202450669211790129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36468251468300446141193419 54702377202450669211790129)
        ·
          refine ⟨41026782901838001908842597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54702377202450669211790129 41026782901838001908842597)
          ·
            refine ⟨7692521794094625357907987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41026782901838001908842597 7692521794094625357907987)
            ·
              refine ⟨11538782691141938036861981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692521794094625357907987 11538782691141938036861981)
              ·
                refine ⟨4327043509178226763823243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11538782691141938036861981 4327043509178226763823243)
                ·
                  refine ⟨6490565263767340145734865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327043509178226763823243 6490565263767340145734865)
                  ·
                    refine ⟨4867923947825505109301149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6490565263767340145734865 4867923947825505109301149)
                    ·
                      refine ⟨1825471480434564415987931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4867923947825505109301149 1825471480434564415987931)
                      ·
                        rfl

theorem cell23_3555093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_3555093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555093 prefixEnd_3555093 := by exact prefixLift 3555093
  have htrace : WordTrace (prefixWord ++ tailWord_3555093) baseStart_3555093 baseEnd_3555093 := by
    simpa [prefixWord, tailWord_3555093, baseEnd_3555093] using wordTrace_append hprefix tailTrace_3555093
  have hstable : (prefixWord ++ tailWord_3555093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555093).length < 2 ^ (prefixWord ++ tailWord_3555093).sum := by decide
  have hdescent : baseEnd_3555093 < baseStart_3555093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555176 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3555176 : Nat := 118140960795 + 3555176 * 2 ^ 59
def prefixEnd_3555176 : Nat := 4983230072969 + 3 ^ 40 * 3555176 * 2
def baseEnd_3555176 : Nat := 1825514099328887591250049

theorem tailTrace_3555176 : CollatzResearch.WordTrace tailWord_3555176 prefixEnd_3555176 1825514099328887591250049 := by
  unfold tailWord_3555176
  simp only [CollatzResearch.WordTrace]
  refine ⟨64833960684106001283090691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86445280912141335044120921 64833960684106001283090691)
  ·
    refine ⟨97250941026159001924636037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64833960684106001283090691 97250941026159001924636037)
    ·
      refine ⟨18234551442404812860869257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97250941026159001924636037 18234551442404812860869257)
      ·
        refine ⟨13675913581803609645651943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18234551442404812860869257 13675913581803609645651943)
        ·
          refine ⟨20513870372705414468477915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13675913581803609645651943 20513870372705414468477915)
          ·
            refine ⟨30770805559058121702716873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20513870372705414468477915 30770805559058121702716873)
            ·
              refine ⟨23078104169293591277037655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30770805559058121702716873 23078104169293591277037655)
              ·
                refine ⟨34617156253940386915556483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23078104169293591277037655 34617156253940386915556483)
                ·
                  refine ⟨51925734380910580373334725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34617156253940386915556483 51925734380910580373334725)
                  ·
                    refine ⟨9736075196420733820000261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51925734380910580373334725 9736075196420733820000261)
                    ·
                      refine ⟨1825514099328887591250049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9736075196420733820000261 1825514099328887591250049)
                      ·
                        rfl

theorem cell23_3555176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3555176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555176 prefixEnd_3555176 := by exact prefixLift 3555176
  have htrace : WordTrace (prefixWord ++ tailWord_3555176) baseStart_3555176 baseEnd_3555176 := by
    simpa [prefixWord, tailWord_3555176, baseEnd_3555176] using wordTrace_append hprefix tailTrace_3555176
  have hstable : (prefixWord ++ tailWord_3555176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555176).length < 2 ^ (prefixWord ++ tailWord_3555176).sum := by decide
  have hdescent : baseEnd_3555176 < baseStart_3555176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555196 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_3555196 : Nat := 118140960795 + 3555196 * 2 ^ 59
def prefixEnd_3555196 : Nat := 4983230072969 + 3 ^ 40 * 3555196 * 2
def baseEnd_3555196 : Nat := 1825524368941977512999957

theorem tailTrace_3555196 : CollatzResearch.WordTrace tailWord_3555196 prefixEnd_3555196 1825524368941977512999957 := by
  unfold tailWord_3555196
  simp only [CollatzResearch.WordTrace]
  refine ⟨64834325414069772990954721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86445767218759697321272961 64834325414069772990954721)
  ·
    refine ⟨48625744060552329743216041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64834325414069772990954721 48625744060552329743216041)
    ·
      refine ⟨36469308045414247307412031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48625744060552329743216041 36469308045414247307412031)
      ·
        refine ⟨54703962068121370961118047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36469308045414247307412031 54703962068121370961118047)
        ·
          refine ⟨82055943102182056441677071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54703962068121370961118047 82055943102182056441677071)
          ·
            refine ⟨123083914653273084662515607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82055943102182056441677071 123083914653273084662515607)
            ·
              refine ⟨184625871979909626993773411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123083914653273084662515607 184625871979909626993773411)
              ·
                refine ⟨276938807969864440490660117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184625871979909626993773411 276938807969864440490660117)
                ·
                  refine ⟨12981506623587395647999693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 276938807969864440490660117 12981506623587395647999693)
                  ·
                    refine ⟨4868064983845273367999885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12981506623587395647999693 4868064983845273367999885)
                    ·
                      refine ⟨1825524368941977512999957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4868064983845273367999885 1825524368941977512999957)
                      ·
                        rfl

theorem cell23_3555196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_3555196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555196 prefixEnd_3555196 := by exact prefixLift 3555196
  have htrace : WordTrace (prefixWord ++ tailWord_3555196) baseStart_3555196 baseEnd_3555196 := by
    simpa [prefixWord, tailWord_3555196, baseEnd_3555196] using wordTrace_append hprefix tailTrace_3555196
  have hstable : (prefixWord ++ tailWord_3555196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555196).length < 2 ^ (prefixWord ++ tailWord_3555196).sum := by decide
  have hdescent : baseEnd_3555196 < baseStart_3555196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555220 : List Nat := [2, 4, 2, 1, 1, 3, 1, 4, 5]
def baseStart_3555220 : Nat := 118140960795 + 3555220 * 2 ^ 59
def prefixEnd_3555220 : Nat := 4983230072969 + 3 ^ 40 * 3555220 * 2
def baseEnd_3555220 : Nat := 202837410275298379899983

theorem tailTrace_3555220 : CollatzResearch.WordTrace tailWord_3555220 prefixEnd_3555220 202837410275298379899983 := by
  unfold tailWord_3555220
  simp only [CollatzResearch.WordTrace]
  refine ⟨64834763090026299040391557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86446350786701732053855409 64834763090026299040391557)
  ·
    refine ⟨12156518079379931070073417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64834763090026299040391557 12156518079379931070073417)
    ·
      refine ⟨9117388559534948302555063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12156518079379931070073417 9117388559534948302555063)
      ·
        refine ⟨13676082839302422453832595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9117388559534948302555063 13676082839302422453832595)
        ·
          refine ⟨20514124258953633680748893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13676082839302422453832595 20514124258953633680748893)
          ·
            refine ⟨7692796597107612630280835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20514124258953633680748893 7692796597107612630280835)
            ·
              refine ⟨11539194895661418945421253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692796597107612630280835 11539194895661418945421253)
              ·
                refine ⟨2163599042936516052266485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11539194895661418945421253 2163599042936516052266485)
                ·
                  refine ⟨202837410275298379899983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2163599042936516052266485 202837410275298379899983)
                  ·
                    rfl

theorem cell23_3555220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_3555220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555220 prefixEnd_3555220 := by exact prefixLift 3555220
  have htrace : WordTrace (prefixWord ++ tailWord_3555220) baseStart_3555220 baseEnd_3555220 := by
    simpa [prefixWord, tailWord_3555220, baseEnd_3555220] using wordTrace_append hprefix tailTrace_3555220
  have hstable : (prefixWord ++ tailWord_3555220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555220).length < 2 ^ (prefixWord ++ tailWord_3555220).sum := by decide
  have hdescent : baseEnd_3555220 < baseStart_3555220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555223 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 2, 5, 2]
def baseStart_3555223 : Nat := 118140960795 + 3555223 * 2 ^ 59
def prefixEnd_3555223 : Nat := 4983230072969 + 3 ^ 40 * 3555223 * 2
def baseEnd_3555223 : Nat := 1825538232919648907362333

theorem tailTrace_3555223 : CollatzResearch.WordTrace tailWord_3555223 prefixEnd_3555223 1825538232919648907362333 := by
  unfold tailWord_3555223
  simp only [CollatzResearch.WordTrace]
  refine ⟨129669635599041729593142323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86446423732694486395428215 129669635599041729593142323)
  ·
    refine ⟨194504453398562594389713485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129669635599041729593142323 194504453398562594389713485)
    ·
      refine ⟨72939170024460972896142557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194504453398562594389713485 72939170024460972896142557)
      ·
        refine ⟨27352188759172864836053459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72939170024460972896142557 27352188759172864836053459)
        ·
          refine ⟨41028283138759297254080189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27352188759172864836053459 41028283138759297254080189)
          ·
            refine ⟨15385606177034736470280071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41028283138759297254080189 15385606177034736470280071)
            ·
              refine ⟨23078409265552104705420107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15385606177034736470280071 23078409265552104705420107)
              ·
                refine ⟨34617613898328157058130161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23078409265552104705420107 34617613898328157058130161)
                ·
                  refine ⟨25963210423746117793597621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34617613898328157058130161 25963210423746117793597621)
                  ·
                    refine ⟨2434050977226198543149777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25963210423746117793597621 2434050977226198543149777)
                    ·
                      refine ⟨1825538232919648907362333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434050977226198543149777 1825538232919648907362333)
                      ·
                        rfl

theorem cell23_3555223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_3555223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555223 prefixEnd_3555223 := by exact prefixLift 3555223
  have htrace : WordTrace (prefixWord ++ tailWord_3555223) baseStart_3555223 baseEnd_3555223 := by
    simpa [prefixWord, tailWord_3555223, baseEnd_3555223] using wordTrace_append hprefix tailTrace_3555223
  have hstable : (prefixWord ++ tailWord_3555223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555223).length < 2 ^ (prefixWord ++ tailWord_3555223).sum := by decide
  have hdescent : baseEnd_3555223 < baseStart_3555223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555253 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3555253 : Nat := 118140960795 + 3555253 * 2 ^ 59
def prefixEnd_3555253 : Nat := 4983230072969 + 3 ^ 40 * 3555253 * 2
def baseEnd_3555253 : Nat := 1825553637339283789987195

theorem tailTrace_3555253 : CollatzResearch.WordTrace tailWord_3555253 prefixEnd_3555253 1825553637339283789987195 := by
  unfold tailWord_3555253
  simp only [CollatzResearch.WordTrace]
  refine ⟨129670729788933044716734413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86447153192622029811156275 129670729788933044716734413)
  ·
    refine ⟨48626523670849891768775405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129670729788933044716734413 48626523670849891768775405)
    ·
      refine ⟨18234946376568709413290777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48626523670849891768775405 18234946376568709413290777)
      ·
        refine ⟨13676209782426532059968083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18234946376568709413290777 13676209782426532059968083)
        ·
          refine ⟨20514314673639798089952125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13676209782426532059968083 20514314673639798089952125)
          ·
            refine ⟨7692868002614924283732047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20514314673639798089952125 7692868002614924283732047)
            ·
              refine ⟨11539302003922386425598071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692868002614924283732047 11539302003922386425598071)
              ·
                refine ⟨17308953005883579638397107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11539302003922386425598071 17308953005883579638397107)
                ·
                  refine ⟨25963429508825369457595661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17308953005883579638397107 25963429508825369457595661)
                  ·
                    refine ⟨9736286065809513546598373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25963429508825369457595661 9736286065809513546598373)
                    ·
                      refine ⟨1825553637339283789987195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9736286065809513546598373 1825553637339283789987195)
                      ·
                        rfl

theorem cell23_3555253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3555253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555253 prefixEnd_3555253 := by exact prefixLift 3555253
  have htrace : WordTrace (prefixWord ++ tailWord_3555253) baseStart_3555253 baseEnd_3555253 := by
    simpa [prefixWord, tailWord_3555253, baseEnd_3555253] using wordTrace_append hprefix tailTrace_3555253
  have hstable : (prefixWord ++ tailWord_3555253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555253).length < 2 ^ (prefixWord ++ tailWord_3555253).sum := by decide
  have hdescent : baseEnd_3555253 < baseStart_3555253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555280 : List Nat := [2, 1, 1, 1, 1, 2, 6, 4, 1, 4]
def baseStart_3555280 : Nat := 118140960795 + 3555280 * 2 ^ 59
def prefixEnd_3555280 : Nat := 4983230072969 + 3 ^ 40 * 3555280 * 2
def baseEnd_3555280 : Nat := 608522500438985061449857

theorem tailTrace_3555280 : CollatzResearch.WordTrace tailWord_3555280 prefixEnd_3555280 608522500438985061449857 := by
  unfold tailWord_3555280
  simp only [CollatzResearch.WordTrace]
  refine ⟨64835857279917614163983647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86447809706556818885311529 64835857279917614163983647)
  ·
    refine ⟨97253785919876421245975471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64835857279917614163983647 97253785919876421245975471)
    ·
      refine ⟨145880678879814631868963207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97253785919876421245975471 145880678879814631868963207)
      ·
        refine ⟨218821018319721947803444811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145880678879814631868963207 218821018319721947803444811)
        ·
          refine ⟨328231527479582921705167217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218821018319721947803444811 328231527479582921705167217)
          ·
            refine ⟨246173645609687191278875413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328231527479582921705167217 246173645609687191278875413)
            ·
              refine ⟨11539389637954087091197285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 246173645609687191278875413 11539389637954087091197285)
              ·
                refine ⟨2163635557116391329599491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11539389637954087091197285 2163635557116391329599491)
                ·
                  refine ⟨3245453335674586994399237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163635557116391329599491 3245453335674586994399237)
                  ·
                    refine ⟨608522500438985061449857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3245453335674586994399237 608522500438985061449857)
                    ·
                      rfl

theorem cell23_3555280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 1, 4].length) (baseStart_3555280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555280 prefixEnd_3555280 := by exact prefixLift 3555280
  have htrace : WordTrace (prefixWord ++ tailWord_3555280) baseStart_3555280 baseEnd_3555280 := by
    simpa [prefixWord, tailWord_3555280, baseEnd_3555280] using wordTrace_append hprefix tailTrace_3555280
  have hstable : (prefixWord ++ tailWord_3555280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555280).length < 2 ^ (prefixWord ++ tailWord_3555280).sum := by decide
  have hdescent : baseEnd_3555280 < baseStart_3555280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555323 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 1, 5]
def baseStart_3555323 : Nat := 118140960795 + 3555323 * 2 ^ 59
def prefixEnd_3555323 : Nat := 4983230072969 + 3 ^ 40 * 3555323 * 2
def baseEnd_3555323 : Nat := 608529860328366172037291

theorem tailTrace_3555323 : CollatzResearch.WordTrace tailWord_3555323 prefixEnd_3555323 608529860328366172037291 := by
  unfold tailWord_3555323
  simp only [CollatzResearch.WordTrace]
  refine ⟨129673282898679446671782623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86448855265786297781188415 129673282898679446671782623)
  ·
    refine ⟨194509924348019170007673935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129673282898679446671782623 194509924348019170007673935)
    ·
      refine ⟨291764886522028755011510903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194509924348019170007673935 291764886522028755011510903)
      ·
        refine ⟨437647329783043132517266355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291764886522028755011510903 437647329783043132517266355)
        ·
          refine ⟨656470994674564698775899533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437647329783043132517266355 656470994674564698775899533)
          ·
            refine ⟨246176623002961762040962325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 656470994674564698775899533 246176623002961762040962325)
            ·
              refine ⟨11539529203263832595670109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 246176623002961762040962325 11539529203263832595670109)
              ·
                refine ⟨4327323451223937223376291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11539529203263832595670109 4327323451223937223376291)
                ·
                  refine ⟨6490985176835905835064437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327323451223937223376291 6490985176835905835064437)
                  ·
                    refine ⟨608529860328366172037291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6490985176835905835064437 608529860328366172037291)
                    ·
                      rfl

theorem cell23_3555323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 5].length) (baseStart_3555323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555323 prefixEnd_3555323 := by exact prefixLift 3555323
  have htrace : WordTrace (prefixWord ++ tailWord_3555323) baseStart_3555323 baseEnd_3555323 := by
    simpa [prefixWord, tailWord_3555323, baseEnd_3555323] using wordTrace_append hprefix tailTrace_3555323
  have hstable : (prefixWord ++ tailWord_3555323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555323).length < 2 ^ (prefixWord ++ tailWord_3555323).sum := by decide
  have hdescent : baseEnd_3555323 < baseStart_3555323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555357 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_3555357 : Nat := 118140960795 + 3555357 * 2 ^ 59
def prefixEnd_3555357 : Nat := 4983230072969 + 3 ^ 40 * 3555357 * 2
def baseEnd_3555357 : Nat := 608535679775783794362239

theorem tailTrace_3555357 : CollatzResearch.WordTrace tailWord_3555357 prefixEnd_3555357 608535679775783794362239 := by
  unfold tailWord_3555357
  simp only [CollatzResearch.WordTrace]
  refine ⟨129674522980556270478520325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86449681987037513652346883 129674522980556270478520325)
  ·
    refine ⟨24313973058854300714722561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129674522980556270478520325 24313973058854300714722561)
    ·
      refine ⟨18235479794140725536041921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24313973058854300714722561 18235479794140725536041921)
      ·
        refine ⟨13676609845605544152031441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18235479794140725536041921 13676609845605544152031441)
        ·
          refine ⟨10257457384204158114023581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13676609845605544152031441 10257457384204158114023581)
          ·
            refine ⟨3846546519076559292758843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10257457384204158114023581 3846546519076559292758843)
            ·
              refine ⟨5769819778614838939138265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846546519076559292758843 5769819778614838939138265)
              ·
                refine ⟨4327364833961129204353699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5769819778614838939138265 4327364833961129204353699)
                ·
                  refine ⟨6491047250941693806530549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327364833961129204353699 6491047250941693806530549)
                  ·
                    refine ⟨608535679775783794362239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6491047250941693806530549 608535679775783794362239)
                    ·
                      rfl

theorem cell23_3555357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_3555357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555357 prefixEnd_3555357 := by exact prefixLift 3555357
  have htrace : WordTrace (prefixWord ++ tailWord_3555357) baseStart_3555357 baseEnd_3555357 := by
    simpa [prefixWord, tailWord_3555357, baseEnd_3555357] using wordTrace_append hprefix tailTrace_3555357
  have hstable : (prefixWord ++ tailWord_3555357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555357).length < 2 ^ (prefixWord ++ tailWord_3555357).sum := by decide
  have hdescent : baseEnd_3555357 < baseStart_3555357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555364 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 2, 3, 2]
def baseStart_3555364 : Nat := 118140960795 + 3555364 * 2 ^ 59
def prefixEnd_3555364 : Nat := 4983230072969 + 3 ^ 40 * 3555364 * 2
def baseEnd_3555364 : Nat := 1825610633691932855699185

theorem tailTrace_3555364 : CollatzResearch.WordTrace tailWord_3555364 prefixEnd_3555364 1825610633691932855699185 := by
  unfold tailWord_3555364
  simp only [CollatzResearch.WordTrace]
  refine ⟨64837389145765455337012573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86449852194353940449350097 64837389145765455337012573)
  ·
    refine ⟨24314020929662045751379715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64837389145765455337012573 24314020929662045751379715)
    ·
      refine ⟨36471031394493068627069573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24314020929662045751379715 36471031394493068627069573)
      ·
        refine ⟨6838318386467450367575545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36471031394493068627069573 6838318386467450367575545)
        ·
          refine ⟨5128738789850587775681659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6838318386467450367575545 5128738789850587775681659)
          ·
            refine ⟨7693108184775881663522489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128738789850587775681659 7693108184775881663522489)
            ·
              refine ⟨5769831138581911247641867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7693108184775881663522489 5769831138581911247641867)
              ·
                refine ⟨8654746707872866871462801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5769831138581911247641867 8654746707872866871462801)
                ·
                  refine ⟨6491060030904650153597101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8654746707872866871462801 6491060030904650153597101)
                  ·
                    refine ⟨2434147511589243807598913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6491060030904650153597101 2434147511589243807598913)
                    ·
                      refine ⟨1825610633691932855699185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434147511589243807598913 1825610633691932855699185)
                      ·
                        rfl

theorem cell23_3555364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_3555364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555364 prefixEnd_3555364 := by exact prefixLift 3555364
  have htrace : WordTrace (prefixWord ++ tailWord_3555364) baseStart_3555364 baseEnd_3555364 := by
    simpa [prefixWord, tailWord_3555364, baseEnd_3555364] using wordTrace_append hprefix tailTrace_3555364
  have hstable : (prefixWord ++ tailWord_3555364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555364).length < 2 ^ (prefixWord ++ tailWord_3555364).sum := by decide
  have hdescent : baseEnd_3555364 < baseStart_3555364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555370 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3555370 : Nat := 118140960795 + 3555370 * 2 ^ 59
def prefixEnd_3555370 : Nat := 4983230072969 + 3 ^ 40 * 3555370 * 2
def baseEnd_3555370 : Nat := 608537904858619944074719

theorem tailTrace_3555370 : CollatzResearch.WordTrace tailWord_3555370 prefixEnd_3555370 608537904858619944074719 := by
  unfold tailWord_3555370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32418749282377293424685891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86449998086339449132495709 32418749282377293424685891)
  ·
    refine ⟨48628123923565940137028837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32418749282377293424685891 48628123923565940137028837)
    ·
      refine ⟨9117773235668613775692907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48628123923565940137028837 9117773235668613775692907)
      ·
        refine ⟨13676659853502920663539361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9117773235668613775692907 13676659853502920663539361)
        ·
          refine ⟨10257494890127190497654521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13676659853502920663539361 10257494890127190497654521)
          ·
            refine ⟨7693121167595392873240891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10257494890127190497654521 7693121167595392873240891)
            ·
              refine ⟨11539681751393089309861337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7693121167595392873240891 11539681751393089309861337)
              ·
                refine ⟨8654761313544816982396003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11539681751393089309861337 8654761313544816982396003)
                ·
                  refine ⟨12982141970317225473594005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8654761313544816982396003 12982141970317225473594005)
                  ·
                    refine ⟨608537904858619944074719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12982141970317225473594005 608537904858619944074719)
                    ·
                      rfl

theorem cell23_3555370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3555370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555370 prefixEnd_3555370 := by exact prefixLift 3555370
  have htrace : WordTrace (prefixWord ++ tailWord_3555370) baseStart_3555370 baseEnd_3555370 := by
    simpa [prefixWord, tailWord_3555370, baseEnd_3555370] using wordTrace_append hprefix tailTrace_3555370
  have hstable : (prefixWord ++ tailWord_3555370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555370).length < 2 ^ (prefixWord ++ tailWord_3555370).sum := by decide
  have hdescent : baseEnd_3555370 < baseStart_3555370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555377 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 1, 1, 4]
def baseStart_3555377 : Nat := 118140960795 + 3555377 * 2 ^ 59
def prefixEnd_3555377 : Nat := 4983230072969 + 3 ^ 40 * 3555377 * 2
def baseEnd_3555377 : Nat := 1825617308940441304836625

theorem tailTrace_3555377 : CollatzResearch.WordTrace tailWord_3555377 prefixEnd_3555377 1825617308940441304836625 := by
  unfold tailWord_3555377
  simp only [CollatzResearch.WordTrace]
  refine ⟨129675252440483813894248385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86450168293655875929498923 129675252440483813894248385)
  ·
    refine ⟨97256439330362860420686289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129675252440483813894248385 97256439330362860420686289)
    ·
      refine ⟨72942329497772145315514717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97256439330362860420686289 72942329497772145315514717)
      ·
        refine ⟨27353373561664554493318019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72942329497772145315514717 27353373561664554493318019)
        ·
          refine ⟨41030060342496831739977029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27353373561664554493318019 41030060342496831739977029)
          ·
            refine ⟨7693136314218155951245693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41030060342496831739977029 7693136314218155951245693)
            ·
              refine ⟨2884926117831808481717135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7693136314218155951245693 2884926117831808481717135)
              ·
                refine ⟨4327389176747712722575703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2884926117831808481717135 4327389176747712722575703)
                ·
                  refine ⟨6491083765121569083863555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327389176747712722575703 6491083765121569083863555)
                  ·
                    refine ⟨9736625647682353625795333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6491083765121569083863555 9736625647682353625795333)
                    ·
                      refine ⟨1825617308940441304836625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9736625647682353625795333 1825617308940441304836625)
                      ·
                        rfl

theorem cell23_3555377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_3555377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555377 prefixEnd_3555377 := by exact prefixLift 3555377
  have htrace : WordTrace (prefixWord ++ tailWord_3555377) baseStart_3555377 baseEnd_3555377 := by
    simpa [prefixWord, tailWord_3555377, baseEnd_3555377] using wordTrace_append hprefix tailTrace_3555377
  have hstable : (prefixWord ++ tailWord_3555377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555377).length < 2 ^ (prefixWord ++ tailWord_3555377).sum := by decide
  have hdescent : baseEnd_3555377 < baseStart_3555377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555414 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3555414 : Nat := 118140960795 + 3555414 * 2 ^ 59
def prefixEnd_3555414 : Nat := 4983230072969 + 3 ^ 40 * 3555414 * 2
def baseEnd_3555414 : Nat := 1825636307724657660073955

theorem tailTrace_3555414 : CollatzResearch.WordTrace tailWord_3555414 prefixEnd_3555414 1825636307724657660073955 := by
  unfold tailWord_3555414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8104787621334360575834081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86451067960899846142230197 8104787621334360575834081)
  ·
    refine ⟨6078590716000770431875561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8104787621334360575834081 6078590716000770431875561)
    ·
      refine ⟨4558943037000577823906671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6078590716000770431875561 4558943037000577823906671)
      ·
        refine ⟨6838414555500866735860007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558943037000577823906671 6838414555500866735860007)
        ·
          refine ⟨10257621833251300103790011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6838414555500866735860007 10257621833251300103790011)
          ·
            refine ⟨15386432749876950155685017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10257621833251300103790011 15386432749876950155685017)
            ·
              refine ⟨11539824562407712616763763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15386432749876950155685017 11539824562407712616763763)
              ·
                refine ⟨17309736843611568925145645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11539824562407712616763763 17309736843611568925145645)
                ·
                  refine ⟨6491151316354338346929617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17309736843611568925145645 6491151316354338346929617)
                  ·
                    refine ⟨4868363487265753760197213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6491151316354338346929617 4868363487265753760197213)
                    ·
                      refine ⟨1825636307724657660073955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4868363487265753760197213 1825636307724657660073955)
                      ·
                        rfl

theorem cell23_3555414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3555414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555414 prefixEnd_3555414 := by exact prefixLift 3555414
  have htrace : WordTrace (prefixWord ++ tailWord_3555414) baseStart_3555414 baseEnd_3555414 := by
    simpa [prefixWord, tailWord_3555414, baseEnd_3555414] using wordTrace_append hprefix tailTrace_3555414
  have hstable : (prefixWord ++ tailWord_3555414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555414).length < 2 ^ (prefixWord ++ tailWord_3555414).sum := by decide
  have hdescent : baseEnd_3555414 < baseStart_3555414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555557 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3555557 : Nat := 118140960795 + 3555557 * 2 ^ 59
def prefixEnd_3555557 : Nat := 4983230072969 + 3 ^ 40 * 3555557 * 2
def baseEnd_3555557 : Nat := 1825709735458250600585797

theorem tailTrace_3555557 : CollatzResearch.WordTrace tailWord_3555557 prefixEnd_3555557 1825709735458250600585797 := by
  unfold tailWord_3555557
  simp only [CollatzResearch.WordTrace]
  refine ⟨129681817579831704635800925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86454545053221136423867283 129681817579831704635800925)
  ·
    refine ⟨48630681592436889238425347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129681817579831704635800925 48630681592436889238425347)
    ·
      refine ⟨72946022388655333857638021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48630681592436889238425347 72946022388655333857638021)
      ·
        refine ⟨13677379197872875098307129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72946022388655333857638021 13677379197872875098307129)
        ·
          refine ⟨10258034398404656323730347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13677379197872875098307129 10258034398404656323730347)
          ·
            refine ⟨15387051597606984485595521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10258034398404656323730347 15387051597606984485595521)
            ·
              refine ⟨11540288698205238364196641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15387051597606984485595521 11540288698205238364196641)
              ·
                refine ⟨8655216523653928773147481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11540288698205238364196641 8655216523653928773147481)
                ·
                  refine ⟨6491412392740446579860611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8655216523653928773147481 6491412392740446579860611)
                  ·
                    refine ⟨9737118589110669869790917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6491412392740446579860611 9737118589110669869790917)
                    ·
                      refine ⟨1825709735458250600585797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9737118589110669869790917 1825709735458250600585797)
                      ·
                        rfl

theorem cell23_3555557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3555557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555557 prefixEnd_3555557 := by exact prefixLift 3555557
  have htrace : WordTrace (prefixWord ++ tailWord_3555557) baseStart_3555557 baseEnd_3555557 := by
    simpa [prefixWord, tailWord_3555557, baseEnd_3555557] using wordTrace_append hprefix tailTrace_3555557
  have hstable : (prefixWord ++ tailWord_3555557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555557).length < 2 ^ (prefixWord ++ tailWord_3555557).sum := by decide
  have hdescent : baseEnd_3555557 < baseStart_3555557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555591 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3555591 : Nat := 118140960795 + 3555591 * 2 ^ 59
def prefixEnd_3555591 : Nat := 4983230072969 + 3 ^ 40 * 3555591 * 2
def baseEnd_3555591 : Nat := 1825727193800503467560641

theorem tailTrace_3555591 : CollatzResearch.WordTrace tailWord_3555591 prefixEnd_3555591 1825727193800503467560641 := by
  unfold tailWord_3555591
  simp only [CollatzResearch.WordTrace]
  refine ⟨129683057661708528442538627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86455371774472352295025751 129683057661708528442538627)
  ·
    refine ⟨194524586492562792663807941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129683057661708528442538627 194524586492562792663807941)
    ·
      refine ⟨36473359967355523624463989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194524586492562792663807941 36473359967355523624463989)
      ·
        refine ⟨3419377496939580339793499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36473359967355523624463989 3419377496939580339793499)
        ·
          refine ⟨5129066245409370509690249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3419377496939580339793499 5129066245409370509690249)
          ·
            refine ⟨3846799684057027882267687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5129066245409370509690249 3846799684057027882267687)
            ·
              refine ⟨5770199526085541823401531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846799684057027882267687 5770199526085541823401531)
              ·
                refine ⟨8655299289128312735102297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5770199526085541823401531 8655299289128312735102297)
                ·
                  refine ⟨6491474466846234551326723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8655299289128312735102297 6491474466846234551326723)
                  ·
                    refine ⟨9737211700269351826990085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6491474466846234551326723 9737211700269351826990085)
                    ·
                      refine ⟨1825727193800503467560641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9737211700269351826990085 1825727193800503467560641)
                      ·
                        rfl

theorem cell23_3555591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3555591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555591 prefixEnd_3555591 := by exact prefixLift 3555591
  have htrace : WordTrace (prefixWord ++ tailWord_3555591) baseStart_3555591 baseEnd_3555591 := by
    simpa [prefixWord, tailWord_3555591, baseEnd_3555591] using wordTrace_append hprefix tailTrace_3555591
  have hstable : (prefixWord ++ tailWord_3555591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555591).length < 2 ^ (prefixWord ++ tailWord_3555591).sum := by decide
  have hdescent : baseEnd_3555591 < baseStart_3555591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555614 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_3555614 : Nat := 118140960795 + 3555614 * 2 ^ 59
def prefixEnd_3555614 : Nat := 4983230072969 + 3 ^ 40 * 3555614 * 2
def baseEnd_3555614 : Nat := 202859889317284097508115

theorem tailTrace_3555614 : CollatzResearch.WordTrace tailWord_3555614 prefixEnd_3555614 202859889317284097508115 := by
  unfold tailWord_3555614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16210487067578150421328237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86455931027083468913750597 16210487067578150421328237)
  ·
    refine ⟨6078932650341806407998089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16210487067578150421328237 6078932650341806407998089)
    ·
      refine ⟨4559199487756354805998567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6078932650341806407998089 4559199487756354805998567)
      ·
        refine ⟨6838799231634532208997851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4559199487756354805998567 6838799231634532208997851)
        ·
          refine ⟨10258198847451798313496777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6838799231634532208997851 10258198847451798313496777)
          ·
            refine ⟨7693649135588848735122583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10258198847451798313496777 7693649135588848735122583)
            ·
              refine ⟨11540473703383273102683875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7693649135588848735122583 11540473703383273102683875)
              ·
                refine ⟨17310710555074909654025813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11540473703383273102683875 17310710555074909654025813)
                ·
                  refine ⟨202859889317284097508115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17310710555074909654025813 202859889317284097508115)
                  ·
                    rfl

theorem cell23_3555614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_3555614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555614 prefixEnd_3555614 := by exact prefixLift 3555614
  have htrace : WordTrace (prefixWord ++ tailWord_3555614) baseStart_3555614 baseEnd_3555614 := by
    simpa [prefixWord, tailWord_3555614, baseEnd_3555614] using wordTrace_append hprefix tailTrace_3555614
  have hstable : (prefixWord ++ tailWord_3555614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555614).length < 2 ^ (prefixWord ++ tailWord_3555614).sum := by decide
  have hdescent : baseEnd_3555614 < baseStart_3555614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555647 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 2, 6, 2]
def baseStart_3555647 : Nat := 118140960795 + 3555647 * 2 ^ 59
def prefixEnd_3555647 : Nat := 4983230072969 + 3 ^ 40 * 3555647 * 2
def baseEnd_3555647 : Nat := 1825755948717155248460383

theorem tailTrace_3555647 : CollatzResearch.WordTrace tailWord_3555647 prefixEnd_3555647 1825755948717155248460383 := by
  unfold tailWord_3555647
  simp only [CollatzResearch.WordTrace]
  refine ⟨129685100149505650006577195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86456733433003766671051463 129685100149505650006577195)
  ·
    refine ⟨194527650224258475009865793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129685100149505650006577195 194527650224258475009865793)
    ·
      refine ⟨145895737668193856257399345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194527650224258475009865793 145895737668193856257399345)
      ·
        refine ⟨109421803251145392193049509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145895737668193856257399345 109421803251145392193049509)
        ·
          refine ⟨20516588109589761036196783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109421803251145392193049509 20516588109589761036196783)
          ·
            refine ⟨30774882164384641554295175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20516588109589761036196783 30774882164384641554295175)
            ·
              refine ⟨46162323246576962331442763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30774882164384641554295175 46162323246576962331442763)
              ·
                refine ⟨69243484869865443497164145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46162323246576962331442763 69243484869865443497164145)
                ·
                  refine ⟨51932613652399082622873109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69243484869865443497164145 51932613652399082622873109)
                  ·
                    refine ⟨2434341264956206997947177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51932613652399082622873109 2434341264956206997947177)
                    ·
                      refine ⟨1825755948717155248460383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434341264956206997947177 1825755948717155248460383)
                      ·
                        rfl

theorem cell23_3555647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_3555647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555647 prefixEnd_3555647 := by exact prefixLift 3555647
  have htrace : WordTrace (prefixWord ++ tailWord_3555647) baseStart_3555647 baseEnd_3555647 := by
    simpa [prefixWord, tailWord_3555647, baseEnd_3555647] using wordTrace_append hprefix tailTrace_3555647
  have hstable : (prefixWord ++ tailWord_3555647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555647).length < 2 ^ (prefixWord ++ tailWord_3555647).sum := by decide
  have hdescent : baseEnd_3555647 < baseStart_3555647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555687 : List Nat := [1, 1, 5, 1, 3, 2, 2, 8]
def baseStart_3555687 : Nat := 118140960795 + 3555687 * 2 ^ 59
def prefixEnd_3555687 : Nat := 4983230072969 + 3 ^ 40 * 3555687 * 2
def baseEnd_3555687 : Nat := 67621351405308707109637

theorem tailTrace_3555687 : CollatzResearch.WordTrace tailWord_3555687 prefixEnd_3555687 67621351405308707109637 := by
  unfold tailWord_3555687
  simp only [CollatzResearch.WordTrace]
  refine ⟨129686559069360736838033315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86457706046240491225355543 129686559069360736838033315)
  ·
    refine ⟨194529838604041105257049973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129686559069360736838033315 194529838604041105257049973)
    ·
      refine ⟨18237172369128853617848435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194529838604041105257049973 18237172369128853617848435)
      ·
        refine ⟨27355758553693280426772653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18237172369128853617848435 27355758553693280426772653)
        ·
          refine ⟨10258409457634980160039745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27355758553693280426772653 10258409457634980160039745)
          ·
            refine ⟨7693807093226235120029809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10258409457634980160039745 7693807093226235120029809)
            ·
              refine ⟨5770355319919676340022357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7693807093226235120029809 5770355319919676340022357)
              ·
                refine ⟨67621351405308707109637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5770355319919676340022357 67621351405308707109637)
                ·
                  rfl

theorem cell23_3555687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 8].length) (baseStart_3555687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555687 prefixEnd_3555687 := by exact prefixLift 3555687
  have htrace : WordTrace (prefixWord ++ tailWord_3555687) baseStart_3555687 baseEnd_3555687 := by
    simpa [prefixWord, tailWord_3555687, baseEnd_3555687] using wordTrace_append hprefix tailTrace_3555687
  have hstable : (prefixWord ++ tailWord_3555687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555687).length < 2 ^ (prefixWord ++ tailWord_3555687).sum := by decide
  have hdescent : baseEnd_3555687 < baseStart_3555687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555697 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 1, 3, 3]
def baseStart_3555697 : Nat := 118140960795 + 3555697 * 2 ^ 59
def prefixEnd_3555697 : Nat := 4983230072969 + 3 ^ 40 * 3555697 * 2
def baseEnd_3555697 : Nat := 1825781622749880052835153

theorem tailTrace_3555697 : CollatzResearch.WordTrace tailWord_3555697 prefixEnd_3555697 1825781622749880052835153 := by
  unfold tailWord_3555697
  simp only [CollatzResearch.WordTrace]
  refine ⟨129686923799324508545897345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86457949199549672363931563 129686923799324508545897345)
  ·
    refine ⟨97265192849493381409423009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129686923799324508545897345 97265192849493381409423009)
    ·
      refine ⟨72948894637120036057067257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97265192849493381409423009 72948894637120036057067257)
      ·
        refine ⟨54711670977840027042800443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72948894637120036057067257 54711670977840027042800443)
        ·
          refine ⟨82067506466760040564200665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54711670977840027042800443 82067506466760040564200665)
          ·
            refine ⟨61550629850070030423150499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82067506466760040564200665 61550629850070030423150499)
            ·
              refine ⟨92325944775105045634725749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61550629850070030423150499 92325944775105045634725749)
              ·
                refine ⟨8655557322666098028255539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92325944775105045634725749 8655557322666098028255539)
                ·
                  refine ⟨12983335983999147042383309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8655557322666098028255539 12983335983999147042383309)
                  ·
                    refine ⟨4868750993999680140893741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12983335983999147042383309 4868750993999680140893741)
                    ·
                      refine ⟨1825781622749880052835153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4868750993999680140893741 1825781622749880052835153)
                      ·
                        rfl

theorem cell23_3555697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_3555697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555697 prefixEnd_3555697 := by exact prefixLift 3555697
  have htrace : WordTrace (prefixWord ++ tailWord_3555697) baseStart_3555697 baseEnd_3555697 := by
    simpa [prefixWord, tailWord_3555697, baseEnd_3555697] using wordTrace_append hprefix tailTrace_3555697
  have hstable : (prefixWord ++ tailWord_3555697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555697).length < 2 ^ (prefixWord ++ tailWord_3555697).sum := by decide
  have hdescent : baseEnd_3555697 < baseStart_3555697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555701 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3555701 : Nat := 118140960795 + 3555701 * 2 ^ 59
def prefixEnd_3555701 : Nat := 4983230072969 + 3 ^ 40 * 3555701 * 2
def baseEnd_3555701 : Nat := 1825783676672498037185135

theorem tailTrace_3555701 : CollatzResearch.WordTrace tailWord_3555701 prefixEnd_3555701 1825783676672498037185135 := by
  unfold tailWord_3555701
  simp only [CollatzResearch.WordTrace]
  refine ⟨129687069691310017229042957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86458046460873344819361971 129687069691310017229042957)
  ·
    refine ⟨48632651134241256460891109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129687069691310017229042957 48632651134241256460891109)
    ·
      refine ⟨9118622087670235586417083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48632651134241256460891109 9118622087670235586417083)
      ·
        refine ⟨13677933131505353379625625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9118622087670235586417083 13677933131505353379625625)
        ·
          refine ⟨10258449848629015034719219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13677933131505353379625625 10258449848629015034719219)
          ·
            refine ⟨15387674772943522552078829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10258449848629015034719219 15387674772943522552078829)
            ·
              refine ⟨5770378039853820957029561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15387674772943522552078829 5770378039853820957029561)
              ·
                refine ⟨4327783529890365717772171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5770378039853820957029561 4327783529890365717772171)
                ·
                  refine ⟨6491675294835548576658257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327783529890365717772171 6491675294835548576658257)
                  ·
                    refine ⟨4868756471126661432493693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6491675294835548576658257 4868756471126661432493693)
                    ·
                      refine ⟨1825783676672498037185135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4868756471126661432493693 1825783676672498037185135)
                      ·
                        rfl

theorem cell23_3555701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3555701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555701 prefixEnd_3555701 := by exact prefixLift 3555701
  have htrace : WordTrace (prefixWord ++ tailWord_3555701) baseStart_3555701 baseEnd_3555701 := by
    simpa [prefixWord, tailWord_3555701, baseEnd_3555701] using wordTrace_append hprefix tailTrace_3555701
  have hstable : (prefixWord ++ tailWord_3555701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555701).length < 2 ^ (prefixWord ++ tailWord_3555701).sum := by decide
  have hdescent : baseEnd_3555701 < baseStart_3555701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555747 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 2, 6]
def baseStart_3555747 : Nat := 118140960795 + 3555747 * 2 ^ 59
def prefixEnd_3555747 : Nat := 4983230072969 + 3 ^ 40 * 3555747 * 2
def baseEnd_3555747 : Nat := 608602432260868285736641

theorem tailTrace_3555747 : CollatzResearch.WordTrace tailWord_3555747 prefixEnd_3555747 608602432260868285736641 := by
  unfold tailWord_3555747
  simp only [CollatzResearch.WordTrace]
  refine ⟨129688747449143367085217495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86459164966095578056811663 129688747449143367085217495)
  ·
    refine ⟨194533121173715050627826243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129688747449143367085217495 194533121173715050627826243)
    ·
      refine ⟨291799681760572575941739365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194533121173715050627826243 291799681760572575941739365)
      ·
        refine ⟨54712440330107357989076131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291799681760572575941739365 54712440330107357989076131)
        ·
          refine ⟨82068660495161036983614197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54712440330107357989076131 82068660495161036983614197)
          ·
            refine ⟨7693936921421347217213831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82068660495161036983614197 7693936921421347217213831)
            ·
              refine ⟨11540905382132020825820747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7693936921421347217213831 11540905382132020825820747)
              ·
                refine ⟨17311358073198031238731121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11540905382132020825820747 17311358073198031238731121)
                ·
                  refine ⟨12983518554898523429048341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17311358073198031238731121 12983518554898523429048341)
                  ·
                    refine ⟨608602432260868285736641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12983518554898523429048341 608602432260868285736641)
                    ·
                      rfl

theorem cell23_3555747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 6].length) (baseStart_3555747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555747 prefixEnd_3555747 := by exact prefixLift 3555747
  have htrace : WordTrace (prefixWord ++ tailWord_3555747) baseStart_3555747 baseEnd_3555747 := by
    simpa [prefixWord, tailWord_3555747, baseEnd_3555747] using wordTrace_append hprefix tailTrace_3555747
  have hstable : (prefixWord ++ tailWord_3555747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555747).length < 2 ^ (prefixWord ++ tailWord_3555747).sum := by decide
  have hdescent : baseEnd_3555747 < baseStart_3555747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555788 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 4, 2, 2]
def baseStart_3555788 : Nat := 118140960795 + 3555788 * 2 ^ 59
def prefixEnd_3555788 : Nat := 4983230072969 + 3 ^ 40 * 3555788 * 2
def baseEnd_3555788 : Nat := 1825828349489439196797235

theorem tailTrace_3555788 : CollatzResearch.WordTrace tailWord_3555788 prefixEnd_3555788 1825828349489439196797235 := by
  unfold tailWord_3555788
  simp only [CollatzResearch.WordTrace]
  refine ⟨64845121420997415543730009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86460161894663220724973345 64845121420997415543730009)
  ·
    refine ⟨48633841065748061657797507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64845121420997415543730009 48633841065748061657797507)
    ·
      refine ⟨72950761598622092486696261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48633841065748061657797507 72950761598622092486696261)
      ·
        refine ⟨13678267799741642341255549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72950761598622092486696261 13678267799741642341255549)
        ·
          refine ⟨5129350424903115877970831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13678267799741642341255549 5129350424903115877970831)
          ·
            refine ⟨7694025637354673816956247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129350424903115877970831 7694025637354673816956247)
            ·
              refine ⟨11541038456032010725434371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694025637354673816956247 11541038456032010725434371)
              ·
                refine ⟨17311557684048016088151557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11541038456032010725434371 17311557684048016088151557)
                ·
                  refine ⟨3245917065759003016528417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17311557684048016088151557 3245917065759003016528417)
                  ·
                    refine ⟨2434437799319252262396313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3245917065759003016528417 2434437799319252262396313)
                    ·
                      refine ⟨1825828349489439196797235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434437799319252262396313 1825828349489439196797235)
                      ·
                        rfl

theorem cell23_3555788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_3555788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555788 prefixEnd_3555788 := by exact prefixLift 3555788
  have htrace : WordTrace (prefixWord ++ tailWord_3555788) baseStart_3555788 baseEnd_3555788 := by
    simpa [prefixWord, tailWord_3555788, baseEnd_3555788] using wordTrace_append hprefix tailTrace_3555788
  have hstable : (prefixWord ++ tailWord_3555788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555788).length < 2 ^ (prefixWord ++ tailWord_3555788).sum := by decide
  have hdescent : baseEnd_3555788 < baseStart_3555788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555805 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_3555805 : Nat := 118140960795 + 3555805 * 2 ^ 59
def prefixEnd_3555805 : Nat := 4983230072969 + 3 ^ 40 * 3555805 * 2
def baseEnd_3555805 : Nat := 1825837078660565630284657

theorem tailTrace_3555805 : CollatzResearch.WordTrace tailWord_3555805 prefixEnd_3555805 1825837078660565630284657 := by
  unfold tailWord_3555805
  simp only [CollatzResearch.WordTrace]
  refine ⟨129690862882933242990828869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86460575255288828660552579 129690862882933242990828869)
  ·
    refine ⟨24317036790549983060780413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129690862882933242990828869 24317036790549983060780413)
    ·
      refine ⟨9118888796456243647792655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24317036790549983060780413 9118888796456243647792655)
      ·
        refine ⟨13678333194684365471688983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9118888796456243647792655 13678333194684365471688983)
        ·
          refine ⟨20517499792026548207533475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13678333194684365471688983 20517499792026548207533475)
          ·
            refine ⟨30776249688039822311300213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20517499792026548207533475 30776249688039822311300213)
            ·
              refine ⟨2885273408253733341684395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30776249688039822311300213 2885273408253733341684395)
              ·
                refine ⟨4327910112380600012526593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885273408253733341684395 4327910112380600012526593)
                ·
                  refine ⟨3245932584285450009394945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4327910112380600012526593 3245932584285450009394945)
                  ·
                    refine ⟨2434449438214087507046209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3245932584285450009394945 2434449438214087507046209)
                    ·
                      refine ⟨1825837078660565630284657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434449438214087507046209 1825837078660565630284657)
                      ·
                        rfl

theorem cell23_3555805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_3555805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555805 prefixEnd_3555805 := by exact prefixLift 3555805
  have htrace : WordTrace (prefixWord ++ tailWord_3555805) baseStart_3555805 baseEnd_3555805 := by
    simpa [prefixWord, tailWord_3555805, baseEnd_3555805] using wordTrace_append hprefix tailTrace_3555805
  have hstable : (prefixWord ++ tailWord_3555805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555805).length < 2 ^ (prefixWord ++ tailWord_3555805).sum := by decide
  have hdescent : baseEnd_3555805 < baseStart_3555805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555807 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 1, 7]
def baseStart_3555807 : Nat := 118140960795 + 3555807 * 2 ^ 59
def prefixEnd_3555807 : Nat := 4983230072969 + 3 ^ 40 * 3555807 * 2
def baseEnd_3555807 : Nat := 608612701873958207486549

theorem tailTrace_3555807 : CollatzResearch.WordTrace tailWord_3555807 prefixEnd_3555807 608612701873958207486549 := by
  unfold tailWord_3555807
  simp only [CollatzResearch.WordTrace]
  refine ⟨129690935828925997332401675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86460623885950664888267783 129690935828925997332401675)
  ·
    refine ⟨194536403743388995998602513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129690935828925997332401675 194536403743388995998602513)
    ·
      refine ⟨145902302807541746998951885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194536403743388995998602513 145902302807541746998951885)
      ·
        refine ⟨54713363552828155124606957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145902302807541746998951885 54713363552828155124606957)
        ·
          refine ⟨20517511332310558171727609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54713363552828155124606957 20517511332310558171727609)
          ·
            refine ⟨15388133499232918628795707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20517511332310558171727609 15388133499232918628795707)
            ·
              refine ⟨23082200248849377943193561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15388133499232918628795707 23082200248849377943193561)
              ·
                refine ⟨17311650186637033457395171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23082200248849377943193561 17311650186637033457395171)
                ·
                  refine ⟨25967475279955550186092757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17311650186637033457395171 25967475279955550186092757)
                  ·
                    refine ⟨608612701873958207486549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25967475279955550186092757 608612701873958207486549)
                    ·
                      rfl

theorem cell23_3555807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_3555807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555807 prefixEnd_3555807 := by exact prefixLift 3555807
  have htrace : WordTrace (prefixWord ++ tailWord_3555807) baseStart_3555807 baseEnd_3555807 := by
    simpa [prefixWord, tailWord_3555807, baseEnd_3555807] using wordTrace_append hprefix tailTrace_3555807
  have hstable : (prefixWord ++ tailWord_3555807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555807).length < 2 ^ (prefixWord ++ tailWord_3555807).sum := by decide
  have hdescent : baseEnd_3555807 < baseStart_3555807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555827 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 4]
def baseStart_3555827 : Nat := 118140960795 + 3555827 * 2 ^ 59
def prefixEnd_3555827 : Nat := 4983230072969 + 3 ^ 40 * 3555827 * 2
def baseEnd_3555827 : Nat := 1825848375234964544209555

theorem tailTrace_3555827 : CollatzResearch.WordTrace tailWord_3555827 prefixEnd_3555827 1825848375234964544209555 := by
  unfold tailWord_3555827
  simp only [CollatzResearch.WordTrace]
  refine ⟨129691665288853540748129735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86461110192569027165419823 129691665288853540748129735)
  ·
    refine ⟨194537497933280311122194603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129691665288853540748129735 194537497933280311122194603)
    ·
      refine ⟨291806246899920466683291905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194537497933280311122194603 291806246899920466683291905)
      ·
        refine ⟨218854685174940350012468929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291806246899920466683291905 218854685174940350012468929)
        ·
          refine ⟨164141013881205262509351697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218854685174940350012468929 164141013881205262509351697)
          ·
            refine ⟨123105760410903946882013773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164141013881205262509351697 123105760410903946882013773)
            ·
              refine ⟨46164660154088980080755165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123105760410903946882013773 46164660154088980080755165)
              ·
                refine ⟨17311747557783367530283187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46164660154088980080755165 17311747557783367530283187)
                ·
                  refine ⟨25967621336675051295424781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17311747557783367530283187 25967621336675051295424781)
                  ·
                    refine ⟨9737858001253144235784293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25967621336675051295424781 9737858001253144235784293)
                    ·
                      refine ⟨1825848375234964544209555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9737858001253144235784293 1825848375234964544209555)
                      ·
                        rfl

theorem cell23_3555827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_3555827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555827 prefixEnd_3555827 := by exact prefixLift 3555827
  have htrace : WordTrace (prefixWord ++ tailWord_3555827) baseStart_3555827 baseEnd_3555827 := by
    simpa [prefixWord, tailWord_3555827, baseEnd_3555827] using wordTrace_append hprefix tailTrace_3555827
  have hstable : (prefixWord ++ tailWord_3555827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555827).length < 2 ^ (prefixWord ++ tailWord_3555827).sum := by decide
  have hdescent : baseEnd_3555827 < baseStart_3555827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555857 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_3555857 : Nat := 118140960795 + 3555857 * 2 ^ 59
def prefixEnd_3555857 : Nat := 4983230072969 + 3 ^ 40 * 3555857 * 2
def baseEnd_3555857 : Nat := 1825863779654599426834417

theorem tailTrace_3555857 : CollatzResearch.WordTrace tailWord_3555857 prefixEnd_3555857 1825863779654599426834417 := by
  unfold tailWord_3555857
  simp only [CollatzResearch.WordTrace]
  refine ⟨129692759478744855871721825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86461839652496570581147883 129692759478744855871721825)
  ·
    refine ⟨97269569609058641903791369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129692759478744855871721825 97269569609058641903791369)
    ·
      refine ⟨72952177206793981427843527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97269569609058641903791369 72952177206793981427843527)
      ·
        refine ⟨109428265810190972141765291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72952177206793981427843527 109428265810190972141765291)
        ·
          refine ⟨164142398715286458212647937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109428265810190972141765291 164142398715286458212647937)
          ·
            refine ⟨123106799036464843659485953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164142398715286458212647937 123106799036464843659485953)
            ·
              refine ⟨92330099277348632744614465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123106799036464843659485953 92330099277348632744614465)
              ·
                refine ⟨69247574458011474558460849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92330099277348632744614465 69247574458011474558460849)
                ·
                  refine ⟨51935680843508605918845637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69247574458011474558460849 51935680843508605918845637)
                  ·
                    refine ⟨9737940158157863609783557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51935680843508605918845637 9737940158157863609783557)
                    ·
                      refine ⟨1825863779654599426834417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9737940158157863609783557 1825863779654599426834417)
                      ·
                        rfl

theorem cell23_3555857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_3555857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555857 prefixEnd_3555857 := by exact prefixLift 3555857
  have htrace : WordTrace (prefixWord ++ tailWord_3555857) baseStart_3555857 baseEnd_3555857 := by
    simpa [prefixWord, tailWord_3555857, baseEnd_3555857] using wordTrace_append hprefix tailTrace_3555857
  have hstable : (prefixWord ++ tailWord_3555857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555857).length < 2 ^ (prefixWord ++ tailWord_3555857).sum := by decide
  have hdescent : baseEnd_3555857 < baseStart_3555857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555901 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 6]
def baseStart_3555901 : Nat := 118140960795 + 3555901 * 2 ^ 59
def prefixEnd_3555901 : Nat := 4983230072969 + 3 ^ 40 * 3555901 * 2
def baseEnd_3555901 : Nat := 202876263644821917187135

theorem tailTrace_3555901 : CollatzResearch.WordTrace tailWord_3555901 prefixEnd_3555901 202876263644821917187135 := by
  unfold tailWord_3555901
  simp only [CollatzResearch.WordTrace]
  refine ⟨129694364290585451386323557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86462909527056967590882371 129694364290585451386323557)
  ·
    refine ⟨24317693304484772134935667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129694364290585451386323557 24317693304484772134935667)
    ·
      refine ⟨36476539956727158202403501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24317693304484772134935667 36476539956727158202403501)
      ·
        refine ⟨13678702483772684325901313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36476539956727158202403501 13678702483772684325901313)
        ·
          refine ⟨10259026862829513244425985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13678702483772684325901313 10259026862829513244425985)
          ·
            refine ⟨7694270147122134933319489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10259026862829513244425985 7694270147122134933319489)
            ·
              refine ⟨5770702610341601199989617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7694270147122134933319489 5770702610341601199989617)
              ·
                refine ⟨4328026957756200899992213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5770702610341601199989617 4328026957756200899992213)
                ·
                  refine ⟨202876263644821917187135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4328026957756200899992213 202876263644821917187135)
                  ·
                    rfl

theorem cell23_3555901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_3555901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555901 prefixEnd_3555901 := by exact prefixLift 3555901
  have htrace : WordTrace (prefixWord ++ tailWord_3555901) baseStart_3555901 baseEnd_3555901 := by
    simpa [prefixWord, tailWord_3555901, baseEnd_3555901] using wordTrace_append hprefix tailTrace_3555901
  have hstable : (prefixWord ++ tailWord_3555901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555901).length < 2 ^ (prefixWord ++ tailWord_3555901).sum := by decide
  have hdescent : baseEnd_3555901 < baseStart_3555901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555905 : List Nat := [1, 2, 5, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3555905 : Nat := 118140960795 + 3555905 * 2 ^ 59
def prefixEnd_3555905 : Nat := 4983230072969 + 3 ^ 40 * 3555905 * 2
def baseEnd_3555905 : Nat := 608629475575338413011399

theorem tailTrace_3555905 : CollatzResearch.WordTrace tailWord_3555905 prefixEnd_3555905 608629475575338413011399 := by
  unfold tailWord_3555905
  simp only [CollatzResearch.WordTrace]
  refine ⟨129694510182570960069469169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86463006788380640046312779 129694510182570960069469169)
  ·
    refine ⟨97270882636928220052101877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129694510182570960069469169 97270882636928220052101877)
    ·
      refine ⟨9119145247212020629884551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97270882636928220052101877 9119145247212020629884551)
      ·
        refine ⟨13678717870818030944826827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9119145247212020629884551 13678717870818030944826827)
        ·
          refine ⟨20518076806227046417240241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13678717870818030944826827 20518076806227046417240241)
          ·
            refine ⟨15388557604670284812930181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20518076806227046417240241 15388557604670284812930181)
            ·
              refine ⟨2885354550875678402424409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15388557604670284812930181 2885354550875678402424409)
              ·
                refine ⟨2164015913156758801818307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2885354550875678402424409 2164015913156758801818307)
                ·
                  refine ⟨3246023869735138202727461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164015913156758801818307 3246023869735138202727461)
                  ·
                    refine ⟨608629475575338413011399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3246023869735138202727461 608629475575338413011399)
                    ·
                      rfl

theorem cell23_3555905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3555905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555905 prefixEnd_3555905 := by exact prefixLift 3555905
  have htrace : WordTrace (prefixWord ++ tailWord_3555905) baseStart_3555905 baseEnd_3555905 := by
    simpa [prefixWord, tailWord_3555905, baseEnd_3555905] using wordTrace_append hprefix tailTrace_3555905
  have hstable : (prefixWord ++ tailWord_3555905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555905).length < 2 ^ (prefixWord ++ tailWord_3555905).sum := by decide
  have hdescent : baseEnd_3555905 < baseStart_3555905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555907 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 5]
def baseStart_3555907 : Nat := 118140960795 + 3555907 * 2 ^ 59
def prefixEnd_3555907 : Nat := 4983230072969 + 3 ^ 40 * 3555907 * 2
def baseEnd_3555907 : Nat := 1825889453687324231209187

theorem tailTrace_3555907 : CollatzResearch.WordTrace tailWord_3555907 prefixEnd_3555907 1825889453687324231209187 := by
  unfold tailWord_3555907
  simp only [CollatzResearch.WordTrace]
  refine ⟨129694583128563714411041975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86463055419042476274027983 129694583128563714411041975)
  ·
    refine ⟨194541874692845571616562963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129694583128563714411041975 194541874692845571616562963)
    ·
      refine ⟨291812812039268357424844445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194541874692845571616562963 291812812039268357424844445)
      ·
        refine ⟨109429804514725634034316667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291812812039268357424844445 109429804514725634034316667)
        ·
          refine ⟨164144706772088451051475001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109429804514725634034316667 164144706772088451051475001)
          ·
            refine ⟨123108530079066338288606251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164144706772088451051475001 123108530079066338288606251)
            ·
              refine ⟨184662795118599507432909377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123108530079066338288606251 184662795118599507432909377)
              ·
                refine ⟨138497096338949630574682033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184662795118599507432909377 138497096338949630574682033)
                ·
                  refine ⟨103872822254212222931011525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138497096338949630574682033 103872822254212222931011525)
                  ·
                    refine ⟨19476154172664791799564661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103872822254212222931011525 19476154172664791799564661)
                    ·
                      refine ⟨1825889453687324231209187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19476154172664791799564661 1825889453687324231209187)
                      ·
                        rfl

theorem cell23_3555907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_3555907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555907 prefixEnd_3555907 := by exact prefixLift 3555907
  have htrace : WordTrace (prefixWord ++ tailWord_3555907) baseStart_3555907 baseEnd_3555907 := by
    simpa [prefixWord, tailWord_3555907, baseEnd_3555907] using wordTrace_append hprefix tailTrace_3555907
  have hstable : (prefixWord ++ tailWord_3555907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555907).length < 2 ^ (prefixWord ++ tailWord_3555907).sum := by decide
  have hdescent : baseEnd_3555907 < baseStart_3555907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555914 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_3555914 : Nat := 118140960795 + 3555914 * 2 ^ 59
def prefixEnd_3555914 : Nat := 4983230072969 + 3 ^ 40 * 3555914 * 2
def baseEnd_3555914 : Nat := 608631016017301901273885

theorem tailTrace_3555914 : CollatzResearch.WordTrace tailWord_3555914 prefixEnd_3555914 608631016017301901273885 := by
  unfold tailWord_3555914
  simp only [CollatzResearch.WordTrace]
  refine ⟨32423709609884588651636699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86463225626358903071031197 32423709609884588651636699)
  ·
    refine ⟨48635564414826882977455049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32423709609884588651636699 48635564414826882977455049)
    ·
      refine ⟨36476673311120162233091287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48635564414826882977455049 36476673311120162233091287)
      ·
        refine ⟨54715009966680243349636931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36476673311120162233091287 54715009966680243349636931)
        ·
          refine ⟨82072514950020365024455397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54715009966680243349636931 82072514950020365024455397)
          ·
            refine ⟨15388596553128818442085387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82072514950020365024455397 15388596553128818442085387)
            ·
              refine ⟨23082894829693227663128081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15388596553128818442085387 23082894829693227663128081)
              ·
                refine ⟨17312171122269920747346061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23082894829693227663128081 17312171122269920747346061)
                ·
                  refine ⟨6492064170851220280254773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17312171122269920747346061 6492064170851220280254773)
                  ·
                    refine ⟨608631016017301901273885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6492064170851220280254773 608631016017301901273885)
                    ·
                      rfl

theorem cell23_3555914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_3555914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555914 prefixEnd_3555914 := by exact prefixLift 3555914
  have htrace : WordTrace (prefixWord ++ tailWord_3555914) baseStart_3555914 baseEnd_3555914 := by
    simpa [prefixWord, tailWord_3555914, baseEnd_3555914] using wordTrace_append hprefix tailTrace_3555914
  have hstable : (prefixWord ++ tailWord_3555914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555914).length < 2 ^ (prefixWord ++ tailWord_3555914).sum := by decide
  have hdescent : baseEnd_3555914 < baseStart_3555914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555961 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 4, 4]
def baseStart_3555961 : Nat := 118140960795 + 3555961 * 2 ^ 59
def prefixEnd_3555961 : Nat := 4983230072969 + 3 ^ 40 * 3555961 * 2
def baseEnd_3555961 : Nat := 608639060547555673311313

theorem tailTrace_3555961 : CollatzResearch.WordTrace tailWord_3555961 prefixEnd_3555961 608639060547555673311313 := by
  unfold tailWord_3555961
  simp only [CollatzResearch.WordTrace]
  refine ⟨129696552670368081633507737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86464368446912054422338491 129696552670368081633507737)
  ·
    refine ⟨97272414502776061225130803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129696552670368081633507737 97272414502776061225130803)
    ·
      refine ⟨145908621754164091837696205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97272414502776061225130803 145908621754164091837696205)
      ·
        refine ⟨54715733157811534439136077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145908621754164091837696205 54715733157811534439136077)
        ·
          refine ⟨20518399934179325414676029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54715733157811534439136077 20518399934179325414676029)
          ·
            refine ⟨7694399975317247030503511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20518399934179325414676029 7694399975317247030503511)
            ·
              refine ⟨11541599962975870545755267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694399975317247030503511 11541599962975870545755267)
              ·
                refine ⟨17312399944463805818632901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11541599962975870545755267 17312399944463805818632901)
                ·
                  refine ⟨3246074989586963590993669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17312399944463805818632901 3246074989586963590993669)
                  ·
                    refine ⟨608639060547555673311313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3246074989586963590993669 608639060547555673311313)
                    ·
                      rfl

theorem cell23_3555961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 4].length) (baseStart_3555961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555961 prefixEnd_3555961 := by exact prefixLift 3555961
  have htrace : WordTrace (prefixWord ++ tailWord_3555961) baseStart_3555961 baseEnd_3555961 := by
    simpa [prefixWord, tailWord_3555961, baseEnd_3555961] using wordTrace_append hprefix tailTrace_3555961
  have hstable : (prefixWord ++ tailWord_3555961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555961).length < 2 ^ (prefixWord ++ tailWord_3555961).sum := by decide
  have hdescent : baseEnd_3555961 < baseStart_3555961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555964 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_3555964 : Nat := 118140960795 + 3555964 * 2 ^ 59
def prefixEnd_3555964 : Nat := 4983230072969 + 3 ^ 40 * 3555964 * 2
def baseEnd_3555964 : Nat := 1825918722084630508196425

theorem tailTrace_3555964 : CollatzResearch.WordTrace tailWord_3555964 prefixEnd_3555964 1825918722084630508196425 := by
  unfold tailWord_3555964
  simp only [CollatzResearch.WordTrace]
  refine ⟨64848331044678606572933473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86464441392904808763911297 64848331044678606572933473)
  ·
    refine ⟨48636248283508954929700105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64848331044678606572933473 48636248283508954929700105)
    ·
      refine ⟨36477186212631716197275079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48636248283508954929700105 36477186212631716197275079)
      ·
        refine ⟨54715779318947574295912619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36477186212631716197275079 54715779318947574295912619)
        ·
          refine ⟨82073668978421361443868929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54715779318947574295912619 82073668978421361443868929)
          ·
            refine ⟨61555251733816021082901697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82073668978421361443868929 61555251733816021082901697)
            ·
              refine ⟨46166438800362015812176273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61555251733816021082901697 46166438800362015812176273)
              ·
                refine ⟨34624829100271511859132205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46166438800362015812176273 34624829100271511859132205)
                ·
                  refine ⟨12984310912601816947174577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34624829100271511859132205 12984310912601816947174577)
                  ·
                    refine ⟨9738233184451362710380933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12984310912601816947174577 9738233184451362710380933)
                    ·
                      refine ⟨1825918722084630508196425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9738233184451362710380933 1825918722084630508196425)
                      ·
                        rfl

theorem cell23_3555964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_3555964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555964 prefixEnd_3555964 := by exact prefixLift 3555964
  have htrace : WordTrace (prefixWord ++ tailWord_3555964) baseStart_3555964 baseEnd_3555964 := by
    simpa [prefixWord, tailWord_3555964, baseEnd_3555964] using wordTrace_append hprefix tailTrace_3555964
  have hstable : (prefixWord ++ tailWord_3555964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555964).length < 2 ^ (prefixWord ++ tailWord_3555964).sum := by decide
  have hdescent : baseEnd_3555964 < baseStart_3555964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555968 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 3, 2, 2]
def baseStart_3555968 : Nat := 118140960795 + 3555968 * 2 ^ 59
def prefixEnd_3555968 : Nat := 4983230072969 + 3 ^ 40 * 3555968 * 2
def baseEnd_3555968 : Nat := 1825920776007248492546407

theorem tailTrace_3555968 : CollatzResearch.WordTrace tailWord_3555968 prefixEnd_3555968 1825920776007248492546407 := by
  unfold tailWord_3555968
  simp only [CollatzResearch.WordTrace]
  refine ⟨64848403990671360914506279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86464538654228481219341705 64848403990671360914506279)
  ·
    refine ⟨97272605986007041371759419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64848403990671360914506279 97272605986007041371759419)
    ·
      refine ⟨145908908979010562057639129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97272605986007041371759419 145908908979010562057639129)
      ·
        refine ⟨109431681734257921543229347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145908908979010562057639129 109431681734257921543229347)
        ·
          refine ⟨164147522601386882314844021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109431681734257921543229347 164147522601386882314844021)
          ·
            refine ⟨15388830243880020217016627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164147522601386882314844021 15388830243880020217016627)
            ·
              refine ⟨23083245365820030325524941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15388830243880020217016627 23083245365820030325524941)
              ·
                refine ⟨8656217012182511372071853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23083245365820030325524941 8656217012182511372071853)
                ·
                  refine ⟨3246081379568441764526945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8656217012182511372071853 3246081379568441764526945)
                  ·
                    refine ⟨2434561034676331323395209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3246081379568441764526945 2434561034676331323395209)
                    ·
                      refine ⟨1825920776007248492546407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434561034676331323395209 1825920776007248492546407)
                      ·
                        rfl

theorem cell23_3555968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_3555968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555968 prefixEnd_3555968 := by exact prefixLift 3555968
  have htrace : WordTrace (prefixWord ++ tailWord_3555968) baseStart_3555968 baseEnd_3555968 := by
    simpa [prefixWord, tailWord_3555968, baseEnd_3555968] using wordTrace_append hprefix tailTrace_3555968
  have hstable : (prefixWord ++ tailWord_3555968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555968).length < 2 ^ (prefixWord ++ tailWord_3555968).sum := by decide
  have hdescent : baseEnd_3555968 < baseStart_3555968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3555978 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_3555978 : Nat := 118140960795 + 3555978 * 2 ^ 59
def prefixEnd_3555978 : Nat := 4983230072969 + 3 ^ 40 * 3555978 * 2
def baseEnd_3555978 : Nat := 608641970271264484473787

theorem tailTrace_3555978 : CollatzResearch.WordTrace tailWord_3555978 prefixEnd_3555978 608641970271264484473787 := by
  unfold tailWord_3555978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32424293177826623384219147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86464781807537662357917725 32424293177826623384219147)
  ·
    refine ⟨48636439766739935076328721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32424293177826623384219147 48636439766739935076328721)
    ·
      refine ⟨36477329825054951307246541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48636439766739935076328721 36477329825054951307246541)
      ·
        refine ⟨13678998684395606740217453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36477329825054951307246541 13678998684395606740217453)
        ·
          refine ⟨5129624506648352527581545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13678998684395606740217453 5129624506648352527581545)
          ·
            refine ⟨3847218379986264395686159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5129624506648352527581545 3847218379986264395686159)
            ·
              refine ⟨5770827569979396593529239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3847218379986264395686159 5770827569979396593529239)
              ·
                refine ⟨8656241354969094890293859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5770827569979396593529239 8656241354969094890293859)
                ·
                  refine ⟨12984362032453642335440789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8656241354969094890293859 12984362032453642335440789)
                  ·
                    refine ⟨608641970271264484473787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12984362032453642335440789 608641970271264484473787)
                    ·
                      rfl

theorem cell23_3555978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_3555978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3555978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3555978 prefixEnd_3555978 := by exact prefixLift 3555978
  have htrace : WordTrace (prefixWord ++ tailWord_3555978) baseStart_3555978 baseEnd_3555978 := by
    simpa [prefixWord, tailWord_3555978, baseEnd_3555978] using wordTrace_append hprefix tailTrace_3555978
  have hstable : (prefixWord ++ tailWord_3555978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3555978).length < 2 ^ (prefixWord ++ tailWord_3555978).sum := by decide
  have hdescent : baseEnd_3555978 < baseStart_3555978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3555978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556018 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_3556018 : Nat := 118140960795 + 3556018 * 2 ^ 59
def prefixEnd_3556018 : Nat := 4983230072969 + 3 ^ 40 * 3556018 * 2
def baseEnd_3556018 : Nat := 1825946450039973296921177

theorem tailTrace_3556018 : CollatzResearch.WordTrace tailWord_3556018 prefixEnd_3556018 1825946450039973296921177 := by
  unfold tailWord_3556018
  simp only [CollatzResearch.WordTrace]
  refine ⟨32424657907790395092083177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86465754420774386912221805 32424657907790395092083177)
  ·
    refine ⟨24318493430842796319062383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32424657907790395092083177 24318493430842796319062383)
    ·
      refine ⟨36477740146264194478593575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24318493430842796319062383 36477740146264194478593575)
      ·
        refine ⟨54716610219396291717890363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36477740146264194478593575 54716610219396291717890363)
        ·
          refine ⟨82074915329094437576835545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54716610219396291717890363 82074915329094437576835545)
          ·
            refine ⟨61556186496820828182626659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82074915329094437576835545 61556186496820828182626659)
            ·
              refine ⟨92334279745231242273939989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61556186496820828182626659 92334279745231242273939989)
              ·
                refine ⟨4328169363057714481590937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92334279745231242273939989 4328169363057714481590937)
                ·
                  refine ⟨3246127022293285861193203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4328169363057714481590937 3246127022293285861193203)
                  ·
                    refine ⟨4869190533439928791789805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3246127022293285861193203 4869190533439928791789805)
                    ·
                      refine ⟨1825946450039973296921177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4869190533439928791789805 1825946450039973296921177)
                      ·
                        rfl

theorem cell23_3556018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_3556018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556018 prefixEnd_3556018 := by exact prefixLift 3556018
  have htrace : WordTrace (prefixWord ++ tailWord_3556018) baseStart_3556018 baseEnd_3556018 := by
    simpa [prefixWord, tailWord_3556018, baseEnd_3556018] using wordTrace_append hprefix tailTrace_3556018
  have hstable : (prefixWord ++ tailWord_3556018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556018).length < 2 ^ (prefixWord ++ tailWord_3556018).sum := by decide
  have hdescent : baseEnd_3556018 < baseStart_3556018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556028 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 3, 3, 2]
def baseStart_3556028 : Nat := 118140960795 + 3556028 * 2 ^ 59
def prefixEnd_3556028 : Nat := 4983230072969 + 3 ^ 40 * 3556028 * 2
def baseEnd_3556028 : Nat := 1825951584846518257796131

theorem tailTrace_3556028 : CollatzResearch.WordTrace tailWord_3556028 prefixEnd_3556028 1825951584846518257796131 := by
  unfold tailWord_3556028
  simp only [CollatzResearch.WordTrace]
  refine ⟨64849498180562676038098369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86465997574083568050797825 64849498180562676038098369)
  ·
    refine ⟨48637123635422007028573777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64849498180562676038098369 48637123635422007028573777)
    ·
      refine ⟨36477842726566505271430333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48637123635422007028573777 36477842726566505271430333)
      ·
        refine ⟨13679191022462439476786375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36477842726566505271430333 13679191022462439476786375)
        ·
          refine ⟨20518786533693659215179563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13679191022462439476786375 20518786533693659215179563)
          ·
            refine ⟨30778179800540488822769345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20518786533693659215179563 30778179800540488822769345)
            ·
              refine ⟨23083634850405366617077009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30778179800540488822769345 23083634850405366617077009)
              ·
                refine ⟨17312726137804024962807757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23083634850405366617077009 17312726137804024962807757)
                ·
                  refine ⟨6492272301676509361052909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17312726137804024962807757 6492272301676509361052909)
                  ·
                    refine ⟨2434602113128691010394841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6492272301676509361052909 2434602113128691010394841)
                    ·
                      refine ⟨1825951584846518257796131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434602113128691010394841 1825951584846518257796131)
                      ·
                        rfl

theorem cell23_3556028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_3556028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556028 prefixEnd_3556028 := by exact prefixLift 3556028
  have htrace : WordTrace (prefixWord ++ tailWord_3556028) baseStart_3556028 baseEnd_3556028 := by
    simpa [prefixWord, tailWord_3556028, baseEnd_3556028] using wordTrace_append hprefix tailTrace_3556028
  have hstable : (prefixWord ++ tailWord_3556028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556028).length < 2 ^ (prefixWord ++ tailWord_3556028).sum := by decide
  have hdescent : baseEnd_3556028 < baseStart_3556028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556041 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 7, 4, 2]
def baseStart_3556041 : Nat := 118140960795 + 3556041 * 2 ^ 59
def prefixEnd_3556041 : Nat := 4983230072969 + 3 ^ 40 * 3556041 * 2
def baseEnd_3556041 : Nat := 1825958260095026706933571

theorem tailTrace_3556041 : CollatzResearch.WordTrace tailWord_3556041 prefixEnd_3556041 1825958260095026706933571 := by
  unfold tailWord_3556041
  simp only [CollatzResearch.WordTrace]
  refine ⟨129699470510078255296419977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86466313673385503530946651 129699470510078255296419977)
  ·
    refine ⟨97274602882558691472314983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129699470510078255296419977 97274602882558691472314983)
    ·
      refine ⟨145911904323838037208472475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97274602882558691472314983 145911904323838037208472475)
      ·
        refine ⟨218867856485757055812708713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145911904323838037208472475 218867856485757055812708713)
        ·
          refine ⟨164150892364317791859531535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218867856485757055812708713 164150892364317791859531535)
          ·
            refine ⟨246226338546476687789297303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164150892364317791859531535 246226338546476687789297303)
            ·
              refine ⟨369339507819715031683945955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246226338546476687789297303 369339507819715031683945955)
              ·
                refine ⟨554009261729572547525918933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369339507819715031683945955 554009261729572547525918933)
                ·
                  refine ⟨12984592071786856582638725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 554009261729572547525918933 12984592071786856582638725)
                  ·
                    refine ⟨2434611013460035609244761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12984592071786856582638725 2434611013460035609244761)
                    ·
                      refine ⟨1825958260095026706933571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434611013460035609244761 1825958260095026706933571)
                      ·
                        rfl

theorem cell23_3556041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 4, 2].length) (baseStart_3556041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556041 prefixEnd_3556041 := by exact prefixLift 3556041
  have htrace : WordTrace (prefixWord ++ tailWord_3556041) baseStart_3556041 baseEnd_3556041 := by
    simpa [prefixWord, tailWord_3556041, baseEnd_3556041] using wordTrace_append hprefix tailTrace_3556041
  have hstable : (prefixWord ++ tailWord_3556041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556041).length < 2 ^ (prefixWord ++ tailWord_3556041).sum := by decide
  have hdescent : baseEnd_3556041 < baseStart_3556041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556058 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2]
def baseStart_3556058 : Nat := 118140960795 + 3556058 * 2 ^ 59
def prefixEnd_3556058 : Nat := 4983230072969 + 3 ^ 40 * 3556058 * 2
def baseEnd_3556058 : Nat := 1825966989266153140420993

theorem tailTrace_3556058 : CollatzResearch.WordTrace tailWord_3556058 prefixEnd_3556058 1825966989266153140420993 := by
  unfold tailWord_3556058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32425022637754166799947207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86466727034011111466525885 32425022637754166799947207)
  ·
    refine ⟨48637533956631250199920811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32425022637754166799947207 48637533956631250199920811)
    ·
      refine ⟨72956300934946875299881217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48637533956631250199920811 72956300934946875299881217)
      ·
        refine ⟨54717225701210156474910913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72956300934946875299881217 54717225701210156474910913)
        ·
          refine ⟨41037919275907617356183185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54717225701210156474910913 41037919275907617356183185)
          ·
            refine ⟨30778439456930713017137389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41037919275907617356183185 30778439456930713017137389)
            ·
              refine ⟨11541914796349017381426521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30778439456930713017137389 11541914796349017381426521)
              ·
                refine ⟨8656436097261763036069891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11541914796349017381426521 8656436097261763036069891)
                ·
                  refine ⟨12984654145892644554104837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8656436097261763036069891 12984654145892644554104837)
                  ·
                    refine ⟨2434622652354870853894657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12984654145892644554104837 2434622652354870853894657)
                    ·
                      refine ⟨1825966989266153140420993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434622652354870853894657 1825966989266153140420993)
                      ·
                        rfl

theorem cell23_3556058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_3556058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556058 prefixEnd_3556058 := by exact prefixLift 3556058
  have htrace : WordTrace (prefixWord ++ tailWord_3556058) baseStart_3556058 baseEnd_3556058 := by
    simpa [prefixWord, tailWord_3556058, baseEnd_3556058] using wordTrace_append hprefix tailTrace_3556058
  have hstable : (prefixWord ++ tailWord_3556058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556058).length < 2 ^ (prefixWord ++ tailWord_3556058).sum := by decide
  have hdescent : baseEnd_3556058 < baseStart_3556058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556098 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 7]
def baseStart_3556098 : Nat := 118140960795 + 3556098 * 2 ^ 59
def prefixEnd_3556098 : Nat := 4983230072969 + 3 ^ 40 * 3556098 * 2
def baseEnd_3556098 : Nat := 202887503165814775991201

theorem tailTrace_3556098 : CollatzResearch.WordTrace tailWord_3556098 prefixEnd_3556098 202887503165814775991201 := by
  unfold tailWord_3556098
  simp only [CollatzResearch.WordTrace]
  refine ⟨32425387367717938507811237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86467699647247836020829965 32425387367717938507811237)
  ·
    refine ⟨6079760131447113470214607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32425387367717938507811237 6079760131447113470214607)
    ·
      refine ⟨9119640197170670205321911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6079760131447113470214607 9119640197170670205321911)
      ·
        refine ⟨13679460295756005307982867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9119640197170670205321911 13679460295756005307982867)
        ·
          refine ⟨20519190443634007961974301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13679460295756005307982867 20519190443634007961974301)
          ·
            refine ⟨7694696416362752985740363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20519190443634007961974301 7694696416362752985740363)
            ·
              refine ⟨11542044624544129478610545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694696416362752985740363 11542044624544129478610545)
              ·
                refine ⟨8656533468408097108957909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11542044624544129478610545 8656533468408097108957909)
                ·
                  refine ⟨202887503165814775991201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8656533468408097108957909 202887503165814775991201)
                  ·
                    rfl

theorem cell23_3556098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_3556098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556098 prefixEnd_3556098 := by exact prefixLift 3556098
  have htrace : WordTrace (prefixWord ++ tailWord_3556098) baseStart_3556098 baseEnd_3556098 := by
    simpa [prefixWord, tailWord_3556098, baseEnd_3556098] using wordTrace_append hprefix tailTrace_3556098
  have hstable : (prefixWord ++ tailWord_3556098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556098).length < 2 ^ (prefixWord ++ tailWord_3556098).sum := by decide
  have hdescent : baseEnd_3556098 < baseStart_3556098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556131 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 4]
def baseStart_3556131 : Nat := 118140960795 + 3556131 * 2 ^ 59
def prefixEnd_3556131 : Nat := 4983230072969 + 3 ^ 40 * 3556131 * 2
def baseEnd_3556131 : Nat := 1826004473353931354808157

theorem tailTrace_3556131 : CollatzResearch.WordTrace tailWord_3556131 prefixEnd_3556131 1826004473353931354808157 := by
  unfold tailWord_3556131
  simp only [CollatzResearch.WordTrace]
  refine ⟨129702753079752200667196247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86468502053168133778130831 129702753079752200667196247)
  ·
    refine ⟨194554129619628301000794371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129702753079752200667196247 194554129619628301000794371)
    ·
      refine ⟨291831194429442451501191557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194554129619628301000794371 291831194429442451501191557)
      ·
        refine ⟨54718348955520459656473417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291831194429442451501191557 54718348955520459656473417)
        ·
          refine ⟨41038761716640344742355063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54718348955520459656473417 41038761716640344742355063)
          ·
            refine ⟨61558142574960517113532595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41038761716640344742355063 61558142574960517113532595)
            ·
              refine ⟨92337213862440775670298893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61558142574960517113532595 92337213862440775670298893)
              ·
                refine ⟨34626455198415290876362085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92337213862440775670298893 34626455198415290876362085)
                ·
                  refine ⟨6492460349702867039317891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34626455198415290876362085 6492460349702867039317891)
                  ·
                    refine ⟨9738690524554300558976837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6492460349702867039317891 9738690524554300558976837)
                    ·
                      refine ⟨1826004473353931354808157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9738690524554300558976837 1826004473353931354808157)
                      ·
                        rfl

theorem cell23_3556131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_3556131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556131 prefixEnd_3556131 := by exact prefixLift 3556131
  have htrace : WordTrace (prefixWord ++ tailWord_3556131) baseStart_3556131 baseEnd_3556131 := by
    simpa [prefixWord, tailWord_3556131, baseEnd_3556131] using wordTrace_append hprefix tailTrace_3556131
  have hstable : (prefixWord ++ tailWord_3556131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556131).length < 2 ^ (prefixWord ++ tailWord_3556131).sum := by decide
  have hdescent : baseEnd_3556131 < baseStart_3556131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556151 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 3]
def baseStart_3556151 : Nat := 118140960795 + 3556151 * 2 ^ 59
def prefixEnd_3556151 : Nat := 4983230072969 + 3 ^ 40 * 3556151 * 2
def baseEnd_3556151 : Nat := 1826014742967021276558065

theorem tailTrace_3556151 : CollatzResearch.WordTrace tailWord_3556151 prefixEnd_3556151 1826014742967021276558065 := by
  unfold tailWord_3556151
  simp only [CollatzResearch.WordTrace]
  refine ⟨129703482539679744082924307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86468988359786496055282871 129703482539679744082924307)
  ·
    refine ⟨194555223809519616124386461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129703482539679744082924307 194555223809519616124386461)
    ·
      refine ⟨72958208928569856046644923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194555223809519616124386461 72958208928569856046644923)
      ·
        refine ⟨109437313392854784069967385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72958208928569856046644923 109437313392854784069967385)
        ·
          refine ⟨82077985044641088052475539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109437313392854784069967385 82077985044641088052475539)
          ·
            refine ⟨123116977566961632078713309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82077985044641088052475539 123116977566961632078713309)
            ·
              refine ⟨46168866587610612029517491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123116977566961632078713309 46168866587610612029517491)
              ·
                refine ⟨69253299881415918044276237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46168866587610612029517491 69253299881415918044276237)
                ·
                  refine ⟨25969987455530969266603589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69253299881415918044276237 25969987455530969266603589)
                  ·
                    refine ⟨4869372647912056737488173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25969987455530969266603589 4869372647912056737488173)
                    ·
                      refine ⟨1826014742967021276558065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4869372647912056737488173 1826014742967021276558065)
                      ·
                        rfl

theorem cell23_3556151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_3556151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556151 prefixEnd_3556151 := by exact prefixLift 3556151
  have htrace : WordTrace (prefixWord ++ tailWord_3556151) baseStart_3556151 baseEnd_3556151 := by
    simpa [prefixWord, tailWord_3556151, baseEnd_3556151] using wordTrace_append hprefix tailTrace_3556151
  have hstable : (prefixWord ++ tailWord_3556151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556151).length < 2 ^ (prefixWord ++ tailWord_3556151).sum := by decide
  have hdescent : baseEnd_3556151 < baseStart_3556151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556166 : List Nat := [6, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_3556166 : Nat := 118140960795 + 3556166 * 2 ^ 59
def prefixEnd_3556166 : Nat := 4983230072969 + 3 ^ 40 * 3556166 * 2
def baseEnd_3556166 : Nat := 202891382797426524207833

theorem tailTrace_3556166 : CollatzResearch.WordTrace tailWord_3556166 prefixEnd_3556166 202891382797426524207833 := by
  unfold tailWord_3556166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4053250926082043801397511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86469353089750267763146901 4053250926082043801397511)
  ·
    refine ⟨6079876389123065702096267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4053250926082043801397511 6079876389123065702096267)
    ·
      refine ⟨9119814583684598553144401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6079876389123065702096267 9119814583684598553144401)
      ·
        refine ⟨6839860937763448914858301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9119814583684598553144401 6839860937763448914858301)
        ·
          refine ⟨2564947851661293343071863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6839860937763448914858301 2564947851661293343071863)
          ·
            refine ⟨3847421777491940014607795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564947851661293343071863 3847421777491940014607795)
            ·
              refine ⟨5771132666237910021911693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3847421777491940014607795 5771132666237910021911693)
              ·
                refine ⟨2164174749839216258216885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5771132666237910021911693 2164174749839216258216885)
                ·
                  refine ⟨202891382797426524207833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2164174749839216258216885 202891382797426524207833)
                  ·
                    rfl

theorem cell23_3556166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_3556166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556166 prefixEnd_3556166 := by exact prefixLift 3556166
  have htrace : WordTrace (prefixWord ++ tailWord_3556166) baseStart_3556166 baseEnd_3556166 := by
    simpa [prefixWord, tailWord_3556166, baseEnd_3556166] using wordTrace_append hprefix tailTrace_3556166
  have hstable : (prefixWord ++ tailWord_3556166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556166).length < 2 ^ (prefixWord ++ tailWord_3556166).sum := by decide
  have hdescent : baseEnd_3556166 < baseStart_3556166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556168 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_3556168 : Nat := 118140960795 + 3556168 * 2 ^ 59
def prefixEnd_3556168 : Nat := 4983230072969 + 3 ^ 40 * 3556168 * 2
def baseEnd_3556168 : Nat := 1826023472138147710045487

theorem tailTrace_3556168 : CollatzResearch.WordTrace tailWord_3556168 prefixEnd_3556168 1826023472138147710045487 := by
  unfold tailWord_3556168
  simp only [CollatzResearch.WordTrace]
  refine ⟨64852051290309077993146579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86469401720412103990862105 64852051290309077993146579)
  ·
    refine ⟨97278076935463616989719869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64852051290309077993146579 97278076935463616989719869)
    ·
      refine ⟨36479278850798856371144951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97278076935463616989719869 36479278850798856371144951)
      ·
        refine ⟨54718918276198284556717427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36479278850798856371144951 54718918276198284556717427)
        ·
          refine ⟨82078377414297426835076141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54718918276198284556717427 82078377414297426835076141)
          ·
            refine ⟨30779391530361535063153553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82078377414297426835076141 30779391530361535063153553)
            ·
              refine ⟨23084543647771151297365165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30779391530361535063153553 23084543647771151297365165)
              ·
                refine ⟨8656703867914181736511937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23084543647771151297365165 8656703867914181736511937)
                ·
                  refine ⟨6492527900935636302383953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8656703867914181736511937 6492527900935636302383953)
                  ·
                    refine ⟨4869395925701727226787965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6492527900935636302383953 4869395925701727226787965)
                    ·
                      refine ⟨1826023472138147710045487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4869395925701727226787965 1826023472138147710045487)
                      ·
                        rfl

theorem cell23_3556168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_3556168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556168 prefixEnd_3556168 := by exact prefixLift 3556168
  have htrace : WordTrace (prefixWord ++ tailWord_3556168) baseStart_3556168 baseEnd_3556168 := by
    simpa [prefixWord, tailWord_3556168, baseEnd_3556168] using wordTrace_append hprefix tailTrace_3556168
  have hstable : (prefixWord ++ tailWord_3556168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556168).length < 2 ^ (prefixWord ++ tailWord_3556168).sum := by decide
  have hdescent : baseEnd_3556168 < baseStart_3556168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556188 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 8]
def baseStart_3556188 : Nat := 118140960795 + 3556188 * 2 ^ 59
def prefixEnd_3556188 : Nat := 4983230072969 + 3 ^ 40 * 3556188 * 2
def baseEnd_3556188 : Nat := 202892637972359736866155

theorem tailTrace_3556188 : CollatzResearch.WordTrace tailWord_3556188 prefixEnd_3556188 202892637972359736866155 := by
  unfold tailWord_3556188
  simp only [CollatzResearch.WordTrace]
  refine ⟨64852416020272849701010609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86469888027030466268014145 64852416020272849701010609)
  ·
    refine ⟨48639312015204637275757957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64852416020272849701010609 48639312015204637275757957)
    ·
      refine ⟨9119871002850869489204617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48639312015204637275757957 9119871002850869489204617)
      ·
        refine ⟨6839903252138152116903463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9119871002850869489204617 6839903252138152116903463)
        ·
          refine ⟨10259854878207228175355195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6839903252138152116903463 10259854878207228175355195)
          ·
            refine ⟨15389782317310842263032793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10259854878207228175355195 15389782317310842263032793)
            ·
              refine ⟨11542336737983131697274595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15389782317310842263032793 11542336737983131697274595)
              ·
                refine ⟨17313505106974697545911893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11542336737983131697274595 17313505106974697545911893)
                ·
                  refine ⟨202892637972359736866155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17313505106974697545911893 202892637972359736866155)
                  ·
                    rfl

theorem cell23_3556188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_3556188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556188 prefixEnd_3556188 := by exact prefixLift 3556188
  have htrace : WordTrace (prefixWord ++ tailWord_3556188) baseStart_3556188 baseEnd_3556188 := by
    simpa [prefixWord, tailWord_3556188, baseEnd_3556188] using wordTrace_append hprefix tailTrace_3556188
  have hstable : (prefixWord ++ tailWord_3556188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556188).length < 2 ^ (prefixWord ++ tailWord_3556188).sum := by decide
  have hdescent : baseEnd_3556188 < baseStart_3556188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556192 : List Nat := [2, 1, 1, 3, 3, 1, 5, 2, 1, 4]
def baseStart_3556192 : Nat := 118140960795 + 3556192 * 2 ^ 59
def prefixEnd_3556192 : Nat := 4983230072969 + 3 ^ 40 * 3556192 * 2
def baseEnd_3556192 : Nat := 608678598557951872048459

theorem tailTrace_3556192 : CollatzResearch.WordTrace tailWord_3556192 prefixEnd_3556192 608678598557951872048459 := by
  unfold tailWord_3556192
  simp only [CollatzResearch.WordTrace]
  refine ⟨64852488966265604042583415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86469985288354138723444553 64852488966265604042583415)
  ·
    refine ⟨97278733449398406063875123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64852488966265604042583415 97278733449398406063875123)
    ·
      refine ⟨145918100174097609095812685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97278733449398406063875123 145918100174097609095812685)
      ·
        refine ⟨54719287565286603410929757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145918100174097609095812685 54719287565286603410929757)
        ·
          refine ⟨20519732836982476279098659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54719287565286603410929757 20519732836982476279098659)
          ·
            refine ⟨30779599255473714418647989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20519732836982476279098659 30779599255473714418647989)
            ·
              refine ⟨2885587430200660726748249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30779599255473714418647989 2885587430200660726748249)
              ·
                refine ⟨2164190572650495545061187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2885587430200660726748249 2164190572650495545061187)
                ·
                  refine ⟨3246285858975743317591781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164190572650495545061187 3246285858975743317591781)
                  ·
                    refine ⟨608678598557951872048459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3246285858975743317591781 608678598557951872048459)
                    ·
                      rfl

theorem cell23_3556192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 1, 4].length) (baseStart_3556192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556192 prefixEnd_3556192 := by exact prefixLift 3556192
  have htrace : WordTrace (prefixWord ++ tailWord_3556192) baseStart_3556192 baseEnd_3556192 := by
    simpa [prefixWord, tailWord_3556192, baseEnd_3556192] using wordTrace_append hprefix tailTrace_3556192
  have hstable : (prefixWord ++ tailWord_3556192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556192).length < 2 ^ (prefixWord ++ tailWord_3556192).sum := by decide
  have hdescent : baseEnd_3556192 < baseStart_3556192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556208 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 3, 5, 2]
def baseStart_3556208 : Nat := 118140960795 + 3556208 * 2 ^ 59
def prefixEnd_3556208 : Nat := 4983230072969 + 3 ^ 40 * 3556208 * 2
def baseEnd_3556208 : Nat := 1826044011364327553545303

theorem tailTrace_3556208 : CollatzResearch.WordTrace tailWord_3556208 prefixEnd_3556208 1826044011364327553545303 := by
  unfold tailWord_3556208
  simp only [CollatzResearch.WordTrace]
  refine ⟨64852780750236621408874639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86470374333648828545166185 64852780750236621408874639)
  ·
    refine ⟨97279171125354932113311959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64852780750236621408874639 97279171125354932113311959)
    ·
      refine ⟨145918756688032398169967939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97279171125354932113311959 145918756688032398169967939)
      ·
        refine ⟨218878135032048597254951909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145918756688032398169967939 218878135032048597254951909)
        ·
          refine ⟨41039650318509111985303483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218878135032048597254951909 41039650318509111985303483)
          ·
            refine ⟨61559475477763667977955225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41039650318509111985303483 61559475477763667977955225)
            ·
              refine ⟨46169606608322750983466419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61559475477763667977955225 46169606608322750983466419)
              ·
                refine ⟨69254409912484126475199629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46169606608322750983466419 69254409912484126475199629)
                ·
                  refine ⟨25970403717181547428199861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69254409912484126475199629 25970403717181547428199861)
                  ·
                    refine ⟨2434725348485770071393737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25970403717181547428199861 2434725348485770071393737)
                    ·
                      refine ⟨1826044011364327553545303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434725348485770071393737 1826044011364327553545303)
                      ·
                        rfl

theorem cell23_3556208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 5, 2].length) (baseStart_3556208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556208 prefixEnd_3556208 := by exact prefixLift 3556208
  have htrace : WordTrace (prefixWord ++ tailWord_3556208) baseStart_3556208 baseEnd_3556208 := by
    simpa [prefixWord, tailWord_3556208, baseEnd_3556208] using wordTrace_append hprefix tailTrace_3556208
  have hstable : (prefixWord ++ tailWord_3556208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556208).length < 2 ^ (prefixWord ++ tailWord_3556208).sum := by decide
  have hdescent : baseEnd_3556208 < baseStart_3556208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556276 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_3556276 : Nat := 118140960795 + 3556276 * 2 ^ 59
def prefixEnd_3556276 : Nat := 4983230072969 + 3 ^ 40 * 3556276 * 2
def baseEnd_3556276 : Nat := 1826078928048833287494991

theorem tailTrace_3556276 : CollatzResearch.WordTrace tailWord_3556276 prefixEnd_3556276 1826078928048833287494991 := by
  unfold tailWord_3556276
  simp only [CollatzResearch.WordTrace]
  refine ⟨64854020832113445215612341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86472027776151260287483121 64854020832113445215612341)
  ·
    refine ⟨6080064453010635488963657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64854020832113445215612341 6080064453010635488963657)
    ·
      refine ⟨4560048339757976616722743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6080064453010635488963657 4560048339757976616722743)
      ·
        refine ⟨6840072509636964925084115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4560048339757976616722743 6840072509636964925084115)
        ·
          refine ⟨10260108764455447387626173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840072509636964925084115 10260108764455447387626173)
          ·
            refine ⟨3847540786670792770359815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10260108764455447387626173 3847540786670792770359815)
            ·
              refine ⟨5771311180006189155539723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3847540786670792770359815 5771311180006189155539723)
              ·
                refine ⟨8656966770009283733309585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5771311180006189155539723 8656966770009283733309585)
                ·
                  refine ⟨6492725077506962799982189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8656966770009283733309585 6492725077506962799982189)
                  ·
                    refine ⟨2434771904065111049993321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6492725077506962799982189 2434771904065111049993321)
                    ·
                      refine ⟨1826078928048833287494991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434771904065111049993321 1826078928048833287494991)
                      ·
                        rfl

theorem cell23_3556276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_3556276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556276 prefixEnd_3556276 := by exact prefixLift 3556276
  have htrace : WordTrace (prefixWord ++ tailWord_3556276) baseStart_3556276 baseEnd_3556276 := by
    simpa [prefixWord, tailWord_3556276, baseEnd_3556276] using wordTrace_append hprefix tailTrace_3556276
  have hstable : (prefixWord ++ tailWord_3556276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556276).length < 2 ^ (prefixWord ++ tailWord_3556276).sum := by decide
  have hdescent : baseEnd_3556276 < baseStart_3556276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556291 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 4, 7]
def baseStart_3556291 : Nat := 118140960795 + 3556291 * 2 ^ 59
def prefixEnd_3556291 : Nat := 4983230072969 + 3 ^ 40 * 3556291 * 2
def baseEnd_3556291 : Nat := 608695543419550242935807

theorem tailTrace_3556291 : CollatzResearch.WordTrace tailWord_3556291 prefixEnd_3556291 608695543419550242935807 := by
  unfold tailWord_3556291
  simp only [CollatzResearch.WordTrace]
  refine ⟨129708588759172547993020727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86472392506115031995347151 129708588759172547993020727)
  ·
    refine ⟨194562883138758821989531091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129708588759172547993020727 194562883138758821989531091)
    ·
      refine ⟨291844324708138232984296637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194562883138758821989531091 291844324708138232984296637)
      ·
        refine ⟨109441621765551837369111239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291844324708138232984296637 109441621765551837369111239)
        ·
          refine ⟨164162432648327756053666859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109441621765551837369111239 164162432648327756053666859)
          ·
            refine ⟨246243648972491634080500289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164162432648327756053666859 246243648972491634080500289)
            ·
              refine ⟨184682736729368725560375217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246243648972491634080500289 184682736729368725560375217)
              ·
                refine ⟨138512052547026544170281413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184682736729368725560375217 138512052547026544170281413)
                ·
                  refine ⟨25971009852567477031927765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138512052547026544170281413 25971009852567477031927765)
                  ·
                    refine ⟨608695543419550242935807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25971009852567477031927765 608695543419550242935807)
                    ·
                      rfl

theorem cell23_3556291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 7].length) (baseStart_3556291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556291 prefixEnd_3556291 := by exact prefixLift 3556291
  have htrace : WordTrace (prefixWord ++ tailWord_3556291) baseStart_3556291 baseEnd_3556291 := by
    simpa [prefixWord, tailWord_3556291, baseEnd_3556291] using wordTrace_append hprefix tailTrace_3556291
  have hstable : (prefixWord ++ tailWord_3556291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556291).length < 2 ^ (prefixWord ++ tailWord_3556291).sum := by decide
  have hdescent : baseEnd_3556291 < baseStart_3556291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556305 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 4, 1, 3]
def baseStart_3556305 : Nat := 118140960795 + 3556305 * 2 ^ 59
def prefixEnd_3556305 : Nat := 4983230072969 + 3 ^ 40 * 3556305 * 2
def baseEnd_3556305 : Nat := 1826093818987813674032357

theorem tailTrace_3556305 : CollatzResearch.WordTrace tailWord_3556305 prefixEnd_3556305 1826093818987813674032357 := by
  unfold tailWord_3556305
  simp only [CollatzResearch.WordTrace]
  refine ⟨129709099381121828384030369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86472732920747885589353579 129709099381121828384030369)
  ·
    refine ⟨97281824535841371288022777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129709099381121828384030369 97281824535841371288022777)
    ·
      refine ⟨72961368401881028466017083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97281824535841371288022777 72961368401881028466017083)
      ·
        refine ⟨109442052602821542699025625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72961368401881028466017083 109442052602821542699025625)
        ·
          refine ⟨82081539452116157024269219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109442052602821542699025625 82081539452116157024269219)
          ·
            refine ⟨123122309178174235536403829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82081539452116157024269219 123122309178174235536403829)
            ·
              refine ⟨11542716485453834581537859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123122309178174235536403829 11542716485453834581537859)
              ·
                refine ⟨17314074728180751872306789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11542716485453834581537859 17314074728180751872306789)
                ·
                  refine ⟨3246389011533890976057523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17314074728180751872306789 3246389011533890976057523)
                  ·
                    refine ⟨4869583517300836464086285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3246389011533890976057523 4869583517300836464086285)
                    ·
                      refine ⟨1826093818987813674032357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4869583517300836464086285 1826093818987813674032357)
                      ·
                        rfl

theorem cell23_3556305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_3556305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556305 prefixEnd_3556305 := by exact prefixLift 3556305
  have htrace : WordTrace (prefixWord ++ tailWord_3556305) baseStart_3556305 baseEnd_3556305 := by
    simpa [prefixWord, tailWord_3556305, baseEnd_3556305] using wordTrace_append hprefix tailTrace_3556305
  have hstable : (prefixWord ++ tailWord_3556305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556305).length < 2 ^ (prefixWord ++ tailWord_3556305).sum := by decide
  have hdescent : baseEnd_3556305 < baseStart_3556305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556306 : List Nat := [3, 2, 2, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_3556306 : Nat := 118140960795 + 3556306 * 2 ^ 59
def prefixEnd_3556306 : Nat := 4983230072969 + 3 ^ 40 * 3556306 * 2
def baseEnd_3556306 : Nat := 1826094332468468170119853

theorem tailTrace_3556306 : CollatzResearch.WordTrace tailWord_3556306 prefixEnd_3556306 1826094332468468170119853 := by
  unfold tailWord_3556306
  simp only [CollatzResearch.WordTrace]
  refine ⟨32427283963529551388704193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86472757236078803703211181 32427283963529551388704193)
  ·
    refine ⟨24320462972647163541528145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32427283963529551388704193 24320462972647163541528145)
    ·
      refine ⟨18240347229485372656146109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24320462972647163541528145 18240347229485372656146109)
      ·
        refine ⟨6840130211057014746054791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18240347229485372656146109 6840130211057014746054791)
        ·
          refine ⟨10260195316585522119082187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840130211057014746054791 10260195316585522119082187)
          ·
            refine ⟨15390292974878283178623281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10260195316585522119082187 15390292974878283178623281)
            ·
              refine ⟨11542719731158712383967461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15390292974878283178623281 11542719731158712383967461)
              ·
                refine ⟨2164259949592258571993899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11542719731158712383967461 2164259949592258571993899)
                ·
                  refine ⟨3246389924388387857990849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164259949592258571993899 3246389924388387857990849)
                  ·
                    refine ⟨2434792443291290893493137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3246389924388387857990849 2434792443291290893493137)
                    ·
                      refine ⟨1826094332468468170119853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434792443291290893493137 1826094332468468170119853)
                      ·
                        rfl

theorem cell23_3556306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_3556306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556306 prefixEnd_3556306 := by exact prefixLift 3556306
  have htrace : WordTrace (prefixWord ++ tailWord_3556306) baseStart_3556306 baseEnd_3556306 := by
    simpa [prefixWord, tailWord_3556306, baseEnd_3556306] using wordTrace_append hprefix tailTrace_3556306
  have hstable : (prefixWord ++ tailWord_3556306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556306).length < 2 ^ (prefixWord ++ tailWord_3556306).sum := by decide
  have hdescent : baseEnd_3556306 < baseStart_3556306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556328 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3556328 : Nat := 118140960795 + 3556328 * 2 ^ 59
def prefixEnd_3556328 : Nat := 4983230072969 + 3 ^ 40 * 3556328 * 2
def baseEnd_3556328 : Nat := 1826105629042867084044751

theorem tailTrace_3556328 : CollatzResearch.WordTrace tailWord_3556328 prefixEnd_3556328 1826105629042867084044751 := by
  unfold tailWord_3556328
  simp only [CollatzResearch.WordTrace]
  refine ⟨64854969130019251656058819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86473292173359002208078425 64854969130019251656058819)
  ·
    refine ⟨97282453695028877484088229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64854969130019251656058819 97282453695028877484088229)
    ·
      refine ⟨18240460067817914528266543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97282453695028877484088229 18240460067817914528266543)
      ·
        refine ⟨27360690101726871792399815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18240460067817914528266543 27360690101726871792399815)
        ·
          refine ⟨41041035152590307688599723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27360690101726871792399815 41041035152590307688599723)
          ·
            refine ⟨61561552728885461532899585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41041035152590307688599723 61561552728885461532899585)
            ·
              refine ⟨46171164546664096149674689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61561552728885461532899585 46171164546664096149674689)
              ·
                refine ⟨34628373409998072112256017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46171164546664096149674689 34628373409998072112256017)
                ·
                  refine ⟨25971280057498554084192013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34628373409998072112256017 25971280057498554084192013)
                  ·
                    refine ⟨9739230021561957781572005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25971280057498554084192013 9739230021561957781572005)
                    ·
                      refine ⟨1826105629042867084044751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9739230021561957781572005 1826105629042867084044751)
                      ·
                        rfl

theorem cell23_3556328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3556328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556328 prefixEnd_3556328 := by exact prefixLift 3556328
  have htrace : WordTrace (prefixWord ++ tailWord_3556328) baseStart_3556328 baseEnd_3556328 := by
    simpa [prefixWord, tailWord_3556328, baseEnd_3556328] using wordTrace_append hprefix tailTrace_3556328
  have hstable : (prefixWord ++ tailWord_3556328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556328).length < 2 ^ (prefixWord ++ tailWord_3556328).sum := by decide
  have hdescent : baseEnd_3556328 < baseStart_3556328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556345 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 3, 4, 2]
def baseStart_3556345 : Nat := 118140960795 + 3556345 * 2 ^ 59
def prefixEnd_3556345 : Nat := 4983230072969 + 3 ^ 40 * 3556345 * 2
def baseEnd_3556345 : Nat := 1826114358213993517532173

theorem tailTrace_3556345 : CollatzResearch.WordTrace tailWord_3556345 prefixEnd_3556345 1826114358213993517532173 := by
  unfold tailWord_3556345
  simp only [CollatzResearch.WordTrace]
  refine ⟨129710558300976915215486489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86473705533984610143657659 129710558300976915215486489)
  ·
    refine ⟨97282918725732686411614867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129710558300976915215486489 97282918725732686411614867)
    ·
      refine ⟨145924378088599029617422301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97282918725732686411614867 145924378088599029617422301)
      ·
        refine ⟨54721641783224636106533363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145924378088599029617422301 54721641783224636106533363)
        ·
          refine ⟨82082462674836954159800045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54721641783224636106533363 82082462674836954159800045)
          ·
            refine ⟨30780923503063857809925017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82082462674836954159800045 30780923503063857809925017)
            ·
              refine ⟨23085692627297893357443763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30780923503063857809925017 23085692627297893357443763)
              ·
                refine ⟨34628538940946840036165645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23085692627297893357443763 34628538940946840036165645)
                ·
                  refine ⟨12985702102855065013562117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34628538940946840036165645 12985702102855065013562117)
                  ·
                    refine ⟨2434819144285324690042897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12985702102855065013562117 2434819144285324690042897)
                    ·
                      refine ⟨1826114358213993517532173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434819144285324690042897 1826114358213993517532173)
                      ·
                        rfl

theorem cell23_3556345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_3556345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556345 prefixEnd_3556345 := by exact prefixLift 3556345
  have htrace : WordTrace (prefixWord ++ tailWord_3556345) baseStart_3556345 baseEnd_3556345 := by
    simpa [prefixWord, tailWord_3556345, baseEnd_3556345] using wordTrace_append hprefix tailTrace_3556345
  have hstable : (prefixWord ++ tailWord_3556345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556345).length < 2 ^ (prefixWord ++ tailWord_3556345).sum := by decide
  have hdescent : baseEnd_3556345 < baseStart_3556345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556348 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_3556348 : Nat := 118140960795 + 3556348 * 2 ^ 59
def prefixEnd_3556348 : Nat := 4983230072969 + 3 ^ 40 * 3556348 * 2
def baseEnd_3556348 : Nat := 1826115898655957005794659

theorem tailTrace_3556348 : CollatzResearch.WordTrace tailWord_3556348 prefixEnd_3556348 1826115898655957005794659 := by
  unfold tailWord_3556348
  simp only [CollatzResearch.WordTrace]
  refine ⟨64855333859983023363922849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86473778479977364485230465 64855333859983023363922849)
  ·
    refine ⟨48641500394987267522942137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64855333859983023363922849 48641500394987267522942137)
    ·
      refine ⟨36481125296240450642206603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48641500394987267522942137 36481125296240450642206603)
      ·
        refine ⟨54721687944360675963309905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36481125296240450642206603 54721687944360675963309905)
        ·
          refine ⟨41041265958270506972482429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54721687944360675963309905 41041265958270506972482429)
          ·
            refine ⟨15390474734351440114680911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41041265958270506972482429 15390474734351440114680911)
            ·
              refine ⟨23085712101527160172021367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15390474734351440114680911 23085712101527160172021367)
              ·
                refine ⟨34628568152290740258032051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23085712101527160172021367 34628568152290740258032051)
                ·
                  refine ⟨51942852228436110387048077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34628568152290740258032051 51942852228436110387048077)
                  ·
                    refine ⟨19478569585663541395143029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51942852228436110387048077 19478569585663541395143029)
                    ·
                      refine ⟨1826115898655957005794659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19478569585663541395143029 1826115898655957005794659)
                      ·
                        rfl

theorem cell23_3556348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_3556348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556348 prefixEnd_3556348 := by exact prefixLift 3556348
  have htrace : WordTrace (prefixWord ++ tailWord_3556348) baseStart_3556348 baseEnd_3556348 := by
    simpa [prefixWord, tailWord_3556348, baseEnd_3556348] using wordTrace_append hprefix tailTrace_3556348
  have hstable : (prefixWord ++ tailWord_3556348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556348).length < 2 ^ (prefixWord ++ tailWord_3556348).sum := by decide
  have hdescent : baseEnd_3556348 < baseStart_3556348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556428 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_3556428 : Nat := 118140960795 + 3556428 * 2 ^ 59
def prefixEnd_3556428 : Nat := 4983230072969 + 3 ^ 40 * 3556428 * 2
def baseEnd_3556428 : Nat := 608718992369438897598097

theorem tailTrace_3556428 : CollatzResearch.WordTrace tailWord_3556428 prefixEnd_3556428 608718992369438897598097 := by
  unfold tailWord_3556428
  simp only [CollatzResearch.WordTrace]
  refine ⟨64856792779838110195378969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86475723706450813593838625 64856792779838110195378969)
  ·
    refine ⟨48642594584878582646534227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64856792779838110195378969 48642594584878582646534227)
    ·
      refine ⟨72963891877317873969801341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48642594584878582646534227 72963891877317873969801341)
      ·
        refine ⟨27361459453994202738675503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72963891877317873969801341 27361459453994202738675503)
        ·
          refine ⟨41042189180991304108013255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27361459453994202738675503 41042189180991304108013255)
          ·
            refine ⟨61563283771486956162019883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41042189180991304108013255 61563283771486956162019883)
            ·
              refine ⟨92344925657230434243029825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61563283771486956162019883 92344925657230434243029825)
              ·
                refine ⟨69258694242922825682272369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92344925657230434243029825 69258694242922825682272369)
                ·
                  refine ⟨51944020682192119261704277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69258694242922825682272369 51944020682192119261704277)
                  ·
                    refine ⟨608718992369438897598097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51944020682192119261704277 608718992369438897598097)
                    ·
                      rfl

theorem cell23_3556428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_3556428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556428 prefixEnd_3556428 := by exact prefixLift 3556428
  have htrace : WordTrace (prefixWord ++ tailWord_3556428) baseStart_3556428 baseEnd_3556428 := by
    simpa [prefixWord, tailWord_3556428, baseEnd_3556428] using wordTrace_append hprefix tailTrace_3556428
  have hstable : (prefixWord ++ tailWord_3556428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556428).length < 2 ^ (prefixWord ++ tailWord_3556428).sum := by decide
  have hdescent : baseEnd_3556428 < baseStart_3556428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556435 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 1, 6, 2]
def baseStart_3556435 : Nat := 118140960795 + 3556435 * 2 ^ 59
def prefixEnd_3556435 : Nat := 4983230072969 + 3 ^ 40 * 3556435 * 2
def baseEnd_3556435 : Nat := 1826160571472898165406759

theorem tailTrace_3556435 : CollatzResearch.WordTrace tailWord_3556435 prefixEnd_3556435 1826160571472898165406759 := by
  unfold tailWord_3556435
  simp only [CollatzResearch.WordTrace]
  refine ⟨129713840870650860586262759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86475893913767240390841839 129713840870650860586262759)
  ·
    refine ⟨194570761305976290879394139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129713840870650860586262759 194570761305976290879394139)
    ·
      refine ⟨291856141958964436319091209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194570761305976290879394139 291856141958964436319091209)
      ·
        refine ⟨218892106469223327239318407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291856141958964436319091209 218892106469223327239318407)
        ·
          refine ⟨328338159703834990858977611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218892106469223327239318407 328338159703834990858977611)
          ·
            refine ⟨492507239555752486288466417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328338159703834990858977611 492507239555752486288466417)
            ·
              refine ⟨369380429666814364716349813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492507239555752486288466417 369380429666814364716349813)
              ·
                refine ⟨34629415281263846692157795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 369380429666814364716349813 34629415281263846692157795)
                ·
                  refine ⟨51944122921895770038236693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34629415281263846692157795 51944122921895770038236693)
                  ·
                    refine ⟨2434880761963864220542345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51944122921895770038236693 2434880761963864220542345)
                    ·
                      refine ⟨1826160571472898165406759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434880761963864220542345 1826160571472898165406759)
                      ·
                        rfl

theorem cell23_3556435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 6, 2].length) (baseStart_3556435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556435 prefixEnd_3556435 := by exact prefixLift 3556435
  have htrace : WordTrace (prefixWord ++ tailWord_3556435) baseStart_3556435 baseEnd_3556435 := by
    simpa [prefixWord, tailWord_3556435, baseEnd_3556435] using wordTrace_append hprefix tailTrace_3556435
  have hstable : (prefixWord ++ tailWord_3556435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556435).length < 2 ^ (prefixWord ++ tailWord_3556435).sum := by decide
  have hdescent : baseEnd_3556435 < baseStart_3556435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556512 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 1, 5, 2]
def baseStart_3556512 : Nat := 118140960795 + 3556512 * 2 ^ 59
def prefixEnd_3556512 : Nat := 4983230072969 + 3 ^ 40 * 3556512 * 2
def baseEnd_3556512 : Nat := 1826200109483294364143905

theorem tailTrace_3556512 : CollatzResearch.WordTrace tailWord_3556512 prefixEnd_3556512 1826200109483294364143905 := by
  unfold tailWord_3556512
  simp only [CollatzResearch.WordTrace]
  refine ⟨64858324645685951368407895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86477766194247935157877193 64858324645685951368407895)
  ·
    refine ⟨97287486968528927052611843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64858324645685951368407895 97287486968528927052611843)
    ·
      refine ⟨145931230452793390578917765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97287486968528927052611843 145931230452793390578917765)
      ·
        refine ⟨27362105709898760733547081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145931230452793390578917765 27362105709898760733547081)
        ·
          refine ⟨20521579282424070550160311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27362105709898760733547081 20521579282424070550160311)
          ·
            refine ⟨30782368923636105825240467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20521579282424070550160311 30782368923636105825240467)
            ·
              refine ⟨46173553385454158737860701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30782368923636105825240467 46173553385454158737860701)
              ·
                refine ⟨17315082519545309526697763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46173553385454158737860701 17315082519545309526697763)
                ·
                  refine ⟨25972623779317964290046645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17315082519545309526697763 25972623779317964290046645)
                  ·
                    refine ⟨2434933479311059152191873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25972623779317964290046645 2434933479311059152191873)
                    ·
                      refine ⟨1826200109483294364143905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434933479311059152191873 1826200109483294364143905)
                      ·
                        rfl

theorem cell23_3556512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_3556512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556512 prefixEnd_3556512 := by exact prefixLift 3556512
  have htrace : WordTrace (prefixWord ++ tailWord_3556512) baseStart_3556512 baseEnd_3556512 := by
    simpa [prefixWord, tailWord_3556512, baseEnd_3556512] using wordTrace_append hprefix tailTrace_3556512
  have hstable : (prefixWord ++ tailWord_3556512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556512).length < 2 ^ (prefixWord ++ tailWord_3556512).sum := by decide
  have hdescent : baseEnd_3556512 < baseStart_3556512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556529 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 4, 3, 2]
def baseStart_3556529 : Nat := 118140960795 + 3556529 * 2 ^ 59
def prefixEnd_3556529 : Nat := 4983230072969 + 3 ^ 40 * 3556529 * 2
def baseEnd_3556529 : Nat := 1826208838654420797631327

theorem tailTrace_3556529 : CollatzResearch.WordTrace tailWord_3556529 prefixEnd_3556529 1826208838654420797631327 := by
  unfold tailWord_3556529
  simp only [CollatzResearch.WordTrace]
  refine ⟨129717269332310314640184641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86478179554873543093456427 129717269332310314640184641)
  ·
    refine ⟨97287951999232735980138481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129717269332310314640184641 97287951999232735980138481)
    ·
      refine ⟨72965963999424551985103861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97287951999232735980138481 72965963999424551985103861)
      ·
        refine ⟨6840559124946051748603487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72965963999424551985103861 6840559124946051748603487)
        ·
          refine ⟨10260838687419077622905231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840559124946051748603487 10260838687419077622905231)
          ·
            refine ⟨15391258031128616434357847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10260838687419077622905231 15391258031128616434357847)
            ·
              refine ⟨23086887046692924651536771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15391258031128616434357847 23086887046692924651536771)
              ·
                refine ⟨34630330570039386977305157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23086887046692924651536771 34630330570039386977305157)
                ·
                  refine ⟨6493186981882385058244717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34630330570039386977305157 6493186981882385058244717)
                  ·
                    refine ⟨2434945118205894396841769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6493186981882385058244717 2434945118205894396841769)
                    ·
                      refine ⟨1826208838654420797631327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2434945118205894396841769 1826208838654420797631327)
                      ·
                        rfl

theorem cell23_3556529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_3556529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556529 prefixEnd_3556529 := by exact prefixLift 3556529
  have htrace : WordTrace (prefixWord ++ tailWord_3556529) baseStart_3556529 baseEnd_3556529 := by
    simpa [prefixWord, tailWord_3556529, baseEnd_3556529] using wordTrace_append hprefix tailTrace_3556529
  have hstable : (prefixWord ++ tailWord_3556529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556529).length < 2 ^ (prefixWord ++ tailWord_3556529).sum := by decide
  have hdescent : baseEnd_3556529 < baseStart_3556529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556595 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 2, 7]
def baseStart_3556595 : Nat := 118140960795 + 3556595 * 2 ^ 59
def prefixEnd_3556595 : Nat := 4983230072969 + 3 ^ 40 * 3556595 * 2
def baseEnd_3556595 : Nat := 608747576125872513135341

theorem tailTrace_3556595 : CollatzResearch.WordTrace tailWord_3556595 prefixEnd_3556595 608747576125872513135341 := by
  unfold tailWord_3556595
  simp only [CollatzResearch.WordTrace]
  refine ⟨129719676550071207912087239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86479784366714138608058159 129719676550071207912087239)
  ·
    refine ⟨194579514825106811868130859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129719676550071207912087239 194579514825106811868130859)
    ·
      refine ⟨291869272237660217802196289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194579514825106811868130859 291869272237660217802196289)
      ·
        refine ⟨218901954178245163351647217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291869272237660217802196289 218901954178245163351647217)
        ·
          refine ⟨164176465633683872513735413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218901954178245163351647217 164176465633683872513735413)
          ·
            refine ⟨15391543653157863048162695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164176465633683872513735413 15391543653157863048162695)
            ·
              refine ⟨23087315479736794572244043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15391543653157863048162695 23087315479736794572244043)
              ·
                refine ⟨34630973219605191858366065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23087315479736794572244043 34630973219605191858366065)
                ·
                  refine ⟨25973229914703893893774549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34630973219605191858366065 25973229914703893893774549)
                  ·
                    refine ⟨608747576125872513135341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25973229914703893893774549 608747576125872513135341)
                    ·
                      rfl

theorem cell23_3556595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 7].length) (baseStart_3556595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556595 prefixEnd_3556595 := by exact prefixLift 3556595
  have htrace : WordTrace (prefixWord ++ tailWord_3556595) baseStart_3556595 baseEnd_3556595 := by
    simpa [prefixWord, tailWord_3556595, baseEnd_3556595] using wordTrace_append hprefix tailTrace_3556595
  have hstable : (prefixWord ++ tailWord_3556595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556595).length < 2 ^ (prefixWord ++ tailWord_3556595).sum := by decide
  have hdescent : baseEnd_3556595 < baseStart_3556595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556605 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_3556605 : Nat := 118140960795 + 3556605 * 2 ^ 59
def prefixEnd_3556605 : Nat := 4983230072969 + 3 ^ 40 * 3556605 * 2
def baseEnd_3556605 : Nat := 1826247863184162500280977

theorem tailTrace_3556605 : CollatzResearch.WordTrace tailWord_3556605 prefixEnd_3556605 1826247863184162500280977 := by
  unfold tailWord_3556605
  simp only [CollatzResearch.WordTrace]
  refine ⟨129720041280034979619951269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86480027520023319746634179 129720041280034979619951269)
  ·
    refine ⟨24322507740006558678740863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129720041280034979619951269 24322507740006558678740863)
    ·
      refine ⟨36483761610009838018111295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24322507740006558678740863 36483761610009838018111295)
      ·
        refine ⟨54725642415014757027166943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36483761610009838018111295 54725642415014757027166943)
        ·
          refine ⟨82088463622522135540750415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54725642415014757027166943 82088463622522135540750415)
          ·
            refine ⟨123132695433783203311125623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82088463622522135540750415 123132695433783203311125623)
            ·
              refine ⟨184699043150674804966688435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123132695433783203311125623 184699043150674804966688435)
              ·
                refine ⟨277048564726012207450032653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184699043150674804966688435 277048564726012207450032653)
                ·
                  refine ⟨103893211772254577793762245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277048564726012207450032653 103893211772254577793762245)
                  ·
                    refine ⟨19479977207297733336330421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103893211772254577793762245 19479977207297733336330421)
                    ·
                      refine ⟨1826247863184162500280977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19479977207297733336330421 1826247863184162500280977)
                      ·
                        rfl

theorem cell23_3556605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_3556605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556605 prefixEnd_3556605 := by exact prefixLift 3556605
  have htrace : WordTrace (prefixWord ++ tailWord_3556605) baseStart_3556605 baseEnd_3556605 := by
    simpa [prefixWord, tailWord_3556605, baseEnd_3556605] using wordTrace_append hprefix tailTrace_3556605
  have hstable : (prefixWord ++ tailWord_3556605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556605).length < 2 ^ (prefixWord ++ tailWord_3556605).sum := by decide
  have hdescent : baseEnd_3556605 < baseStart_3556605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556609 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_3556609 : Nat := 118140960795 + 3556609 * 2 ^ 59
def prefixEnd_3556609 : Nat := 4983230072969 + 3 ^ 40 * 3556609 * 2
def baseEnd_3556609 : Nat := 1826249917106780484630959

theorem tailTrace_3556609 : CollatzResearch.WordTrace tailWord_3556609 prefixEnd_3556609 1826249917106780484630959 := by
  unfold tailWord_3556609
  simp only [CollatzResearch.WordTrace]
  refine ⟨129720187172020488303096881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86480124781346992202064587 129720187172020488303096881)
  ·
    refine ⟨97290140379015366227322661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129720187172020488303096881 97290140379015366227322661)
    ·
      refine ⟨18241901321065381167622999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97290140379015366227322661 18241901321065381167622999)
      ·
        refine ⟨27362851981598071751434499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18241901321065381167622999 27362851981598071751434499)
        ·
          refine ⟨41044277972397107627151749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27362851981598071751434499 41044277972397107627151749)
          ·
            refine ⟨7695802119824457680090953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41044277972397107627151749 7695802119824457680090953)
            ·
              refine ⟨5771851589868343260068215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7695802119824457680090953 5771851589868343260068215)
              ·
                refine ⟨8657777384802514890102323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5771851589868343260068215 8657777384802514890102323)
                ·
                  refine ⟨12986666077203772335153485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8657777384802514890102323 12986666077203772335153485)
                  ·
                    refine ⟨4869999778951414625682557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12986666077203772335153485 4869999778951414625682557)
                    ·
                      refine ⟨1826249917106780484630959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4869999778951414625682557 1826249917106780484630959)
                      ·
                        rfl

theorem cell23_3556609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_3556609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556609 prefixEnd_3556609 := by exact prefixLift 3556609
  have htrace : WordTrace (prefixWord ++ tailWord_3556609) baseStart_3556609 baseEnd_3556609 := by
    simpa [prefixWord, tailWord_3556609, baseEnd_3556609] using wordTrace_append hprefix tailTrace_3556609
  have hstable : (prefixWord ++ tailWord_3556609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556609).length < 2 ^ (prefixWord ++ tailWord_3556609).sum := by decide
  have hdescent : baseEnd_3556609 < baseStart_3556609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556619 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 3, 3, 2]
def baseStart_3556619 : Nat := 118140960795 + 3556619 * 2 ^ 59
def prefixEnd_3556619 : Nat := 4983230072969 + 3 ^ 40 * 3556619 * 2
def baseEnd_3556619 : Nat := 1826255051913325445505913

theorem tailTrace_3556619 : CollatzResearch.WordTrace tailWord_3556619 prefixEnd_3556619 1826255051913325445505913 := by
  unfold tailWord_3556619
  simp only [CollatzResearch.WordTrace]
  refine ⟨129720551901984260010960911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86480367934656173340640607 129720551901984260010960911)
  ·
    refine ⟨194580827852976390016441367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129720551901984260010960911 194580827852976390016441367)
    ·
      refine ⟨291871241779464585024662051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194580827852976390016441367 291871241779464585024662051)
      ·
        refine ⟨437806862669196877536993077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291871241779464585024662051 437806862669196877536993077)
        ·
          refine ⟨41044393375237207269093101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 437806862669196877536993077 41044393375237207269093101)
          ·
            refine ⟨15391647515713952725909913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41044393375237207269093101 15391647515713952725909913)
            ·
              refine ⟨11543735636785464544432435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15391647515713952725909913 11543735636785464544432435)
              ·
                refine ⟨17315603455178196816648653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11543735636785464544432435 17315603455178196816648653)
                ·
                  refine ⟨6493351295691823806243245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17315603455178196816648653 6493351295691823806243245)
                  ·
                    refine ⟨2435006735884433927341217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6493351295691823806243245 2435006735884433927341217)
                    ·
                      refine ⟨1826255051913325445505913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435006735884433927341217 1826255051913325445505913)
                      ·
                        rfl

theorem cell23_3556619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 3, 2].length) (baseStart_3556619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556619 prefixEnd_3556619 := by exact prefixLift 3556619
  have htrace : WordTrace (prefixWord ++ tailWord_3556619) baseStart_3556619 baseEnd_3556619 := by
    simpa [prefixWord, tailWord_3556619, baseEnd_3556619] using wordTrace_append hprefix tailTrace_3556619
  have hstable : (prefixWord ++ tailWord_3556619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556619).length < 2 ^ (prefixWord ++ tailWord_3556619).sum := by decide
  have hdescent : baseEnd_3556619 < baseStart_3556619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556625 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 1, 8]
def baseStart_3556625 : Nat := 118140960795 + 3556625 * 2 ^ 59
def prefixEnd_3556625 : Nat := 4983230072969 + 3 ^ 40 * 3556625 * 2
def baseEnd_3556625 : Nat := 608752710932417474010295

theorem tailTrace_3556625 : CollatzResearch.WordTrace tailWord_3556625 prefixEnd_3556625 608752710932417474010295 := by
  unfold tailWord_3556625
  simp only [CollatzResearch.WordTrace]
  refine ⟨129720770739962523035679329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86480513826641682023786219 129720770739962523035679329)
  ·
    refine ⟨97290578054971892276759497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129720770739962523035679329 97290578054971892276759497)
    ·
      refine ⟨72967933541228919207569623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97290578054971892276759497 72967933541228919207569623)
      ·
        refine ⟨109451900311843378811354435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72967933541228919207569623 109451900311843378811354435)
        ·
          refine ⟨164177850467765068217031653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109451900311843378811354435 164177850467765068217031653)
          ·
            refine ⟨30783346962705950290693435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164177850467765068217031653 30783346962705950290693435)
            ·
              refine ⟨46175020444058925436040153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30783346962705950290693435 46175020444058925436040153)
              ·
                refine ⟨34631265333044194077030115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46175020444058925436040153 34631265333044194077030115)
                ·
                  refine ⟨51946897999566291115545173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34631265333044194077030115 51946897999566291115545173)
                  ·
                    refine ⟨608752710932417474010295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51946897999566291115545173 608752710932417474010295)
                    ·
                      rfl

theorem cell23_3556625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_3556625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556625 prefixEnd_3556625 := by exact prefixLift 3556625
  have htrace : WordTrace (prefixWord ++ tailWord_3556625) baseStart_3556625 baseEnd_3556625 := by
    simpa [prefixWord, tailWord_3556625, baseEnd_3556625] using wordTrace_append hprefix tailTrace_3556625
  have hstable : (prefixWord ++ tailWord_3556625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556625).length < 2 ^ (prefixWord ++ tailWord_3556625).sum := by decide
  have hdescent : baseEnd_3556625 < baseStart_3556625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556635 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 5]
def baseStart_3556635 : Nat := 118140960795 + 3556635 * 2 ^ 59
def prefixEnd_3556635 : Nat := 4983230072969 + 3 ^ 40 * 3556635 * 2
def baseEnd_3556635 : Nat := 1826263267603797382905839

theorem tailTrace_3556635 : CollatzResearch.WordTrace tailWord_3556635 prefixEnd_3556635 1826263267603797382905839 := by
  unfold tailWord_3556635
  simp only [CollatzResearch.WordTrace]
  refine ⟨129721135469926294743543359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86480756979950863162362239 129721135469926294743543359)
  ·
    refine ⟨194581703204889442115315039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129721135469926294743543359 194581703204889442115315039)
    ·
      refine ⟨291872554807334163172972559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194581703204889442115315039 291872554807334163172972559)
      ·
        refine ⟨437808832211001244759458839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291872554807334163172972559 437808832211001244759458839)
        ·
          refine ⟨656713248316501867139188259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437808832211001244759458839 656713248316501867139188259)
          ·
            refine ⟨985069872474752800708782389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656713248316501867139188259 985069872474752800708782389)
            ·
              refine ⟨92350300544508075066448349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 985069872474752800708782389 92350300544508075066448349)
              ·
                refine ⟨34631362704190528149918131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92350300544508075066448349 34631362704190528149918131)
                ·
                  refine ⟨51947044056285792224877197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34631362704190528149918131 51947044056285792224877197)
                  ·
                    refine ⟨19480141521107172084328949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51947044056285792224877197 19480141521107172084328949)
                    ·
                      refine ⟨1826263267603797382905839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19480141521107172084328949 1826263267603797382905839)
                      ·
                        rfl

theorem cell23_3556635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_3556635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556635 prefixEnd_3556635 := by exact prefixLift 3556635
  have htrace : WordTrace (prefixWord ++ tailWord_3556635) baseStart_3556635 baseEnd_3556635 := by
    simpa [prefixWord, tailWord_3556635, baseEnd_3556635] using wordTrace_append hprefix tailTrace_3556635
  have hstable : (prefixWord ++ tailWord_3556635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556635).length < 2 ^ (prefixWord ++ tailWord_3556635).sum := by decide
  have hdescent : baseEnd_3556635 < baseStart_3556635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556682 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_3556682 : Nat := 118140960795 + 3556682 * 2 ^ 59
def prefixEnd_3556682 : Nat := 4983230072969 + 3 ^ 40 * 3556682 * 2
def baseEnd_3556682 : Nat := 1826287401194558699018123

theorem tailTrace_3556682 : CollatzResearch.WordTrace tailWord_3556682 prefixEnd_3556682 1826287401194558699018123 := by
  unfold tailWord_3556682
  simp only [CollatzResearch.WordTrace]
  refine ⟨32430712425189005442626075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86481899800504014513669533 32430712425189005442626075)
  ·
    refine ⟨48646068637783508163939113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32430712425189005442626075 48646068637783508163939113)
    ·
      refine ⟨36484551478337631122954335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48646068637783508163939113 36484551478337631122954335)
      ·
        refine ⟨54726827217506446684431503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36484551478337631122954335 54726827217506446684431503)
        ·
          refine ⟨82090240826259670026647255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54726827217506446684431503 82090240826259670026647255)
          ·
            refine ⟨123135361239389505039970883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82090240826259670026647255 123135361239389505039970883)
            ·
              refine ⟨184703041859084257559956325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123135361239389505039970883 184703041859084257559956325)
              ·
                refine ⟨34631820348578298292491811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184703041859084257559956325 34631820348578298292491811)
                ·
                  refine ⟨51947730522867447438737717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34631820348578298292491811 51947730522867447438737717)
                  ·
                    refine ⟨4870099736518823197381661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51947730522867447438737717 4870099736518823197381661)
                    ·
                      refine ⟨1826287401194558699018123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4870099736518823197381661 1826287401194558699018123)
                      ·
                        rfl

theorem cell23_3556682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_3556682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556682 prefixEnd_3556682 := by exact prefixLift 3556682
  have htrace : WordTrace (prefixWord ++ tailWord_3556682) baseStart_3556682 baseEnd_3556682 := by
    simpa [prefixWord, tailWord_3556682, baseEnd_3556682] using wordTrace_append hprefix tailTrace_3556682
  have hstable : (prefixWord ++ tailWord_3556682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556682).length < 2 ^ (prefixWord ++ tailWord_3556682).sum := by decide
  have hdescent : baseEnd_3556682 < baseStart_3556682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556709 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 2, 5, 2]
def baseStart_3556709 : Nat := 118140960795 + 3556709 * 2 ^ 59
def prefixEnd_3556709 : Nat := 4983230072969 + 3 ^ 40 * 3556709 * 2
def baseEnd_3556709 : Nat := 1826301265172230093380499

theorem tailTrace_3556709 : CollatzResearch.WordTrace tailWord_3556709 prefixEnd_3556709 1826301265172230093380499 := by
  unfold tailWord_3556709
  simp only [CollatzResearch.WordTrace]
  refine ⟨129723834471658205381737181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86482556314438803587824787 129723834471658205381737181)
  ·
    refine ⟨48646437926871827018151443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129723834471658205381737181 48646437926871827018151443)
    ·
      refine ⟨72969656890307740527227165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48646437926871827018151443 72969656890307740527227165)
      ·
        refine ⟨27363621333865402697710187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72969656890307740527227165 27363621333865402697710187)
        ·
          refine ⟨41045432000798104046565281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27363621333865402697710187 41045432000798104046565281)
          ·
            refine ⟨30784074000598578034923961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41045432000798104046565281 30784074000598578034923961)
            ·
              refine ⟨23088055500448933526192971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30784074000598578034923961 23088055500448933526192971)
              ·
                refine ⟨34632083250673400289289457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23088055500448933526192971 34632083250673400289289457)
                ·
                  refine ⟨25974062438005050216967093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34632083250673400289289457 25974062438005050216967093)
                  ·
                    refine ⟨2435068353562973457840665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25974062438005050216967093 2435068353562973457840665)
                    ·
                      refine ⟨1826301265172230093380499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435068353562973457840665 1826301265172230093380499)
                      ·
                        rfl

theorem cell23_3556709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_3556709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556709 prefixEnd_3556709 := by exact prefixLift 3556709
  have htrace : WordTrace (prefixWord ++ tailWord_3556709) baseStart_3556709 baseEnd_3556709 := by
    simpa [prefixWord, tailWord_3556709, baseEnd_3556709] using wordTrace_append hprefix tailTrace_3556709
  have hstable : (prefixWord ++ tailWord_3556709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556709).length < 2 ^ (prefixWord ++ tailWord_3556709).sum := by decide
  have hdescent : baseEnd_3556709 < baseStart_3556709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556739 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 4]
def baseStart_3556739 : Nat := 118140960795 + 3556739 * 2 ^ 59
def prefixEnd_3556739 : Nat := 4983230072969 + 3 ^ 40 * 3556739 * 2
def baseEnd_3556739 : Nat := 1826316669591864976005361

theorem tailTrace_3556739 : CollatzResearch.WordTrace tailWord_3556739 prefixEnd_3556739 1826316669591864976005361 := by
  unfold tailWord_3556739
  simp only [CollatzResearch.WordTrace]
  refine ⟨129724928661549520505329271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86483285774366347003552847 129724928661549520505329271)
  ·
    refine ⟨194587392992324280757993907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129724928661549520505329271 194587392992324280757993907)
    ·
      refine ⟨291881089488486421136990861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194587392992324280757993907 291881089488486421136990861)
      ·
        refine ⟨109455408558182407926371573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291881089488486421136990861 109455408558182407926371573)
        ·
          refine ⟨10261444552329600743097335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109455408558182407926371573 10261444552329600743097335)
          ·
            refine ⟨15392166828494401114646003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10261444552329600743097335 15392166828494401114646003)
            ·
              refine ⟨23088250242741601671969005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15392166828494401114646003 23088250242741601671969005)
              ·
                refine ⟨8658093841028100626988377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23088250242741601671969005 8658093841028100626988377)
                ·
                  refine ⟨6493570380771075470241283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8658093841028100626988377 6493570380771075470241283)
                  ·
                    refine ⟨9740355571156613205361925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6493570380771075470241283 9740355571156613205361925)
                    ·
                      refine ⟨1826316669591864976005361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9740355571156613205361925 1826316669591864976005361)
                      ·
                        rfl

theorem cell23_3556739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_3556739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556739 prefixEnd_3556739 := by exact prefixLift 3556739
  have htrace : WordTrace (prefixWord ++ tailWord_3556739) baseStart_3556739 baseEnd_3556739 := by
    simpa [prefixWord, tailWord_3556739, baseEnd_3556739] using wordTrace_append hprefix tailTrace_3556739
  have hstable : (prefixWord ++ tailWord_3556739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556739).length < 2 ^ (prefixWord ++ tailWord_3556739).sum := by decide
  have hdescent : baseEnd_3556739 < baseStart_3556739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556756 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3556756 : Nat := 118140960795 + 3556756 * 2 ^ 59
def prefixEnd_3556756 : Nat := 4983230072969 + 3 ^ 40 * 3556756 * 2
def baseEnd_3556756 : Nat := 1826325398762991409492783

theorem tailTrace_3556756 : CollatzResearch.WordTrace tailWord_3556756 prefixEnd_3556756 1826325398762991409492783 := by
  unfold tailWord_3556756
  simp only [CollatzResearch.WordTrace]
  refine ⟨64862774351243966204349061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86483699134991954939132081 64862774351243966204349061)
  ·
    refine ⟨12161770190858243663315449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64862774351243966204349061 12161770190858243663315449)
    ·
      refine ⟨9121327643143682747486587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12161770190858243663315449 9121327643143682747486587)
      ·
        refine ⟨13681991464715524121229881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9121327643143682747486587 13681991464715524121229881)
        ·
          refine ⟨10261493598536643090922411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13681991464715524121229881 10261493598536643090922411)
          ·
            refine ⟨15392240397804964636383617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10261493598536643090922411 15392240397804964636383617)
            ·
              refine ⟨11544180298353723477287713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15392240397804964636383617 11544180298353723477287713)
              ·
                refine ⟨8658135223765292607965785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11544180298353723477287713 8658135223765292607965785)
                ·
                  refine ⟨6493601417823969455974339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8658135223765292607965785 6493601417823969455974339)
                  ·
                    refine ⟨9740402126735954183961509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6493601417823969455974339 9740402126735954183961509)
                    ·
                      refine ⟨1826325398762991409492783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9740402126735954183961509 1826325398762991409492783)
                      ·
                        rfl

theorem cell23_3556756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3556756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556756 prefixEnd_3556756 := by exact prefixLift 3556756
  have htrace : WordTrace (prefixWord ++ tailWord_3556756) baseStart_3556756 baseEnd_3556756 := by
    simpa [prefixWord, tailWord_3556756, baseEnd_3556756] using wordTrace_append hprefix tailTrace_3556756
  have hstable : (prefixWord ++ tailWord_3556756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556756).length < 2 ^ (prefixWord ++ tailWord_3556756).sum := by decide
  have hdescent : baseEnd_3556756 < baseStart_3556756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556793 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3556793 : Nat := 118140960795 + 3556793 * 2 ^ 59
def prefixEnd_3556793 : Nat := 4983230072969 + 3 ^ 40 * 3556793 * 2
def baseEnd_3556793 : Nat := 1826344397547207764730113

theorem tailTrace_3556793 : CollatzResearch.WordTrace tailWord_3556793 prefixEnd_3556793 1826344397547207764730113 := by
  unfold tailWord_3556793
  simp only [CollatzResearch.WordTrace]
  refine ⟨129726898203353887727795033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86484598802235925151863355 129726898203353887727795033)
  ·
    refine ⟨97295173652515415795846275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129726898203353887727795033 97295173652515415795846275)
    ·
      refine ⟨145942760478773123693769413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97295173652515415795846275 145942760478773123693769413)
      ·
        refine ⟨27364267589769960692581765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145942760478773123693769413 27364267589769960692581765)
        ·
          refine ⟨5130800173081867629859081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27364267589769960692581765 5130800173081867629859081)
          ·
            refine ⟨3848100129811400722394311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5130800173081867629859081 3848100129811400722394311)
            ·
              refine ⟨5772150194717101083591467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848100129811400722394311 5772150194717101083591467)
              ·
                refine ⟨8658225292075651625387201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772150194717101083591467 8658225292075651625387201)
                ·
                  refine ⟨6493668969056738719040401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8658225292075651625387201 6493668969056738719040401)
                  ·
                    refine ⟨4870251726792554039280301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6493668969056738719040401 4870251726792554039280301)
                    ·
                      refine ⟨1826344397547207764730113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4870251726792554039280301 1826344397547207764730113)
                      ·
                        rfl

theorem cell23_3556793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3556793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556793 prefixEnd_3556793 := by exact prefixLift 3556793
  have htrace : WordTrace (prefixWord ++ tailWord_3556793) baseStart_3556793 baseEnd_3556793 := by
    simpa [prefixWord, tailWord_3556793, baseEnd_3556793] using wordTrace_append hprefix tailTrace_3556793
  have hstable : (prefixWord ++ tailWord_3556793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556793).length < 2 ^ (prefixWord ++ tailWord_3556793).sum := by decide
  have hdescent : baseEnd_3556793 < baseStart_3556793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556846 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_3556846 : Nat := 118140960795 + 3556846 * 2 ^ 59
def prefixEnd_3556846 : Nat := 4983230072969 + 3 ^ 40 * 3556846 * 2
def baseEnd_3556846 : Nat := 1826371612021896057367369

theorem tailTrace_3556846 : CollatzResearch.WordTrace tailWord_3556846 prefixEnd_3556846 1826371612021896057367369 := by
  unfold tailWord_3556846
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216103909020234722434299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86485887514774585186316261 16216103909020234722434299)
  ·
    refine ⟨24324155863530352083651449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16216103909020234722434299 24324155863530352083651449)
    ·
      refine ⟨18243116897647764062738587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24324155863530352083651449 18243116897647764062738587)
      ·
        refine ⟨27364675346471646094107881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18243116897647764062738587 27364675346471646094107881)
        ·
          refine ⟨20523506509853734570580911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27364675346471646094107881 20523506509853734570580911)
          ·
            refine ⟨30785259764780601855871367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20523506509853734570580911 30785259764780601855871367)
            ·
              refine ⟨46177889647170902783807051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30785259764780601855871367 46177889647170902783807051)
              ·
                refine ⟨69266834470756354175710577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46177889647170902783807051 69266834470756354175710577)
                ·
                  refine ⟨51950125853067265631782933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69266834470756354175710577 51950125853067265631782933)
                  ·
                    refine ⟨2435162149362528076489825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51950125853067265631782933 2435162149362528076489825)
                    ·
                      refine ⟨1826371612021896057367369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435162149362528076489825 1826371612021896057367369)
                      ·
                        rfl

theorem cell23_3556846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_3556846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556846 prefixEnd_3556846 := by exact prefixLift 3556846
  have htrace : WordTrace (prefixWord ++ tailWord_3556846) baseStart_3556846 baseEnd_3556846 := by
    simpa [prefixWord, tailWord_3556846, baseEnd_3556846] using wordTrace_append hprefix tailTrace_3556846
  have hstable : (prefixWord ++ tailWord_3556846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556846).length < 2 ^ (prefixWord ++ tailWord_3556846).sum := by decide
  have hdescent : baseEnd_3556846 < baseStart_3556846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556894 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3556894 : Nat := 118140960795 + 3556894 * 2 ^ 59
def prefixEnd_3556894 : Nat := 4983230072969 + 3 ^ 40 * 3556894 * 2
def baseEnd_3556894 : Nat := 608798753031103956522383

theorem tailTrace_3556894 : CollatzResearch.WordTrace tailWord_3556894 prefixEnd_3556894 608798753031103956522383 := by
  unfold tailWord_3556894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216322746998497747152717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86487054650658654651481157 16216322746998497747152717)
  ·
    refine ⟨6081121030124436655182269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16216322746998497747152717 6081121030124436655182269)
    ·
      refine ⟨2280420386296663745693351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6081121030124436655182269 2280420386296663745693351)
      ·
        refine ⟨3420630579444995618540027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280420386296663745693351 3420630579444995618540027)
        ·
          refine ⟨5130945869167493427810041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3420630579444995618540027 5130945869167493427810041)
          ·
            refine ⟨3848209401875620070857531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5130945869167493427810041 3848209401875620070857531)
            ·
              refine ⟨5772314102813430106286297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848209401875620070857531 5772314102813430106286297)
              ·
                refine ⟨4329235577110072579714723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5772314102813430106286297 4329235577110072579714723)
                ·
                  refine ⟨6493853365665108869572085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329235577110072579714723 6493853365665108869572085)
                  ·
                    refine ⟨608798753031103956522383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6493853365665108869572085 608798753031103956522383)
                    ·
                      rfl

theorem cell23_3556894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3556894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556894 prefixEnd_3556894 := by exact prefixLift 3556894
  have htrace : WordTrace (prefixWord ++ tailWord_3556894) baseStart_3556894 baseEnd_3556894 := by
    simpa [prefixWord, tailWord_3556894, baseEnd_3556894] using wordTrace_append hprefix tailTrace_3556894
  have hstable : (prefixWord ++ tailWord_3556894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556894).length < 2 ^ (prefixWord ++ tailWord_3556894).sum := by decide
  have hdescent : baseEnd_3556894 < baseStart_3556894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556946 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_3556946 : Nat := 118140960795 + 3556946 * 2 ^ 59
def prefixEnd_3556946 : Nat := 4983230072969 + 3 ^ 40 * 3556946 * 2
def baseEnd_3556946 : Nat := 608807653362448555372303

theorem tailTrace_3556946 : CollatzResearch.WordTrace tailWord_3556946 prefixEnd_3556946 608807653362448555372303 := by
  unfold tailWord_3556946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32433119642949898714528673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86488319047866396572076461 32433119642949898714528673)
  ·
    refine ⟨24324839732212424035896505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32433119642949898714528673 24324839732212424035896505)
    ·
      refine ⟨18243629799159318026922379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24324839732212424035896505 18243629799159318026922379)
      ·
        refine ⟨27365444698738977040383569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18243629799159318026922379 27365444698738977040383569)
        ·
          refine ⟨20524083524054232780287677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27365444698738977040383569 20524083524054232780287677)
          ·
            refine ⟨7696531321520337292607879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20524083524054232780287677 7696531321520337292607879)
            ·
              refine ⟨11544796982280505938911819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7696531321520337292607879 11544796982280505938911819)
              ·
                refine ⟨17317195473420758908367729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11544796982280505938911819 17317195473420758908367729)
                ·
                  refine ⟨12987896605065569181275797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17317195473420758908367729 12987896605065569181275797)
                  ·
                    refine ⟨608807653362448555372303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12987896605065569181275797 608807653362448555372303)
                    ·
                      rfl

theorem cell23_3556946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_3556946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556946 prefixEnd_3556946 := by exact prefixLift 3556946
  have htrace : WordTrace (prefixWord ++ tailWord_3556946) baseStart_3556946 baseEnd_3556946 := by
    simpa [prefixWord, tailWord_3556946, baseEnd_3556946] using wordTrace_append hprefix tailTrace_3556946
  have hstable : (prefixWord ++ tailWord_3556946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556946).length < 2 ^ (prefixWord ++ tailWord_3556946).sum := by decide
  have hdescent : baseEnd_3556946 < baseStart_3556946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556974 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_3556974 : Nat := 118140960795 + 3556974 * 2 ^ 59
def prefixEnd_3556974 : Nat := 4983230072969 + 3 ^ 40 * 3556974 * 2
def baseEnd_3556974 : Nat := 1826437337545671556566781

theorem tailTrace_3556974 : CollatzResearch.WordTrace tailWord_3556974 prefixEnd_3556974 1826437337545671556566781 := by
  unfold tailWord_3556974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216687476962269455016747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86488999877132103760089317 16216687476962269455016747)
  ·
    refine ⟨24325031215443404182525121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16216687476962269455016747 24325031215443404182525121)
    ·
      refine ⟨18243773411582553136893841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24325031215443404182525121 18243773411582553136893841)
      ·
        refine ⟨13682830058686914852670381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18243773411582553136893841 13682830058686914852670381)
        ·
          refine ⟨5131061272007593069751393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13682830058686914852670381 5131061272007593069751393)
          ·
            refine ⟨3848295954005694802313545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5131061272007593069751393 3848295954005694802313545)
            ·
              refine ⟨2886221965504271101735159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3848295954005694802313545 2886221965504271101735159)
              ·
                refine ⟨4329332948256406652602739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886221965504271101735159 4329332948256406652602739)
                ·
                  refine ⟨6493999422384609978904109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329332948256406652602739 6493999422384609978904109)
                  ·
                    refine ⟨2435249783394228742089041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6493999422384609978904109 2435249783394228742089041)
                    ·
                      refine ⟨1826437337545671556566781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435249783394228742089041 1826437337545671556566781)
                      ·
                        rfl

theorem cell23_3556974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_3556974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556974 prefixEnd_3556974 := by exact prefixLift 3556974
  have htrace : WordTrace (prefixWord ++ tailWord_3556974) baseStart_3556974 baseEnd_3556974 := by
    simpa [prefixWord, tailWord_3556974, baseEnd_3556974] using wordTrace_append hprefix tailTrace_3556974
  have hstable : (prefixWord ++ tailWord_3556974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556974).length < 2 ^ (prefixWord ++ tailWord_3556974).sum := by decide
  have hdescent : baseEnd_3556974 < baseStart_3556974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3556993 : List Nat := [1, 2, 4, 2, 1, 2, 2, 4, 5]
def baseStart_3556993 : Nat := 118140960795 + 3556993 * 2 ^ 59
def prefixEnd_3556993 : Nat := 4983230072969 + 3 ^ 40 * 3556993 * 2
def baseEnd_3556993 : Nat := 202938565964234109136577

theorem tailTrace_3556993 : CollatzResearch.WordTrace tailWord_3556993 prefixEnd_3556993 202938565964234109136577 := by
  unfold tailWord_3556993
  simp only [CollatzResearch.WordTrace]
  refine ⟨129734192802629321885075633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86489461868419547923383755 129734192802629321885075633)
  ·
    refine ⟨97300644601971991413806725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129734192802629321885075633 97300644601971991413806725)
    ·
      refine ⟨18243870862869748390088761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97300644601971991413806725 18243870862869748390088761)
      ·
        refine ⟨13682903147152311292566571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18243870862869748390088761 13682903147152311292566571)
        ·
          refine ⟨20524354720728466938849857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13682903147152311292566571 20524354720728466938849857)
          ·
            refine ⟨15393266040546350204137393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20524354720728466938849857 15393266040546350204137393)
            ·
              refine ⟨11544949530409762653103045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15393266040546350204137393 11544949530409762653103045)
              ·
                refine ⟨2164678036951830497456821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11544949530409762653103045 2164678036951830497456821)
                ·
                  refine ⟨202938565964234109136577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2164678036951830497456821 202938565964234109136577)
                  ·
                    rfl

theorem cell23_3556993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 5].length) (baseStart_3556993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3556993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3556993 prefixEnd_3556993 := by exact prefixLift 3556993
  have htrace : WordTrace (prefixWord ++ tailWord_3556993) baseStart_3556993 baseEnd_3556993 := by
    simpa [prefixWord, tailWord_3556993, baseEnd_3556993] using wordTrace_append hprefix tailTrace_3556993
  have hstable : (prefixWord ++ tailWord_3556993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3556993).length < 2 ^ (prefixWord ++ tailWord_3556993).sum := by decide
  have hdescent : baseEnd_3556993 < baseStart_3556993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3556993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557006 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_3557006 : Nat := 118140960795 + 3557006 * 2 ^ 59
def prefixEnd_3557006 : Nat := 4983230072969 + 3 ^ 40 * 3557006 * 2
def baseEnd_3557006 : Nat := 608817922975538477122211

theorem tailTrace_3557006 : CollatzResearch.WordTrace tailWord_3557006 prefixEnd_3557006 608817922975538477122211 := by
  unfold tailWord_3557006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216833368947778138162359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86489777967721483403532581 16216833368947778138162359)
  ·
    refine ⟨24325250053421667207243539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16216833368947778138162359 24325250053421667207243539)
    ·
      refine ⟨36487875080132500810865309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24325250053421667207243539 36487875080132500810865309)
      ·
        refine ⟨13682953155049687804074491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36487875080132500810865309 13682953155049687804074491)
        ·
          refine ⟨20524429732574531706111737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13682953155049687804074491 20524429732574531706111737)
          ·
            refine ⟨15393322299430898779583803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20524429732574531706111737 15393322299430898779583803)
            ·
              refine ⟨23089983449146348169375705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15393322299430898779583803 23089983449146348169375705)
              ·
                refine ⟨17317487586859761127031779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23089983449146348169375705 17317487586859761127031779)
                ·
                  refine ⟨25976231380289641690547669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17317487586859761127031779 25976231380289641690547669)
                  ·
                    refine ⟨608817922975538477122211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25976231380289641690547669 608817922975538477122211)
                    ·
                      rfl

theorem cell23_3557006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_3557006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557006 prefixEnd_3557006 := by exact prefixLift 3557006
  have htrace : WordTrace (prefixWord ++ tailWord_3557006) baseStart_3557006 baseEnd_3557006 := by
    simpa [prefixWord, tailWord_3557006, baseEnd_3557006] using wordTrace_append hprefix tailTrace_3557006
  have hstable : (prefixWord ++ tailWord_3557006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557006).length < 2 ^ (prefixWord ++ tailWord_3557006).sum := by decide
  have hdescent : baseEnd_3557006 < baseStart_3557006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557127 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3557127 : Nat := 118140960795 + 3557127 * 2 ^ 59
def prefixEnd_3557127 : Nat := 4983230072969 + 3 ^ 40 * 3557127 * 2
def baseEnd_3557127 : Nat := 1826515900085809457953577

theorem tailTrace_3557127 : CollatzResearch.WordTrace tailWord_3557127 prefixEnd_3557127 1826515900085809457953577 := by
  unfold tailWord_3557127
  simp only [CollatzResearch.WordTrace]
  refine ⟨129739080184143862770453635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86492720122762575180302423 129739080184143862770453635)
  ·
    refine ⟨194608620276215794155680453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129739080184143862770453635 194608620276215794155680453)
    ·
      refine ⟨36489116301790461404190085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194608620276215794155680453 36489116301790461404190085)
      ·
        refine ⟨6841709306585711513285641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36489116301790461404190085 6841709306585711513285641)
        ·
          refine ⟨5131281979939283634964231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6841709306585711513285641 5131281979939283634964231)
          ·
            refine ⟨7696922969908925452446347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131281979939283634964231 7696922969908925452446347)
            ·
              refine ⟨11545384454863388178669521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7696922969908925452446347 11545384454863388178669521)
              ·
                refine ⟨8659038341147541134002141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11545384454863388178669521 8659038341147541134002141)
                ·
                  refine ⟨3247139377930327925250803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8659038341147541134002141 3247139377930327925250803)
                  ·
                    refine ⟨4870709066895491887876205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3247139377930327925250803 4870709066895491887876205)
                    ·
                      refine ⟨1826515900085809457953577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4870709066895491887876205 1826515900085809457953577)
                      ·
                        rfl

theorem cell23_3557127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3557127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557127 prefixEnd_3557127 := by exact prefixLift 3557127
  have htrace : WordTrace (prefixWord ++ tailWord_3557127) baseStart_3557127 baseEnd_3557127 := by
    simpa [prefixWord, tailWord_3557127, baseEnd_3557127] using wordTrace_append hprefix tailTrace_3557127
  have hstable : (prefixWord ++ tailWord_3557127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557127).length < 2 ^ (prefixWord ++ tailWord_3557127).sum := by decide
  have hdescent : baseEnd_3557127 < baseStart_3557127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557143 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 1, 6]
def baseStart_3557143 : Nat := 118140960795 + 3557143 * 2 ^ 59
def prefixEnd_3557143 : Nat := 4983230072969 + 3 ^ 40 * 3557143 * 2
def baseEnd_3557143 : Nat := 608841371925427131784501

theorem tailTrace_3557143 : CollatzResearch.WordTrace tailWord_3557143 prefixEnd_3557143 608841371925427131784501 := by
  unfold tailWord_3557143
  simp only [CollatzResearch.WordTrace]
  refine ⟨129739663752085897503036083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86493109168057265002024055 129739663752085897503036083)
  ·
    refine ⟨194609495628128846254554125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129739663752085897503036083 194609495628128846254554125)
    ·
      refine ⟨72978560860548317345457797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194609495628128846254554125 72978560860548317345457797)
      ·
        refine ⟨13683480161352809502273337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72978560860548317345457797 13683480161352809502273337)
        ·
          refine ⟨10262610121014607126705003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13683480161352809502273337 10262610121014607126705003)
          ·
            refine ⟨15393915181521910690057505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10262610121014607126705003 15393915181521910690057505)
            ·
              refine ⟨11545436386141433017543129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15393915181521910690057505 11545436386141433017543129)
              ·
                refine ⟨8659077289606074763157347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11545436386141433017543129 8659077289606074763157347)
                ·
                  refine ⟨12988615934409112144736021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8659077289606074763157347 12988615934409112144736021)
                  ·
                    refine ⟨608841371925427131784501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12988615934409112144736021 608841371925427131784501)
                    ·
                      rfl

theorem cell23_3557143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_3557143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557143 prefixEnd_3557143 := by exact prefixLift 3557143
  have htrace : WordTrace (prefixWord ++ tailWord_3557143) baseStart_3557143 baseEnd_3557143 := by
    simpa [prefixWord, tailWord_3557143, baseEnd_3557143] using wordTrace_append hprefix tailTrace_3557143
  have hstable : (prefixWord ++ tailWord_3557143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557143).length < 2 ^ (prefixWord ++ tailWord_3557143).sum := by decide
  have hdescent : baseEnd_3557143 < baseStart_3557143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557160 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 4, 4]
def baseStart_3557160 : Nat := 118140960795 + 3557160 * 2 ^ 59
def prefixEnd_3557160 : Nat := 4983230072969 + 3 ^ 40 * 3557160 * 2
def baseEnd_3557160 : Nat := 608844281649135942946975

theorem tailTrace_3557160 : CollatzResearch.WordTrace tailWord_3557160 prefixEnd_3557160 608844281649135942946975 := by
  unfold tailWord_3557160
  simp only [CollatzResearch.WordTrace]
  refine ⟨64870141896512154703202467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86493522528682872937603289 64870141896512154703202467)
  ·
    refine ⟨97305212844768232054803701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64870141896512154703202467 97305212844768232054803701)
    ·
      refine ⟨9122363704197021755137847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97305212844768232054803701 9122363704197021755137847)
      ·
        refine ⟨13683545556295532632706771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9122363704197021755137847 13683545556295532632706771)
        ·
          refine ⟨20525318334443298949060157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13683545556295532632706771 20525318334443298949060157)
          ·
            refine ⟨7696994375416237105897559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20525318334443298949060157 7696994375416237105897559)
            ·
              refine ⟨11545491563124355658846339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7696994375416237105897559 11545491563124355658846339)
              ·
                refine ⟨17318237344686533488269509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11545491563124355658846339 17318237344686533488269509)
                ·
                  refine ⟨3247169502128725029050533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17318237344686533488269509 3247169502128725029050533)
                  ·
                    refine ⟨608844281649135942946975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3247169502128725029050533 608844281649135942946975)
                    ·
                      rfl

theorem cell23_3557160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_3557160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557160 prefixEnd_3557160 := by exact prefixLift 3557160
  have htrace : WordTrace (prefixWord ++ tailWord_3557160) baseStart_3557160 baseEnd_3557160 := by
    simpa [prefixWord, tailWord_3557160, baseEnd_3557160] using wordTrace_append hprefix tailTrace_3557160
  have hstable : (prefixWord ++ tailWord_3557160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557160).length < 2 ^ (prefixWord ++ tailWord_3557160).sum := by decide
  have hdescent : baseEnd_3557160 < baseStart_3557160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557177 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 1, 6]
def baseStart_3557177 : Nat := 118140960795 + 3557177 * 2 ^ 59
def prefixEnd_3557177 : Nat := 4983230072969 + 3 ^ 40 * 3557177 * 2
def baseEnd_3557177 : Nat := 608847191372844754109449

theorem tailTrace_3557177 : CollatzResearch.WordTrace tailWord_3557177 prefixEnd_3557177 608847191372844754109449 := by
  unfold tailWord_3557177
  simp only [CollatzResearch.WordTrace]
  refine ⟨129740903833962721309773785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86493935889308480873182523 129740903833962721309773785)
  ·
    refine ⟨97305677875472040982330339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129740903833962721309773785 97305677875472040982330339)
    ·
      refine ⟨145958516813208061473495509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97305677875472040982330339 145958516813208061473495509)
      ·
        refine ⟨3420902737809563940785051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 145958516813208061473495509 3420902737809563940785051)
        ·
          refine ⟨5131354106714345911177577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3420902737809563940785051 5131354106714345911177577)
          ·
            refine ⟨3848515580035759433383183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5131354106714345911177577 3848515580035759433383183)
            ·
              refine ⟨5772773370053639150074775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848515580035759433383183 5772773370053639150074775)
              ·
                refine ⟨8659160055080458725112163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772773370053639150074775 8659160055080458725112163)
                ·
                  refine ⟨12988740082620688087668245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8659160055080458725112163 12988740082620688087668245)
                  ·
                    refine ⟨608847191372844754109449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12988740082620688087668245 608847191372844754109449)
                    ·
                      rfl

theorem cell23_3557177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 6].length) (baseStart_3557177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557177 prefixEnd_3557177 := by exact prefixLift 3557177
  have htrace : WordTrace (prefixWord ++ tailWord_3557177) baseStart_3557177 baseEnd_3557177 := by
    simpa [prefixWord, tailWord_3557177, baseEnd_3557177] using wordTrace_append hprefix tailTrace_3557177
  have hstable : (prefixWord ++ tailWord_3557177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557177).length < 2 ^ (prefixWord ++ tailWord_3557177).sum := by decide
  have hdescent : baseEnd_3557177 < baseStart_3557177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557201 : List Nat := [1, 2, 2, 1, 5, 3, 1, 3, 1, 2, 2]
def baseStart_3557201 : Nat := 118140960795 + 3557201 * 2 ^ 59
def prefixEnd_3557201 : Nat := 4983230072969 + 3 ^ 40 * 3557201 * 2
def baseEnd_3557201 : Nat := 1826553897654242168428237

theorem tailTrace_3557201 : CollatzResearch.WordTrace tailWord_3557201 prefixEnd_3557201 1826553897654242168428237 := by
  unfold tailWord_3557201
  simp only [CollatzResearch.WordTrace]
  refine ⟨129741779185875773408647457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86494519457250515605764971 129741779185875773408647457)
  ·
    refine ⟨97306334389406830056485593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129741779185875773408647457 97306334389406830056485593)
    ·
      refine ⟨72979750792055122542364195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97306334389406830056485593 72979750792055122542364195)
      ·
        refine ⟨109469626188082683813546293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72979750792055122542364195 109469626188082683813546293)
        ·
          refine ⟨10262777455132751607519965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109469626188082683813546293 10262777455132751607519965)
          ·
            refine ⟨3848541545674781852819987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10262777455132751607519965 3848541545674781852819987)
            ·
              refine ⟨5772812318512172779229981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848541545674781852819987 5772812318512172779229981)
              ·
                refine ⟨2164804619442064792211243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5772812318512172779229981 2164804619442064792211243)
                ·
                  refine ⟨3247206929163097188316865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164804619442064792211243 3247206929163097188316865)
                  ·
                    refine ⟨2435405196872322891237649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3247206929163097188316865 2435405196872322891237649)
                    ·
                      refine ⟨1826553897654242168428237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435405196872322891237649 1826553897654242168428237)
                      ·
                        rfl

theorem cell23_3557201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 1, 2, 2].length) (baseStart_3557201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557201 prefixEnd_3557201 := by exact prefixLift 3557201
  have htrace : WordTrace (prefixWord ++ tailWord_3557201) baseStart_3557201 baseEnd_3557201 := by
    simpa [prefixWord, tailWord_3557201, baseEnd_3557201] using wordTrace_append hprefix tailTrace_3557201
  have hstable : (prefixWord ++ tailWord_3557201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557201).length < 2 ^ (prefixWord ++ tailWord_3557201).sum := by decide
  have hdescent : baseEnd_3557201 < baseStart_3557201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557218 : List Nat := [3, 3, 2, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_3557218 : Nat := 118140960795 + 3557218 * 2 ^ 59
def prefixEnd_3557218 : Nat := 4983230072969 + 3 ^ 40 * 3557218 * 2
def baseEnd_3557218 : Nat := 1826562626825368601915659

theorem tailTrace_3557218 : CollatzResearch.WordTrace tailWord_3557218 prefixEnd_3557218 1826562626825368601915659 := by
  unfold tailWord_3557218
  simp only [CollatzResearch.WordTrace]
  refine ⟨32435599806703546328004077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86494932817876123541344205 32435599806703546328004077)
  ·
    refine ⟨12163349927513829873001529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32435599806703546328004077 12163349927513829873001529)
    ·
      refine ⟨9122512445635372404751147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12163349927513829873001529 9122512445635372404751147)
      ·
        refine ⟨13683768668453058607126721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9122512445635372404751147 13683768668453058607126721)
        ·
          refine ⟨10262826501339793955345041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13683768668453058607126721 10262826501339793955345041)
          ·
            refine ⟨7697119876004845466508781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10262826501339793955345041 7697119876004845466508781)
            ·
              refine ⟨2886419953501817049940793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7697119876004845466508781 2886419953501817049940793)
              ·
                refine ⟨2164814965126362787455595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2886419953501817049940793 2164814965126362787455595)
                ·
                  refine ⟨3247222447689544181183393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164814965126362787455595 3247222447689544181183393)
                  ·
                    refine ⟨2435416835767158135887545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3247222447689544181183393 2435416835767158135887545)
                    ·
                      refine ⟨1826562626825368601915659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435416835767158135887545 1826562626825368601915659)
                      ·
                        rfl

theorem cell23_3557218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_3557218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557218 prefixEnd_3557218 := by exact prefixLift 3557218
  have htrace : WordTrace (prefixWord ++ tailWord_3557218) baseStart_3557218 baseEnd_3557218 := by
    simpa [prefixWord, tailWord_3557218, baseEnd_3557218] using wordTrace_append hprefix tailTrace_3557218
  have hstable : (prefixWord ++ tailWord_3557218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557218).length < 2 ^ (prefixWord ++ tailWord_3557218).sum := by decide
  have hdescent : baseEnd_3557218 < baseStart_3557218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557223 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_3557223 : Nat := 118140960795 + 3557223 * 2 ^ 59
def prefixEnd_3557223 : Nat := 4983230072969 + 3 ^ 40 * 3557223 * 2
def baseEnd_3557223 : Nat := 1826565194228641082353135

theorem tailTrace_3557223 : CollatzResearch.WordTrace tailWord_3557223 prefixEnd_3557223 1826565194228641082353135 := by
  unfold tailWord_3557223
  simp only [CollatzResearch.WordTrace]
  refine ⟨129742581591796071165948323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86495054394530714110632215 129742581591796071165948323)
  ·
    refine ⟨194613872387694106748922485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129742581591796071165948323 194613872387694106748922485)
    ·
      refine ⟨18245050536346322507711483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194613872387694106748922485 18245050536346322507711483)
      ·
        refine ⟨27367575804519483761567225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18245050536346322507711483 27367575804519483761567225)
        ·
          refine ⟨20525681853389612821175419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27367575804519483761567225 20525681853389612821175419)
          ·
            refine ⟨30788522780084419231763129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20525681853389612821175419 30788522780084419231763129)
            ·
              refine ⟨23091392085063314423822347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30788522780084419231763129 23091392085063314423822347)
              ·
                refine ⟨34637088127594971635733521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23091392085063314423822347 34637088127594971635733521)
                ·
                  refine ⟨25977816095696228726800141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34637088127594971635733521 25977816095696228726800141)
                  ·
                    refine ⟨9741681035886085772550053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25977816095696228726800141 9741681035886085772550053)
                    ·
                      refine ⟨1826565194228641082353135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9741681035886085772550053 1826565194228641082353135)
                      ·
                        rfl

theorem cell23_3557223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_3557223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557223 prefixEnd_3557223 := by exact prefixLift 3557223
  have htrace : WordTrace (prefixWord ++ tailWord_3557223) baseStart_3557223 baseEnd_3557223 := by
    simpa [prefixWord, tailWord_3557223, baseEnd_3557223] using wordTrace_append hprefix tailTrace_3557223
  have hstable : (prefixWord ++ tailWord_3557223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557223).length < 2 ^ (prefixWord ++ tailWord_3557223).sum := by decide
  have hdescent : baseEnd_3557223 < baseStart_3557223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557274 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2]
def baseStart_3557274 : Nat := 118140960795 + 3557274 * 2 ^ 59
def prefixEnd_3557274 : Nat := 4983230072969 + 3 ^ 40 * 3557274 * 2
def baseEnd_3557274 : Nat := 1826591381742020382815401

theorem tailTrace_3557274 : CollatzResearch.WordTrace tailWord_3557274 prefixEnd_3557274 1826591381742020382815401 := by
  unfold tailWord_3557274
  simp only [CollatzResearch.WordTrace]
  refine ⟨32436110428652826719013719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86496294476407537917369917 32436110428652826719013719)
  ·
    refine ⟨48654165642979240078520579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32436110428652826719013719 48654165642979240078520579)
    ·
      refine ⟨72981248464468860117780869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48654165642979240078520579 72981248464468860117780869)
      ·
        refine ⟨13683984087087911272083913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72981248464468860117780869 13683984087087911272083913)
        ·
          refine ⟨10262988065315933454062935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13683984087087911272083913 10262988065315933454062935)
          ·
            refine ⟨15394482097973900181094403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10262988065315933454062935 15394482097973900181094403)
            ·
              refine ⟨23091723146960850271641605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15394482097973900181094403 23091723146960850271641605)
              ·
                refine ⟨4329698090055159425932801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23091723146960850271641605 4329698090055159425932801)
                ·
                  refine ⟨3247273567541369569449601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4329698090055159425932801 3247273567541369569449601)
                  ·
                    refine ⟨2435455175656027177087201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3247273567541369569449601 2435455175656027177087201)
                    ·
                      refine ⟨1826591381742020382815401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435455175656027177087201 1826591381742020382815401)
                      ·
                        rfl

theorem cell23_3557274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_3557274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557274 prefixEnd_3557274 := by exact prefixLift 3557274
  have htrace : WordTrace (prefixWord ++ tailWord_3557274) baseStart_3557274 baseEnd_3557274 := by
    simpa [prefixWord, tailWord_3557274, baseEnd_3557274] using wordTrace_append hprefix tailTrace_3557274
  have hstable : (prefixWord ++ tailWord_3557274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557274).length < 2 ^ (prefixWord ++ tailWord_3557274).sum := by decide
  have hdescent : baseEnd_3557274 < baseStart_3557274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557310 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_3557310 : Nat := 118140960795 + 3557310 * 2 ^ 59
def prefixEnd_3557310 : Nat := 4983230072969 + 3 ^ 40 * 3557310 * 2
def baseEnd_3557310 : Nat := 608869955681860747321745

theorem tailTrace_3557310 : CollatzResearch.WordTrace tailWord_3557310 prefixEnd_3557310 608869955681860747321745 := by
  unfold tailWord_3557310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218219342810110628045673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86497169828320590016243589 16218219342810110628045673)
  ·
    refine ⟨12163664507107582971034255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16218219342810110628045673 12163664507107582971034255)
    ·
      refine ⟨18245496760661374456551383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12163664507107582971034255 18245496760661374456551383)
      ·
        refine ⟨27368245140992061684827075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18245496760661374456551383 27368245140992061684827075)
        ·
          refine ⟨41052367711488092527240613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27368245140992061684827075 41052367711488092527240613)
          ·
            refine ⟨7697318945904017348857615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41052367711488092527240613 7697318945904017348857615)
            ·
              refine ⟨11545978418856026023286423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7697318945904017348857615 11545978418856026023286423)
              ·
                refine ⟨17318967628284039034929635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11545978418856026023286423 17318967628284039034929635)
                ·
                  refine ⟨25978451442426058552394453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17318967628284039034929635 25978451442426058552394453)
                  ·
                    refine ⟨608869955681860747321745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25978451442426058552394453 608869955681860747321745)
                    ·
                      rfl

theorem cell23_3557310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_3557310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557310 prefixEnd_3557310 := by exact prefixLift 3557310
  have htrace : WordTrace (prefixWord ++ tailWord_3557310) baseStart_3557310 baseEnd_3557310 := by
    simpa [prefixWord, tailWord_3557310, baseEnd_3557310] using wordTrace_append hprefix tailTrace_3557310
  have hstable : (prefixWord ++ tailWord_3557310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557310).length < 2 ^ (prefixWord ++ tailWord_3557310).sum := by decide
  have hdescent : baseEnd_3557310 < baseStart_3557310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557347 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 2, 4, 2]
def baseStart_3557347 : Nat := 118140960795 + 3557347 * 2 ^ 59
def prefixEnd_3557347 : Nat := 4983230072969 + 3 ^ 40 * 3557347 * 2
def baseEnd_3557347 : Nat := 1826628865829798597202565

theorem tailTrace_3557347 : CollatzResearch.WordTrace tailWord_3557347 prefixEnd_3557347 1826628865829798597202565 := by
  unfold tailWord_3557347
  simp only [CollatzResearch.WordTrace]
  refine ⟨129747104243346840343462295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86498069495564560228974863 129747104243346840343462295)
  ·
    refine ⟨194620656365020260515193443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129747104243346840343462295 194620656365020260515193443)
    ·
      refine ⟨291930984547530390772790165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194620656365020260515193443 291930984547530390772790165)
      ·
        refine ⟨13684264900665487067474539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 291930984547530390772790165 13684264900665487067474539)
        ·
          refine ⟨20526397350998230601211809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13684264900665487067474539 20526397350998230601211809)
          ·
            refine ⟨15394798013248672950908857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20526397350998230601211809 15394798013248672950908857)
            ·
              refine ⟨11546098509936504713181643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15394798013248672950908857 11546098509936504713181643)
              ·
                refine ⟨17319147764904757069772465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11546098509936504713181643 17319147764904757069772465)
                ·
                  refine ⟨12989360823678567802329349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17319147764904757069772465 12989360823678567802329349)
                  ·
                    refine ⟨2435505154439731462936753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12989360823678567802329349 2435505154439731462936753)
                    ·
                      refine ⟨1826628865829798597202565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435505154439731462936753 1826628865829798597202565)
                      ·
                        rfl

theorem cell23_3557347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_3557347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557347 prefixEnd_3557347 := by exact prefixLift 3557347
  have htrace : WordTrace (prefixWord ++ tailWord_3557347) baseStart_3557347 baseEnd_3557347 := by
    simpa [prefixWord, tailWord_3557347, baseEnd_3557347] using wordTrace_append hprefix tailTrace_3557347
  have hstable : (prefixWord ++ tailWord_3557347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557347).length < 2 ^ (prefixWord ++ tailWord_3557347).sum := by decide
  have hdescent : baseEnd_3557347 < baseStart_3557347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557393 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_3557393 : Nat := 118140960795 + 3557393 * 2 ^ 59
def prefixEnd_3557393 : Nat := 4983230072969 + 3 ^ 40 * 3557393 * 2
def baseEnd_3557393 : Nat := 1826652485939905417227353

theorem tailTrace_3557393 : CollatzResearch.WordTrace tailWord_3557393 prefixEnd_3557393 1826652485939905417227353 := by
  unfold tailWord_3557393
  simp only [CollatzResearch.WordTrace]
  refine ⟨129748782001180190199636833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86499188000786793466424555 129748782001180190199636833)
  ·
    refine ⟨97311586500885142649727625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129748782001180190199636833 97311586500885142649727625)
    ·
      refine ⟨72983689875663856987295719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97311586500885142649727625 72983689875663856987295719)
      ·
        refine ⟨109475534813495785480943579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72983689875663856987295719 109475534813495785480943579)
        ·
          refine ⟨164213302220243678221415369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109475534813495785480943579 164213302220243678221415369)
          ·
            refine ⟨123159976665182758666061527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164213302220243678221415369 123159976665182758666061527)
            ·
              refine ⟨184739964997774137999092291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123159976665182758666061527 184739964997774137999092291)
              ·
                refine ⟨277109947496661206998638437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184739964997774137999092291 277109947496661206998638437)
                ·
                  refine ⟨51958115155623976312244707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277109947496661206998638437 51958115155623976312244707)
                  ·
                    refine ⟨77937172733435964468367061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51958115155623976312244707 77937172733435964468367061)
                    ·
                      refine ⟨1826652485939905417227353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77937172733435964468367061 1826652485939905417227353)
                      ·
                        rfl

theorem cell23_3557393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_3557393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557393 prefixEnd_3557393 := by exact prefixLift 3557393
  have htrace : WordTrace (prefixWord ++ tailWord_3557393) baseStart_3557393 baseEnd_3557393 := by
    simpa [prefixWord, tailWord_3557393, baseEnd_3557393] using wordTrace_append hprefix tailTrace_3557393
  have hstable : (prefixWord ++ tailWord_3557393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557393).length < 2 ^ (prefixWord ++ tailWord_3557393).sum := by decide
  have hdescent : baseEnd_3557393 < baseStart_3557393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557400 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 3, 5]
def baseStart_3557400 : Nat := 118140960795 + 3557400 * 2 ^ 59
def prefixEnd_3557400 : Nat := 4983230072969 + 3 ^ 40 * 3557400 * 2
def baseEnd_3557400 : Nat := 608885360101495629946607

theorem tailTrace_3557400 : CollatzResearch.WordTrace tailWord_3557400 prefixEnd_3557400 608885360101495629946607 := by
  unfold tailWord_3557400
  simp only [CollatzResearch.WordTrace]
  refine ⟨64874518656077415197570827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86499358208103220263427769 64874518656077415197570827)
  ·
    refine ⟨97311777984116122796356241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64874518656077415197570827 97311777984116122796356241)
    ·
      refine ⟨72983833488087092097267181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97311777984116122796356241 72983833488087092097267181)
      ·
        refine ⟨27368937558032659536475193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72983833488087092097267181 27368937558032659536475193)
        ·
          refine ⟨20526703168524494652356395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27368937558032659536475193 20526703168524494652356395)
          ·
            refine ⟨30790054752786741978534593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20526703168524494652356395 30790054752786741978534593)
            ·
              refine ⟨23092541064590056483900945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30790054752786741978534593 23092541064590056483900945)
              ·
                refine ⟨17319405798442542362925709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23092541064590056483900945 17319405798442542362925709)
                ·
                  refine ⟨6494777174415953386097141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17319405798442542362925709 6494777174415953386097141)
                  ·
                    refine ⟨608885360101495629946607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6494777174415953386097141 608885360101495629946607)
                    ·
                      rfl

theorem cell23_3557400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_3557400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557400 prefixEnd_3557400 := by exact prefixLift 3557400
  have htrace : WordTrace (prefixWord ++ tailWord_3557400) baseStart_3557400 baseEnd_3557400 := by
    simpa [prefixWord, tailWord_3557400, baseEnd_3557400] using wordTrace_append hprefix tailTrace_3557400
  have hstable : (prefixWord ++ tailWord_3557400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557400).length < 2 ^ (prefixWord ++ tailWord_3557400).sum := by decide
  have hdescent : baseEnd_3557400 < baseStart_3557400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557404 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 6]
def baseStart_3557404 : Nat := 118140960795 + 3557404 * 2 ^ 59
def prefixEnd_3557404 : Nat := 4983230072969 + 3 ^ 40 * 3557404 * 2
def baseEnd_3557404 : Nat := 202962014914122763798867

theorem tailTrace_3557404 : CollatzResearch.WordTrace tailWord_3557404 prefixEnd_3557404 202962014914122763798867 := by
  unfold tailWord_3557404
  simp only [CollatzResearch.WordTrace]
  refine ⟨64874591602070169539143633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86499455469426892718858177 64874591602070169539143633)
  ·
    refine ⟨48655943701552627154357725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64874591602070169539143633 48655943701552627154357725)
    ·
      refine ⟨18245978888082235182884147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48655943701552627154357725 18245978888082235182884147)
      ·
        refine ⟨27368968332123352774326221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18245978888082235182884147 27368968332123352774326221)
        ·
          refine ⟨10263363124546257290372333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27368968332123352774326221 10263363124546257290372333)
          ·
            refine ⟨3848761171704846483889625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10263363124546257290372333 3848761171704846483889625)
            ·
              refine ⟨2886570878778634862917219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3848761171704846483889625 2886570878778634862917219)
              ·
                refine ⟨4329856318167952294375829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886570878778634862917219 4329856318167952294375829)
                ·
                  refine ⟨202962014914122763798867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4329856318167952294375829 202962014914122763798867)
                  ·
                    rfl

theorem cell23_3557404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_3557404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557404 prefixEnd_3557404 := by exact prefixLift 3557404
  have htrace : WordTrace (prefixWord ++ tailWord_3557404) baseStart_3557404 baseEnd_3557404 := by
    simpa [prefixWord, tailWord_3557404, baseEnd_3557404] using wordTrace_append hprefix tailTrace_3557404
  have hstable : (prefixWord ++ tailWord_3557404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557404).length < 2 ^ (prefixWord ++ tailWord_3557404).sum := by decide
  have hdescent : baseEnd_3557404 < baseStart_3557404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557407 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 4, 3, 2]
def baseStart_3557407 : Nat := 118140960795 + 3557407 * 2 ^ 59
def prefixEnd_3557407 : Nat := 4983230072969 + 3 ^ 40 * 3557407 * 2
def baseEnd_3557407 : Nat := 1826659674669068362452289

theorem tailTrace_3557407 : CollatzResearch.WordTrace tailWord_3557407 prefixEnd_3557407 1826659674669068362452289 := by
  unfold tailWord_3557407
  simp only [CollatzResearch.WordTrace]
  refine ⟨129749292623129470590646475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86499528415419647060430983 129749292623129470590646475)
  ·
    refine ⟨194623938934694205885969713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129749292623129470590646475 194623938934694205885969713)
    ·
      refine ⟨145967954201020654414477285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194623938934694205885969713 145967954201020654414477285)
      ·
        refine ⟨27368991412691372702714491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145967954201020654414477285 27368991412691372702714491)
        ·
          refine ⟨41053487119037059054071737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27368991412691372702714491 41053487119037059054071737)
          ·
            refine ⟨30790115339277794290553803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41053487119037059054071737 30790115339277794290553803)
            ·
              refine ⟨46185173008916691435830705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30790115339277794290553803 46185173008916691435830705)
              ·
                refine ⟨34638879756687518576873029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46185173008916691435830705 34638879756687518576873029)
                ·
                  refine ⟨6494789954378909733163693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34638879756687518576873029 6494789954378909733163693)
                  ·
                    refine ⟨2435546232892091149936385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6494789954378909733163693 2435546232892091149936385)
                    ·
                      refine ⟨1826659674669068362452289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435546232892091149936385 1826659674669068362452289)
                      ·
                        rfl

theorem cell23_3557407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_3557407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557407 prefixEnd_3557407 := by exact prefixLift 3557407
  have htrace : WordTrace (prefixWord ++ tailWord_3557407) baseStart_3557407 baseEnd_3557407 := by
    simpa [prefixWord, tailWord_3557407, baseEnd_3557407] using wordTrace_append hprefix tailTrace_3557407
  have hstable : (prefixWord ++ tailWord_3557407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557407).length < 2 ^ (prefixWord ++ tailWord_3557407).sum := by decide
  have hdescent : baseEnd_3557407 < baseStart_3557407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557424 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 2, 3, 2]
def baseStart_3557424 : Nat := 118140960795 + 3557424 * 2 ^ 59
def prefixEnd_3557424 : Nat := 4983230072969 + 3 ^ 40 * 3557424 * 2
def baseEnd_3557424 : Nat := 1826668403840194795939711

theorem tailTrace_3557424 : CollatzResearch.WordTrace tailWord_3557424 prefixEnd_3557424 1826668403840194795939711 := by
  unfold tailWord_3557424
  simp only [CollatzResearch.WordTrace]
  refine ⟨64874956332033941247007663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86499941776045254996010217 64874956332033941247007663)
  ·
    refine ⟨97312434498050911870511495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64874956332033941247007663 97312434498050911870511495)
    ·
      refine ⟨145968651747076367805767243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97312434498050911870511495 145968651747076367805767243)
      ·
        refine ⟨218952977620614551708650865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145968651747076367805767243 218952977620614551708650865)
        ·
          refine ⟨164214733215460913781488149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218952977620614551708650865 164214733215460913781488149)
          ·
            refine ⟨7697565619474730333507257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164214733215460913781488149 7697565619474730333507257)
            ·
              refine ⟨5773174214606047750130443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7697565619474730333507257 5773174214606047750130443)
              ·
                refine ⟨8659761321909071625195665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5773174214606047750130443 8659761321909071625195665)
                ·
                  refine ⟨6494820991431803718896749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8659761321909071625195665 6494820991431803718896749)
                  ·
                    refine ⟨2435557871786926394586281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6494820991431803718896749 2435557871786926394586281)
                    ·
                      refine ⟨1826668403840194795939711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435557871786926394586281 1826668403840194795939711)
                      ·
                        rfl

theorem cell23_3557424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 3, 2].length) (baseStart_3557424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557424 prefixEnd_3557424 := by exact prefixLift 3557424
  have htrace : WordTrace (prefixWord ++ tailWord_3557424) baseStart_3557424 baseEnd_3557424 := by
    simpa [prefixWord, tailWord_3557424, baseEnd_3557424] using wordTrace_append hprefix tailTrace_3557424
  have hstable : (prefixWord ++ tailWord_3557424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557424).length < 2 ^ (prefixWord ++ tailWord_3557424).sum := by decide
  have hdescent : baseEnd_3557424 < baseStart_3557424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557450 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_3557450 : Nat := 118140960795 + 3557450 * 2 ^ 59
def prefixEnd_3557450 : Nat := 4983230072969 + 3 ^ 40 * 3557450 * 2
def baseEnd_3557450 : Nat := 1826681754337211694214591

theorem tailTrace_3557450 : CollatzResearch.WordTrace tailWord_3557450 prefixEnd_3557450 1826681754337211694214591 := by
  unfold tailWord_3557450
  simp only [CollatzResearch.WordTrace]
  refine ⟨32437715240493422233615451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86500573974649125956307869 32437715240493422233615451)
  ·
    refine ⟨48656572860740133350423177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32437715240493422233615451 48656572860740133350423177)
    ·
      refine ⟨36492429645555100012817383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48656572860740133350423177 36492429645555100012817383)
      ·
        refine ⟨54738644468332650019226075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36492429645555100012817383 54738644468332650019226075)
        ·
          refine ⟨82107966702498975028839113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54738644468332650019226075 82107966702498975028839113)
          ·
            refine ⟨61580975026874231271629335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82107966702498975028839113 61580975026874231271629335)
            ·
              refine ⟨92371462540311346907444003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61580975026874231271629335 92371462540311346907444003)
              ·
                refine ⟨138557193810467020361166005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92371462540311346907444003 138557193810467020361166005)
                ·
                  refine ⟨12989736919731283158859313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138557193810467020361166005 12989736919731283158859313)
                  ·
                    refine ⟨9742302689798462369144485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12989736919731283158859313 9742302689798462369144485)
                    ·
                      refine ⟨1826681754337211694214591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9742302689798462369144485 1826681754337211694214591)
                      ·
                        rfl

theorem cell23_3557450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_3557450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557450 prefixEnd_3557450 := by exact prefixLift 3557450
  have htrace : WordTrace (prefixWord ++ tailWord_3557450) baseStart_3557450 baseEnd_3557450 := by
    simpa [prefixWord, tailWord_3557450, baseEnd_3557450] using wordTrace_append hprefix tailTrace_3557450
  have hstable : (prefixWord ++ tailWord_3557450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557450).length < 2 ^ (prefixWord ++ tailWord_3557450).sum := by decide
  have hdescent : baseEnd_3557450 < baseStart_3557450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557477 : List Nat := [1, 3, 1, 3, 2, 3, 3, 7]
def baseStart_3557477 : Nat := 118140960795 + 3557477 * 2 ^ 59
def prefixEnd_3557477 : Nat := 4983230072969 + 3 ^ 40 * 3557477 * 2
def baseEnd_3557477 : Nat := 67655393270921595873221

theorem tailTrace_3557477 : CollatzResearch.WordTrace tailWord_3557477 prefixEnd_3557477 67655393270921595873221 := by
  unfold tailWord_3557477
  simp only [CollatzResearch.WordTrace]
  refine ⟨129751845732875872545694685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86501230488583915030463123 129751845732875872545694685)
  ·
    refine ⟨48656942149828452204635507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129751845732875872545694685 48656942149828452204635507)
    ·
      refine ⟨72985413224742678306953261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48656942149828452204635507 72985413224742678306953261)
      ·
        refine ⟨27369529959278504365107473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72985413224742678306953261 27369529959278504365107473)
        ·
          refine ⟨20527147469458878273830605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27369529959278504365107473 20527147469458878273830605)
          ·
            refine ⟨7697680301047079352686477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20527147469458878273830605 7697680301047079352686477)
            ·
              refine ⟨2886630112892654757257429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7697680301047079352686477 2886630112892654757257429)
              ·
                refine ⟨67655393270921595873221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2886630112892654757257429 67655393270921595873221)
                ·
                  rfl

theorem cell23_3557477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 7].length) (baseStart_3557477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557477 prefixEnd_3557477 := by exact prefixLift 3557477
  have htrace : WordTrace (prefixWord ++ tailWord_3557477) baseStart_3557477 baseEnd_3557477 := by
    simpa [prefixWord, tailWord_3557477, baseEnd_3557477] using wordTrace_append hprefix tailTrace_3557477
  have hstable : (prefixWord ++ tailWord_3557477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557477).length < 2 ^ (prefixWord ++ tailWord_3557477).sum := by decide
  have hdescent : baseEnd_3557477 < baseStart_3557477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557487 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 3]
def baseStart_3557487 : Nat := 118140960795 + 3557487 * 2 ^ 59
def prefixEnd_3557487 : Nat := 4983230072969 + 3 ^ 40 * 3557487 * 2
def baseEnd_3557487 : Nat := 1826700753121428049451921

theorem tailTrace_3557487 : CollatzResearch.WordTrace tailWord_3557487 prefixEnd_3557487 1826700753121428049451921 := by
  unfold tailWord_3557487
  simp only [CollatzResearch.WordTrace]
  refine ⟨129752210462839644253558715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86501473641893096169039143 129752210462839644253558715)
  ·
    refine ⟨194628315694259466380338073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129752210462839644253558715 194628315694259466380338073)
    ·
      refine ⟨145971236770694599785253555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194628315694259466380338073 145971236770694599785253555)
      ·
        refine ⟨218956855156041899677880333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145971236770694599785253555 218956855156041899677880333)
        ·
          refine ⟨82108820683515712379205125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218956855156041899677880333 82108820683515712379205125)
          ·
            refine ⟨15395403878159196071100961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82108820683515712379205125 15395403878159196071100961)
            ·
              refine ⟨11546552908619397053325721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15395403878159196071100961 11546552908619397053325721)
              ·
                refine ⟨8659914681464547789994291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11546552908619397053325721 8659914681464547789994291)
                ·
                  refine ⟨12989872022196821684991437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8659914681464547789994291 12989872022196821684991437)
                  ·
                    refine ⟨4871202008323808131871789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12989872022196821684991437 4871202008323808131871789)
                    ·
                      refine ⟨1826700753121428049451921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4871202008323808131871789 1826700753121428049451921)
                      ·
                        rfl

theorem cell23_3557487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 3].length) (baseStart_3557487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557487 prefixEnd_3557487 := by exact prefixLift 3557487
  have htrace : WordTrace (prefixWord ++ tailWord_3557487) baseStart_3557487 baseEnd_3557487 := by
    simpa [prefixWord, tailWord_3557487, baseEnd_3557487] using wordTrace_append hprefix tailTrace_3557487
  have hstable : (prefixWord ++ tailWord_3557487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557487).length < 2 ^ (prefixWord ++ tailWord_3557487).sum := by decide
  have hdescent : baseEnd_3557487 < baseStart_3557487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557488 : List Nat := [2, 1, 1, 1, 5, 3, 2, 3, 1, 2, 2]
def baseStart_3557488 : Nat := 118140960795 + 3557488 * 2 ^ 59
def prefixEnd_3557488 : Nat := 4983230072969 + 3 ^ 40 * 3557488 * 2
def baseEnd_3557488 : Nat := 1826701266602082545539417

theorem tailTrace_3557488 : CollatzResearch.WordTrace tailWord_3557488 prefixEnd_3557488 1826701266602082545539417 := by
  unfold tailWord_3557488
  simp only [CollatzResearch.WordTrace]
  refine ⟨64876123467918010712172559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86501497957224014282896745 64876123467918010712172559)
  ·
    refine ⟨97314185201877016068258839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64876123467918010712172559 97314185201877016068258839)
    ·
      refine ⟨145971277802815524102388259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97314185201877016068258839 145971277802815524102388259)
      ·
        refine ⟨218956916704223286153582389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145971277802815524102388259 218956916704223286153582389)
        ·
          refine ⟨20527210941020933076898349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218956916704223286153582389 20527210941020933076898349)
          ·
            refine ⟨7697704102882849903836881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20527210941020933076898349 7697704102882849903836881)
            ·
              refine ⟨5773278077162137427877661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7697704102882849903836881 5773278077162137427877661)
              ·
                refine ⟨2164979278935801535454123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5773278077162137427877661 2164979278935801535454123)
                ·
                  refine ⟨3247468918403702303181185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164979278935801535454123 3247468918403702303181185)
                  ·
                    refine ⟨2435601688802776727385889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3247468918403702303181185 2435601688802776727385889)
                    ·
                      refine ⟨1826701266602082545539417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435601688802776727385889 1826701266602082545539417)
                      ·
                        rfl

theorem cell23_3557488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 1, 2, 2].length) (baseStart_3557488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557488 prefixEnd_3557488 := by exact prefixLift 3557488
  have htrace : WordTrace (prefixWord ++ tailWord_3557488) baseStart_3557488 baseEnd_3557488 := by
    simpa [prefixWord, tailWord_3557488, baseEnd_3557488] using wordTrace_append hprefix tailTrace_3557488
  have hstable : (prefixWord ++ tailWord_3557488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557488).length < 2 ^ (prefixWord ++ tailWord_3557488).sum := by decide
  have hdescent : baseEnd_3557488 < baseStart_3557488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557520 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 2, 6]
def baseStart_3557520 : Nat := 118140960795 + 3557520 * 2 ^ 59
def prefixEnd_3557520 : Nat := 4983230072969 + 3 ^ 40 * 3557520 * 2
def baseEnd_3557520 : Nat := 608905899327675473446423

theorem tailTrace_3557520 : CollatzResearch.WordTrace tailWord_3557520 prefixEnd_3557520 608905899327675473446423 := by
  unfold tailWord_3557520
  simp only [CollatzResearch.WordTrace]
  refine ⟨64876707035860045444755007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86502276047813393926340009 64876707035860045444755007)
  ·
    refine ⟨97315060553790068167132511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64876707035860045444755007 97315060553790068167132511)
    ·
      refine ⟨145972590830685102250698767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97315060553790068167132511 145972590830685102250698767)
      ·
        refine ⟨218958886246027653376048151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145972590830685102250698767 218958886246027653376048151)
        ·
          refine ⟨328438329369041480064072227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218958886246027653376048151 328438329369041480064072227)
          ·
            refine ⟨492657494053562220096108341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328438329369041480064072227 492657494053562220096108341)
            ·
              refine ⟨46186640067521458134010157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 492657494053562220096108341 46186640067521458134010157)
              ·
                refine ⟨17319990025320546800253809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46186640067521458134010157 17319990025320546800253809)
                ·
                  refine ⟨12989992518990410100190357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17319990025320546800253809 12989992518990410100190357)
                  ·
                    refine ⟨608905899327675473446423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12989992518990410100190357 608905899327675473446423)
                    ·
                      rfl

theorem cell23_3557520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_3557520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557520 prefixEnd_3557520 := by exact prefixLift 3557520
  have htrace : WordTrace (prefixWord ++ tailWord_3557520) baseStart_3557520 baseEnd_3557520 := by
    simpa [prefixWord, tailWord_3557520, baseEnd_3557520] using wordTrace_append hprefix tailTrace_3557520
  have hstable : (prefixWord ++ tailWord_3557520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557520).length < 2 ^ (prefixWord ++ tailWord_3557520).sum := by decide
  have hdescent : baseEnd_3557520 < baseStart_3557520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557556 : List Nat := [2, 5, 3, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3557556 : Nat := 118140960795 + 3557556 * 2 ^ 59
def prefixEnd_3557556 : Nat := 4983230072969 + 3 ^ 40 * 3557556 * 2
def baseEnd_3557556 : Nat := 1826736183286588279489105

theorem tailTrace_3557556 : CollatzResearch.WordTrace tailWord_3557556 prefixEnd_3557556 1826736183286588279489105 := by
  unfold tailWord_3557556
  simp only [CollatzResearch.WordTrace]
  refine ⟨64877363549794834518910261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86503151399726446025213681 64877363549794834518910261)
  ·
    refine ⟨6082252832793265736147837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64877363549794834518910261 6082252832793265736147837)
    ·
      refine ⟨2280844812297474651055439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6082252832793265736147837 2280844812297474651055439)
      ·
        refine ⟨3421267218446211976583159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280844812297474651055439 3421267218446211976583159)
        ·
          refine ⟨5131900827669317964874739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421267218446211976583159 5131900827669317964874739)
          ·
            refine ⟨7697851241503976947312109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131900827669317964874739 7697851241503976947312109)
            ·
              refine ⟨2886694215563991355242041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7697851241503976947312109 2886694215563991355242041)
              ·
                refine ⟨2165020661672993516431531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2886694215563991355242041 2165020661672993516431531)
                ·
                  refine ⟨3247530992509490274647297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165020661672993516431531 3247530992509490274647297)
                  ·
                    refine ⟨2435648244382117705985473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3247530992509490274647297 2435648244382117705985473)
                    ·
                      refine ⟨1826736183286588279489105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435648244382117705985473 1826736183286588279489105)
                      ·
                        rfl

theorem cell23_3557556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3557556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557556 prefixEnd_3557556 := by exact prefixLift 3557556
  have htrace : WordTrace (prefixWord ++ tailWord_3557556) baseStart_3557556 baseEnd_3557556 := by
    simpa [prefixWord, tailWord_3557556, baseEnd_3557556] using wordTrace_append hprefix tailTrace_3557556
  have hstable : (prefixWord ++ tailWord_3557556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557556).length < 2 ^ (prefixWord ++ tailWord_3557556).sum := by decide
  have hdescent : baseEnd_3557556 < baseStart_3557556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557560 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_3557560 : Nat := 118140960795 + 3557560 * 2 ^ 59
def prefixEnd_3557560 : Nat := 4983230072969 + 3 ^ 40 * 3557560 * 2
def baseEnd_3557560 : Nat := 1826738237209206263839085

theorem tailTrace_3557560 : CollatzResearch.WordTrace tailWord_3557560 prefixEnd_3557560 1826738237209206263839085 := by
  unfold tailWord_3557560
  simp only [CollatzResearch.WordTrace]
  refine ⟨64877436495787588860483067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86503248661050118480644089 64877436495787588860483067)
  ·
    refine ⟨97316154743681383290724601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64877436495787588860483067 97316154743681383290724601)
    ·
      refine ⟨72987116057761037468043451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97316154743681383290724601 72987116057761037468043451)
      ·
        refine ⟨109480674086641556202065177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72987116057761037468043451 109480674086641556202065177)
        ·
          refine ⟨82110505564981167151548883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109480674086641556202065177 82110505564981167151548883)
          ·
            refine ⟨123165758347471750727323325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82110505564981167151548883 123165758347471750727323325)
            ·
              refine ⟨46187159380301906522746247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123165758347471750727323325 46187159380301906522746247)
              ·
                refine ⟨69280739070452859784119371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46187159380301906522746247 69280739070452859784119371)
                ·
                  refine ⟨103921108605679289676179057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69280739070452859784119371 103921108605679289676179057)
                  ·
                    refine ⟨77940831454259467257134293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103921108605679289676179057 77940831454259467257134293)
                    ·
                      refine ⟨1826738237209206263839085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77940831454259467257134293 1826738237209206263839085)
                      ·
                        rfl

theorem cell23_3557560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_3557560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557560 prefixEnd_3557560 := by exact prefixLift 3557560
  have htrace : WordTrace (prefixWord ++ tailWord_3557560) baseStart_3557560 baseEnd_3557560 := by
    simpa [prefixWord, tailWord_3557560, baseEnd_3557560] using wordTrace_append hprefix tailTrace_3557560
  have hstable : (prefixWord ++ tailWord_3557560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557560).length < 2 ^ (prefixWord ++ tailWord_3557560).sum := by decide
  have hdescent : baseEnd_3557560 < baseStart_3557560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557561 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 2, 2, 2]
def baseStart_3557561 : Nat := 118140960795 + 3557561 * 2 ^ 59
def prefixEnd_3557561 : Nat := 4983230072969 + 3 ^ 40 * 3557561 * 2
def baseEnd_3557561 : Nat := 1826738750689860759926581

theorem tailTrace_3557561 : CollatzResearch.WordTrace tailWord_3557561 prefixEnd_3557561 1826738750689860759926581 := by
  unfold tailWord_3557561
  simp only [CollatzResearch.WordTrace]
  refine ⟨129754909464571554891752537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86503272976381036594501691 129754909464571554891752537)
  ·
    refine ⟨97316182098428666168814403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129754909464571554891752537 97316182098428666168814403)
    ·
      refine ⟨145974273147642999253221605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97316182098428666168814403 145974273147642999253221605)
      ·
        refine ⟨27370176215183062359979051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145974273147642999253221605 27370176215183062359979051)
        ·
          refine ⟨41055264322774593539968577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27370176215183062359979051 41055264322774593539968577)
          ·
            refine ⟨30791448242080945154976433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41055264322774593539968577 30791448242080945154976433)
            ·
              refine ⟨23093586181560708866232325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30791448242080945154976433 23093586181560708866232325)
              ·
                refine ⟨4330047409042632912418561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23093586181560708866232325 4330047409042632912418561)
                ·
                  refine ⟨3247535556781974684313921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4330047409042632912418561 3247535556781974684313921)
                  ·
                    refine ⟨2435651667586481013235441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3247535556781974684313921 2435651667586481013235441)
                    ·
                      refine ⟨1826738750689860759926581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435651667586481013235441 1826738750689860759926581)
                      ·
                        rfl

theorem cell23_3557561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_3557561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557561 prefixEnd_3557561 := by exact prefixLift 3557561
  have htrace : WordTrace (prefixWord ++ tailWord_3557561) baseStart_3557561 baseEnd_3557561 := by
    simpa [prefixWord, tailWord_3557561, baseEnd_3557561] using wordTrace_append hprefix tailTrace_3557561
  have hstable : (prefixWord ++ tailWord_3557561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557561).length < 2 ^ (prefixWord ++ tailWord_3557561).sum := by decide
  have hdescent : baseEnd_3557561 < baseStart_3557561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557618 : List Nat := [3, 2, 1, 3, 2, 3, 2, 2, 5]
def baseStart_3557618 : Nat := 118140960795 + 3557618 * 2 ^ 59
def prefixEnd_3557618 : Nat := 4983230072969 + 3 ^ 40 * 3557618 * 2
def baseEnd_3557618 : Nat := 202974224343018559657091

theorem tailTrace_3557618 : CollatzResearch.WordTrace tailWord_3557618 prefixEnd_3557618 202974224343018559657091 := by
  unfold tailWord_3557618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32439247106341263406644377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86504658950243369084385005 32439247106341263406644377)
  ·
    refine ⟨24329435329755947554983283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32439247106341263406644377 24329435329755947554983283)
    ·
      refine ⟨36494152994633921332474925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24329435329755947554983283 36494152994633921332474925)
      ·
        refine ⟨13685307372987720499678097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36494152994633921332474925 13685307372987720499678097)
        ·
          refine ⟨10263980529740790374758573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13685307372987720499678097 10263980529740790374758573)
          ·
            refine ⟨3848992698652796390534465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10263980529740790374758573 3848992698652796390534465)
            ·
              refine ⟨2886744523989597292900849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3848992698652796390534465 2886744523989597292900849)
              ·
                refine ⟨2165058392992197969675637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2886744523989597292900849 2165058392992197969675637)
                ·
                  refine ⟨202974224343018559657091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2165058392992197969675637 202974224343018559657091)
                  ·
                    rfl

theorem cell23_3557618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_3557618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557618 prefixEnd_3557618 := by exact prefixLift 3557618
  have htrace : WordTrace (prefixWord ++ tailWord_3557618) baseStart_3557618 baseEnd_3557618 := by
    simpa [prefixWord, tailWord_3557618, baseEnd_3557618] using wordTrace_append hprefix tailTrace_3557618
  have hstable : (prefixWord ++ tailWord_3557618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557618).length < 2 ^ (prefixWord ++ tailWord_3557618).sum := by decide
  have hdescent : baseEnd_3557618 < baseStart_3557618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557627 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 9, 4]
def baseStart_3557627 : Nat := 118140960795 + 3557627 * 2 ^ 59
def prefixEnd_3557627 : Nat := 4983230072969 + 3 ^ 40 * 3557627 * 2
def baseEnd_3557627 : Nat := 608924213471019167233759

theorem tailTrace_3557627 : CollatzResearch.WordTrace tailWord_3557627 prefixEnd_3557627 608924213471019167233759 := by
  unfold tailWord_3557627
  simp only [CollatzResearch.WordTrace]
  refine ⟨129757316682332448163655135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86504877788221632109103423 129757316682332448163655135)
  ·
    refine ⟨194635975023498672245482703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129757316682332448163655135 194635975023498672245482703)
    ·
      refine ⟨291953962535248008368224055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194635975023498672245482703 291953962535248008368224055)
      ·
        refine ⟨437930943802872012552336083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291953962535248008368224055 437930943802872012552336083)
        ·
          refine ⟨656896415704308018828504125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437930943802872012552336083 656896415704308018828504125)
          ·
            refine ⟨246336155889115507060689047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 656896415704308018828504125 246336155889115507060689047)
            ·
              refine ⟨369504233833673260591033571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246336155889115507060689047 369504233833673260591033571)
              ·
                refine ⟨554256350750509890886550357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369504233833673260591033571 554256350750509890886550357)
                ·
                  refine ⟨3247595805178768891913381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 554256350750509890886550357 3247595805178768891913381)
                  ·
                    refine ⟨608924213471019167233759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3247595805178768891913381 608924213471019167233759)
                    ·
                      rfl

theorem cell23_3557627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 4].length) (baseStart_3557627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557627 prefixEnd_3557627 := by exact prefixLift 3557627
  have htrace : WordTrace (prefixWord ++ tailWord_3557627) baseStart_3557627 baseEnd_3557627 := by
    simpa [prefixWord, tailWord_3557627, baseEnd_3557627] using wordTrace_append hprefix tailTrace_3557627
  have hstable : (prefixWord ++ tailWord_3557627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557627).length < 2 ^ (prefixWord ++ tailWord_3557627).sum := by decide
  have hdescent : baseEnd_3557627 < baseStart_3557627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557644 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_3557644 : Nat := 118140960795 + 3557644 * 2 ^ 59
def prefixEnd_3557644 : Nat := 4983230072969 + 3 ^ 40 * 3557644 * 2
def baseEnd_3557644 : Nat := 608927123194727978396233

theorem tailTrace_3557644 : CollatzResearch.WordTrace tailWord_3557644 prefixEnd_3557644 608927123194727978396233 := by
  unfold tailWord_3557644
  simp only [CollatzResearch.WordTrace]
  refine ⟨64878968361635430033511993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86505291148847240044682657 64878968361635430033511993)
  ·
    refine ⟨48659226271226572525133995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64878968361635430033511993 48659226271226572525133995)
    ·
      refine ⟨72988839406839858787700993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48659226271226572525133995 72988839406839858787700993)
      ·
        refine ⟨54741629555129894090775745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72988839406839858787700993 54741629555129894090775745)
        ·
          refine ⟨41056222166347420568081809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54741629555129894090775745 41056222166347420568081809)
          ·
            refine ⟨30792166624760565426061357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41056222166347420568081809 30792166624760565426061357)
            ·
              refine ⟨11547062484285212034773009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30792166624760565426061357 11547062484285212034773009)
              ·
                refine ⟨8660296863213909026079757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11547062484285212034773009 8660296863213909026079757)
                ·
                  refine ⟨3247611323705215884779909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8660296863213909026079757 3247611323705215884779909)
                  ·
                    refine ⟨608927123194727978396233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3247611323705215884779909 608927123194727978396233)
                    ·
                      rfl

theorem cell23_3557644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_3557644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557644 prefixEnd_3557644 := by exact prefixLift 3557644
  have htrace : WordTrace (prefixWord ++ tailWord_3557644) baseStart_3557644 baseEnd_3557644 := by
    simpa [prefixWord, tailWord_3557644, baseEnd_3557644] using wordTrace_append hprefix tailTrace_3557644
  have hstable : (prefixWord ++ tailWord_3557644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557644).length < 2 ^ (prefixWord ++ tailWord_3557644).sum := by decide
  have hdescent : baseEnd_3557644 < baseStart_3557644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557687 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 5, 5]
def baseStart_3557687 : Nat := 118140960795 + 3557687 * 2 ^ 59
def prefixEnd_3557687 : Nat := 4983230072969 + 3 ^ 40 * 3557687 * 2
def baseEnd_3557687 : Nat := 608934483084109088983667

theorem tailTrace_3557687 : CollatzResearch.WordTrace tailWord_3557687 prefixEnd_3557687 608934483084109088983667 := by
  unfold tailWord_3557687
  simp only [CollatzResearch.WordTrace]
  refine ⟨129759505062115078410839315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86506336708076718940559543 129759505062115078410839315)
  ·
    refine ⟨194639257593172617616258973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129759505062115078410839315 194639257593172617616258973)
    ·
      refine ⟨72989721597439731606097115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194639257593172617616258973 72989721597439731606097115)
      ·
        refine ⟨109484582396159597409145673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72989721597439731606097115 109484582396159597409145673)
        ·
          refine ⟨82113436797119698056859255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109484582396159597409145673 82113436797119698056859255)
          ·
            refine ⟨123170155195679547085288883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82113436797119698056859255 123170155195679547085288883)
            ·
              refine ⟨184755232793519320627933325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123170155195679547085288883 184755232793519320627933325)
              ·
                refine ⟨69283212297569745235474997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184755232793519320627933325 69283212297569745235474997)
                ·
                  refine ⟨6495301152897163615825781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69283212297569745235474997 6495301152897163615825781)
                  ·
                    refine ⟨608934483084109088983667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6495301152897163615825781 608934483084109088983667)
                    ·
                      rfl

theorem cell23_3557687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_3557687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557687 prefixEnd_3557687 := by exact prefixLift 3557687
  have htrace : WordTrace (prefixWord ++ tailWord_3557687) baseStart_3557687 baseEnd_3557687 := by
    simpa [prefixWord, tailWord_3557687, baseEnd_3557687] using wordTrace_append hprefix tailTrace_3557687
  have hstable : (prefixWord ++ tailWord_3557687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557687).length < 2 ^ (prefixWord ++ tailWord_3557687).sum := by decide
  have hdescent : baseEnd_3557687 < baseStart_3557687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557704 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 1, 5]
def baseStart_3557704 : Nat := 118140960795 + 3557704 * 2 ^ 59
def prefixEnd_3557704 : Nat := 4983230072969 + 3 ^ 40 * 3557704 * 2
def baseEnd_3557704 : Nat := 608937392807817900146141

theorem tailTrace_3557704 : CollatzResearch.WordTrace tailWord_3557704 prefixEnd_3557704 608937392807817900146141 := by
  unfold tailWord_3557704
  simp only [CollatzResearch.WordTrace]
  refine ⟨64880062551526745157104083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86506750068702326876138777 64880062551526745157104083)
  ·
    refine ⟨97320093827290117735656125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64880062551526745157104083 97320093827290117735656125)
    ·
      refine ⟨36495035185233794150871047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97320093827290117735656125 36495035185233794150871047)
      ·
        refine ⟨54742552777850691226306571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36495035185233794150871047 54742552777850691226306571)
        ·
          refine ⟨82113829166776036839459857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54742552777850691226306571 82113829166776036839459857)
          ·
            refine ⟨61585371875082027629594893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82113829166776036839459857 61585371875082027629594893)
            ·
              refine ⟨23094514453155760361098085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61585371875082027629594893 23094514453155760361098085)
              ·
                refine ⟨4330221459966705067705891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23094514453155760361098085 4330221459966705067705891)
                ·
                  refine ⟨6495332189950057601558837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330221459966705067705891 6495332189950057601558837)
                  ·
                    refine ⟨608937392807817900146141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6495332189950057601558837 608937392807817900146141)
                    ·
                      rfl

theorem cell23_3557704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_3557704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557704 prefixEnd_3557704 := by exact prefixLift 3557704
  have htrace : WordTrace (prefixWord ++ tailWord_3557704) baseStart_3557704 baseEnd_3557704 := by
    simpa [prefixWord, tailWord_3557704, baseEnd_3557704] using wordTrace_append hprefix tailTrace_3557704
  have hstable : (prefixWord ++ tailWord_3557704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557704).length < 2 ^ (prefixWord ++ tailWord_3557704).sum := by decide
  have hdescent : baseEnd_3557704 < baseStart_3557704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557728 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 2, 3, 2]
def baseStart_3557728 : Nat := 118140960795 + 3557728 * 2 ^ 59
def prefixEnd_3557728 : Nat := 4983230072969 + 3 ^ 40 * 3557728 * 2
def baseEnd_3557728 : Nat := 1826824501959161606538313

theorem tailTrace_3557728 : CollatzResearch.WordTrace tailWord_3557728 prefixEnd_3557728 1826824501959161606538313 := by
  unfold tailWord_3557728
  simp only [CollatzResearch.WordTrace]
  refine ⟨64880500227483271206540919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86507333636644361608721225 64880500227483271206540919)
  ·
    refine ⟨97320750341224906809811379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64880500227483271206540919 97320750341224906809811379)
    ·
      refine ⟨145981125511837360214717069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97320750341224906809811379 145981125511837360214717069)
      ·
        refine ⟨54742922066939010080518901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145981125511837360214717069 54742922066939010080518901)
        ·
          refine ⟨5132148943775532195048647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54742922066939010080518901 5132148943775532195048647)
          ·
            refine ⟨7698223415663298292572971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132148943775532195048647 7698223415663298292572971)
            ·
              refine ⟨11547335123494947438859457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7698223415663298292572971 11547335123494947438859457)
              ·
                refine ⟨8660501342621210579144593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11547335123494947438859457 8660501342621210579144593)
                ·
                  refine ⟨6495376006965907934358445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8660501342621210579144593 6495376006965907934358445)
                  ·
                    refine ⟨2435766002612215475384417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6495376006965907934358445 2435766002612215475384417)
                    ·
                      refine ⟨1826824501959161606538313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435766002612215475384417 1826824501959161606538313)
                      ·
                        rfl

theorem cell23_3557728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_3557728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557728 prefixEnd_3557728 := by exact prefixLift 3557728
  have htrace : WordTrace (prefixWord ++ tailWord_3557728) baseStart_3557728 baseEnd_3557728 := by
    simpa [prefixWord, tailWord_3557728, baseEnd_3557728] using wordTrace_append hprefix tailTrace_3557728
  have hstable : (prefixWord ++ tailWord_3557728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557728).length < 2 ^ (prefixWord ++ tailWord_3557728).sum := by decide
  have hdescent : baseEnd_3557728 < baseStart_3557728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557737 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_3557737 : Nat := 118140960795 + 3557737 * 2 ^ 59
def prefixEnd_3557737 : Nat := 4983230072969 + 3 ^ 40 * 3557737 * 2
def baseEnd_3557737 : Nat := 1826829123285052071325771

theorem tailTrace_3557737 : CollatzResearch.WordTrace tailWord_3557737 prefixEnd_3557737 1826829123285052071325771 := by
  unfold tailWord_3557737
  simp only [CollatzResearch.WordTrace]
  refine ⟨129761328711933936950159465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86507552474622624633439643 129761328711933936950159465)
  ·
    refine ⟨97320996533950452712619599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129761328711933936950159465 97320996533950452712619599)
    ·
      refine ⟨145981494800925679068929399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97320996533950452712619599 145981494800925679068929399)
      ·
        refine ⟨218972242201388518603394099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145981494800925679068929399 218972242201388518603394099)
        ·
          refine ⟨328458363302082777905091149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218972242201388518603394099 328458363302082777905091149)
          ·
            refine ⟨123171886238281041714409181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328458363302082777905091149 123171886238281041714409181)
            ·
              refine ⟨46189457339355390642903443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123171886238281041714409181 46189457339355390642903443)
              ·
                refine ⟨69284186009033085964355165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46189457339355390642903443 69284186009033085964355165)
                ·
                  refine ⟨25981569753387407236633187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69284186009033085964355165 25981569753387407236633187)
                  ·
                    refine ⟨38972354630081110854949781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25981569753387407236633187 38972354630081110854949781)
                    ·
                      refine ⟨1826829123285052071325771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38972354630081110854949781 1826829123285052071325771)
                      ·
                        rfl

theorem cell23_3557737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_3557737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557737 prefixEnd_3557737 := by exact prefixLift 3557737
  have htrace : WordTrace (prefixWord ++ tailWord_3557737) baseStart_3557737 baseEnd_3557737 := by
    simpa [prefixWord, tailWord_3557737, baseEnd_3557737] using wordTrace_append hprefix tailTrace_3557737
  have hstable : (prefixWord ++ tailWord_3557737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557737).length < 2 ^ (prefixWord ++ tailWord_3557737).sum := by decide
  have hdescent : baseEnd_3557737 < baseStart_3557737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557744 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 5]
def baseStart_3557744 : Nat := 118140960795 + 3557744 * 2 ^ 59
def prefixEnd_3557744 : Nat := 4983230072969 + 3 ^ 40 * 3557744 * 2
def baseEnd_3557744 : Nat := 1826832717649633543938239

theorem tailTrace_3557744 : CollatzResearch.WordTrace tailWord_3557744 prefixEnd_3557744 1826832717649633543938239 := by
  unfold tailWord_3557744
  simp only [CollatzResearch.WordTrace]
  refine ⟨64880792011454288572832143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86507722681939051430442857 64880792011454288572832143)
  ·
    refine ⟨97321188017181432859248215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64880792011454288572832143 97321188017181432859248215)
    ·
      refine ⟨145981782025772149288872323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97321188017181432859248215 145981782025772149288872323)
      ·
        refine ⟨218972673038658223933308485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145981782025772149288872323 218972673038658223933308485)
        ·
          refine ⟨41057376194748416987495341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218972673038658223933308485 41057376194748416987495341)
          ·
            refine ⟨15396516073030656370310753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41057376194748416987495341 15396516073030656370310753)
            ·
              refine ⟨11547387054772992277733065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15396516073030656370310753 11547387054772992277733065)
              ·
                refine ⟨8660540291079744208299799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11547387054772992277733065 8660540291079744208299799)
                ·
                  refine ⟨12990810436619616312449699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8660540291079744208299799 12990810436619616312449699)
                  ·
                    refine ⟨19486215654929424468674549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12990810436619616312449699 19486215654929424468674549)
                    ·
                      refine ⟨1826832717649633543938239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19486215654929424468674549 1826832717649633543938239)
                      ·
                        rfl

theorem cell23_3557744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_3557744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557744 prefixEnd_3557744 := by exact prefixLift 3557744
  have htrace : WordTrace (prefixWord ++ tailWord_3557744) baseStart_3557744 baseEnd_3557744 := by
    simpa [prefixWord, tailWord_3557744, baseEnd_3557744] using wordTrace_append hprefix tailTrace_3557744
  have hstable : (prefixWord ++ tailWord_3557744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557744).length < 2 ^ (prefixWord ++ tailWord_3557744).sum := by decide
  have hdescent : baseEnd_3557744 < baseStart_3557744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557762 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_3557762 : Nat := 118140960795 + 3557762 * 2 ^ 59
def prefixEnd_3557762 : Nat := 4983230072969 + 3 ^ 40 * 3557762 * 2
def baseEnd_3557762 : Nat := 1826841960301414473513157

theorem tailTrace_3557762 : CollatzResearch.WordTrace tailWord_3557762 prefixEnd_3557762 1826841960301414473513157 := by
  unfold tailWord_3557762
  simp only [CollatzResearch.WordTrace]
  refine ⟨32440560134210841554954885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86508160357895577479879693 32440560134210841554954885)
  ·
    refine ⟨6082605025164532791554041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32440560134210841554954885 6082605025164532791554041)
    ·
      refine ⟨4561953768873399593665531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6082605025164532791554041 4561953768873399593665531)
      ·
        refine ⟨6842930653310099390498297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4561953768873399593665531 6842930653310099390498297)
        ·
          refine ⟨5132197989982574542873723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6842930653310099390498297 5132197989982574542873723)
          ·
            refine ⟨7698296984973861814310585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132197989982574542873723 7698296984973861814310585)
            ·
              refine ⟨5773722738730396360732939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7698296984973861814310585 5773722738730396360732939)
              ·
                refine ⟨8660584108095594541099409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5773722738730396360732939 8660584108095594541099409)
                ·
                  refine ⟨6495438081071695905824557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8660584108095594541099409 6495438081071695905824557)
                  ·
                    refine ⟨2435789280401885964684209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6495438081071695905824557 2435789280401885964684209)
                    ·
                      refine ⟨1826841960301414473513157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435789280401885964684209 1826841960301414473513157)
                      ·
                        rfl

theorem cell23_3557762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_3557762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557762 prefixEnd_3557762 := by exact prefixLift 3557762
  have htrace : WordTrace (prefixWord ++ tailWord_3557762) baseStart_3557762 baseEnd_3557762 := by
    simpa [prefixWord, tailWord_3557762, baseEnd_3557762] using wordTrace_append hprefix tailTrace_3557762
  have hstable : (prefixWord ++ tailWord_3557762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557762).length < 2 ^ (prefixWord ++ tailWord_3557762).sum := by decide
  have hdescent : baseEnd_3557762 < baseStart_3557762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557777 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 3, 9]
def baseStart_3557777 : Nat := 118140960795 + 3557777 * 2 ^ 59
def prefixEnd_3557777 : Nat := 4983230072969 + 3 ^ 40 * 3557777 * 2
def baseEnd_3557777 : Nat := 608949887503743971608529

theorem tailTrace_3557777 : CollatzResearch.WordTrace tailWord_3557777 prefixEnd_3557777 608949887503743971608529 := by
  unfold tailWord_3557777
  simp only [CollatzResearch.WordTrace]
  refine ⟨129762787631789023781615585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86508525087859349187743723 129762787631789023781615585)
  ·
    refine ⟨97322090723841767836211689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129762787631789023781615585 97322090723841767836211689)
    ·
      refine ⟨72991568042881325877158767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97322090723841767836211689 72991568042881325877158767)
      ·
        refine ⟨109487352064321988815738151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72991568042881325877158767 109487352064321988815738151)
        ·
          refine ⟨164231028096482983223607227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109487352064321988815738151 164231028096482983223607227)
          ·
            refine ⟨246346542144724474835410841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164231028096482983223607227 246346542144724474835410841)
            ·
              refine ⟨184759906608543356126558131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246346542144724474835410841 184759906608543356126558131)
              ·
                refine ⟨277139859912815034189837197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184759906608543356126558131 277139859912815034189837197)
                ·
                  refine ⟨103927447467305637821188949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277139859912815034189837197 103927447467305637821188949)
                  ·
                    refine ⟨608949887503743971608529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 103927447467305637821188949 608949887503743971608529)
                    ·
                      rfl

theorem cell23_3557777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_3557777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557777 prefixEnd_3557777 := by exact prefixLift 3557777
  have htrace : WordTrace (prefixWord ++ tailWord_3557777) baseStart_3557777 baseEnd_3557777 := by
    simpa [prefixWord, tailWord_3557777, baseEnd_3557777] using wordTrace_append hprefix tailTrace_3557777
  have hstable : (prefixWord ++ tailWord_3557777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557777).length < 2 ^ (prefixWord ++ tailWord_3557777).sum := by decide
  have hdescent : baseEnd_3557777 < baseStart_3557777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557792 : List Nat := [2, 1, 1, 4, 1, 3, 4, 2, 1, 2, 2]
def baseStart_3557792 : Nat := 118140960795 + 3557792 * 2 ^ 59
def prefixEnd_3557792 : Nat := 4983230072969 + 3 ^ 40 * 3557792 * 2
def baseEnd_3557792 : Nat := 1826857364721049356138019

theorem tailTrace_3557792 : CollatzResearch.WordTrace tailWord_3557792 prefixEnd_3557792 1826857364721049356138019 := by
  unfold tailWord_3557792
  simp only [CollatzResearch.WordTrace]
  refine ⟨64881667363367340671705815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86508889817823120895607753 64881667363367340671705815)
  ·
    refine ⟨97322501045051011007558723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64881667363367340671705815 97322501045051011007558723)
    ·
      refine ⟨145983751567576516511338085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97322501045051011007558723 145983751567576516511338085)
      ·
        refine ⟨27371953418920596845875891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145983751567576516511338085 27371953418920596845875891)
        ·
          refine ⟨41057930128380895268813837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27371953418920596845875891 41057930128380895268813837)
          ·
            refine ⟨15396723798142835725805189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41057930128380895268813837 15396723798142835725805189)
            ·
              refine ⟨2886885712151781698588473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15396723798142835725805189 2886885712151781698588473)
              ·
                refine ⟨2165164284113836273941355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2886885712151781698588473 2165164284113836273941355)
                ·
                  refine ⟨3247746426170754410912033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165164284113836273941355 3247746426170754410912033)
                  ·
                    refine ⟨2435809819628065808184025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3247746426170754410912033 2435809819628065808184025)
                    ·
                      refine ⟨1826857364721049356138019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2435809819628065808184025 1826857364721049356138019)
                      ·
                        rfl

theorem cell23_3557792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_3557792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557792 prefixEnd_3557792 := by exact prefixLift 3557792
  have htrace : WordTrace (prefixWord ++ tailWord_3557792) baseStart_3557792 baseEnd_3557792 := by
    simpa [prefixWord, tailWord_3557792, baseEnd_3557792] using wordTrace_append hprefix tailTrace_3557792
  have hstable : (prefixWord ++ tailWord_3557792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557792).length < 2 ^ (prefixWord ++ tailWord_3557792).sum := by decide
  have hdescent : baseEnd_3557792 < baseStart_3557792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557794 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3557794 : Nat := 118140960795 + 3557794 * 2 ^ 59
def prefixEnd_3557794 : Nat := 4983230072969 + 3 ^ 40 * 3557794 * 2
def baseEnd_3557794 : Nat := 608952797227452782771003

theorem tailTrace_3557794 : CollatzResearch.WordTrace tailWord_3557794 prefixEnd_3557794 608952797227452782771003 := by
  unfold tailWord_3557794
  simp only [CollatzResearch.WordTrace]
  refine ⟨32440851918181858921246109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86508938448484957123322957 32440851918181858921246109)
  ·
    refine ⟨12165319469318197095467291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32440851918181858921246109 12165319469318197095467291)
    ·
      refine ⟨18247979203977295643200937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12165319469318197095467291 18247979203977295643200937)
      ·
        refine ⟨13685984402982971732400703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18247979203977295643200937 13685984402982971732400703)
        ·
          refine ⟨20528976604474457598601055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13685984402982971732400703 20528976604474457598601055)
          ·
            refine ⟨30793464906711686397901583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20528976604474457598601055 30793464906711686397901583)
            ·
              refine ⟨46190197360067529596852375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30793464906711686397901583 46190197360067529596852375)
              ·
                refine ⟨69285296040101294395278563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46190197360067529596852375 69285296040101294395278563)
                ·
                  refine ⟨103927944060151941592917845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69285296040101294395278563 103927944060151941592917845)
                  ·
                    refine ⟨608952797227452782771003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 103927944060151941592917845 608952797227452782771003)
                    ·
                      rfl

theorem cell23_3557794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3557794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557794 prefixEnd_3557794 := by exact prefixLift 3557794
  have htrace : WordTrace (prefixWord ++ tailWord_3557794) baseStart_3557794 baseEnd_3557794 := by
    simpa [prefixWord, tailWord_3557794, baseEnd_3557794] using wordTrace_append hprefix tailTrace_3557794
  have hstable : (prefixWord ++ tailWord_3557794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557794).length < 2 ^ (prefixWord ++ tailWord_3557794).sum := by decide
  have hdescent : baseEnd_3557794 < baseStart_3557794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557834 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_3557834 : Nat := 118140960795 + 3557834 * 2 ^ 59
def prefixEnd_3557834 : Nat := 4983230072969 + 3 ^ 40 * 3557834 * 2
def baseEnd_3557834 : Nat := 1826878930908538191812825

theorem tailTrace_3557834 : CollatzResearch.WordTrace tailWord_3557834 prefixEnd_3557834 1826878930908538191812825 := by
  unfold tailWord_3557834
  simp only [CollatzResearch.WordTrace]
  refine ⟨32441216648145630629110139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86509911061721681677627037 32441216648145630629110139)
  ·
    refine ⟨48661824972218445943665209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32441216648145630629110139 48661824972218445943665209)
    ·
      refine ⟨36496368729163834457748907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48661824972218445943665209 36496368729163834457748907)
      ·
        refine ⟨54744553093745751686623361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36496368729163834457748907 54744553093745751686623361)
        ·
          refine ⟨41058414820309313764967521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54744553093745751686623361 41058414820309313764967521)
          ·
            refine ⟨30793811115231985323725641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41058414820309313764967521 30793811115231985323725641)
            ·
              refine ⟨23095358336423988992794231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30793811115231985323725641 23095358336423988992794231)
              ·
                refine ⟨34643037504635983489191347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23095358336423988992794231 34643037504635983489191347)
                ·
                  refine ⟨51964556256953975233787021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34643037504635983489191347 51964556256953975233787021)
                  ·
                    refine ⟨19486708596357740712670133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51964556256953975233787021 19486708596357740712670133)
                    ·
                      refine ⟨1826878930908538191812825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19486708596357740712670133 1826878930908538191812825)
                      ·
                        rfl

theorem cell23_3557834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_3557834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557834 prefixEnd_3557834 := by exact prefixLift 3557834
  have htrace : WordTrace (prefixWord ++ tailWord_3557834) baseStart_3557834 baseEnd_3557834 := by
    simpa [prefixWord, tailWord_3557834, baseEnd_3557834] using wordTrace_append hprefix tailTrace_3557834
  have hstable : (prefixWord ++ tailWord_3557834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557834).length < 2 ^ (prefixWord ++ tailWord_3557834).sum := by decide
  have hdescent : baseEnd_3557834 < baseStart_3557834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557921 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3557921 : Nat := 118140960795 + 3557921 * 2 ^ 59
def prefixEnd_3557921 : Nat := 4983230072969 + 3 ^ 40 * 3557921 * 2
def baseEnd_3557921 : Nat := 1826923603725479351424925

theorem tailTrace_3557921 : CollatzResearch.WordTrace tailWord_3557921 prefixEnd_3557921 1826923603725479351424925 := by
  unfold tailWord_3557921
  simp only [CollatzResearch.WordTrace]
  refine ⟨129768039743267336374857617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86512026495511557583238411 129768039743267336374857617)
  ·
    refine ⟨97326029807450502281143213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129768039743267336374857617 97326029807450502281143213)
    ·
      refine ⟨36497261177793938355428705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97326029807450502281143213 36497261177793938355428705)
      ·
        refine ⟨27372945883345453766571529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36497261177793938355428705 27372945883345453766571529)
        ·
          refine ⟨20529709412509090324928647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27372945883345453766571529 20529709412509090324928647)
          ·
            refine ⟨30794564118763635487392971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20529709412509090324928647 30794564118763635487392971)
            ·
              refine ⟨46191846178145453231089457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30794564118763635487392971 46191846178145453231089457)
              ·
                refine ⟨34643884633609089923317093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46191846178145453231089457 34643884633609089923317093)
                ·
                  refine ⟨6495728368801704360621955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34643884633609089923317093 6495728368801704360621955)
                  ·
                    refine ⟨9743592553202556540932933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6495728368801704360621955 9743592553202556540932933)
                    ·
                      refine ⟨1826923603725479351424925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9743592553202556540932933 1826923603725479351424925)
                      ·
                        rfl

theorem cell23_3557921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3557921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557921 prefixEnd_3557921 := by exact prefixLift 3557921
  have htrace : WordTrace (prefixWord ++ tailWord_3557921) baseStart_3557921 baseEnd_3557921 := by
    simpa [prefixWord, tailWord_3557921, baseEnd_3557921] using wordTrace_append hprefix tailTrace_3557921
  have hstable : (prefixWord ++ tailWord_3557921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557921).length < 2 ^ (prefixWord ++ tailWord_3557921).sum := by decide
  have hdescent : baseEnd_3557921 < baseStart_3557921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557931 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 3, 4]
def baseStart_3557931 : Nat := 118140960795 + 3557931 * 2 ^ 59
def prefixEnd_3557931 : Nat := 4983230072969 + 3 ^ 40 * 3557931 * 2
def baseEnd_3557931 : Nat := 608976246177341437433293

theorem tailTrace_3557931 : CollatzResearch.WordTrace tailWord_3557931 prefixEnd_3557931 608976246177341437433293 := by
  unfold tailWord_3557931
  simp only [CollatzResearch.WordTrace]
  refine ⟨129768404473231108082721647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86512269648820738721814431 129768404473231108082721647)
  ·
    refine ⟨194652606709846662124082471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129768404473231108082721647 194652606709846662124082471)
    ·
      refine ⟨291978910064769993186123707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194652606709846662124082471 291978910064769993186123707)
      ·
        refine ⟨437968365097154989779185561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291978910064769993186123707 437968365097154989779185561)
        ·
          refine ⟨328476273822866242334389171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437968365097154989779185561 328476273822866242334389171)
          ·
            refine ⟨492714410734299363501583757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328476273822866242334389171 492714410734299363501583757)
            ·
              refine ⟨184767904025362261313093909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 492714410734299363501583757 184767904025362261313093909)
              ·
                refine ⟨8660995501188855999051277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184767904025362261313093909 8660995501188855999051277)
                ·
                  refine ⟨3247873312945820999644229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8660995501188855999051277 3247873312945820999644229)
                  ·
                    refine ⟨608976246177341437433293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3247873312945820999644229 608976246177341437433293)
                    ·
                      rfl

theorem cell23_3557931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 4].length) (baseStart_3557931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557931 prefixEnd_3557931 := by exact prefixLift 3557931
  have htrace : WordTrace (prefixWord ++ tailWord_3557931) baseStart_3557931 baseEnd_3557931 := by
    simpa [prefixWord, tailWord_3557931, baseEnd_3557931] using wordTrace_append hprefix tailTrace_3557931
  have hstable : (prefixWord ++ tailWord_3557931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557931).length < 2 ^ (prefixWord ++ tailWord_3557931).sum := by decide
  have hdescent : baseEnd_3557931 < baseStart_3557931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557956 : List Nat := [2, 3, 5, 1, 1, 2, 2, 2, 5]
def baseStart_3557956 : Nat := 118140960795 + 3557956 * 2 ^ 59
def prefixEnd_3557956 : Nat := 4983230072969 + 3 ^ 40 * 3557956 * 2
def baseEnd_3557956 : Nat := 202993508394265190498585

theorem tailTrace_3557956 : CollatzResearch.WordTrace tailWord_3557956 prefixEnd_3557956 202993508394265190498585 := by
  unfold tailWord_3557956
  simp only [CollatzResearch.WordTrace]
  refine ⟨64884658149070268676190861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86512877532093691568254481 64884658149070268676190861)
  ·
    refine ⟨24331746805901350753571573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64884658149070268676190861 24331746805901350753571573)
    ·
      refine ⟨2281101263053251633147335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24331746805901350753571573 2281101263053251633147335)
      ·
        refine ⟨3421651894579877449721003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281101263053251633147335 3421651894579877449721003)
        ·
          refine ⟨5132477841869816174581505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421651894579877449721003 5132477841869816174581505)
          ·
            refine ⟨3849358381402362130936129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5132477841869816174581505 3849358381402362130936129)
            ·
              refine ⟨2887018786051771598202097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3849358381402362130936129 2887018786051771598202097)
              ·
                refine ⟨2165264089538828698651573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2887018786051771598202097 2165264089538828698651573)
                ·
                  refine ⟨202993508394265190498585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2165264089538828698651573 202993508394265190498585)
                  ·
                    rfl

theorem cell23_3557956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_3557956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557956 prefixEnd_3557956 := by exact prefixLift 3557956
  have htrace : WordTrace (prefixWord ++ tailWord_3557956) baseStart_3557956 baseEnd_3557956 := by
    simpa [prefixWord, tailWord_3557956, baseEnd_3557956] using wordTrace_append hprefix tailTrace_3557956
  have hstable : (prefixWord ++ tailWord_3557956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557956).length < 2 ^ (prefixWord ++ tailWord_3557956).sum := by decide
  have hdescent : baseEnd_3557956 < baseStart_3557956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3557992 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3557992 : Nat := 118140960795 + 3557992 * 2 ^ 59
def prefixEnd_3557992 : Nat := 4983230072969 + 3 ^ 40 * 3557992 * 2
def baseEnd_3557992 : Nat := 1826960060851948573637099

theorem tailTrace_3557992 : CollatzResearch.WordTrace tailWord_3557992 prefixEnd_3557992 1826960060851948573637099 := by
  unfold tailWord_3557992
  simp only [CollatzResearch.WordTrace]
  refine ⟨64885314663005057750346115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86513752884006743667128153 64885314663005057750346115)
  ·
    refine ⟨97327971994507586625519173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64885314663005057750346115 97327971994507586625519173)
    ·
      refine ⟨18248994748970172492284845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97327971994507586625519173 18248994748970172492284845)
      ·
        refine ⟨6843373030863814684606817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18248994748970172492284845 6843373030863814684606817)
        ·
          refine ⟨5132529773147861013455113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6843373030863814684606817 5132529773147861013455113)
          ·
            refine ⟨3849397329860895760091335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5132529773147861013455113 3849397329860895760091335)
            ·
              refine ⟨5774095994791343640137003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849397329860895760091335 5774095994791343640137003)
              ·
                refine ⟨8661143992187015460205505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5774095994791343640137003 8661143992187015460205505)
                ·
                  refine ⟨6495857994140261595154129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8661143992187015460205505 6495857994140261595154129)
                  ·
                    refine ⟨4871893495605196196365597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6495857994140261595154129 4871893495605196196365597)
                    ·
                      refine ⟨1826960060851948573637099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4871893495605196196365597 1826960060851948573637099)
                      ·
                        rfl

theorem cell23_3557992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3557992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3557992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3557992 prefixEnd_3557992 := by exact prefixLift 3557992
  have htrace : WordTrace (prefixWord ++ tailWord_3557992) baseStart_3557992 baseEnd_3557992 := by
    simpa [prefixWord, tailWord_3557992, baseEnd_3557992] using wordTrace_append hprefix tailTrace_3557992
  have hstable : (prefixWord ++ tailWord_3557992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3557992).length < 2 ^ (prefixWord ++ tailWord_3557992).sum := by decide
  have hdescent : baseEnd_3557992 < baseStart_3557992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3557992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558011 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 4]
def baseStart_3558011 : Nat := 118140960795 + 3558011 * 2 ^ 59
def prefixEnd_3558011 : Nat := 4983230072969 + 3 ^ 40 * 3558011 * 2
def baseEnd_3558011 : Nat := 1826969816984383999299511

theorem tailTrace_3558011 : CollatzResearch.WordTrace tailWord_3558011 prefixEnd_3558011 1826969816984383999299511 := by
  unfold tailWord_3558011
  simp only [CollatzResearch.WordTrace]
  refine ⟨129771322312941281745633887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86514214875294187830422591 129771322312941281745633887)
  ·
    refine ⟨194656983469411922618450831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129771322312941281745633887 194656983469411922618450831)
    ·
      refine ⟨291985475204117883927676247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194656983469411922618450831 291985475204117883927676247)
      ·
        refine ⟨437978212806176825891514371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291985475204117883927676247 437978212806176825891514371)
        ·
          refine ⟨656967319209265238837271557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437978212806176825891514371 656967319209265238837271557)
          ·
            refine ⟨123181372351737232281988417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 656967319209265238837271557 123181372351737232281988417)
            ·
              refine ⟨92386029263802924211491313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123181372351737232281988417 92386029263802924211491313)
              ·
                refine ⟨69289521947852193158618485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92386029263802924211491313 69289521947852193158618485)
                ·
                  refine ⟨6495892682611143108620483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69289521947852193158618485 6495892682611143108620483)
                  ·
                    refine ⟨9743839023916714662930725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6495892682611143108620483 9743839023916714662930725)
                    ·
                      refine ⟨1826969816984383999299511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9743839023916714662930725 1826969816984383999299511)
                      ·
                        rfl

theorem cell23_3558011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 4].length) (baseStart_3558011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558011 prefixEnd_3558011 := by exact prefixLift 3558011
  have htrace : WordTrace (prefixWord ++ tailWord_3558011) baseStart_3558011 baseEnd_3558011 := by
    simpa [prefixWord, tailWord_3558011, baseEnd_3558011] using wordTrace_append hprefix tailTrace_3558011
  have hstable : (prefixWord ++ tailWord_3558011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558011).length < 2 ^ (prefixWord ++ tailWord_3558011).sum := by decide
  have hdescent : baseEnd_3558011 < baseStart_3558011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558031 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 5]
def baseStart_3558031 : Nat := 118140960795 + 3558031 * 2 ^ 59
def prefixEnd_3558031 : Nat := 4983230072969 + 3 ^ 40 * 3558031 * 2
def baseEnd_3558031 : Nat := 1826980086597473921049419

theorem tailTrace_3558031 : CollatzResearch.WordTrace tailWord_3558031 prefixEnd_3558031 1826980086597473921049419 := by
  unfold tailWord_3558031
  simp only [CollatzResearch.WordTrace]
  refine ⟨129772051772868825161361947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86514701181912550107574631 129772051772868825161361947)
  ·
    refine ⟨194658077659303237742042921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129772051772868825161361947 194658077659303237742042921)
    ·
      refine ⟨145993558244477428306532191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194658077659303237742042921 145993558244477428306532191)
      ·
        refine ⟨218990337366716142459798287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145993558244477428306532191 218990337366716142459798287)
        ·
          refine ⟨328485506050074213689697431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218990337366716142459798287 328485506050074213689697431)
          ·
            refine ⟨492728259075111320534546147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328485506050074213689697431 492728259075111320534546147)
            ·
              refine ⟨739092388612666980801819221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492728259075111320534546147 739092388612666980801819221)
              ·
                refine ⟨8661238929054691181271319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 739092388612666980801819221 8661238929054691181271319)
                ·
                  refine ⟨12991858393582036771906979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8661238929054691181271319 12991858393582036771906979)
                  ·
                    refine ⟨19487787590373055157860469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12991858393582036771906979 19487787590373055157860469)
                    ·
                      refine ⟨1826980086597473921049419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19487787590373055157860469 1826980086597473921049419)
                      ·
                        rfl

theorem cell23_3558031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_3558031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558031 prefixEnd_3558031 := by exact prefixLift 3558031
  have htrace : WordTrace (prefixWord ++ tailWord_3558031) baseStart_3558031 baseEnd_3558031 := by
    simpa [prefixWord, tailWord_3558031, baseEnd_3558031] using wordTrace_append hprefix tailTrace_3558031
  have hstable : (prefixWord ++ tailWord_3558031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558031).length < 2 ^ (prefixWord ++ tailWord_3558031).sum := by decide
  have hdescent : baseEnd_3558031 < baseStart_3558031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558041 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_3558041 : Nat := 118140960795 + 3558041 * 2 ^ 59
def prefixEnd_3558041 : Nat := 4983230072969 + 3 ^ 40 * 3558041 * 2
def baseEnd_3558041 : Nat := 1826985221404018881924373

theorem tailTrace_3558041 : CollatzResearch.WordTrace tailWord_3558041 prefixEnd_3558041 1826985221404018881924373 := by
  unfold tailWord_3558041
  simp only [CollatzResearch.WordTrace]
  refine ⟨129772416502832596869225977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86514944335221731246150651 129772416502832596869225977)
  ·
    refine ⟨97329312377124447651919483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129772416502832596869225977 97329312377124447651919483)
    ·
      refine ⟨145993968565686671477879225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97329312377124447651919483 145993968565686671477879225)
      ·
        refine ⟨109495476424265003608409419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145993968565686671477879225 109495476424265003608409419)
        ·
          refine ⟨164243214636397505412614129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109495476424265003608409419 164243214636397505412614129)
          ·
            refine ⟨123182410977298129059460597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164243214636397505412614129 123182410977298129059460597)
            ·
              refine ⟨11548351029121699599324431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123182410977298129059460597 11548351029121699599324431)
              ·
                refine ⟨17322526543682549398986647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11548351029121699599324431 17322526543682549398986647)
                ·
                  refine ⟨25983789815523824098479971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17322526543682549398986647 25983789815523824098479971)
                  ·
                    refine ⟨38975684723285736147719957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25983789815523824098479971 38975684723285736147719957)
                    ·
                      refine ⟨1826985221404018881924373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38975684723285736147719957 1826985221404018881924373)
                      ·
                        rfl

theorem cell23_3558041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_3558041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558041 prefixEnd_3558041 := by exact prefixLift 3558041
  have htrace : WordTrace (prefixWord ++ tailWord_3558041) baseStart_3558041 baseEnd_3558041 := by
    simpa [prefixWord, tailWord_3558041, baseEnd_3558041] using wordTrace_append hprefix tailTrace_3558041
  have hstable : (prefixWord ++ tailWord_3558041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558041).length < 2 ^ (prefixWord ++ tailWord_3558041).sum := by decide
  have hdescent : baseEnd_3558041 < baseStart_3558041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558042 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_3558042 : Nat := 118140960795 + 3558042 * 2 ^ 59
def prefixEnd_3558042 : Nat := 4983230072969 + 3 ^ 40 * 3558042 * 2
def baseEnd_3558042 : Nat := 608995244961557792670623

theorem tailTrace_3558042 : CollatzResearch.WordTrace tailWord_3558042 prefixEnd_3558042 608995244961557792670623 := by
  unfold tailWord_3558042
  simp only [CollatzResearch.WordTrace]
  refine ⟨32443113243957243510003095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86514968650552649360008253 32443113243957243510003095)
  ·
    refine ⟨48664669865935865265004643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32443113243957243510003095 48664669865935865265004643)
    ·
      refine ⟨72997004798903797897506965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48664669865935865265004643 72997004798903797897506965)
      ·
        refine ⟨3421734599948615526445639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72997004798903797897506965 3421734599948615526445639)
        ·
          refine ⟨5132601899922923289668459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421734599948615526445639 5132601899922923289668459)
          ·
            refine ⟨7698902849884384934502689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132601899922923289668459 7698902849884384934502689)
            ·
              refine ⟨5774177137413288700877017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7698902849884384934502689 5774177137413288700877017)
              ·
                refine ⟨4330632853059966525657763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5774177137413288700877017 4330632853059966525657763)
                ·
                  refine ⟨6495949279589949788486645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330632853059966525657763 6495949279589949788486645)
                  ·
                    refine ⟨608995244961557792670623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6495949279589949788486645 608995244961557792670623)
                    ·
                      rfl

theorem cell23_3558042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_3558042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558042 prefixEnd_3558042 := by exact prefixLift 3558042
  have htrace : WordTrace (prefixWord ++ tailWord_3558042) baseStart_3558042 baseEnd_3558042 := by
    simpa [prefixWord, tailWord_3558042, baseEnd_3558042] using wordTrace_append hprefix tailTrace_3558042
  have hstable : (prefixWord ++ tailWord_3558042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558042).length < 2 ^ (prefixWord ++ tailWord_3558042).sum := by decide
  have hdescent : baseEnd_3558042 < baseStart_3558042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558062 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3558062 : Nat := 118140960795 + 3558062 * 2 ^ 59
def prefixEnd_3558062 : Nat := 4983230072969 + 3 ^ 40 * 3558062 * 2
def baseEnd_3558062 : Nat := 1826996004497763299761777

theorem tailTrace_3558062 : CollatzResearch.WordTrace tailWord_3558062 prefixEnd_3558062 1826996004497763299761777 := by
  unfold tailWord_3558062
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221647804469564681967555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86515454957171011637160293 16221647804469564681967555)
  ·
    refine ⟨24332471706704347022951333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16221647804469564681967555 24332471706704347022951333)
    ·
      refine ⟨4562338445007065066803375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24332471706704347022951333 4562338445007065066803375)
      ·
        refine ⟨6843507667510597600205063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4562338445007065066803375 6843507667510597600205063)
        ·
          refine ⟨10265261501265896400307595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6843507667510597600205063 10265261501265896400307595)
          ·
            refine ⟨15397892251898844600461393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10265261501265896400307595 15397892251898844600461393)
            ·
              refine ⟨11548419188924133450346045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15397892251898844600461393 11548419188924133450346045)
              ·
                refine ⟨4330657195846550043879767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11548419188924133450346045 4330657195846550043879767)
                ·
                  refine ⟨6495985793769825065819651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330657195846550043879767 6495985793769825065819651)
                  ·
                    refine ⟨9743978690654737598729477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6495985793769825065819651 9743978690654737598729477)
                    ·
                      refine ⟨1826996004497763299761777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9743978690654737598729477 1826996004497763299761777)
                      ·
                        rfl

theorem cell23_3558062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3558062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558062 prefixEnd_3558062 := by exact prefixLift 3558062
  have htrace : WordTrace (prefixWord ++ tailWord_3558062) baseStart_3558062 baseEnd_3558062 := by
    simpa [prefixWord, tailWord_3558062, baseEnd_3558062] using wordTrace_append hprefix tailTrace_3558062
  have hstable : (prefixWord ++ tailWord_3558062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558062).length < 2 ^ (prefixWord ++ tailWord_3558062).sum := by decide
  have hdescent : baseEnd_3558062 < baseStart_3558062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558105 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 3, 3, 2]
def baseStart_3558105 : Nat := 118140960795 + 3558105 * 2 ^ 59
def prefixEnd_3558105 : Nat := 4983230072969 + 3 ^ 40 * 3558105 * 2
def baseEnd_3558105 : Nat := 1827018084165906631524079

theorem tailTrace_3558105 : CollatzResearch.WordTrace tailWord_3558105 prefixEnd_3558105 1827018084165906631524079 := by
  unfold tailWord_3558105
  simp only [CollatzResearch.WordTrace]
  refine ⟨129774750774600735799555769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86516500516400490533037179 129774750774600735799555769)
  ·
    refine ⟨97331063080950551849666827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129774750774600735799555769 97331063080950551849666827)
    ·
      refine ⟨145996594621425827774500241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97331063080950551849666827 145996594621425827774500241)
      ·
        refine ⟨109497445966069370830875181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145996594621425827774500241 109497445966069370830875181)
        ·
          refine ⟨41061542237276014061578193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109497445966069370830875181 41061542237276014061578193)
          ·
            refine ⟨30796156677957010546183645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41061542237276014061578193 30796156677957010546183645)
            ·
              refine ⟨11548558754233878954818867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30796156677957010546183645 11548558754233878954818867)
              ·
                refine ⟨17322838131350818432228301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11548558754233878954818867 17322838131350818432228301)
                ·
                  refine ⟨6496064299256556912085613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17322838131350818432228301 6496064299256556912085613)
                  ·
                    refine ⟨2436024112221208842032105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6496064299256556912085613 2436024112221208842032105)
                    ·
                      refine ⟨1827018084165906631524079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436024112221208842032105 1827018084165906631524079)
                      ·
                        rfl

theorem cell23_3558105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_3558105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558105 prefixEnd_3558105 := by exact prefixLift 3558105
  have htrace : WordTrace (prefixWord ++ tailWord_3558105) baseStart_3558105 baseEnd_3558105 := by
    simpa [prefixWord, tailWord_3558105, baseEnd_3558105] using wordTrace_append hprefix tailTrace_3558105
  have hstable : (prefixWord ++ tailWord_3558105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558105).length < 2 ^ (prefixWord ++ tailWord_3558105).sum := by decide
  have hdescent : baseEnd_3558105 < baseStart_3558105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558131 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 6]
def baseStart_3558131 : Nat := 118140960795 + 3558131 * 2 ^ 59
def prefixEnd_3558131 : Nat := 4983230072969 + 3 ^ 40 * 3558131 * 2
def baseEnd_3558131 : Nat := 1827031434662923529798959

theorem tailTrace_3558131 : CollatzResearch.WordTrace tailWord_3558131 prefixEnd_3558131 1827031434662923529798959 := by
  unfold tailWord_3558131
  simp only [CollatzResearch.WordTrace]
  refine ⟨129775699072506542240002247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86517132715004361493334831 129775699072506542240002247)
  ·
    refine ⟨194663548608759813360003371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129775699072506542240002247 194663548608759813360003371)
    ·
      refine ⟨291995322913139720040005057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194663548608759813360003371 291995322913139720040005057)
      ·
        refine ⟨218996492184854790030003793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291995322913139720040005057 218996492184854790030003793)
        ·
          refine ⟨164247369138641092522502845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218996492184854790030003793 164247369138641092522502845)
          ·
            refine ⟨61592763426990409695938567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164247369138641092522502845 61592763426990409695938567)
            ·
              refine ⟨92389145140485614543907851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61592763426990409695938567 92389145140485614543907851)
              ·
                refine ⟨138583717710728421815861777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92389145140485614543907851 138583717710728421815861777)
                ·
                  refine ⟨103937788283046316361896333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138583717710728421815861777 103937788283046316361896333)
                  ·
                    refine ⟨38976670606142368635711125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103937788283046316361896333 38976670606142368635711125)
                    ·
                      refine ⟨1827031434662923529798959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38976670606142368635711125 1827031434662923529798959)
                      ·
                        rfl

theorem cell23_3558131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_3558131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558131 prefixEnd_3558131 := by exact prefixLift 3558131
  have htrace : WordTrace (prefixWord ++ tailWord_3558131) baseStart_3558131 baseEnd_3558131 := by
    simpa [prefixWord, tailWord_3558131, baseEnd_3558131] using wordTrace_append hprefix tailTrace_3558131
  have hstable : (prefixWord ++ tailWord_3558131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558131).length < 2 ^ (prefixWord ++ tailWord_3558131).sum := by decide
  have hdescent : baseEnd_3558131 < baseStart_3558131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558138 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3]
def baseStart_3558138 : Nat := 118140960795 + 3558138 * 2 ^ 59
def prefixEnd_3558138 : Nat := 4983230072969 + 3 ^ 40 * 3558138 * 2
def baseEnd_3558138 : Nat := 1827035029027505002411427

theorem tailTrace_3558138 : CollatzResearch.WordTrace tailWord_3558138 prefixEnd_3558138 1827035029027505002411427 := by
  unfold tailWord_3558138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32443988595870295608876767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86517302922320788290338045 32443988595870295608876767)
  ·
    refine ⟨48665982893805443413315151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32443988595870295608876767 48665982893805443413315151)
    ·
      refine ⟨72998974340708165119972727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48665982893805443413315151 72998974340708165119972727)
      ·
        refine ⟨109498461511062247679959091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72998974340708165119972727 109498461511062247679959091)
        ·
          refine ⟨164247692266593371519938637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109498461511062247679959091 164247692266593371519938637)
          ·
            refine ⟨61592884599972514319976989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164247692266593371519938637 61592884599972514319976989)
            ·
              refine ⟨23097331724989692869991371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61592884599972514319976989 23097331724989692869991371)
              ·
                refine ⟨34645997587484539304987057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23097331724989692869991371 34645997587484539304987057)
                ·
                  refine ⟨25984498190613404478740293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34645997587484539304987057 25984498190613404478740293)
                  ·
                    refine ⟨4872093410740013339763805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25984498190613404478740293 4872093410740013339763805)
                    ·
                      refine ⟨1827035029027505002411427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4872093410740013339763805 1827035029027505002411427)
                      ·
                        rfl

theorem cell23_3558138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_3558138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558138 prefixEnd_3558138 := by exact prefixLift 3558138
  have htrace : WordTrace (prefixWord ++ tailWord_3558138) baseStart_3558138 baseEnd_3558138 := by
    simpa [prefixWord, tailWord_3558138, baseEnd_3558138] using wordTrace_append hprefix tailTrace_3558138
  have hstable : (prefixWord ++ tailWord_3558138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558138).length < 2 ^ (prefixWord ++ tailWord_3558138).sum := by decide
  have hdescent : baseEnd_3558138 < baseStart_3558138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558152 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 1, 4, 2]
def baseStart_3558152 : Nat := 118140960795 + 3558152 * 2 ^ 59
def prefixEnd_3558152 : Nat := 4983230072969 + 3 ^ 40 * 3558152 * 2
def baseEnd_3558152 : Nat := 1827042217756667947636363

theorem tailTrace_3558152 : CollatzResearch.WordTrace tailWord_3558152 prefixEnd_3558152 1827042217756667947636363 := by
  unfold tailWord_3558152
  simp only [CollatzResearch.WordTrace]
  refine ⟨64888232502715231413258355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86517643336953641884344473 64888232502715231413258355)
  ·
    refine ⟨97332348754072847119887533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64888232502715231413258355 97332348754072847119887533)
    ·
      refine ⟨36499630782777317669957825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97332348754072847119887533 36499630782777317669957825)
      ·
        refine ⟨27374723087082988252468369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36499630782777317669957825 27374723087082988252468369)
        ·
          refine ⟨20531042315312241189351277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27374723087082988252468369 20531042315312241189351277)
          ·
            refine ⟨7699140868242090446006729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20531042315312241189351277 7699140868242090446006729)
            ·
              refine ⟨5774355651181567834505047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7699140868242090446006729 5774355651181567834505047)
              ·
                refine ⟨8661533476772351751757571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5774355651181567834505047 8661533476772351751757571)
                ·
                  refine ⟨12992300215158527627636357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8661533476772351751757571 12992300215158527627636357)
                  ·
                    refine ⟨2436056290342223930181817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12992300215158527627636357 2436056290342223930181817)
                    ·
                      refine ⟨1827042217756667947636363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436056290342223930181817 1827042217756667947636363)
                      ·
                        rfl

theorem cell23_3558152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_3558152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558152 prefixEnd_3558152 := by exact prefixLift 3558152
  have htrace : WordTrace (prefixWord ++ tailWord_3558152) baseStart_3558152 baseEnd_3558152 := by
    simpa [prefixWord, tailWord_3558152, baseEnd_3558152] using wordTrace_append hprefix tailTrace_3558152
  have hstable : (prefixWord ++ tailWord_3558152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558152).length < 2 ^ (prefixWord ++ tailWord_3558152).sum := by decide
  have hdescent : baseEnd_3558152 < baseStart_3558152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558168 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 3, 5, 3]
def baseStart_3558168 : Nat := 118140960795 + 3558168 * 2 ^ 59
def prefixEnd_3558168 : Nat := 4983230072969 + 3 ^ 40 * 3558168 * 2
def baseEnd_3558168 : Nat := 1827050433447139885036289

theorem tailTrace_3558168 : CollatzResearch.WordTrace tailWord_3558168 prefixEnd_3558168 1827050433447139885036289 := by
  unfold tailWord_3558168
  simp only [CollatzResearch.WordTrace]
  refine ⟨64888524286686248779549579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86518032382248331706066105 64888524286686248779549579)
  ·
    refine ⟨97332786430029373169324369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64888524286686248779549579 97332786430029373169324369)
    ·
      refine ⟨72999589822522029876993277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97332786430029373169324369 72999589822522029876993277)
      ·
        refine ⟨27374846183445761203872479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72999589822522029876993277 27374846183445761203872479)
        ·
          refine ⟨41062269275168641805808719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27374846183445761203872479 41062269275168641805808719)
          ·
            refine ⟨61593403912752962708713079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41062269275168641805808719 61593403912752962708713079)
            ·
              refine ⟨92390105869129444063069619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61593403912752962708713079 92390105869129444063069619)
              ·
                refine ⟨138585158803694166094604429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92390105869129444063069619 138585158803694166094604429)
                ·
                  refine ⟨51969434551385312285476661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138585158803694166094604429 51969434551385312285476661)
                  ·
                    refine ⟨4872134489192373026763437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51969434551385312285476661 4872134489192373026763437)
                    ·
                      refine ⟨1827050433447139885036289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4872134489192373026763437 1827050433447139885036289)
                      ·
                        rfl

theorem cell23_3558168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_3558168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558168 prefixEnd_3558168 := by exact prefixLift 3558168
  have htrace : WordTrace (prefixWord ++ tailWord_3558168) baseStart_3558168 baseEnd_3558168 := by
    simpa [prefixWord, tailWord_3558168, baseEnd_3558168] using wordTrace_append hprefix tailTrace_3558168
  have hstable : (prefixWord ++ tailWord_3558168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558168).length < 2 ^ (prefixWord ++ tailWord_3558168).sum := by decide
  have hdescent : baseEnd_3558168 < baseStart_3558168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558173 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_3558173 : Nat := 118140960795 + 3558173 * 2 ^ 59
def prefixEnd_3558173 : Nat := 4983230072969 + 3 ^ 40 * 3558173 * 2
def baseEnd_3558173 : Nat := 1827053000850412365473767

theorem tailTrace_3558173 : CollatzResearch.WordTrace tailWord_3558173 prefixEnd_3558173 1827053000850412365473767 := by
  unfold tailWord_3558173
  simp only [CollatzResearch.WordTrace]
  refine ⟨129777230938354383413031173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86518153958902922275354115 129777230938354383413031173)
  ·
    refine ⟨24333230800941446889943345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129777230938354383413031173 24333230800941446889943345)
    ·
      refine ⟨18249923100706085167457509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24333230800941446889943345 18249923100706085167457509)
      ·
        refine ⟨3421860581382390968898283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18249923100706085167457509 3421860581382390968898283)
        ·
          refine ⟨5132790872073586453347425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421860581382390968898283 5132790872073586453347425)
          ·
            refine ⟨3849593154055189840010569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5132790872073586453347425 3849593154055189840010569)
            ·
              refine ⟨2887194865541392380007927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3849593154055189840010569 2887194865541392380007927)
              ·
                refine ⟨4330792298312088570011891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887194865541392380007927 4330792298312088570011891)
                ·
                  refine ⟨6496188447468132855017837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330792298312088570011891 6496188447468132855017837)
                  ·
                    refine ⟨2436070667800549820631689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6496188447468132855017837 2436070667800549820631689)
                    ·
                      refine ⟨1827053000850412365473767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436070667800549820631689 1827053000850412365473767)
                      ·
                        rfl

theorem cell23_3558173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_3558173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558173 prefixEnd_3558173 := by exact prefixLift 3558173
  have htrace : WordTrace (prefixWord ++ tailWord_3558173) baseStart_3558173 baseEnd_3558173 := by
    simpa [prefixWord, tailWord_3558173, baseEnd_3558173] using wordTrace_append hprefix tailTrace_3558173
  have hstable : (prefixWord ++ tailWord_3558173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558173).length < 2 ^ (prefixWord ++ tailWord_3558173).sum := by decide
  have hdescent : baseEnd_3558173 < baseStart_3558173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558175 : List Nat := [1, 1, 2, 4, 2, 2, 1, 5, 5]
def baseStart_3558175 : Nat := 118140960795 + 3558175 * 2 ^ 59
def prefixEnd_3558175 : Nat := 4983230072969 + 3 ^ 40 * 3558175 * 2
def baseEnd_3558175 : Nat := 203006003090191261960973

theorem tailTrace_3558175 : CollatzResearch.WordTrace tailWord_3558175 prefixEnd_3558175 203006003090191261960973 := by
  unfold tailWord_3558175
  simp only [CollatzResearch.WordTrace]
  refine ⟨129777303884347137754603979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86518202589564758503069319 129777303884347137754603979)
  ·
    refine ⟨194665955826520706631905969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129777303884347137754603979 194665955826520706631905969)
    ·
      refine ⟨145999466869890529973929477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194665955826520706631905969 145999466869890529973929477)
      ·
        refine ⟨27374900038104474370111777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145999466869890529973929477 27374900038104474370111777)
        ·
          refine ⟨20531175028578355777583833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27374900038104474370111777 20531175028578355777583833)
          ·
            refine ⟨15398381271433766833187875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20531175028578355777583833 15398381271433766833187875)
            ·
              refine ⟨23097571907150650249781813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15398381271433766833187875 23097571907150650249781813)
              ·
                refine ⟨2165397366295373460917045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23097571907150650249781813 2165397366295373460917045)
                ·
                  refine ⟨203006003090191261960973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2165397366295373460917045 203006003090191261960973)
                  ·
                    rfl

theorem cell23_3558175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 5].length) (baseStart_3558175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558175 prefixEnd_3558175 := by exact prefixLift 3558175
  have htrace : WordTrace (prefixWord ++ tailWord_3558175) baseStart_3558175 baseEnd_3558175 := by
    simpa [prefixWord, tailWord_3558175, baseEnd_3558175] using wordTrace_append hprefix tailTrace_3558175
  have hstable : (prefixWord ++ tailWord_3558175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558175).length < 2 ^ (prefixWord ++ tailWord_3558175).sum := by decide
  have hdescent : baseEnd_3558175 < baseStart_3558175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558186 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3558186 : Nat := 118140960795 + 3558186 * 2 ^ 59
def prefixEnd_3558186 : Nat := 4983230072969 + 3 ^ 40 * 3558186 * 2
def baseEnd_3558186 : Nat := 1827059676098920814611207

theorem tailTrace_3558186 : CollatzResearch.WordTrace tailWord_3558186 prefixEnd_3558186 1827059676098920814611207 := by
  unfold tailWord_3558186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32444426271826821658313603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86518470058204857755502941 32444426271826821658313603)
  ·
    refine ⟨48666639407740232487470405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32444426271826821658313603 48666639407740232487470405)
    ·
      refine ⟨9124994888951293591400701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48666639407740232487470405 9124994888951293591400701)
      ·
        refine ⟨3421873083356735096775263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9124994888951293591400701 3421873083356735096775263)
        ·
          refine ⟨5132809625035102645162895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421873083356735096775263 5132809625035102645162895)
          ·
            refine ⟨7699214437552653967744343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132809625035102645162895 7699214437552653967744343)
            ·
              refine ⟨11548821656328980951616515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7699214437552653967744343 11548821656328980951616515)
              ·
                refine ⟨17323232484493471427424773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11548821656328980951616515 17323232484493471427424773)
                ·
                  refine ⟨3248106090842525892642145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17323232484493471427424773 3248106090842525892642145)
                  ·
                    refine ⟨2436079568131894419481609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3248106090842525892642145 2436079568131894419481609)
                    ·
                      refine ⟨1827059676098920814611207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436079568131894419481609 1827059676098920814611207)
                      ·
                        rfl

theorem cell23_3558186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3558186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558186 prefixEnd_3558186 := by exact prefixLift 3558186
  have htrace : WordTrace (prefixWord ++ tailWord_3558186) baseStart_3558186 baseEnd_3558186 := by
    simpa [prefixWord, tailWord_3558186, baseEnd_3558186] using wordTrace_append hprefix tailTrace_3558186
  have hstable : (prefixWord ++ tailWord_3558186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558186).length < 2 ^ (prefixWord ++ tailWord_3558186).sum := by decide
  have hdescent : baseEnd_3558186 < baseStart_3558186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558188 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_3558188 : Nat := 118140960795 + 3558188 * 2 ^ 59
def prefixEnd_3558188 : Nat := 4983230072969 + 3 ^ 40 * 3558188 * 2
def baseEnd_3558188 : Nat := 609020234353409935595399

theorem tailTrace_3558188 : CollatzResearch.WordTrace tailWord_3558188 prefixEnd_3558188 609020234353409935595399 := by
  unfold tailWord_3558188
  simp only [CollatzResearch.WordTrace]
  refine ⟨64888889016650020487413609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86518518688866693983218145 64888889016650020487413609)
  ·
    refine ⟨48666666762487515365560207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64888889016650020487413609 48666666762487515365560207)
    ·
      refine ⟨73000000143731273048340311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48666666762487515365560207 73000000143731273048340311)
      ·
        refine ⟨109500000215596909572510467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73000000143731273048340311 109500000215596909572510467)
        ·
          refine ⟨164250000323395364358765701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109500000215596909572510467 164250000323395364358765701)
          ·
            refine ⟨30796875060636630817268569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164250000323395364358765701 30796875060636630817268569)
            ·
              refine ⟨23097656295477473112951427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30796875060636630817268569 23097656295477473112951427)
              ·
                refine ⟨34646484443216209669427141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23097656295477473112951427 34646484443216209669427141)
                ·
                  refine ⟨6496215833103039313017589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34646484443216209669427141 6496215833103039313017589)
                  ·
                    refine ⟨609020234353409935595399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6496215833103039313017589 609020234353409935595399)
                    ·
                      rfl

theorem cell23_3558188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_3558188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558188 prefixEnd_3558188 := by exact prefixLift 3558188
  have htrace : WordTrace (prefixWord ++ tailWord_3558188) baseStart_3558188 baseEnd_3558188 := by
    simpa [prefixWord, tailWord_3558188, baseEnd_3558188] using wordTrace_append hprefix tailTrace_3558188
  have hstable : (prefixWord ++ tailWord_3558188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558188).length < 2 ^ (prefixWord ++ tailWord_3558188).sum := by decide
  have hdescent : baseEnd_3558188 < baseStart_3558188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558245 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 4, 2, 3]
def baseStart_3558245 : Nat := 118140960795 + 3558245 * 2 ^ 59
def prefixEnd_3558245 : Nat := 4983230072969 + 3 ^ 40 * 3558245 * 2
def baseEnd_3558245 : Nat := 1827089971457536083773435

theorem tailTrace_3558245 : CollatzResearch.WordTrace tailWord_3558245 prefixEnd_3558245 1827089971457536083773435 := by
  unfold tailWord_3558245
  simp only [CollatzResearch.WordTrace]
  refine ⟨129779856994093539709652189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86519904662729026473101459 129779856994093539709652189)
  ·
    refine ⟨48667446372785077391119571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129779856994093539709652189 48667446372785077391119571)
    ·
      refine ⟨73001169559177616086679357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48667446372785077391119571 73001169559177616086679357)
      ·
        refine ⟨27375438584691606032504759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73001169559177616086679357 27375438584691606032504759)
        ·
          refine ⟨41063157877037409048757139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27375438584691606032504759 41063157877037409048757139)
          ·
            refine ⟨61594736815556113573135709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41063157877037409048757139 61594736815556113573135709)
            ·
              refine ⟨23098026305833542589925891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61594736815556113573135709 23098026305833542589925891)
              ·
                refine ⟨34647039458750313884888837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23098026305833542589925891 34647039458750313884888837)
                ·
                  refine ⟨6496319898515683853416657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34647039458750313884888837 6496319898515683853416657)
                  ·
                    refine ⟨4872239923886762890062493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6496319898515683853416657 4872239923886762890062493)
                    ·
                      refine ⟨1827089971457536083773435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4872239923886762890062493 1827089971457536083773435)
                      ·
                        rfl

theorem cell23_3558245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_3558245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558245 prefixEnd_3558245 := by exact prefixLift 3558245
  have htrace : WordTrace (prefixWord ++ tailWord_3558245) baseStart_3558245 baseEnd_3558245 := by
    simpa [prefixWord, tailWord_3558245, baseEnd_3558245] using wordTrace_append hprefix tailTrace_3558245
  have hstable : (prefixWord ++ tailWord_3558245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558245).length < 2 ^ (prefixWord ++ tailWord_3558245).sum := by decide
  have hdescent : baseEnd_3558245 < baseStart_3558245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558265 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 6]
def baseStart_3558265 : Nat := 118140960795 + 3558265 * 2 ^ 59
def prefixEnd_3558265 : Nat := 4983230072969 + 3 ^ 40 * 3558265 * 2
def baseEnd_3558265 : Nat := 203011137896736222835927

theorem tailTrace_3558265 : CollatzResearch.WordTrace tailWord_3558265 prefixEnd_3558265 203011137896736222835927 := by
  unfold tailWord_3558265
  simp only [CollatzResearch.WordTrace]
  refine ⟨129780586454021083125380249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86520390969347388750253499 129780586454021083125380249)
  ·
    refine ⟨97335439840515812344035187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129780586454021083125380249 97335439840515812344035187)
    ·
      refine ⟨146003159760773718516052781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97335439840515812344035187 146003159760773718516052781)
      ·
        refine ⟨54751184910290144443519793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146003159760773718516052781 54751184910290144443519793)
        ·
          refine ⟨41063388682717608332639845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54751184910290144443519793 41063388682717608332639845)
          ·
            refine ⟨7699385378009551562369971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41063388682717608332639845 7699385378009551562369971)
            ·
              refine ⟨11549078067014327343554957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7699385378009551562369971 11549078067014327343554957)
              ·
                refine ⟨4330904275130372753833109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11549078067014327343554957 4330904275130372753833109)
                ·
                  refine ⟨203011137896736222835927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4330904275130372753833109 203011137896736222835927)
                  ·
                    rfl

theorem cell23_3558265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 6].length) (baseStart_3558265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558265 prefixEnd_3558265 := by exact prefixLift 3558265
  have htrace : WordTrace (prefixWord ++ tailWord_3558265) baseStart_3558265 baseEnd_3558265 := by
    simpa [prefixWord, tailWord_3558265, baseEnd_3558265] using wordTrace_append hprefix tailTrace_3558265
  have hstable : (prefixWord ++ tailWord_3558265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558265).length < 2 ^ (prefixWord ++ tailWord_3558265).sum := by decide
  have hdescent : baseEnd_3558265 < baseStart_3558265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558268 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_3558268 : Nat := 118140960795 + 3558268 * 2 ^ 59
def prefixEnd_3558268 : Nat := 4983230072969 + 3 ^ 40 * 3558268 * 2
def baseEnd_3558268 : Nat := 1827101781512589493785829

theorem tailTrace_3558268 : CollatzResearch.WordTrace tailWord_3558268 prefixEnd_3558268 1827101781512589493785829 := by
  unfold tailWord_3558268
  simp only [CollatzResearch.WordTrace]
  refine ⟨64890347936505107318869729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86520463915340143091826305 64890347936505107318869729)
  ·
    refine ⟨48667760952378830489152297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64890347936505107318869729 48667760952378830489152297)
    ·
      refine ⟨36500820714284122866864223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48667760952378830489152297 36500820714284122866864223)
      ·
        refine ⟨54751231071426184300296335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36500820714284122866864223 54751231071426184300296335)
        ·
          refine ⟨82126846607139276450444503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54751231071426184300296335 82126846607139276450444503)
          ·
            refine ⟨123190269910708914675666755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82126846607139276450444503 123190269910708914675666755)
            ·
              refine ⟨184785404866063372013500133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123190269910708914675666755 184785404866063372013500133)
              ·
                refine ⟨34647263412386882252531275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184785404866063372013500133 34647263412386882252531275)
                ·
                  refine ⟨51970895118580323378796913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34647263412386882252531275 51970895118580323378796913)
                  ·
                    refine ⟨38978171338935242534097685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51970895118580323378796913 38978171338935242534097685)
                    ·
                      refine ⟨1827101781512589493785829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38978171338935242534097685 1827101781512589493785829)
                      ·
                        rfl

theorem cell23_3558268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_3558268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558268 prefixEnd_3558268 := by exact prefixLift 3558268
  have htrace : WordTrace (prefixWord ++ tailWord_3558268) baseStart_3558268 baseEnd_3558268 := by
    simpa [prefixWord, tailWord_3558268, baseEnd_3558268] using wordTrace_append hprefix tailTrace_3558268
  have hstable : (prefixWord ++ tailWord_3558268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558268).length < 2 ^ (prefixWord ++ tailWord_3558268).sum := by decide
  have hdescent : baseEnd_3558268 < baseStart_3558268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558389 : List Nat := [1, 3, 5, 2, 1, 1, 1, 9]
def baseStart_3558389 : Nat := 118140960795 + 3558389 * 2 ^ 59
def prefixEnd_3558389 : Nat := 4983230072969 + 3 ^ 40 * 3558389 * 2
def baseEnd_3558389 : Nat := 67672737506362352606399

theorem tailTrace_3558389 : CollatzResearch.WordTrace tailWord_3558389 prefixEnd_3558389 67672737506362352606399 := by
  unfold tailWord_3558389
  simp only [CollatzResearch.WordTrace]
  refine ⟨129785109105571852302894221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86523406070381234868596147 129785109105571852302894221)
  ·
    refine ⟨48669415914589444613585333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129785109105571852302894221 48669415914589444613585333)
    ·
      refine ⟨4562757741992760432523625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48669415914589444613585333 4562757741992760432523625)
      ·
        refine ⟨3422068306494570324392719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4562757741992760432523625 3422068306494570324392719)
        ·
          refine ⟨5133102459741855486589079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422068306494570324392719 5133102459741855486589079)
          ·
            refine ⟨7699653689612783229883619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5133102459741855486589079 7699653689612783229883619)
            ·
              refine ⟨11549480534419174844825429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7699653689612783229883619 11549480534419174844825429)
              ·
                refine ⟨67672737506362352606399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11549480534419174844825429 67672737506362352606399)
                ·
                  rfl

theorem cell23_3558389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 9].length) (baseStart_3558389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558389 prefixEnd_3558389 := by exact prefixLift 3558389
  have htrace : WordTrace (prefixWord ++ tailWord_3558389) baseStart_3558389 baseEnd_3558389 := by
    simpa [prefixWord, tailWord_3558389, baseEnd_3558389] using wordTrace_append hprefix tailTrace_3558389
  have hstable : (prefixWord ++ tailWord_3558389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558389).length < 2 ^ (prefixWord ++ tailWord_3558389).sum := by decide
  have hdescent : baseEnd_3558389 < baseStart_3558389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558433 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 2, 1, 3]
def baseStart_3558433 : Nat := 118140960795 + 3558433 * 2 ^ 59
def prefixEnd_3558433 : Nat := 4983230072969 + 3 ^ 40 * 3558433 * 2
def baseEnd_3558433 : Nat := 1827186505820581348222571

theorem tailTrace_3558433 : CollatzResearch.WordTrace tailWord_3558433 prefixEnd_3558433 1827186505820581348222571 := by
  unfold tailWord_3558433
  simp only [CollatzResearch.WordTrace]
  refine ⟨129786713917412447817495953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86524475944941631878330635 129786713917412447817495953)
  ·
    refine ⟨97340035438059335863121965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129786713917412447817495953 97340035438059335863121965)
    ·
      refine ⟨36502513289272250948670737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97340035438059335863121965 36502513289272250948670737)
      ·
        refine ⟨27376884966954188211503053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36502513289272250948670737 27376884966954188211503053)
        ·
          refine ⟨10266331862607820579313645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27376884966954188211503053 10266331862607820579313645)
          ·
            refine ⟨3849874448477932717242617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10266331862607820579313645 3849874448477932717242617)
            ·
              refine ⟨2887405836358449537931963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3849874448477932717242617 2887405836358449537931963)
              ·
                refine ⟨4331108754537674306897945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887405836358449537931963 4331108754537674306897945)
                ·
                  refine ⟨3248331565903255730173459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4331108754537674306897945 3248331565903255730173459)
                  ·
                    refine ⟨4872497348854883595260189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3248331565903255730173459 4872497348854883595260189)
                    ·
                      refine ⟨1827186505820581348222571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4872497348854883595260189 1827186505820581348222571)
                      ·
                        rfl

theorem cell23_3558433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_3558433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558433 prefixEnd_3558433 := by exact prefixLift 3558433
  have htrace : WordTrace (prefixWord ++ tailWord_3558433) baseStart_3558433 baseEnd_3558433 := by
    simpa [prefixWord, tailWord_3558433, baseEnd_3558433] using wordTrace_append hprefix tailTrace_3558433
  have hstable : (prefixWord ++ tailWord_3558433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558433).length < 2 ^ (prefixWord ++ tailWord_3558433).sum := by decide
  have hdescent : baseEnd_3558433 < baseStart_3558433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558472 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_3558472 : Nat := 118140960795 + 3558472 * 2 ^ 59
def prefixEnd_3558472 : Nat := 4983230072969 + 3 ^ 40 * 3558472 * 2
def baseEnd_3558472 : Nat := 1827206531566106695634891

theorem tailTrace_3558472 : CollatzResearch.WordTrace tailWord_3558472 prefixEnd_3558472 1827206531566106695634891 := by
  unfold tailWord_3558472
  simp only [CollatzResearch.WordTrace]
  refine ⟨64894068182135578739082835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86525424242847438318777113 64894068182135578739082835)
  ·
    refine ⟨97341102273203368108624253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64894068182135578739082835 97341102273203368108624253)
    ·
      refine ⟨36502913352451263040734095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97341102273203368108624253 36502913352451263040734095)
      ·
        refine ⟨54754370028676894561101143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36502913352451263040734095 54754370028676894561101143)
        ·
          refine ⟨82131555043015341841651715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54754370028676894561101143 82131555043015341841651715)
          ·
            refine ⟨123197332564523012762477573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82131555043015341841651715 123197332564523012762477573)
            ·
              refine ⟨23099499855848064892964545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123197332564523012762477573 23099499855848064892964545)
              ·
                refine ⟨17324624891886048669723409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23099499855848064892964545 17324624891886048669723409)
                ·
                  refine ⟨12993468668914536502292557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17324624891886048669723409 12993468668914536502292557)
                  ·
                    refine ⟨4872550750842951188359709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12993468668914536502292557 4872550750842951188359709)
                    ·
                      refine ⟨1827206531566106695634891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4872550750842951188359709 1827206531566106695634891)
                      ·
                        rfl

theorem cell23_3558472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_3558472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558472 prefixEnd_3558472 := by exact prefixLift 3558472
  have htrace : WordTrace (prefixWord ++ tailWord_3558472) baseStart_3558472 baseEnd_3558472 := by
    simpa [prefixWord, tailWord_3558472, baseEnd_3558472] using wordTrace_append hprefix tailTrace_3558472
  have hstable : (prefixWord ++ tailWord_3558472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558472).length < 2 ^ (prefixWord ++ tailWord_3558472).sum := by decide
  have hdescent : baseEnd_3558472 < baseStart_3558472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558492 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3558492 : Nat := 118140960795 + 3558492 * 2 ^ 59
def prefixEnd_3558492 : Nat := 4983230072969 + 3 ^ 40 * 3558492 * 2
def baseEnd_3558492 : Nat := 609072267059732205794933

theorem tailTrace_3558492 : CollatzResearch.WordTrace tailWord_3558492 prefixEnd_3558492 609072267059732205794933 := by
  unfold tailWord_3558492
  simp only [CollatzResearch.WordTrace]
  refine ⟨64894432912099350446946865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86525910549465800595929153 64894432912099350446946865)
  ·
    refine ⟨48670824684074512835210149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64894432912099350446946865 48670824684074512835210149)
    ·
      refine ⟨9125779628263971156601903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48670824684074512835210149 9125779628263971156601903)
      ·
        refine ⟨13688669442395956734902855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9125779628263971156601903 13688669442395956734902855)
        ·
          refine ⟨20533004163593935102354283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13688669442395956734902855 20533004163593935102354283)
          ·
            refine ⟨30799506245390902653531425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20533004163593935102354283 30799506245390902653531425)
            ·
              refine ⟨23099629684043176990148569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30799506245390902653531425 23099629684043176990148569)
              ·
                refine ⟨17324722263032382742611427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23099629684043176990148569 17324722263032382742611427)
                ·
                  refine ⟨25987083394548574113917141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17324722263032382742611427 25987083394548574113917141)
                  ·
                    refine ⟨609072267059732205794933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25987083394548574113917141 609072267059732205794933)
                    ·
                      rfl

theorem cell23_3558492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3558492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558492 prefixEnd_3558492 := by exact prefixLift 3558492
  have htrace : WordTrace (prefixWord ++ tailWord_3558492) baseStart_3558492 baseEnd_3558492 := by
    simpa [prefixWord, tailWord_3558492, baseEnd_3558492] using wordTrace_append hprefix tailTrace_3558492
  have hstable : (prefixWord ++ tailWord_3558492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558492).length < 2 ^ (prefixWord ++ tailWord_3558492).sum := by decide
  have hdescent : baseEnd_3558492 < baseStart_3558492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558509 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_3558509 : Nat := 118140960795 + 3558509 * 2 ^ 59
def prefixEnd_3558509 : Nat := 4983230072969 + 3 ^ 40 * 3558509 * 2
def baseEnd_3558509 : Nat := 609075176783441016957407

theorem tailTrace_3558509 : CollatzResearch.WordTrace tailWord_3558509 prefixEnd_3558509 609075176783441016957407 := by
  unfold tailWord_3558509
  simp only [CollatzResearch.WordTrace]
  refine ⟨129789485865137112797262581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86526323910091408531508387 129789485865137112797262581)
  ·
    refine ⟨12167764299856604324743367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129789485865137112797262581 12167764299856604324743367)
    ·
      refine ⟨18251646449784906487115051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12167764299856604324743367 18251646449784906487115051)
      ·
        refine ⟨27377469674677359730672577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18251646449784906487115051 27377469674677359730672577)
        ·
          refine ⟨20533102256008019798004433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27377469674677359730672577 20533102256008019798004433)
          ·
            refine ⟨15399826692006014848503325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20533102256008019798004433 15399826692006014848503325)
            ·
              refine ⟨5774935009502255568188747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15399826692006014848503325 5774935009502255568188747)
              ·
                refine ⟨8662402514253383352283121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5774935009502255568188747 8662402514253383352283121)
                ·
                  refine ⟨6496801885690037514212341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8662402514253383352283121 6496801885690037514212341)
                  ·
                    refine ⟨609075176783441016957407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6496801885690037514212341 609075176783441016957407)
                    ·
                      rfl

theorem cell23_3558509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_3558509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558509 prefixEnd_3558509 := by exact prefixLift 3558509
  have htrace : WordTrace (prefixWord ++ tailWord_3558509) baseStart_3558509 baseEnd_3558509 := by
    simpa [prefixWord, tailWord_3558509, baseEnd_3558509] using wordTrace_append hprefix tailTrace_3558509
  have hstable : (prefixWord ++ tailWord_3558509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558509).length < 2 ^ (prefixWord ++ tailWord_3558509).sum := by decide
  have hdescent : baseEnd_3558509 < baseStart_3558509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558512 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_3558512 : Nat := 118140960795 + 3558512 * 2 ^ 59
def prefixEnd_3558512 : Nat := 4983230072969 + 3 ^ 40 * 3558512 * 2
def baseEnd_3558512 : Nat := 1827227070792286539134707

theorem tailTrace_3558512 : CollatzResearch.WordTrace tailWord_3558512 prefixEnd_3558512 1827227070792286539134707 := by
  unfold tailWord_3558512
  simp only [CollatzResearch.WordTrace]
  refine ⟨64894797642063122154810895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86526396856084162873081193 64894797642063122154810895)
  ·
    refine ⟨97342196463094683232216343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64894797642063122154810895 97342196463094683232216343)
    ·
      refine ⟨146013294694642024848324515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97342196463094683232216343 146013294694642024848324515)
      ·
        refine ⟨219019942041963037272486773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146013294694642024848324515 219019942041963037272486773)
        ·
          refine ⟨20533119566434034744295635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219019942041963037272486773 20533119566434034744295635)
          ·
            refine ⟨30799679349651052116443453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20533119566434034744295635 30799679349651052116443453)
            ·
              refine ⟨11549879756119144543666295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30799679349651052116443453 11549879756119144543666295)
              ·
                refine ⟨17324819634178716815499443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11549879756119144543666295 17324819634178716815499443)
                ·
                  refine ⟨25987229451268075223249165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17324819634178716815499443 25987229451268075223249165)
                  ·
                    refine ⟨9745211044225528208718437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25987229451268075223249165 9745211044225528208718437)
                    ·
                      refine ⟨1827227070792286539134707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9745211044225528208718437 1827227070792286539134707)
                      ·
                        rfl

theorem cell23_3558512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_3558512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558512 prefixEnd_3558512 := by exact prefixLift 3558512
  have htrace : WordTrace (prefixWord ++ tailWord_3558512) baseStart_3558512 baseEnd_3558512 := by
    simpa [prefixWord, tailWord_3558512, baseEnd_3558512] using wordTrace_append hprefix tailTrace_3558512
  have hstable : (prefixWord ++ tailWord_3558512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558512).length < 2 ^ (prefixWord ++ tailWord_3558512).sum := by decide
  have hdescent : baseEnd_3558512 < baseStart_3558512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558546 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_3558546 : Nat := 118140960795 + 3558546 * 2 ^ 59
def prefixEnd_3558546 : Nat := 4983230072969 + 3 ^ 40 * 3558546 * 2
def baseEnd_3558546 : Nat := 1827244529134539406109551

theorem tailTrace_3558546 : CollatzResearch.WordTrace tailWord_3558546 prefixEnd_3558546 1827244529134539406109551 := by
  unfold tailWord_3558546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32447708841500767029089873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86527223577335378744239661 32447708841500767029089873)
  ·
    refine ⟨24335781631125575271817405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32447708841500767029089873 24335781631125575271817405)
    ·
      refine ⟨9125918111672090726931527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24335781631125575271817405 9125918111672090726931527)
      ·
        refine ⟨13688877167508136090397291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9125918111672090726931527 13688877167508136090397291)
        ·
          refine ⟨20533315751262204135595937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13688877167508136090397291 20533315751262204135595937)
          ·
            refine ⟨15399986813446653101696953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20533315751262204135595937 15399986813446653101696953)
            ·
              refine ⟨11549990110084989826272715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15399986813446653101696953 11549990110084989826272715)
              ·
                refine ⟨17324985165127484739409073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11549990110084989826272715 17324985165127484739409073)
                ·
                  refine ⟨12993738873845613554556805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17324985165127484739409073 12993738873845613554556805)
                  ·
                    refine ⟨2436326038846052541479401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12993738873845613554556805 2436326038846052541479401)
                    ·
                      refine ⟨1827244529134539406109551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436326038846052541479401 1827244529134539406109551)
                      ·
                        rfl

theorem cell23_3558546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_3558546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558546 prefixEnd_3558546 := by exact prefixLift 3558546
  have htrace : WordTrace (prefixWord ++ tailWord_3558546) baseStart_3558546 baseEnd_3558546 := by
    simpa [prefixWord, tailWord_3558546, baseEnd_3558546] using wordTrace_append hprefix tailTrace_3558546
  have hstable : (prefixWord ++ tailWord_3558546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558546).length < 2 ^ (prefixWord ++ tailWord_3558546).sum := by decide
  have hdescent : baseEnd_3558546 < baseStart_3558546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558579 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 5, 1, 3]
def baseStart_3558579 : Nat := 118140960795 + 3558579 * 2 ^ 59
def prefixEnd_3558579 : Nat := 4983230072969 + 3 ^ 40 * 3558579 * 2
def baseEnd_3558579 : Nat := 1827261473996137776996899

theorem tailTrace_3558579 : CollatzResearch.WordTrace tailWord_3558579 prefixEnd_3558579 1827261473996137776996899 := by
  unfold tailWord_3558579
  simp only [CollatzResearch.WordTrace]
  refine ⟨129792038974883514752310791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86528025983255676501540527 129792038974883514752310791)
  ·
    refine ⟨194688058462325272128466187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129792038974883514752310791 194688058462325272128466187)
    ·
      refine ⟨292032087693487908192699281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194688058462325272128466187 292032087693487908192699281)
      ·
        refine ⟨219024065770115931144524461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292032087693487908192699281 219024065770115931144524461)
        ·
          refine ⟨82134024663793474179196673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219024065770115931144524461 82134024663793474179196673)
          ·
            refine ⟨61600518497845105634397505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82134024663793474179196673 61600518497845105634397505)
            ·
              refine ⟨46200388873383829225798129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61600518497845105634397505 46200388873383829225798129)
              ·
                refine ⟨34650291655037871919348597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46200388873383829225798129 34650291655037871919348597)
                ·
                  refine ⟨3248464842659800492438931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34650291655037871919348597 3248464842659800492438931)
                  ·
                    refine ⟨4872697263989700738658397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3248464842659800492438931 4872697263989700738658397)
                    ·
                      refine ⟨1827261473996137776996899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4872697263989700738658397 1827261473996137776996899)
                      ·
                        rfl

theorem cell23_3558579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 1, 3].length) (baseStart_3558579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558579 prefixEnd_3558579 := by exact prefixLift 3558579
  have htrace : WordTrace (prefixWord ++ tailWord_3558579) baseStart_3558579 baseEnd_3558579 := by
    simpa [prefixWord, tailWord_3558579, baseEnd_3558579] using wordTrace_append hprefix tailTrace_3558579
  have hstable : (prefixWord ++ tailWord_3558579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558579).length < 2 ^ (prefixWord ++ tailWord_3558579).sum := by decide
  have hdescent : baseEnd_3558579 < baseStart_3558579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558590 : List Nat := [4, 2, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_3558590 : Nat := 118140960795 + 3558590 * 2 ^ 59
def prefixEnd_3558590 : Nat := 4983230072969 + 3 ^ 40 * 3558590 * 2
def baseEnd_3558590 : Nat := 609089040761112411319783

theorem tailTrace_3558590 : CollatzResearch.WordTrace tailWord_3558590 prefixEnd_3558590 609089040761112411319783 := by
  unfold tailWord_3558590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16224055022230457953870153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86528293451895775753974149 16224055022230457953870153)
  ·
    refine ⟨12168041266672843465402615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16224055022230457953870153 12168041266672843465402615)
    ·
      refine ⟨18252061900009265198103923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12168041266672843465402615 18252061900009265198103923)
      ·
        refine ⟨27378092850013897797155885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18252061900009265198103923 27378092850013897797155885)
        ·
          refine ⟨10266784818755211673933457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27378092850013897797155885 10266784818755211673933457)
          ·
            refine ⟨7700088614066408755450093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10266784818755211673933457 7700088614066408755450093)
            ·
              refine ⟨2887533230274903283293785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7700088614066408755450093 2887533230274903283293785)
              ·
                refine ⟨2165649922706177462470339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2887533230274903283293785 2165649922706177462470339)
                ·
                  refine ⟨3248474884059266193705509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165649922706177462470339 3248474884059266193705509)
                  ·
                    refine ⟨609089040761112411319783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3248474884059266193705509 609089040761112411319783)
                    ·
                      rfl

theorem cell23_3558590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_3558590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558590 prefixEnd_3558590 := by exact prefixLift 3558590
  have htrace : WordTrace (prefixWord ++ tailWord_3558590) baseStart_3558590 baseEnd_3558590 := by
    simpa [prefixWord, tailWord_3558590, baseEnd_3558590] using wordTrace_append hprefix tailTrace_3558590
  have hstable : (prefixWord ++ tailWord_3558590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558590).length < 2 ^ (prefixWord ++ tailWord_3558590).sum := by decide
  have hdescent : baseEnd_3558590 < baseStart_3558590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558642 : List Nat := [3, 2, 1, 3, 14]
def baseStart_3558642 : Nat := 118140960795 + 3558642 * 2 ^ 59
def prefixEnd_3558642 : Nat := 4983230072969 + 3 ^ 40 * 3558642 * 2
def baseEnd_3558642 : Nat := 2506575889269370412221

theorem tailTrace_3558642 : CollatzResearch.WordTrace tailWord_3558642 prefixEnd_3558642 2506575889269370412221 := by
  unfold tailWord_3558642
  simp only [CollatzResearch.WordTrace]
  refine ⟨32448584193413819127963545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86529557849103517674569453 32448584193413819127963545)
  ·
    refine ⟨24336438145060364345972659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32448584193413819127963545 24336438145060364345972659)
    ·
      refine ⟨36504657217590546518958989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24336438145060364345972659 36504657217590546518958989)
      ·
        refine ⟨13689246456596454944609621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36504657217590546518958989 13689246456596454944609621)
        ·
          refine ⟨2506575889269370412221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 13689246456596454944609621 2506575889269370412221)
          ·
            rfl

theorem cell23_3558642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 14].length) (baseStart_3558642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558642 prefixEnd_3558642 := by exact prefixLift 3558642
  have htrace : WordTrace (prefixWord ++ tailWord_3558642) baseStart_3558642 baseEnd_3558642 := by
    simpa [prefixWord, tailWord_3558642, baseEnd_3558642] using wordTrace_append hprefix tailTrace_3558642
  have hstable : (prefixWord ++ tailWord_3558642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558642).length < 2 ^ (prefixWord ++ tailWord_3558642).sum := by decide
  have hdescent : baseEnd_3558642 < baseStart_3558642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558659 : List Nat := [1, 1, 1, 3, 2, 6, 1, 8]
def baseStart_3558659 : Nat := 118140960795 + 3558659 * 2 ^ 59
def prefixEnd_3558659 : Nat := 4983230072969 + 3 ^ 40 * 3558659 * 2
def baseEnd_3558659 : Nat := 67677872312907313481353

theorem tailTrace_3558659 : CollatzResearch.WordTrace tailWord_3558659 prefixEnd_3558659 67677872312907313481353 := by
  unfold tailWord_3558659
  simp only [CollatzResearch.WordTrace]
  refine ⟨129794956814593688415223031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86529971209729125610148687 129794956814593688415223031)
  ·
    refine ⟨194692435221890532622834547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129794956814593688415223031 194692435221890532622834547)
    ·
      refine ⟨292038652832835798934251821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194692435221890532622834547 292038652832835798934251821)
      ·
        refine ⟨109514494812313424600344433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292038652832835798934251821 109514494812313424600344433)
        ·
          refine ⟨82135871109235068450258325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109514494812313424600344433 82135871109235068450258325)
          ·
            refine ⟨3850118958245393833605859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82135871109235068450258325 3850118958245393833605859)
            ·
              refine ⟨5775178437368090750408789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850118958245393833605859 5775178437368090750408789)
              ·
                refine ⟨67677872312907313481353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5775178437368090750408789 67677872312907313481353)
                ·
                  rfl

theorem cell23_3558659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 8].length) (baseStart_3558659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558659 prefixEnd_3558659 := by exact prefixLift 3558659
  have htrace : WordTrace (prefixWord ++ tailWord_3558659) baseStart_3558659 baseEnd_3558659 := by
    simpa [prefixWord, tailWord_3558659, baseEnd_3558659] using wordTrace_append hprefix tailTrace_3558659
  have hstable : (prefixWord ++ tailWord_3558659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558659).length < 2 ^ (prefixWord ++ tailWord_3558659).sum := by decide
  have hdescent : baseEnd_3558659 < baseStart_3558659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558674 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3558674 : Nat := 118140960795 + 3558674 * 2 ^ 59
def prefixEnd_3558674 : Nat := 4983230072969 + 3 ^ 40 * 3558674 * 2
def baseEnd_3558674 : Nat := 1827310254658314905308963

theorem tailTrace_3558674 : CollatzResearch.WordTrace tailWord_3558674 prefixEnd_3558674 1827310254658314905308963 := by
  unfold tailWord_3558674
  simp only [CollatzResearch.WordTrace]
  refine ⟨32448875977384836494254769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86530335939692897318012717 32448875977384836494254769)
  ·
    refine ⟨24336656983038627370691077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32448875977384836494254769 24336656983038627370691077)
    ·
      refine ⟨4563123184319742632004577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24336656983038627370691077 4563123184319742632004577)
      ·
        refine ⟨3422342388239806974003433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4563123184319742632004577 3422342388239806974003433)
        ·
          refine ⟨2566756791179855230502575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3422342388239806974003433 2566756791179855230502575)
          ·
            refine ⟨3850135186769782845753863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566756791179855230502575 3850135186769782845753863)
            ·
              refine ⟨5775202780154674268630795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850135186769782845753863 5775202780154674268630795)
              ·
                refine ⟨8662804170232011402946193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5775202780154674268630795 8662804170232011402946193)
                ·
                  refine ⟨6497103127674008552209645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8662804170232011402946193 6497103127674008552209645)
                  ·
                    refine ⟨2436413672877753207078617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6497103127674008552209645 2436413672877753207078617)
                    ·
                      refine ⟨1827310254658314905308963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436413672877753207078617 1827310254658314905308963)
                      ·
                        rfl

theorem cell23_3558674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3558674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558674 prefixEnd_3558674 := by exact prefixLift 3558674
  have htrace : WordTrace (prefixWord ++ tailWord_3558674) baseStart_3558674 baseEnd_3558674 := by
    simpa [prefixWord, tailWord_3558674, baseEnd_3558674] using wordTrace_append hprefix tailTrace_3558674
  have hstable : (prefixWord ++ tailWord_3558674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558674).length < 2 ^ (prefixWord ++ tailWord_3558674).sum := by decide
  have hdescent : baseEnd_3558674 < baseStart_3558674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558687 : List Nat := [1, 1, 2, 4, 4, 1, 2, 3, 1, 2, 2]
def baseStart_3558687 : Nat := 118140960795 + 3558687 * 2 ^ 59
def prefixEnd_3558687 : Nat := 4983230072969 + 3 ^ 40 * 3558687 * 2
def baseEnd_3558687 : Nat := 1827316929906823354446403

theorem tailTrace_3558687 : CollatzResearch.WordTrace tailWord_3558687 prefixEnd_3558687 1827316929906823354446403 := by
  unfold tailWord_3558687
  simp only [CollatzResearch.WordTrace]
  refine ⟨129795978058492249197242315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86530652038994832798161543 129795978058492249197242315)
  ·
    refine ⟨194693967087738373795863473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129795978058492249197242315 194693967087738373795863473)
    ·
      refine ⟨146020475315803780346897605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194693967087738373795863473 146020475315803780346897605)
      ·
        refine ⟨27378839121713208815043301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146020475315803780346897605 27378839121713208815043301)
        ·
          refine ⟨5133532335321226652820619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27378839121713208815043301 5133532335321226652820619)
          ·
            refine ⟨7700298502981839979230929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5133532335321226652820619 7700298502981839979230929)
            ·
              refine ⟨5775223877236379984423197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7700298502981839979230929 5775223877236379984423197)
              ·
                refine ⟨2165708953963642494158699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5775223877236379984423197 2165708953963642494158699)
                ·
                  refine ⟨3248563430945463741238049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165708953963642494158699 3248563430945463741238049)
                  ·
                    refine ⟨2436422573209097805928537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3248563430945463741238049 2436422573209097805928537)
                    ·
                      refine ⟨1827316929906823354446403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436422573209097805928537 1827316929906823354446403)
                      ·
                        rfl

theorem cell23_3558687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_3558687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558687 prefixEnd_3558687 := by exact prefixLift 3558687
  have htrace : WordTrace (prefixWord ++ tailWord_3558687) baseStart_3558687 baseEnd_3558687 := by
    simpa [prefixWord, tailWord_3558687, baseEnd_3558687] using wordTrace_append hprefix tailTrace_3558687
  have hstable : (prefixWord ++ tailWord_3558687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558687).length < 2 ^ (prefixWord ++ tailWord_3558687).sum := by decide
  have hdescent : baseEnd_3558687 < baseStart_3558687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558719 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 2, 6]
def baseStart_3558719 : Nat := 118140960795 + 3558719 * 2 ^ 59
def prefixEnd_3558719 : Nat := 4983230072969 + 3 ^ 40 * 3558719 * 2
def baseEnd_3558719 : Nat := 609111120429255743082085

theorem tailTrace_3558719 : CollatzResearch.WordTrace tailWord_3558719 prefixEnd_3558719 609111120429255743082085 := by
  unfold tailWord_3558719
  simp only [CollatzResearch.WordTrace]
  refine ⟨129797145194376318662407211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86531430129584212441604807 129797145194376318662407211)
  ·
    refine ⟨194695717791564477993610817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129797145194376318662407211 194695717791564477993610817)
    ·
      refine ⟨146021788343673358495208113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194695717791564477993610817 146021788343673358495208113)
      ·
        refine ⟨109516341257755018871406085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146021788343673358495208113 109516341257755018871406085)
        ·
          refine ⟨20534313985829066038388641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109516341257755018871406085 20534313985829066038388641)
          ·
            refine ⟨15400735489371799528791481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20534313985829066038388641 15400735489371799528791481)
            ·
              refine ⟨11550551617028849646593611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15400735489371799528791481 11550551617028849646593611)
              ·
                refine ⟨17325827425543274469890417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11550551617028849646593611 17325827425543274469890417)
                ·
                  refine ⟨12994370569157455852417813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17325827425543274469890417 12994370569157455852417813)
                  ·
                    refine ⟨609111120429255743082085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12994370569157455852417813 609111120429255743082085)
                    ·
                      rfl

theorem cell23_3558719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_3558719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558719 prefixEnd_3558719 := by exact prefixLift 3558719
  have htrace : WordTrace (prefixWord ++ tailWord_3558719) baseStart_3558719 baseEnd_3558719 := by
    simpa [prefixWord, tailWord_3558719, baseEnd_3558719] using wordTrace_append hprefix tailTrace_3558719
  have hstable : (prefixWord ++ tailWord_3558719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558719).length < 2 ^ (prefixWord ++ tailWord_3558719).sum := by decide
  have hdescent : baseEnd_3558719 < baseStart_3558719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558729 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 3]
def baseStart_3558729 : Nat := 118140960795 + 3558729 * 2 ^ 59
def prefixEnd_3558729 : Nat := 4983230072969 + 3 ^ 40 * 3558729 * 2
def baseEnd_3558729 : Nat := 1827338496094312190121209

theorem tailTrace_3558729 : CollatzResearch.WordTrace tailWord_3558729 prefixEnd_3558729 1827338496094312190121209 := by
  unfold tailWord_3558729
  simp only [CollatzResearch.WordTrace]
  refine ⟨129797509924340090370271241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86531673282893393580180827 129797509924340090370271241)
  ·
    refine ⟨97348132443255067777703431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129797509924340090370271241 97348132443255067777703431)
    ·
      refine ⟨146022198664882601666555147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97348132443255067777703431 146022198664882601666555147)
      ·
        refine ⟨219033297997323902499832721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146022198664882601666555147 219033297997323902499832721)
        ·
          refine ⟨164274973497992926874874541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219033297997323902499832721 164274973497992926874874541)
          ·
            refine ⟨61603115061747347578077953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164274973497992926874874541 61603115061747347578077953)
            ·
              refine ⟨46202336296310510683558465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61603115061747347578077953 46202336296310510683558465)
              ·
                refine ⟨34651752222232883012668849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46202336296310510683558465 34651752222232883012668849)
                ·
                  refine ⟨25988814166674662259501637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34651752222232883012668849 25988814166674662259501637)
                  ·
                    refine ⟨4872902656251499173656557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25988814166674662259501637 4872902656251499173656557)
                    ·
                      refine ⟨1827338496094312190121209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4872902656251499173656557 1827338496094312190121209)
                      ·
                        rfl

theorem cell23_3558729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 3].length) (baseStart_3558729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558729 prefixEnd_3558729 := by exact prefixLift 3558729
  have htrace : WordTrace (prefixWord ++ tailWord_3558729) baseStart_3558729 baseEnd_3558729 := by
    simpa [prefixWord, tailWord_3558729, baseEnd_3558729] using wordTrace_append hprefix tailTrace_3558729
  have hstable : (prefixWord ++ tailWord_3558729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558729).length < 2 ^ (prefixWord ++ tailWord_3558729).sum := by decide
  have hdescent : baseEnd_3558729 < baseStart_3558729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558743 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 4, 2, 2]
def baseStart_3558743 : Nat := 118140960795 + 3558743 * 2 ^ 59
def prefixEnd_3558743 : Nat := 4983230072969 + 3 ^ 40 * 3558743 * 2
def baseEnd_3558743 : Nat := 1827345684823475135346145

theorem tailTrace_3558743 : CollatzResearch.WordTrace tailWord_3558743 prefixEnd_3558743 1827345684823475135346145 := by
  unfold tailWord_3558743
  simp only [CollatzResearch.WordTrace]
  refine ⟨129798020546289370761280883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86532013697526247174187255 129798020546289370761280883)
  ·
    refine ⟨194697030819434056141921325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129798020546289370761280883 194697030819434056141921325)
    ·
      refine ⟨73011386557287771053220497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194697030819434056141921325 73011386557287771053220497)
      ·
        refine ⟨54758539917965828289915373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73011386557287771053220497 54758539917965828289915373)
        ·
          refine ⟨20534452469237185608718265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54758539917965828289915373 20534452469237185608718265)
          ·
            refine ⟨15400839351927889206538699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20534452469237185608718265 15400839351927889206538699)
            ·
              refine ⟨23101259027891833809808049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15400839351927889206538699 23101259027891833809808049)
              ·
                refine ⟨17325944270918875357356037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23101259027891833809808049 17325944270918875357356037)
                ·
                  refine ⟨3248614550797289129504257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17325944270918875357356037 3248614550797289129504257)
                  ·
                    refine ⟨2436460913097966847128193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3248614550797289129504257 2436460913097966847128193)
                    ·
                      refine ⟨1827345684823475135346145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436460913097966847128193 1827345684823475135346145)
                      ·
                        rfl

theorem cell23_3558743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_3558743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558743 prefixEnd_3558743 := by exact prefixLift 3558743
  have htrace : WordTrace (prefixWord ++ tailWord_3558743) baseStart_3558743 baseEnd_3558743 := by
    simpa [prefixWord, tailWord_3558743, baseEnd_3558743] using wordTrace_append hprefix tailTrace_3558743
  have hstable : (prefixWord ++ tailWord_3558743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558743).length < 2 ^ (prefixWord ++ tailWord_3558743).sum := by decide
  have hdescent : baseEnd_3558743 < baseStart_3558743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558779 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 4, 5]
def baseStart_3558779 : Nat := 118140960795 + 3558779 * 2 ^ 59
def prefixEnd_3558779 : Nat := 4983230072969 + 3 ^ 40 * 3558779 * 2
def baseEnd_3558779 : Nat := 609121390042345664831993

theorem tailTrace_3558779 : CollatzResearch.WordTrace tailWord_3558779 prefixEnd_3558779 609121390042345664831993 := by
  unfold tailWord_3558779
  simp only [CollatzResearch.WordTrace]
  refine ⟨129799333574158948909591391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86532889049439299273060927 129799333574158948909591391)
  ·
    refine ⟨194699000361238423364387087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129799333574158948909591391 194699000361238423364387087)
    ·
      refine ⟨292048500541857635046580631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194699000361238423364387087 292048500541857635046580631)
      ·
        refine ⟨438072750812786452569870947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292048500541857635046580631 438072750812786452569870947)
        ·
          refine ⟨657109126219179678854806421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438072750812786452569870947 657109126219179678854806421)
          ·
            refine ⟨30801990291524047446319051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 657109126219179678854806421 30801990291524047446319051)
            ·
              refine ⟨46202985437286071169478577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30801990291524047446319051 46202985437286071169478577)
              ·
                refine ⟨34652239077964553377108933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46202985437286071169478577 34652239077964553377108933)
                ·
                  refine ⟨6497294827118353758207925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34652239077964553377108933 6497294827118353758207925)
                  ·
                    refine ⟨609121390042345664831993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6497294827118353758207925 609121390042345664831993)
                    ·
                      rfl

theorem cell23_3558779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 5].length) (baseStart_3558779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558779 prefixEnd_3558779 := by exact prefixLift 3558779
  have htrace : WordTrace (prefixWord ++ tailWord_3558779) baseStart_3558779 baseEnd_3558779 := by
    simpa [prefixWord, tailWord_3558779, baseEnd_3558779] using wordTrace_append hprefix tailTrace_3558779
  have hstable : (prefixWord ++ tailWord_3558779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558779).length < 2 ^ (prefixWord ++ tailWord_3558779).sum := by decide
  have hdescent : baseEnd_3558779 < baseStart_3558779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558796 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_3558796 : Nat := 118140960795 + 3558796 * 2 ^ 59
def prefixEnd_3558796 : Nat := 4983230072969 + 3 ^ 40 * 3558796 * 2
def baseEnd_3558796 : Nat := 609124299766054475994467

theorem tailTrace_3558796 : CollatzResearch.WordTrace tailWord_3558796 prefixEnd_3558796 609124299766054475994467 := by
  unfold tailWord_3558796
  simp only [CollatzResearch.WordTrace]
  refine ⟨64899976807548680406480121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86533302410064907208640161 64899976807548680406480121)
  ·
    refine ⟨48674982605661510304860091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64899976807548680406480121 48674982605661510304860091)
    ·
      refine ⟨73012473908492265457290137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48674982605661510304860091 73012473908492265457290137)
      ·
        refine ⟨54759355431369199092967603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73012473908492265457290137 54759355431369199092967603)
        ·
          refine ⟨82139033147053798639451405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54759355431369199092967603 82139033147053798639451405)
          ·
            refine ⟨30802137430145174489794277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82139033147053798639451405 30802137430145174489794277)
            ·
              refine ⟨5775400768152220216836427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30802137430145174489794277 5775400768152220216836427)
              ·
                refine ⟨8663101152228330325254641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5775400768152220216836427 8663101152228330325254641)
                ·
                  refine ⟨6497325864171247743940981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8663101152228330325254641 6497325864171247743940981)
                  ·
                    refine ⟨609124299766054475994467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6497325864171247743940981 609124299766054475994467)
                    ·
                      rfl

theorem cell23_3558796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_3558796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558796 prefixEnd_3558796 := by exact prefixLift 3558796
  have htrace : WordTrace (prefixWord ++ tailWord_3558796) baseStart_3558796 baseEnd_3558796 := by
    simpa [prefixWord, tailWord_3558796, baseEnd_3558796] using wordTrace_append hprefix tailTrace_3558796
  have hstable : (prefixWord ++ tailWord_3558796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558796).length < 2 ^ (prefixWord ++ tailWord_3558796).sum := by decide
  have hdescent : baseEnd_3558796 < baseStart_3558796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558816 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 4]
def baseStart_3558816 : Nat := 118140960795 + 3558816 * 2 ^ 59
def prefixEnd_3558816 : Nat := 4983230072969 + 3 ^ 40 * 3558816 * 2
def baseEnd_3558816 : Nat := 1827383168911253349733309

theorem tailTrace_3558816 : CollatzResearch.WordTrace tailWord_3558816 prefixEnd_3558816 1827383168911253349733309 := by
  unfold tailWord_3558816
  simp only [CollatzResearch.WordTrace]
  refine ⟨64900341537512452114344151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86533788716683269485792201 64900341537512452114344151)
  ·
    refine ⟨97350512306268678171516227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64900341537512452114344151 97350512306268678171516227)
    ·
      refine ⟨146025768459403017257274341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97350512306268678171516227 146025768459403017257274341)
      ·
        refine ⟨27379831586138065735738939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146025768459403017257274341 27379831586138065735738939)
        ·
          refine ⟨41069747379207098603608409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27379831586138065735738939 41069747379207098603608409)
          ·
            refine ⟨30802310534405323952706307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41069747379207098603608409 30802310534405323952706307)
            ·
              refine ⟨46203465801607985929059461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30802310534405323952706307 46203465801607985929059461)
              ·
                refine ⟨8663149837801497361698649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46203465801607985929059461 8663149837801497361698649)
                ·
                  refine ⟨6497362378351123021273987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8663149837801497361698649 6497362378351123021273987)
                  ·
                    refine ⟨9746043567526684531910981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6497362378351123021273987 9746043567526684531910981)
                    ·
                      refine ⟨1827383168911253349733309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9746043567526684531910981 1827383168911253349733309)
                      ·
                        rfl

theorem cell23_3558816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_3558816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558816 prefixEnd_3558816 := by exact prefixLift 3558816
  have htrace : WordTrace (prefixWord ++ tailWord_3558816) baseStart_3558816 baseEnd_3558816 := by
    simpa [prefixWord, tailWord_3558816, baseEnd_3558816] using wordTrace_append hprefix tailTrace_3558816
  have hstable : (prefixWord ++ tailWord_3558816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558816).length < 2 ^ (prefixWord ++ tailWord_3558816).sum := by decide
  have hdescent : baseEnd_3558816 < baseStart_3558816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558819 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 5]
def baseStart_3558819 : Nat := 118140960795 + 3558819 * 2 ^ 59
def prefixEnd_3558819 : Nat := 4983230072969 + 3 ^ 40 * 3558819 * 2
def baseEnd_3558819 : Nat := 1827384709353216837995795

theorem tailTrace_3558819 : CollatzResearch.WordTrace tailWord_3558819 prefixEnd_3558819 1827384709353216837995795 := by
  unfold tailWord_3558819
  simp only [CollatzResearch.WordTrace]
  refine ⟨129800792494014035741047511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86533861662676023827365007 129800792494014035741047511)
  ·
    refine ⟨194701188741021053611571267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129800792494014035741047511 194701188741021053611571267)
    ·
      refine ⟨292051783111531580417356901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194701188741021053611571267 292051783111531580417356901)
      ·
        refine ⟨54759709333412171328254419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292051783111531580417356901 54759709333412171328254419)
        ·
          refine ⟨82139564000118256992381629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54759709333412171328254419 82139564000118256992381629)
          ·
            refine ⟨30802336500044346372143111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82139564000118256992381629 30802336500044346372143111)
            ·
              refine ⟨46203504750066519558214667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30802336500044346372143111 46203504750066519558214667)
              ·
                refine ⟨69305257125099779337322001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46203504750066519558214667 69305257125099779337322001)
                ·
                  refine ⟨51978942843824834502991501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69305257125099779337322001 51978942843824834502991501)
                  ·
                    refine ⟨19492103566434312938621813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51978942843824834502991501 19492103566434312938621813)
                    ·
                      refine ⟨1827384709353216837995795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19492103566434312938621813 1827384709353216837995795)
                      ·
                        rfl

theorem cell23_3558819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_3558819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558819 prefixEnd_3558819 := by exact prefixLift 3558819
  have htrace : WordTrace (prefixWord ++ tailWord_3558819) baseStart_3558819 baseEnd_3558819 := by
    simpa [prefixWord, tailWord_3558819, baseEnd_3558819] using wordTrace_append hprefix tailTrace_3558819
  have hstable : (prefixWord ++ tailWord_3558819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558819).length < 2 ^ (prefixWord ++ tailWord_3558819).sum := by decide
  have hdescent : baseEnd_3558819 < baseStart_3558819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558833 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 2, 4, 2]
def baseStart_3558833 : Nat := 118140960795 + 3558833 * 2 ^ 59
def prefixEnd_3558833 : Nat := 4983230072969 + 3 ^ 40 * 3558833 * 2
def baseEnd_3558833 : Nat := 1827391898082379783220731

theorem tailTrace_3558833 : CollatzResearch.WordTrace tailWord_3558833 prefixEnd_3558833 1827391898082379783220731 := by
  unfold tailWord_3558833
  simp only [CollatzResearch.WordTrace]
  refine ⟨129801303115963316132057153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86534202077308877421371435 129801303115963316132057153)
  ·
    refine ⟨97350977336972487099042865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129801303115963316132057153 97350977336972487099042865)
    ·
      refine ⟨73013233002729365324282149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97350977336972487099042865 73013233002729365324282149)
      ·
        refine ⟨13689981188011755998302903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73013233002729365324282149 13689981188011755998302903)
        ·
          refine ⟨20534971782017633997454355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13689981188011755998302903 20534971782017633997454355)
          ·
            refine ⟨30802457673026450996181533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20534971782017633997454355 30802457673026450996181533)
            ·
              refine ⟨11550921627384919123568075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30802457673026450996181533 11550921627384919123568075)
              ·
                refine ⟨17326382441077378685352113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11550921627384919123568075 17326382441077378685352113)
                ·
                  refine ⟨12994786830808034014014085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17326382441077378685352113 12994786830808034014014085)
                  ·
                    refine ⟨2436522530776506377627641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12994786830808034014014085 2436522530776506377627641)
                    ·
                      refine ⟨1827391898082379783220731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436522530776506377627641 1827391898082379783220731)
                      ·
                        rfl

theorem cell23_3558833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_3558833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558833 prefixEnd_3558833 := by exact prefixLift 3558833
  have htrace : WordTrace (prefixWord ++ tailWord_3558833) baseStart_3558833 baseEnd_3558833 := by
    simpa [prefixWord, tailWord_3558833, baseEnd_3558833] using wordTrace_append hprefix tailTrace_3558833
  have hstable : (prefixWord ++ tailWord_3558833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558833).length < 2 ^ (prefixWord ++ tailWord_3558833).sum := by decide
  have hdescent : baseEnd_3558833 < baseStart_3558833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558860 : List Nat := [2, 2, 1, 4, 2, 1, 1, 5, 1, 4]
def baseStart_3558860 : Nat := 118140960795 + 3558860 * 2 ^ 59
def prefixEnd_3558860 : Nat := 4983230072969 + 3 ^ 40 * 3558860 * 2
def baseEnd_3558860 : Nat := 609135254020017059194369

theorem tailTrace_3558860 : CollatzResearch.WordTrace tailWord_3558860 prefixEnd_3558860 609135254020017059194369 := by
  unfold tailWord_3558860
  simp only [CollatzResearch.WordTrace]
  refine ⟨64901143943432749871645017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86534858591243666495526689 64901143943432749871645017)
  ·
    refine ⟨48675857957574562403733763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64901143943432749871645017 48675857957574562403733763)
    ·
      refine ⟨73013786936361843605600645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48675857957574562403733763 73013786936361843605600645)
      ·
        refine ⟨13690085050567845676050121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73013786936361843605600645 13690085050567845676050121)
        ·
          refine ⟨10267563787925884257037591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13690085050567845676050121 10267563787925884257037591)
          ·
            refine ⟨15401345681888826385556387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10267563787925884257037591 15401345681888826385556387)
            ·
              refine ⟨23102018522833239578334581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15401345681888826385556387 23102018522833239578334581)
              ·
                refine ⟨2165814236515616210468867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23102018522833239578334581 2165814236515616210468867)
                ·
                  refine ⟨3248721354773424315703301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165814236515616210468867 3248721354773424315703301)
                  ·
                    refine ⟨609135254020017059194369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3248721354773424315703301 609135254020017059194369)
                    ·
                      rfl

theorem cell23_3558860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_3558860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558860 prefixEnd_3558860 := by exact prefixLift 3558860
  have htrace : WordTrace (prefixWord ++ tailWord_3558860) baseStart_3558860 baseEnd_3558860 := by
    simpa [prefixWord, tailWord_3558860, baseEnd_3558860] using wordTrace_append hprefix tailTrace_3558860
  have hstable : (prefixWord ++ tailWord_3558860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558860).length < 2 ^ (prefixWord ++ tailWord_3558860).sum := by decide
  have hdescent : baseEnd_3558860 < baseStart_3558860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558873 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 6]
def baseStart_3558873 : Nat := 118140960795 + 3558873 * 2 ^ 59
def prefixEnd_3558873 : Nat := 4983230072969 + 3 ^ 40 * 3558873 * 2
def baseEnd_3558873 : Nat := 203045826367617736302283

theorem tailTrace_3558873 : CollatzResearch.WordTrace tailWord_3558873 prefixEnd_3558873 203045826367617736302283 := by
  unfold tailWord_3558873
  simp only [CollatzResearch.WordTrace]
  refine ⟨129802762035818402963513273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86535174690545601975675515 129802762035818402963513273)
  ·
    refine ⟨97352071526863802222634955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129802762035818402963513273 97352071526863802222634955)
    ·
      refine ⟨146028107290295703333952433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97352071526863802222634955 146028107290295703333952433)
      ·
        refine ⟨109521080467721777500464325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146028107290295703333952433 109521080467721777500464325)
        ·
          refine ⟨20535202587697833281337061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109521080467721777500464325 20535202587697833281337061)
          ·
            refine ⟨3850350485193343740250699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20535202587697833281337061 3850350485193343740250699)
            ·
              refine ⟨5775525727790015610376049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850350485193343740250699 5775525727790015610376049)
              ·
                refine ⟨4331644295842511707782037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5775525727790015610376049 4331644295842511707782037)
                ·
                  refine ⟨203045826367617736302283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4331644295842511707782037 203045826367617736302283)
                  ·
                    rfl

theorem cell23_3558873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 6].length) (baseStart_3558873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558873 prefixEnd_3558873 := by exact prefixLift 3558873
  have htrace : WordTrace (prefixWord ++ tailWord_3558873) baseStart_3558873 baseEnd_3558873 := by
    simpa [prefixWord, tailWord_3558873, baseEnd_3558873] using wordTrace_append hprefix tailTrace_3558873
  have hstable : (prefixWord ++ tailWord_3558873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558873).length < 2 ^ (prefixWord ++ tailWord_3558873).sum := by decide
  have hdescent : baseEnd_3558873 < baseStart_3558873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558890 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 6]
def baseStart_3558890 : Nat := 118140960795 + 3558890 * 2 ^ 59
def prefixEnd_3558890 : Nat := 4983230072969 + 3 ^ 40 * 3558890 * 2
def baseEnd_3558890 : Nat := 203046796275520673356441

theorem tailTrace_3558890 : CollatzResearch.WordTrace tailWord_3558890 prefixEnd_3558890 203046796275520673356441 := by
  unfold tailWord_3558890
  simp only [CollatzResearch.WordTrace]
  refine ⟨32450845519189203716720531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86535588051171209911254749 32450845519189203716720531)
  ·
    refine ⟨48676268278783805575080797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32450845519189203716720531 48676268278783805575080797)
    ·
      refine ⟨18253600604543927090655299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48676268278783805575080797 18253600604543927090655299)
      ·
        refine ⟨27380400906815890635982949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18253600604543927090655299 27380400906815890635982949)
        ·
          refine ⟨5133825170027979494246803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27380400906815890635982949 5133825170027979494246803)
          ·
            refine ⟨7700737755041969241370205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5133825170027979494246803 7700737755041969241370205)
            ·
              refine ⟨2887776658140738465513827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7700737755041969241370205 2887776658140738465513827)
              ·
                refine ⟨4331664987211107698270741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887776658140738465513827 4331664987211107698270741)
                ·
                  refine ⟨203046796275520673356441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4331664987211107698270741 203046796275520673356441)
                  ·
                    rfl

theorem cell23_3558890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_3558890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558890 prefixEnd_3558890 := by exact prefixLift 3558890
  have htrace : WordTrace (prefixWord ++ tailWord_3558890) baseStart_3558890 baseEnd_3558890 := by
    simpa [prefixWord, tailWord_3558890, baseEnd_3558890] using wordTrace_append hprefix tailTrace_3558890
  have hstable : (prefixWord ++ tailWord_3558890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558890).length < 2 ^ (prefixWord ++ tailWord_3558890).sum := by decide
  have hdescent : baseEnd_3558890 < baseStart_3558890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558933 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_3558933 : Nat := 118140960795 + 3558933 * 2 ^ 59
def prefixEnd_3558933 : Nat := 4983230072969 + 3 ^ 40 * 3558933 * 2
def baseEnd_3558933 : Nat := 609147748715943130656757

theorem tailTrace_3558933 : CollatzResearch.WordTrace tailWord_3558933 prefixEnd_3558933 609147748715943130656757 := by
  unfold tailWord_3558933
  simp only [CollatzResearch.WordTrace]
  refine ⟨129804950415601033210697453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86536633610400688807131635 129804950415601033210697453)
  ·
    refine ⟨48676856405850387454011545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129804950415601033210697453 48676856405850387454011545)
    ·
      refine ⟨36507642304387790590508659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48676856405850387454011545 36507642304387790590508659)
      ·
        refine ⟨54761463456581685885762989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36507642304387790590508659 54761463456581685885762989)
        ·
          refine ⟨20535548796218132207161121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54761463456581685885762989 20535548796218132207161121)
          ·
            refine ⟨15401661597163599155370841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20535548796218132207161121 15401661597163599155370841)
            ·
              refine ⟨11551246197872699366528131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15401661597163599155370841 11551246197872699366528131)
              ·
                refine ⟨17326869296809049049792197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11551246197872699366528131 17326869296809049049792197)
                ·
                  refine ⟨3248787993151696696836037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17326869296809049049792197 3248787993151696696836037)
                  ·
                    refine ⟨609147748715943130656757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3248787993151696696836037 609147748715943130656757)
                    ·
                      rfl

theorem cell23_3558933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_3558933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558933 prefixEnd_3558933 := by exact prefixLift 3558933
  have htrace : WordTrace (prefixWord ++ tailWord_3558933) baseStart_3558933 baseEnd_3558933 := by
    simpa [prefixWord, tailWord_3558933, baseEnd_3558933] using wordTrace_append hprefix tailTrace_3558933
  have hstable : (prefixWord ++ tailWord_3558933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558933).length < 2 ^ (prefixWord ++ tailWord_3558933).sum := by decide
  have hdescent : baseEnd_3558933 < baseStart_3558933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558946 : List Nat := [3, 3, 1, 1, 1, 1, 3, 10]
def baseStart_3558946 : Nat := 118140960795 + 3558946 * 2 ^ 59
def prefixEnd_3558946 : Nat := 4983230072969 + 3 ^ 40 * 3558946 * 2
def baseEnd_3558946 : Nat := 67683330422086586707693

theorem tailTrace_3558946 : CollatzResearch.WordTrace tailWord_3558946 prefixEnd_3558946 67683330422086586707693 := by
  unfold tailWord_3558946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32451356141138484107730173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86536949709702624287280461 32451356141138484107730173)
  ·
    refine ⟨12169258552926931540398815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32451356141138484107730173 12169258552926931540398815)
    ·
      refine ⟨18253887829390397310598223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12169258552926931540398815 18253887829390397310598223)
      ·
        refine ⟨27380831744085595965897335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18253887829390397310598223 27380831744085595965897335)
        ·
          refine ⟨41071247616128393948846003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27380831744085595965897335 41071247616128393948846003)
          ·
            refine ⟨61606871424192590923269005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41071247616128393948846003 61606871424192590923269005)
            ·
              refine ⟨23102576784072221596225877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61606871424192590923269005 23102576784072221596225877)
              ·
                refine ⟨67683330422086586707693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23102576784072221596225877 67683330422086586707693)
                ·
                  rfl

theorem cell23_3558946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 10].length) (baseStart_3558946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558946 prefixEnd_3558946 := by exact prefixLift 3558946
  have htrace : WordTrace (prefixWord ++ tailWord_3558946) baseStart_3558946 baseEnd_3558946 := by
    simpa [prefixWord, tailWord_3558946, baseEnd_3558946] using wordTrace_append hprefix tailTrace_3558946
  have hstable : (prefixWord ++ tailWord_3558946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558946).length < 2 ^ (prefixWord ++ tailWord_3558946).sum := by decide
  have hdescent : baseEnd_3558946 < baseStart_3558946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558977 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_3558977 : Nat := 118140960795 + 3558977 * 2 ^ 59
def prefixEnd_3558977 : Nat := 4983230072969 + 3 ^ 40 * 3558977 * 2
def baseEnd_3558977 : Nat := 1827465839296627219820069

theorem tailTrace_3558977 : CollatzResearch.WordTrace tailWord_3558977 prefixEnd_3558977 1827465839296627219820069 := by
  unfold tailWord_3558977
  simp only [CollatzResearch.WordTrace]
  refine ⟨129806555227441628725299185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86537703484961085816866123 129806555227441628725299185)
  ·
    refine ⟨97354916420581221543974389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129806555227441628725299185 97354916420581221543974389)
    ·
      refine ⟨9127023414429489519747599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97354916420581221543974389 9127023414429489519747599)
      ·
        refine ⟨13690535121644234279621399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9127023414429489519747599 13690535121644234279621399)
        ·
          refine ⟨20535802682466351419432099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13690535121644234279621399 20535802682466351419432099)
          ·
            refine ⟨30803704023699527129148149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20535802682466351419432099 30803704023699527129148149)
            ·
              refine ⟨2887847252221830668357639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30803704023699527129148149 2887847252221830668357639)
              ·
                refine ⟨4331770878332746002536459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887847252221830668357639 4331770878332746002536459)
                ·
                  refine ⟨6497656317499119003804689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4331770878332746002536459 6497656317499119003804689)
                  ·
                    refine ⟨4873242238124339252853517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6497656317499119003804689 4873242238124339252853517)
                    ·
                      refine ⟨1827465839296627219820069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4873242238124339252853517 1827465839296627219820069)
                      ·
                        rfl

theorem cell23_3558977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_3558977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3558977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3558977 prefixEnd_3558977 := by exact prefixLift 3558977
  have htrace : WordTrace (prefixWord ++ tailWord_3558977) baseStart_3558977 baseEnd_3558977 := by
    simpa [prefixWord, tailWord_3558977, baseEnd_3558977] using wordTrace_append hprefix tailTrace_3558977
  have hstable : (prefixWord ++ tailWord_3558977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558977).length < 2 ^ (prefixWord ++ tailWord_3558977).sum := by decide
  have hdescent : baseEnd_3558977 < baseStart_3558977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559036 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 11]
def baseStart_3559036 : Nat := 118140960795 + 3559036 * 2 ^ 59
def prefixEnd_3559036 : Nat := 4983230072969 + 3 ^ 40 * 3559036 * 2
def baseEnd_3559036 : Nat := 203055126072804720998033

theorem tailTrace_3559036 : CollatzResearch.WordTrace tailWord_3559036 prefixEnd_3559036 203055126072804720998033 := by
  unfold tailWord_3559036
  simp only [CollatzResearch.WordTrace]
  refine ⟨64904353567113940900848481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86539138089485254534464641 64904353567113940900848481)
  ·
    refine ⟨48678265175335455675636361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64904353567113940900848481 48678265175335455675636361)
    ·
      refine ⟨36508698881501591756727271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48678265175335455675636361 36508698881501591756727271)
      ·
        refine ⟨54763048322252387635090907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36508698881501591756727271 54763048322252387635090907)
        ·
          refine ⟨82144572483378581452636361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54763048322252387635090907 82144572483378581452636361)
          ·
            refine ⟨61608429362533936089477271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82144572483378581452636361 61608429362533936089477271)
            ·
              refine ⟨92412644043800904134215907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61608429362533936089477271 92412644043800904134215907)
              ·
                refine ⟨138618966065701356201323861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92412644043800904134215907 138618966065701356201323861)
                ·
                  refine ⟨203055126072804720998033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 138618966065701356201323861 203055126072804720998033)
                  ·
                    rfl

theorem cell23_3559036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_3559036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559036 prefixEnd_3559036 := by exact prefixLift 3559036
  have htrace : WordTrace (prefixWord ++ tailWord_3559036) baseStart_3559036 baseEnd_3559036 := by
    simpa [prefixWord, tailWord_3559036, baseEnd_3559036] using wordTrace_append hprefix tailTrace_3559036
  have hstable : (prefixWord ++ tailWord_3559036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559036).length < 2 ^ (prefixWord ++ tailWord_3559036).sum := by decide
  have hdescent : baseEnd_3559036 < baseStart_3559036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559047 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 4, 2, 2]
def baseStart_3559047 : Nat := 118140960795 + 3559047 * 2 ^ 59
def prefixEnd_3559047 : Nat := 4983230072969 + 3 ^ 40 * 3559047 * 2
def baseEnd_3559047 : Nat := 1827501782942441945944747

theorem tailTrace_3559047 : CollatzResearch.WordTrace tailWord_3559047 prefixEnd_3559047 1827501782942441945944747 := by
  unfold tailWord_3559047
  simp only [CollatzResearch.WordTrace]
  refine ⟨129809108337188030680347395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86539405558125353786898263 129809108337188030680347395)
  ·
    refine ⟨194713662505782046020521093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129809108337188030680347395 194713662505782046020521093)
    ·
      refine ⟨36508811719834133628847705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194713662505782046020521093 36508811719834133628847705)
      ·
        refine ⟨27381608789875600221635779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36508811719834133628847705 27381608789875600221635779)
        ·
          refine ⟨41072413184813400332453669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27381608789875600221635779 41072413184813400332453669)
          ·
            refine ⟨7701077472152512562335063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41072413184813400332453669 7701077472152512562335063)
            ·
              refine ⟨11551616208228768843502595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7701077472152512562335063 11551616208228768843502595)
              ·
                refine ⟨17327424312343153265253893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11551616208228768843502595 17327424312343153265253893)
                ·
                  refine ⟨3248892058564341237235105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17327424312343153265253893 3248892058564341237235105)
                  ·
                    refine ⟨2436669043923255927926329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3248892058564341237235105 2436669043923255927926329)
                    ·
                      refine ⟨1827501782942441945944747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436669043923255927926329 1827501782942441945944747)
                      ·
                        rfl

theorem cell23_3559047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_3559047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559047 prefixEnd_3559047 := by exact prefixLift 3559047
  have htrace : WordTrace (prefixWord ++ tailWord_3559047) baseStart_3559047 baseEnd_3559047 := by
    simpa [prefixWord, tailWord_3559047, baseEnd_3559047] using wordTrace_append hprefix tailTrace_3559047
  have hstable : (prefixWord ++ tailWord_3559047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559047).length < 2 ^ (prefixWord ++ tailWord_3559047).sum := by decide
  have hdescent : baseEnd_3559047 < baseStart_3559047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559070 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_3559070 : Nat := 118140960795 + 3559070 * 2 ^ 59
def prefixEnd_3559070 : Nat := 4983230072969 + 3 ^ 40 * 3559070 * 2
def baseEnd_3559070 : Nat := 203057065888610595106349

theorem tailTrace_3559070 : CollatzResearch.WordTrace tailWord_3559070 prefixEnd_3559070 203057065888610595106349 := by
  unfold tailWord_3559070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16226243402013088201054333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86539964810736470405623109 16226243402013088201054333)
  ·
    refine ⟨6084841275754908075395375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16226243402013088201054333 6084841275754908075395375)
    ·
      refine ⟨9127261913632362113093063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6084841275754908075395375 9127261913632362113093063)
      ·
        refine ⟨13690892870448543169639595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9127261913632362113093063 13690892870448543169639595)
        ·
          refine ⟨20536339305672814754459393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13690892870448543169639595 20536339305672814754459393)
          ·
            refine ⟨15402254479254611065844545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20536339305672814754459393 15402254479254611065844545)
            ·
              refine ⟨11551690859440958299383409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15402254479254611065844545 11551690859440958299383409)
              ·
                refine ⟨8663768144580718724537557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11551690859440958299383409 8663768144580718724537557)
                ·
                  refine ⟨203057065888610595106349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8663768144580718724537557 203057065888610595106349)
                  ·
                    rfl

theorem cell23_3559070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_3559070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559070 prefixEnd_3559070 := by exact prefixLift 3559070
  have htrace : WordTrace (prefixWord ++ tailWord_3559070) baseStart_3559070 baseEnd_3559070 := by
    simpa [prefixWord, tailWord_3559070, baseEnd_3559070] using wordTrace_append hprefix tailTrace_3559070
  have hstable : (prefixWord ++ tailWord_3559070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559070).length < 2 ^ (prefixWord ++ tailWord_3559070).sum := by decide
  have hdescent : baseEnd_3559070 < baseStart_3559070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559100 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_3559100 : Nat := 118140960795 + 3559100 * 2 ^ 59
def prefixEnd_3559100 : Nat := 4983230072969 + 3 ^ 40 * 3559100 * 2
def baseEnd_3559100 : Nat := 609176332472376746194001

theorem tailTrace_3559100 : CollatzResearch.WordTrace tailWord_3559100 prefixEnd_3559100 609176332472376746194001 := by
  unfold tailWord_3559100
  simp only [CollatzResearch.WordTrace]
  refine ⟨64905520702998010366013377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86540694270664013821351169 64905520702998010366013377)
  ·
    refine ⟨48679140527248507774510033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64905520702998010366013377 48679140527248507774510033)
    ·
      refine ⟨36509355395436380830882525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48679140527248507774510033 36509355395436380830882525)
      ·
        refine ⟨13691008273288642811580947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36509355395436380830882525 13691008273288642811580947)
        ·
          refine ⟨20536512409932964217371421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13691008273288642811580947 20536512409932964217371421)
          ·
            refine ⟨7701192153724861581514283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20536512409932964217371421 7701192153724861581514283)
            ·
              refine ⟨11551788230587292372271425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7701192153724861581514283 11551788230587292372271425)
              ·
                refine ⟨8663841172940469279203569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11551788230587292372271425 8663841172940469279203569)
                ·
                  refine ⟨6497880879705351959402677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8663841172940469279203569 6497880879705351959402677)
                  ·
                    refine ⟨609176332472376746194001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6497880879705351959402677 609176332472376746194001)
                    ·
                      rfl

theorem cell23_3559100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_3559100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559100 prefixEnd_3559100 := by exact prefixLift 3559100
  have htrace : WordTrace (prefixWord ++ tailWord_3559100) baseStart_3559100 baseEnd_3559100 := by
    simpa [prefixWord, tailWord_3559100, baseEnd_3559100] using wordTrace_append hprefix tailTrace_3559100
  have hstable : (prefixWord ++ tailWord_3559100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559100).length < 2 ^ (prefixWord ++ tailWord_3559100).sum := by decide
  have hdescent : baseEnd_3559100 < baseStart_3559100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559137 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_3559137 : Nat := 118140960795 + 3559137 * 2 ^ 59
def prefixEnd_3559137 : Nat := 4983230072969 + 3 ^ 40 * 3559137 * 2
def baseEnd_3559137 : Nat := 1827547996201346593819333

theorem tailTrace_3559137 : CollatzResearch.WordTrace tailWord_3559137 prefixEnd_3559137 1827547996201346593819333 := by
  unfold tailWord_3559137
  simp only [CollatzResearch.WordTrace]
  refine ⟨129812390906861976051123665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86541593937907984034082443 129812390906861976051123665)
  ·
    refine ⟨97359293180146482038342749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129812390906861976051123665 97359293180146482038342749)
    ·
      refine ⟨36509734942554930764378531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97359293180146482038342749 36509734942554930764378531)
      ·
        refine ⟨54764602413832396146567797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36509734942554930764378531 54764602413832396146567797)
        ·
          refine ⟨5134181476296787138740731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54764602413832396146567797 5134181476296787138740731)
          ·
            refine ⟨7701272214445180708111097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5134181476296787138740731 7701272214445180708111097)
            ·
              refine ⟨5775954160833885531083323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7701272214445180708111097 5775954160833885531083323)
              ·
                refine ⟨8663931241250828296624985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5775954160833885531083323 8663931241250828296624985)
                ·
                  refine ⟨6497948430938121222468739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8663931241250828296624985 6497948430938121222468739)
                  ·
                    refine ⟨9746922646407181833703109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6497948430938121222468739 9746922646407181833703109)
                    ·
                      refine ⟨1827547996201346593819333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9746922646407181833703109 1827547996201346593819333)
                      ·
                        rfl

theorem cell23_3559137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_3559137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559137 prefixEnd_3559137 := by exact prefixLift 3559137
  have htrace : WordTrace (prefixWord ++ tailWord_3559137) baseStart_3559137 baseEnd_3559137 := by
    simpa [prefixWord, tailWord_3559137, baseEnd_3559137] using wordTrace_append hprefix tailTrace_3559137
  have hstable : (prefixWord ++ tailWord_3559137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559137).length < 2 ^ (prefixWord ++ tailWord_3559137).sum := by decide
  have hdescent : baseEnd_3559137 < baseStart_3559137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559188 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3559188 : Nat := 118140960795 + 3559188 * 2 ^ 59
def prefixEnd_3559188 : Nat := 4983230072969 + 3 ^ 40 * 3559188 * 2
def baseEnd_3559188 : Nat := 1827574183714725894281599

theorem tailTrace_3559188 : CollatzResearch.WordTrace tailWord_3559188 prefixEnd_3559188 1827574183714725894281599 := by
  unfold tailWord_3559188
  simp only [CollatzResearch.WordTrace]
  refine ⟨64907125514838605880615109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86542834019784807840820145 64907125514838605880615109)
  ·
    refine ⟨12170086034032238602615333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64907125514838605880615109 12170086034032238602615333)
    ·
      refine ⟨2281891131381044737990375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12170086034032238602615333 2281891131381044737990375)
      ·
        refine ⟨3422836697071567106985563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281891131381044737990375 3422836697071567106985563)
        ·
          refine ⟨5134255045607350660478345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422836697071567106985563 5134255045607350660478345)
          ·
            refine ⟨3850691284205512995358759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5134255045607350660478345 3850691284205512995358759)
            ·
              refine ⟨5776036926308269493038139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850691284205512995358759 5776036926308269493038139)
              ·
                refine ⟨8664055389462404239557209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776036926308269493038139 8664055389462404239557209)
                ·
                  refine ⟨6498041542096803179667907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8664055389462404239557209 6498041542096803179667907)
                  ·
                    refine ⟨9747062313145204769501861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6498041542096803179667907 9747062313145204769501861)
                    ·
                      refine ⟨1827574183714725894281599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9747062313145204769501861 1827574183714725894281599)
                      ·
                        rfl

theorem cell23_3559188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3559188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559188 prefixEnd_3559188 := by exact prefixLift 3559188
  have htrace : WordTrace (prefixWord ++ tailWord_3559188) baseStart_3559188 baseEnd_3559188 := by
    simpa [prefixWord, tailWord_3559188, baseEnd_3559188] using wordTrace_append hprefix tailTrace_3559188
  have hstable : (prefixWord ++ tailWord_3559188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559188).length < 2 ^ (prefixWord ++ tailWord_3559188).sum := by decide
  have hdescent : baseEnd_3559188 < baseStart_3559188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559240 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_3559240 : Nat := 118140960795 + 3559240 * 2 ^ 59
def prefixEnd_3559240 : Nat := 4983230072969 + 3 ^ 40 * 3559240 * 2
def baseEnd_3559240 : Nat := 1827600884708759690831359

theorem tailTrace_3559240 : CollatzResearch.WordTrace tailWord_3559240 prefixEnd_3559240 1827600884708759690831359 := by
  unfold tailWord_3559240
  simp only [CollatzResearch.WordTrace]
  refine ⟨64908073812744412321061587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86544098416992549761415449 64908073812744412321061587)
  ·
    refine ⟨97362110719116618481592381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64908073812744412321061587 97362110719116618481592381)
    ·
      refine ⟨36510791519668731930597143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97362110719116618481592381 36510791519668731930597143)
      ·
        refine ⟨54766187279503097895895715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36510791519668731930597143 54766187279503097895895715)
        ·
          refine ⟨82149280919254646843843573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54766187279503097895895715 82149280919254646843843573)
          ·
            refine ⟨7701495086180123141610335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82149280919254646843843573 7701495086180123141610335)
            ·
              refine ⟨11552242629270184712415503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7701495086180123141610335 11552242629270184712415503)
              ·
                refine ⟨17328363943905277068623255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11552242629270184712415503 17328363943905277068623255)
                ·
                  refine ⟨25992545915857915602934883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17328363943905277068623255 25992545915857915602934883)
                  ·
                    refine ⟨38988818873786873404402325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25992545915857915602934883 38988818873786873404402325)
                    ·
                      refine ⟨1827600884708759690831359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38988818873786873404402325 1827600884708759690831359)
                      ·
                        rfl

theorem cell23_3559240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_3559240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559240 prefixEnd_3559240 := by exact prefixLift 3559240
  have htrace : WordTrace (prefixWord ++ tailWord_3559240) baseStart_3559240 baseEnd_3559240 := by
    simpa [prefixWord, tailWord_3559240, baseEnd_3559240] using wordTrace_append hprefix tailTrace_3559240
  have hstable : (prefixWord ++ tailWord_3559240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559240).length < 2 ^ (prefixWord ++ tailWord_3559240).sum := by decide
  have hdescent : baseEnd_3559240 < baseStart_3559240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559244 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3559244 : Nat := 118140960795 + 3559244 * 2 ^ 59
def prefixEnd_3559244 : Nat := 4983230072969 + 3 ^ 40 * 3559244 * 2
def baseEnd_3559244 : Nat := 1827602938631377675181341

theorem tailTrace_3559244 : CollatzResearch.WordTrace tailWord_3559244 prefixEnd_3559244 1827602938631377675181341 := by
  unfold tailWord_3559244
  simp only [CollatzResearch.WordTrace]
  refine ⟨64908146758737166662634393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86544195678316222216845857 64908146758737166662634393)
  ·
    refine ⟨48681110069052874996975795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64908146758737166662634393 48681110069052874996975795)
    ·
      refine ⟨73021665103579312495463693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48681110069052874996975795 73021665103579312495463693)
      ·
        refine ⟨27383124413842242185798885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73021665103579312495463693 27383124413842242185798885)
        ·
          refine ⟨5134335827595420409837291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27383124413842242185798885 5134335827595420409837291)
          ·
            refine ⟨7701503741393130614755937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5134335827595420409837291 7701503741393130614755937)
            ·
              refine ⟨5776127806044847961066953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7701503741393130614755937 5776127806044847961066953)
              ·
                refine ⟨4332095854533635970800215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5776127806044847961066953 4332095854533635970800215)
                ·
                  refine ⟨6498143781800453956200323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332095854533635970800215 6498143781800453956200323)
                  ·
                    refine ⟨9747215672700680934300485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6498143781800453956200323 9747215672700680934300485)
                    ·
                      refine ⟨1827602938631377675181341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9747215672700680934300485 1827602938631377675181341)
                      ·
                        rfl

theorem cell23_3559244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3559244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559244 prefixEnd_3559244 := by exact prefixLift 3559244
  have htrace : WordTrace (prefixWord ++ tailWord_3559244) baseStart_3559244 baseEnd_3559244 := by
    simpa [prefixWord, tailWord_3559244, baseEnd_3559244] using wordTrace_append hprefix tailTrace_3559244
  have hstable : (prefixWord ++ tailWord_3559244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559244).length < 2 ^ (prefixWord ++ tailWord_3559244).sum := by decide
  have hdescent : baseEnd_3559244 < baseStart_3559244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559250 : List Nat := [3, 2, 2, 1, 1, 4, 1, 9]
def baseStart_3559250 : Nat := 118140960795 + 3559250 * 2 ^ 59
def prefixEnd_3559250 : Nat := 4983230072969 + 3 ^ 40 * 3559250 * 2
def baseEnd_3559250 : Nat := 67689111833900172285419

theorem tailTrace_3559250 : CollatzResearch.WordTrace tailWord_3559250 prefixEnd_3559250 67689111833900172285419 := by
  unfold tailWord_3559250
  simp only [CollatzResearch.WordTrace]
  refine ⟨32454128088863149087496801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86544341570301730899991469 32454128088863149087496801)
  ·
    refine ⟨24340596066647361815622601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32454128088863149087496801 24340596066647361815622601)
    ·
      refine ⟨18255447049985521361716951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24340596066647361815622601 18255447049985521361716951)
      ·
        refine ⟨27383170574978282042575427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18255447049985521361716951 27383170574978282042575427)
        ·
          refine ⟨41074755862467423063863141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27383170574978282042575427 41074755862467423063863141)
          ·
            refine ⟨7701516724212641824474339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41074755862467423063863141 7701516724212641824474339)
            ·
              refine ⟨11552275086318962736711509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7701516724212641824474339 11552275086318962736711509)
              ·
                refine ⟨67689111833900172285419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11552275086318962736711509 67689111833900172285419)
                ·
                  rfl

theorem cell23_3559250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 9].length) (baseStart_3559250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559250 prefixEnd_3559250 := by exact prefixLift 3559250
  have htrace : WordTrace (prefixWord ++ tailWord_3559250) baseStart_3559250 baseEnd_3559250 := by
    simpa [prefixWord, tailWord_3559250, baseEnd_3559250] using wordTrace_append hprefix tailTrace_3559250
  have hstable : (prefixWord ++ tailWord_3559250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559250).length < 2 ^ (prefixWord ++ tailWord_3559250).sum := by decide
  have hdescent : baseEnd_3559250 < baseStart_3559250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559267 : List Nat := [1, 1, 1, 5, 5, 1, 9]
def baseStart_3559267 : Nat := 118140960795 + 3559267 * 2 ^ 59
def prefixEnd_3559267 : Nat := 4983230072969 + 3 ^ 40 * 3559267 * 2
def baseEnd_3559267 : Nat := 22563145045511494878935

theorem tailTrace_3559267 : CollatzResearch.WordTrace tailWord_3559267 prefixEnd_3559267 22563145045511494878935 := by
  unfold tailWord_3559267
  simp only [CollatzResearch.WordTrace]
  refine ⟨129817132396391008253356055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86544754930927338835570703 129817132396391008253356055)
  ·
    refine ⟨194725698594586512380034083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129817132396391008253356055 194725698594586512380034083)
    ·
      refine ⟨292088547891879768570051125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194725698594586512380034083 292088547891879768570051125)
      ·
        refine ⟨27383301364863728303442293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292088547891879768570051125 27383301364863728303442293)
        ·
          refine ⟨2567184502955974528447715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27383301364863728303442293 2567184502955974528447715)
          ·
            refine ⟨3850776754433961792671573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567184502955974528447715 3850776754433961792671573)
            ·
              refine ⟨22563145045511494878935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3850776754433961792671573 22563145045511494878935)
              ·
                rfl

theorem cell23_3559267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 9].length) (baseStart_3559267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559267 prefixEnd_3559267 := by exact prefixLift 3559267
  have htrace : WordTrace (prefixWord ++ tailWord_3559267) baseStart_3559267 baseEnd_3559267 := by
    simpa [prefixWord, tailWord_3559267, baseEnd_3559267] using wordTrace_append hprefix tailTrace_3559267
  have hstable : (prefixWord ++ tailWord_3559267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559267).length < 2 ^ (prefixWord ++ tailWord_3559267).sum := by decide
  have hdescent : baseEnd_3559267 < baseStart_3559267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559278 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_3559278 : Nat := 118140960795 + 3559278 * 2 ^ 59
def prefixEnd_3559278 : Nat := 4983230072969 + 3 ^ 40 * 3559278 * 2
def baseEnd_3559278 : Nat := 1827620396973630542156185

theorem tailTrace_3559278 : CollatzResearch.WordTrace tailWord_3559278 prefixEnd_3559278 1827620396973630542156185 := by
  unfold tailWord_3559278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16227191699918894641500811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86545022399567438088004325 16227191699918894641500811)
  ·
    refine ⟨24340787549878341962251217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16227191699918894641500811 24340787549878341962251217)
    ·
      refine ⟨18255590662408756471688413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24340787549878341962251217 18255590662408756471688413)
      ·
        refine ⟨6845846498403283676883155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18255590662408756471688413 6845846498403283676883155)
        ·
          refine ⟨10268769747604925515324733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6845846498403283676883155 10268769747604925515324733)
          ·
            refine ⟨3850788655351847068246775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10268769747604925515324733 3850788655351847068246775)
            ·
              refine ⟨5776182983027770602370163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850788655351847068246775 5776182983027770602370163)
              ·
                refine ⟨8664274474541655903555245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776182983027770602370163 8664274474541655903555245)
                ·
                  refine ⟨3249102927953120963833217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8664274474541655903555245 3249102927953120963833217)
                  ·
                    refine ⟨2436827195964840722874913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3249102927953120963833217 2436827195964840722874913)
                    ·
                      refine ⟨1827620396973630542156185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436827195964840722874913 1827620396973630542156185)
                      ·
                        rfl

theorem cell23_3559278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_3559278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559278 prefixEnd_3559278 := by exact prefixLift 3559278
  have htrace : WordTrace (prefixWord ++ tailWord_3559278) baseStart_3559278 baseEnd_3559278 := by
    simpa [prefixWord, tailWord_3559278, baseEnd_3559278] using wordTrace_append hprefix tailTrace_3559278
  have hstable : (prefixWord ++ tailWord_3559278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559278).length < 2 ^ (prefixWord ++ tailWord_3559278).sum := by decide
  have hdescent : baseEnd_3559278 < baseStart_3559278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559357 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 7]
def baseStart_3559357 : Nat := 118140960795 + 3559357 * 2 ^ 59
def prefixEnd_3559357 : Nat := 4983230072969 + 3 ^ 40 * 3559357 * 2
def baseEnd_3559357 : Nat := 203073440216148414785369

theorem tailTrace_3559357 : CollatzResearch.WordTrace tailWord_3559357 prefixEnd_3559357 203073440216148414785369 := by
  unfold tailWord_3559357
  simp only [CollatzResearch.WordTrace]
  refine ⟨129820414966064953624132325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86546943310709969082754883 129820414966064953624132325)
  ·
    refine ⟨24341327806137178804524811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129820414966064953624132325 24341327806137178804524811)
    ·
      refine ⟨36511991709205768206787217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24341327806137178804524811 36511991709205768206787217)
      ·
        refine ⟨27383993781904326155090413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36511991709205768206787217 27383993781904326155090413)
        ·
          refine ⟨10268997668214122308158905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27383993781904326155090413 10268997668214122308158905)
          ·
            refine ⟨7701748251160591731119179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10268997668214122308158905 7701748251160591731119179)
            ·
              refine ⟨11552622376740887596678769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7701748251160591731119179 11552622376740887596678769)
              ·
                refine ⟨8664466782555665697509077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11552622376740887596678769 8664466782555665697509077)
                ·
                  refine ⟨203073440216148414785369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8664466782555665697509077 203073440216148414785369)
                  ·
                    rfl

theorem cell23_3559357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_3559357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559357 prefixEnd_3559357 := by exact prefixLift 3559357
  have htrace : WordTrace (prefixWord ++ tailWord_3559357) baseStart_3559357 baseEnd_3559357 := by
    simpa [prefixWord, tailWord_3559357, baseEnd_3559357] using wordTrace_append hprefix tailTrace_3559357
  have hstable : (prefixWord ++ tailWord_3559357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559357).length < 2 ^ (prefixWord ++ tailWord_3559357).sum := by decide
  have hdescent : baseEnd_3559357 < baseStart_3559357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559374 : List Nat := [4, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_3559374 : Nat := 118140960795 + 3559374 * 2 ^ 59
def prefixEnd_3559374 : Nat := 4983230072969 + 3 ^ 40 * 3559374 * 2
def baseEnd_3559374 : Nat := 203074410124051351839527

theorem tailTrace_3559374 : CollatzResearch.WordTrace tailWord_3559374 prefixEnd_3559374 203074410124051351839527 := by
  unfold tailWord_3559374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16227629375875420690937647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86547356671335577018334117 16227629375875420690937647)
  ·
    refine ⟨24341444063813131036406471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16227629375875420690937647 24341444063813131036406471)
    ·
      refine ⟨36512166095719696554609707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24341444063813131036406471 36512166095719696554609707)
      ·
        refine ⟨54768249143579544831914561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36512166095719696554609707 54768249143579544831914561)
        ·
          refine ⟨41076186857684658623935921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54768249143579544831914561 41076186857684658623935921)
          ·
            refine ⟨30807140143263493967951941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41076186857684658623935921 30807140143263493967951941)
            ·
              refine ⟨5776338776861905118990989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30807140143263493967951941 5776338776861905118990989)
              ·
                refine ⟨2166127041323214419621621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5776338776861905118990989 2166127041323214419621621)
                ·
                  refine ⟨203074410124051351839527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2166127041323214419621621 203074410124051351839527)
                  ·
                    rfl

theorem cell23_3559374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_3559374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559374 prefixEnd_3559374 := by exact prefixLift 3559374
  have htrace : WordTrace (prefixWord ++ tailWord_3559374) baseStart_3559374 baseEnd_3559374 := by
    simpa [prefixWord, tailWord_3559374, baseEnd_3559374] using wordTrace_append hprefix tailTrace_3559374
  have hstable : (prefixWord ++ tailWord_3559374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559374).length < 2 ^ (prefixWord ++ tailWord_3559374).sum := by decide
  have hdescent : baseEnd_3559374 < baseStart_3559374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559377 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 1, 7, 2]
def baseStart_3559377 : Nat := 118140960795 + 3559377 * 2 ^ 59
def prefixEnd_3559377 : Nat := 4983230072969 + 3 ^ 40 * 3559377 * 2
def baseEnd_3559377 : Nat := 1827671231558425654818229

theorem tailTrace_3559377 : CollatzResearch.WordTrace tailWord_3559377 prefixEnd_3559377 1827671231558425654818229 := by
  unfold tailWord_3559377
  simp only [CollatzResearch.WordTrace]
  refine ⟨129821144425992497039860385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86547429617328331359906923 129821144425992497039860385)
  ·
    refine ⟨97365858319494372779895289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129821144425992497039860385 97365858319494372779895289)
    ·
      refine ⟨73024393739620779584921467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97365858319494372779895289 73024393739620779584921467)
      ·
        refine ⟨109536590609431169377382201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73024393739620779584921467 109536590609431169377382201)
        ·
          refine ⟨82152442957073377033036651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109536590609431169377382201 82152442957073377033036651)
          ·
            refine ⟨123228664435610065549554977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82152442957073377033036651 123228664435610065549554977)
            ·
              refine ⟨92421498326707549162166233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123228664435610065549554977 92421498326707549162166233)
              ·
                refine ⟨69316123745030661871624675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92421498326707549162166233 69316123745030661871624675)
                ·
                  refine ⟨103974185617545992807437013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69316123745030661871624675 103974185617545992807437013)
                  ·
                    refine ⟨2436894975411234206424305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 103974185617545992807437013 2436894975411234206424305)
                    ·
                      refine ⟨1827671231558425654818229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436894975411234206424305 1827671231558425654818229)
                      ·
                        rfl

theorem cell23_3559377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_3559377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559377 prefixEnd_3559377 := by exact prefixLift 3559377
  have htrace : WordTrace (prefixWord ++ tailWord_3559377) baseStart_3559377 baseEnd_3559377 := by
    simpa [prefixWord, tailWord_3559377, baseEnd_3559377] using wordTrace_append hprefix tailTrace_3559377
  have hstable : (prefixWord ++ tailWord_3559377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559377).length < 2 ^ (prefixWord ++ tailWord_3559377).sum := by decide
  have hdescent : baseEnd_3559377 < baseStart_3559377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559385 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 2, 2, 2]
def baseStart_3559385 : Nat := 118140960795 + 3559385 * 2 ^ 59
def prefixEnd_3559385 : Nat := 4983230072969 + 3 ^ 40 * 3559385 * 2
def baseEnd_3559385 : Nat := 1827675339403661623518193

theorem tailTrace_3559385 : CollatzResearch.WordTrace tailWord_3559385 prefixEnd_3559385 1827675339403661623518193 := by
  unfold tailWord_3559385
  simp only [CollatzResearch.WordTrace]
  refine ⟨129821436209963514406151609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86547624139975676270767739 129821436209963514406151609)
  ·
    refine ⟨97366077157472635804613707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129821436209963514406151609 97366077157472635804613707)
    ·
      refine ⟨146049115736208953706920561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97366077157472635804613707 146049115736208953706920561)
      ·
        refine ⟨109536836802156715280190421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146049115736208953706920561 109536836802156715280190421)
        ·
          refine ⟨2567269612550548014379463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 109536836802156715280190421 2567269612550548014379463)
          ·
            refine ⟨3850904418825822021569195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567269612550548014379463 3850904418825822021569195)
            ·
              refine ⟨5776356628238733032353793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850904418825822021569195 5776356628238733032353793)
              ·
                refine ⟨4332267471179049774265345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5776356628238733032353793 4332267471179049774265345)
                ·
                  refine ⟨3249200603384287330699009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4332267471179049774265345 3249200603384287330699009)
                  ·
                    refine ⟨2436900452538215498024257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3249200603384287330699009 2436900452538215498024257)
                    ·
                      refine ⟨1827675339403661623518193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2436900452538215498024257 1827675339403661623518193)
                      ·
                        rfl

theorem cell23_3559385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_3559385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559385 prefixEnd_3559385 := by exact prefixLift 3559385
  have htrace : WordTrace (prefixWord ++ tailWord_3559385) baseStart_3559385 baseEnd_3559385 := by
    simpa [prefixWord, tailWord_3559385, baseEnd_3559385] using wordTrace_append hprefix tailTrace_3559385
  have hstable : (prefixWord ++ tailWord_3559385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559385).length < 2 ^ (prefixWord ++ tailWord_3559385).sum := by decide
  have hdescent : baseEnd_3559385 < baseStart_3559385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559427 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 3]
def baseStart_3559427 : Nat := 118140960795 + 3559427 * 2 ^ 59
def prefixEnd_3559427 : Nat := 4983230072969 + 3 ^ 40 * 3559427 * 2
def baseEnd_3559427 : Nat := 1827696905591150459192999

theorem tailTrace_3559427 : CollatzResearch.WordTrace tailWord_3559427 prefixEnd_3559427 1827696905591150459192999 := by
  unfold tailWord_3559427
  simp only [CollatzResearch.WordTrace]
  refine ⟨129822968075811355579180535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86548645383874237052787023 129822968075811355579180535)
  ·
    refine ⟨194734452113717033368770803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129822968075811355579180535 194734452113717033368770803)
    ·
      refine ⟨292101678170575550053156205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194734452113717033368770803 292101678170575550053156205)
      ·
        refine ⟨109538129313965831269933577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292101678170575550053156205 109538129313965831269933577)
        ·
          refine ⟨82153596985474373452450183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109538129313965831269933577 82153596985474373452450183)
          ·
            refine ⟨123230395478211560178675275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82153596985474373452450183 123230395478211560178675275)
            ·
              refine ⟨184845593217317340268012913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123230395478211560178675275 184845593217317340268012913)
              ·
                refine ⟨138634194912988005201009685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184845593217317340268012913 138634194912988005201009685)
                ·
                  refine ⟨6498477886546312743797329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138634194912988005201009685 6498477886546312743797329)
                  ·
                    refine ⟨4873858414909734557847997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6498477886546312743797329 4873858414909734557847997)
                    ·
                      refine ⟨1827696905591150459192999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4873858414909734557847997 1827696905591150459192999)
                      ·
                        rfl

theorem cell23_3559427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_3559427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559427 prefixEnd_3559427 := by exact prefixLift 3559427
  have htrace : WordTrace (prefixWord ++ tailWord_3559427) baseStart_3559427 baseEnd_3559427 := by
    simpa [prefixWord, tailWord_3559427, baseEnd_3559427] using wordTrace_append hprefix tailTrace_3559427
  have hstable : (prefixWord ++ tailWord_3559427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559427).length < 2 ^ (prefixWord ++ tailWord_3559427).sum := by decide
  have hdescent : baseEnd_3559427 < baseStart_3559427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559548 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 1, 1, 4]
def baseStart_3559548 : Nat := 118140960795 + 3559548 * 2 ^ 59
def prefixEnd_3559548 : Nat := 4983230072969 + 3 ^ 40 * 3559548 * 2
def baseEnd_3559548 : Nat := 1827759036750344485779943

theorem tailTrace_3559548 : CollatzResearch.WordTrace tailWord_3559548 prefixEnd_3559548 1827759036750344485779943 := by
  unfold tailWord_3559548
  simp only [CollatzResearch.WordTrace]
  refine ⟨64913690654186496622167649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86551587538915328829556865 64913690654186496622167649)
  ·
    refine ⟨48685267990639872466625737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64913690654186496622167649 48685267990639872466625737)
    ·
      refine ⟨36513950992979904349969303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48685267990639872466625737 36513950992979904349969303)
      ·
        refine ⟨54770926489469856524953955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36513950992979904349969303 54770926489469856524953955)
        ·
          refine ⟨82156389734204784787430933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54770926489469856524953955 82156389734204784787430933)
          ·
            refine ⟨3851080768790849286910825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82156389734204784787430933 3851080768790849286910825)
            ·
              refine ⟨2888310576593136965183119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3851080768790849286910825 2888310576593136965183119)
              ·
                refine ⟨4332465864889705447774679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888310576593136965183119 4332465864889705447774679)
                ·
                  refine ⟨6498698797334558171662019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332465864889705447774679 6498698797334558171662019)
                  ·
                    refine ⟨9748048196001837257493029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6498698797334558171662019 9748048196001837257493029)
                    ·
                      refine ⟨1827759036750344485779943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9748048196001837257493029 1827759036750344485779943)
                      ·
                        rfl

theorem cell23_3559548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_3559548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559548 prefixEnd_3559548 := by exact prefixLift 3559548
  have htrace : WordTrace (prefixWord ++ tailWord_3559548) baseStart_3559548 baseEnd_3559548 := by
    simpa [prefixWord, tailWord_3559548, baseEnd_3559548] using wordTrace_append hprefix tailTrace_3559548
  have hstable : (prefixWord ++ tailWord_3559548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559548).length < 2 ^ (prefixWord ++ tailWord_3559548).sum := by decide
  have hdescent : baseEnd_3559548 < baseStart_3559548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559577 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_3559577 : Nat := 118140960795 + 3559577 * 2 ^ 59
def prefixEnd_3559577 : Nat := 4983230072969 + 3 ^ 40 * 3559577 * 2
def baseEnd_3559577 : Nat := 1827773927689324872317309

theorem tailTrace_3559577 : CollatzResearch.WordTrace tailWord_3559577 prefixEnd_3559577 1827773927689324872317309 := by
  unfold tailWord_3559577
  simp only [CollatzResearch.WordTrace]
  refine ⟨129828439025267931197140985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86552292683511954131427323 129828439025267931197140985)
  ·
    refine ⟨97371329268950948397855739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129828439025267931197140985 97371329268950948397855739)
    ·
      refine ⟨146056993903426422596783609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97371329268950948397855739 146056993903426422596783609)
      ·
        refine ⟨109542745427569816947587707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146056993903426422596783609 109542745427569816947587707)
        ·
          refine ⟨164314118141354725421381561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109542745427569816947587707 164314118141354725421381561)
          ·
            refine ⟨123235588606016044066036171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164314118141354725421381561 123235588606016044066036171)
            ·
              refine ⟨184853382909024066099054257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123235588606016044066036171 184853382909024066099054257)
              ·
                refine ⟨138640037181768049574290693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184853382909024066099054257 138640037181768049574290693)
                ·
                  refine ⟨25995006971581509295179505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138640037181768049574290693 25995006971581509295179505)
                  ·
                    refine ⟨19496255228686131971384629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25995006971581509295179505 19496255228686131971384629)
                    ·
                      refine ⟨1827773927689324872317309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19496255228686131971384629 1827773927689324872317309)
                      ·
                        rfl

theorem cell23_3559577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_3559577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559577 prefixEnd_3559577 := by exact prefixLift 3559577
  have htrace : WordTrace (prefixWord ++ tailWord_3559577) baseStart_3559577 baseEnd_3559577 := by
    simpa [prefixWord, tailWord_3559577, baseEnd_3559577] using wordTrace_append hprefix tailTrace_3559577
  have hstable : (prefixWord ++ tailWord_3559577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559577).length < 2 ^ (prefixWord ++ tailWord_3559577).sum := by decide
  have hdescent : baseEnd_3559577 < baseStart_3559577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559578 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3559578 : Nat := 118140960795 + 3559578 * 2 ^ 59
def prefixEnd_3559578 : Nat := 4983230072969 + 3 ^ 40 * 3559578 * 2
def baseEnd_3559578 : Nat := 1827774441169979368404805

theorem tailTrace_3559578 : CollatzResearch.WordTrace tailWord_3559578 prefixEnd_3559578 1827774441169979368404805 := by
  unfold tailWord_3559578
  simp only [CollatzResearch.WordTrace]
  refine ⟨32457118874566077091981847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86552316998842872245284925 32457118874566077091981847)
  ·
    refine ⟨48685678311849115637972771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32457118874566077091981847 48685678311849115637972771)
    ·
      refine ⟨73028517467773673456959157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48685678311849115637972771 73028517467773673456959157)
      ·
        refine ⟨6846423512603781886589921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73028517467773673456959157 6846423512603781886589921)
        ·
          refine ⟨5134817634452836414942441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6846423512603781886589921 5134817634452836414942441)
          ·
            refine ⟨3851113225839627311206831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5134817634452836414942441 3851113225839627311206831)
            ·
              refine ⟨5776669838759440966810247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851113225839627311206831 5776669838759440966810247)
              ·
                refine ⟨8665004758139161450215371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776669838759440966810247 8665004758139161450215371)
                ·
                  refine ⟨12997507137208742175323057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8665004758139161450215371 12997507137208742175323057)
                  ·
                    refine ⟨9748130352906556631492293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12997507137208742175323057 9748130352906556631492293)
                    ·
                      refine ⟨1827774441169979368404805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9748130352906556631492293 1827774441169979368404805)
                      ·
                        rfl

theorem cell23_3559578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3559578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559578 prefixEnd_3559578 := by exact prefixLift 3559578
  have htrace : WordTrace (prefixWord ++ tailWord_3559578) baseStart_3559578 baseEnd_3559578 := by
    simpa [prefixWord, tailWord_3559578, baseEnd_3559578] using wordTrace_append hprefix tailTrace_3559578
  have hstable : (prefixWord ++ tailWord_3559578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559578).length < 2 ^ (prefixWord ++ tailWord_3559578).sum := by decide
  have hdescent : baseEnd_3559578 < baseStart_3559578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559581 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_3559581 : Nat := 118140960795 + 3559581 * 2 ^ 59
def prefixEnd_3559581 : Nat := 4983230072969 + 3 ^ 40 * 3559581 * 2
def baseEnd_3559581 : Nat := 1827775981611942856667291

theorem tailTrace_3559581 : CollatzResearch.WordTrace tailWord_3559581 prefixEnd_3559581 1827775981611942856667291 := by
  unfold tailWord_3559581
  simp only [CollatzResearch.WordTrace]
  refine ⟨129828584917253439880286597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86552389944835626586857731 129828584917253439880286597)
  ·
    refine ⟨24342859671985019977553737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129828584917253439880286597 24342859671985019977553737)
    ·
      refine ⟨18257144753988764983165303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24342859671985019977553737 18257144753988764983165303)
      ·
        refine ⟨27385717130983147474747955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18257144753988764983165303 27385717130983147474747955)
        ·
          refine ⟨41078575696474721212121933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27385717130983147474747955 41078575696474721212121933)
          ·
            refine ⟨15404465886178020454545725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41078575696474721212121933 15404465886178020454545725)
            ·
              refine ⟨5776674707316757670454647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15404465886178020454545725 5776674707316757670454647)
              ·
                refine ⟨8665012060975136505681971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776674707316757670454647 8665012060975136505681971)
                ·
                  refine ⟨12997518091462704758522957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8665012060975136505681971 12997518091462704758522957)
                  ·
                    refine ⟨4874069284298514284446109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12997518091462704758522957 4874069284298514284446109)
                    ·
                      refine ⟨1827775981611942856667291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4874069284298514284446109 1827775981611942856667291)
                      ·
                        rfl

theorem cell23_3559581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_3559581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559581 prefixEnd_3559581 := by exact prefixLift 3559581
  have htrace : WordTrace (prefixWord ++ tailWord_3559581) baseStart_3559581 baseEnd_3559581 := by
    simpa [prefixWord, tailWord_3559581, baseEnd_3559581] using wordTrace_append hprefix tailTrace_3559581
  have hstable : (prefixWord ++ tailWord_3559581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559581).length < 2 ^ (prefixWord ++ tailWord_3559581).sum := by decide
  have hdescent : baseEnd_3559581 < baseStart_3559581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559588 : List Nat := [2, 3, 1, 2, 5, 1, 2, 7]
def baseStart_3559588 : Nat := 118140960795 + 3559588 * 2 ^ 59
def prefixEnd_3559588 : Nat := 4983230072969 + 3 ^ 40 * 3559588 * 2
def baseEnd_3559588 : Nat := 67695539850982382565917

theorem tailTrace_3559588 : CollatzResearch.WordTrace tailWord_3559588 prefixEnd_3559588 67695539850982382565917 := by
  unfold tailWord_3559588
  simp only [CollatzResearch.WordTrace]
  refine ⟨64914420114114040037895709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86552560152152053383860945 64914420114114040037895709)
  ·
    refine ⟨24342907542792765014210891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64914420114114040037895709 24342907542792765014210891)
    ·
      refine ⟨36514361314189147521316337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24342907542792765014210891 36514361314189147521316337)
      ·
        refine ⟨27385770985641860640987253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36514361314189147521316337 27385770985641860640987253)
        ·
          refine ⟨2567416029903924435092555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27385770985641860640987253 2567416029903924435092555)
          ·
            refine ⟨3851124044855886652638833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567416029903924435092555 3851124044855886652638833)
            ·
              refine ⟨2888343033641914989479125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3851124044855886652638833 2888343033641914989479125)
              ·
                refine ⟨67695539850982382565917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2888343033641914989479125 67695539850982382565917)
                ·
                  rfl

theorem cell23_3559588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 7].length) (baseStart_3559588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559588 prefixEnd_3559588 := by exact prefixLift 3559588
  have htrace : WordTrace (prefixWord ++ tailWord_3559588) baseStart_3559588 baseEnd_3559588 := by
    simpa [prefixWord, tailWord_3559588, baseEnd_3559588] using wordTrace_append hprefix tailTrace_3559588
  have hstable : (prefixWord ++ tailWord_3559588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559588).length < 2 ^ (prefixWord ++ tailWord_3559588).sum := by decide
  have hdescent : baseEnd_3559588 < baseStart_3559588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559624 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_3559624 : Nat := 118140960795 + 3559624 * 2 ^ 59
def prefixEnd_3559624 : Nat := 4983230072969 + 3 ^ 40 * 3559624 * 2
def baseEnd_3559624 : Nat := 1827798061280086188429593

theorem tailTrace_3559624 : CollatzResearch.WordTrace tailWord_3559624 prefixEnd_3559624 1827798061280086188429593 := by
  unfold tailWord_3559624
  simp only [CollatzResearch.WordTrace]
  refine ⟨64915076628048829112050963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86553435504065105482734617 64915076628048829112050963)
  ·
    refine ⟨97372614942073243668076445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64915076628048829112050963 97372614942073243668076445)
    ·
      refine ⟨36514730603277466375528667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97372614942073243668076445 36514730603277466375528667)
      ·
        refine ⟨54772095904916199563293001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36514730603277466375528667 54772095904916199563293001)
        ·
          refine ⟨41079071928687149672469751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54772095904916199563293001 41079071928687149672469751)
          ·
            refine ⟨61618607893030724508704627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41079071928687149672469751 61618607893030724508704627)
            ·
              refine ⟨92427911839546086763056941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61618607893030724508704627 92427911839546086763056941)
              ·
                refine ⟨34660466939829782536146353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92427911839546086763056941 34660466939829782536146353)
                ·
                  refine ⟨25995350204872336902109765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34660466939829782536146353 25995350204872336902109765)
                  ·
                    refine ⟨4874128163413563169145581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25995350204872336902109765 4874128163413563169145581)
                    ·
                      refine ⟨1827798061280086188429593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4874128163413563169145581 1827798061280086188429593)
                      ·
                        rfl

theorem cell23_3559624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_3559624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559624 prefixEnd_3559624 := by exact prefixLift 3559624
  have htrace : WordTrace (prefixWord ++ tailWord_3559624) baseStart_3559624 baseEnd_3559624 := by
    simpa [prefixWord, tailWord_3559624, baseEnd_3559624] using wordTrace_append hprefix tailTrace_3559624
  have hstable : (prefixWord ++ tailWord_3559624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559624).length < 2 ^ (prefixWord ++ tailWord_3559624).sum := by decide
  have hdescent : baseEnd_3559624 < baseStart_3559624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559678 : List Nat := [4, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_3559678 : Nat := 118140960795 + 3559678 * 2 ^ 59
def prefixEnd_3559678 : Nat := 4983230072969 + 3 ^ 40 * 3559678 * 2
def baseEnd_3559678 : Nat := 203091754359492108572705

theorem tailTrace_3559678 : CollatzResearch.WordTrace tailWord_3559678 prefixEnd_3559678 203091754359492108572705 := by
  unfold tailWord_3559678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16229015349737753180820961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86554748531934683631045125 16229015349737753180820961)
  ·
    refine ⟨12171761512303314885615721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16229015349737753180820961 12171761512303314885615721)
    ·
      refine ⟨9128821134227486164211791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12171761512303314885615721 9128821134227486164211791)
      ·
        refine ⟨13693231701341229246317687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9128821134227486164211791 13693231701341229246317687)
        ·
          refine ⟨20539847552011843869476531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13693231701341229246317687 20539847552011843869476531)
          ·
            refine ⟨30809771328017765804214797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20539847552011843869476531 30809771328017765804214797)
            ·
              refine ⟨11553664248006662176580549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30809771328017765804214797 11553664248006662176580549)
              ·
                refine ⟨2166312046501249158108853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11553664248006662176580549 2166312046501249158108853)
                ·
                  refine ⟨203091754359492108572705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2166312046501249158108853 203091754359492108572705)
                  ·
                    rfl

theorem cell23_3559678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_3559678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559678 prefixEnd_3559678 := by exact prefixLift 3559678
  have htrace : WordTrace (prefixWord ++ tailWord_3559678) baseStart_3559678 baseEnd_3559678 := by
    simpa [prefixWord, tailWord_3559678, baseEnd_3559678] using wordTrace_append hprefix tailTrace_3559678
  have hstable : (prefixWord ++ tailWord_3559678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559678).length < 2 ^ (prefixWord ++ tailWord_3559678).sum := by decide
  have hdescent : baseEnd_3559678 < baseStart_3559678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559681 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_3559681 : Nat := 118140960795 + 3559681 * 2 ^ 59
def prefixEnd_3559681 : Nat := 4983230072969 + 3 ^ 40 * 3559681 * 2
def baseEnd_3559681 : Nat := 1827827329677392465416831

theorem tailTrace_3559681 : CollatzResearch.WordTrace tailWord_3559681 prefixEnd_3559681 1827827329677392465416831 := by
  unfold tailWord_3559681
  simp only [CollatzResearch.WordTrace]
  refine ⟨129832232216891156958926897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86554821477927437972617931 129832232216891156958926897)
  ·
    refine ⟨97374174162668367719195173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129832232216891156958926897 97374174162668367719195173)
    ·
      refine ⟨18257657655500318947349095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97374174162668367719195173 18257657655500318947349095)
      ·
        refine ⟨27386486483250478421023643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18257657655500318947349095 27386486483250478421023643)
        ·
          refine ⟨41079729724875717631535465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27386486483250478421023643 41079729724875717631535465)
          ·
            refine ⟨30809797293656788223651599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41079729724875717631535465 30809797293656788223651599)
            ·
              refine ⟨46214695940485182335477399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30809797293656788223651599 46214695940485182335477399)
              ·
                refine ⟨69322043910727773503216099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46214695940485182335477399 69322043910727773503216099)
                ·
                  refine ⟨103983065866091660254824149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69322043910727773503216099 103983065866091660254824149)
                  ·
                    refine ⟨2437103106236523287222441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 103983065866091660254824149 2437103106236523287222441)
                    ·
                      refine ⟨1827827329677392465416831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437103106236523287222441 1827827329677392465416831)
                      ·
                        rfl

theorem cell23_3559681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_3559681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559681 prefixEnd_3559681 := by exact prefixLift 3559681
  have htrace : WordTrace (prefixWord ++ tailWord_3559681) baseStart_3559681 baseEnd_3559681 := by
    simpa [prefixWord, tailWord_3559681, baseEnd_3559681] using wordTrace_append hprefix tailTrace_3559681
  have hstable : (prefixWord ++ tailWord_3559681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559681).length < 2 ^ (prefixWord ++ tailWord_3559681).sum := by decide
  have hdescent : baseEnd_3559681 < baseStart_3559681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559711 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 4]
def baseStart_3559711 : Nat := 118140960795 + 3559711 * 2 ^ 59
def prefixEnd_3559711 : Nat := 4983230072969 + 3 ^ 40 * 3559711 * 2
def baseEnd_3559711 : Nat := 1827842734097027348041693

theorem tailTrace_3559711 : CollatzResearch.WordTrace tailWord_3559711 prefixEnd_3559711 1827842734097027348041693 := by
  unfold tailWord_3559711
  simp only [CollatzResearch.WordTrace]
  refine ⟨129833326406782472082518987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86555550937854981388345991 129833326406782472082518987)
  ·
    refine ⟨194749989610173708123778481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129833326406782472082518987 194749989610173708123778481)
    ·
      refine ⟨146062492207630281092833861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194749989610173708123778481 146062492207630281092833861)
      ·
        refine ⟨27386717288930677704906349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146062492207630281092833861 27386717288930677704906349)
        ·
          refine ⟨10270018983349004139339881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27386717288930677704906349 10270018983349004139339881)
          ·
            refine ⟨7702514237511753104504911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10270018983349004139339881 7702514237511753104504911)
            ·
              refine ⟨11553771356267629656757367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7702514237511753104504911 11553771356267629656757367)
              ·
                refine ⟨17330657034401444485136051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11553771356267629656757367 17330657034401444485136051)
                ·
                  refine ⟨25995985551602166727704077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17330657034401444485136051 25995985551602166727704077)
                  ·
                    refine ⟨9748494581850812522889029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25995985551602166727704077 9748494581850812522889029)
                    ·
                      refine ⟨1827842734097027348041693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9748494581850812522889029 1827842734097027348041693)
                      ·
                        rfl

theorem cell23_3559711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_3559711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559711 prefixEnd_3559711 := by exact prefixLift 3559711
  have htrace : WordTrace (prefixWord ++ tailWord_3559711) baseStart_3559711 baseEnd_3559711 := by
    simpa [prefixWord, tailWord_3559711, baseEnd_3559711] using wordTrace_append hprefix tailTrace_3559711
  have hstable : (prefixWord ++ tailWord_3559711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559711).length < 2 ^ (prefixWord ++ tailWord_3559711).sum := by decide
  have hdescent : baseEnd_3559711 < baseStart_3559711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559724 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_3559724 : Nat := 118140960795 + 3559724 * 2 ^ 59
def prefixEnd_3559724 : Nat := 4983230072969 + 3 ^ 40 * 3559724 * 2
def baseEnd_3559724 : Nat := 1827849409345535797179133

theorem tailTrace_3559724 : CollatzResearch.WordTrace tailWord_3559724 prefixEnd_3559724 1827849409345535797179133 := by
  unfold tailWord_3559724
  simp only [CollatzResearch.WordTrace]
  refine ⟨64916900277867687651371113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86555867037156916868494817 64916900277867687651371113)
  ·
    refine ⟨48687675208400765738528335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64916900277867687651371113 48687675208400765738528335)
    ·
      refine ⟨73031512812601148607792503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48687675208400765738528335 73031512812601148607792503)
      ·
        refine ⟨109547269218901722911688755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73031512812601148607792503 109547269218901722911688755)
        ·
          refine ⟨164320903828352584367533133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109547269218901722911688755 164320903828352584367533133)
          ·
            refine ⟨61620338935632219137824925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164320903828352584367533133 61620338935632219137824925)
            ·
              refine ⟨23107627100862082176684347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61620338935632219137824925 23107627100862082176684347)
              ·
                refine ⟨34661440651293123265026521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23107627100862082176684347 34661440651293123265026521)
                ·
                  refine ⟨25996080488469842448769891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34661440651293123265026521 25996080488469842448769891)
                  ·
                    refine ⟨38994120732704763673154837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25996080488469842448769891 38994120732704763673154837)
                    ·
                      refine ⟨1827849409345535797179133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38994120732704763673154837 1827849409345535797179133)
                      ·
                        rfl

theorem cell23_3559724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_3559724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559724 prefixEnd_3559724 := by exact prefixLift 3559724
  have htrace : WordTrace (prefixWord ++ tailWord_3559724) baseStart_3559724 baseEnd_3559724 := by
    simpa [prefixWord, tailWord_3559724, baseEnd_3559724] using wordTrace_append hprefix tailTrace_3559724
  have hstable : (prefixWord ++ tailWord_3559724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559724).length < 2 ^ (prefixWord ++ tailWord_3559724).sum := by decide
  have hdescent : baseEnd_3559724 < baseStart_3559724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559731 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 3]
def baseStart_3559731 : Nat := 118140960795 + 3559731 * 2 ^ 59
def prefixEnd_3559731 : Nat := 4983230072969 + 3 ^ 40 * 3559731 * 2
def baseEnd_3559731 : Nat := 1827853003710117269791601

theorem tailTrace_3559731 : CollatzResearch.WordTrace tailWord_3559731 prefixEnd_3559731 1827853003710117269791601 := by
  unfold tailWord_3559731
  simp only [CollatzResearch.WordTrace]
  refine ⟨129834055866710015498247047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86556037244473343665498031 129834055866710015498247047)
  ·
    refine ⟨194751083800065023247370571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129834055866710015498247047 194751083800065023247370571)
    ·
      refine ⟨292126625700097534871055857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194751083800065023247370571 292126625700097534871055857)
      ·
        refine ⟨219094969275073151153291893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292126625700097534871055857 219094969275073151153291893)
        ·
          refine ⟨20540153369538107920621115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219094969275073151153291893 20540153369538107920621115)
          ·
            refine ⟨30810230054307161880931673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20540153369538107920621115 30810230054307161880931673)
            ·
              refine ⟨23107672540730371410698755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30810230054307161880931673 23107672540730371410698755)
              ·
                refine ⟨34661508811095557116048133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23107672540730371410698755 34661508811095557116048133)
                ·
                  refine ⟨6499032902080416959259025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34661508811095557116048133 6499032902080416959259025)
                  ·
                    refine ⟨4874274676560312719444269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6499032902080416959259025 4874274676560312719444269)
                    ·
                      refine ⟨1827853003710117269791601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4874274676560312719444269 1827853003710117269791601)
                      ·
                        rfl

theorem cell23_3559731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 3].length) (baseStart_3559731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559731 prefixEnd_3559731 := by exact prefixLift 3559731
  have htrace : WordTrace (prefixWord ++ tailWord_3559731) baseStart_3559731 baseEnd_3559731 := by
    simpa [prefixWord, tailWord_3559731, baseEnd_3559731] using wordTrace_append hprefix tailTrace_3559731
  have hstable : (prefixWord ++ tailWord_3559731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559731).length < 2 ^ (prefixWord ++ tailWord_3559731).sum := by decide
  have hdescent : baseEnd_3559731 < baseStart_3559731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559738 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_3559738 : Nat := 118140960795 + 3559738 * 2 ^ 59
def prefixEnd_3559738 : Nat := 4983230072969 + 3 ^ 40 * 3559738 * 2
def baseEnd_3559738 : Nat := 609285532691566247468023

theorem tailTrace_3559738 : CollatzResearch.WordTrace tailWord_3559738 prefixEnd_3559738 609285532691566247468023 := by
  unfold tailWord_3559738
  simp only [CollatzResearch.WordTrace]
  refine ⟨32458577794421163923437967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86556207451789770462501245 32458577794421163923437967)
  ·
    refine ⟨48687866691631745885156951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32458577794421163923437967 48687866691631745885156951)
    ·
      refine ⟨73031800037447618827735427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48687866691631745885156951 73031800037447618827735427)
      ·
        refine ⟨109547700056171428241603141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73031800037447618827735427 109547700056171428241603141)
        ·
          refine ⟨20540193760532142795300589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109547700056171428241603141 20540193760532142795300589)
          ·
            refine ⟨7702572660199553548237721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20540193760532142795300589 7702572660199553548237721)
            ·
              refine ⟨5776929495149665161178291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7702572660199553548237721 5776929495149665161178291)
              ·
                refine ⟨8665394242724497741767437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776929495149665161178291 8665394242724497741767437)
                ·
                  refine ⟨3249522841021686653162789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8665394242724497741767437 3249522841021686653162789)
                  ·
                    refine ⟨609285532691566247468023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3249522841021686653162789 609285532691566247468023)
                    ·
                      rfl

theorem cell23_3559738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_3559738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559738 prefixEnd_3559738 := by exact prefixLift 3559738
  have htrace : WordTrace (prefixWord ++ tailWord_3559738) baseStart_3559738 baseEnd_3559738 := by
    simpa [prefixWord, tailWord_3559738, baseEnd_3559738] using wordTrace_append hprefix tailTrace_3559738
  have hstable : (prefixWord ++ tailWord_3559738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559738).length < 2 ^ (prefixWord ++ tailWord_3559738).sum := by decide
  have hdescent : baseEnd_3559738 < baseStart_3559738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559801 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3559801 : Nat := 118140960795 + 3559801 * 2 ^ 59
def prefixEnd_3559801 : Nat := 4983230072969 + 3 ^ 40 * 3559801 * 2
def baseEnd_3559801 : Nat := 1827888947355931995916279

theorem tailTrace_3559801 : CollatzResearch.WordTrace tailWord_3559801 prefixEnd_3559801 1827888947355931995916279 := by
  unfold tailWord_3559801
  simp only [CollatzResearch.WordTrace]
  refine ⟨129836608976456417453295257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86557739317637611635530171 129836608976456417453295257)
  ·
    refine ⟨97377456732342313089971443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129836608976456417453295257 97377456732342313089971443)
    ·
      refine ⟨146066185098513469634957165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97377456732342313089971443 146066185098513469634957165)
      ·
        refine ⟨54774819411942551113108937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146066185098513469634957165 54774819411942551113108937)
        ·
          refine ⟨41081114558956913334831703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54774819411942551113108937 41081114558956913334831703)
          ·
            refine ⟨61621671838435370002247555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41081114558956913334831703 61621671838435370002247555)
            ·
              refine ⟨92432507757653055003371333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61621671838435370002247555 92432507757653055003371333)
              ·
                refine ⟨17331095204559947813132125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92432507757653055003371333 17331095204559947813132125)
                ·
                  refine ⟨6499160701709980429924547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17331095204559947813132125 6499160701709980429924547)
                  ·
                    refine ⟨9748741052564970644886821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6499160701709980429924547 9748741052564970644886821)
                    ·
                      refine ⟨1827888947355931995916279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9748741052564970644886821 1827888947355931995916279)
                      ·
                        rfl

theorem cell23_3559801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3559801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559801 prefixEnd_3559801 := by exact prefixLift 3559801
  have htrace : WordTrace (prefixWord ++ tailWord_3559801) baseStart_3559801 baseEnd_3559801 := by
    simpa [prefixWord, tailWord_3559801, baseEnd_3559801] using wordTrace_append hprefix tailTrace_3559801
  have hstable : (prefixWord ++ tailWord_3559801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559801).length < 2 ^ (prefixWord ++ tailWord_3559801).sum := by decide
  have hdescent : baseEnd_3559801 < baseStart_3559801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559822 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3559822 : Nat := 118140960795 + 3559822 * 2 ^ 59
def prefixEnd_3559822 : Nat := 4983230072969 + 3 ^ 40 * 3559822 * 2
def baseEnd_3559822 : Nat := 1827899730449676413753683

theorem tailTrace_3559822 : CollatzResearch.WordTrace tailWord_3559822 prefixEnd_3559822 1827899730449676413753683 := by
  unfold tailWord_3559822
  simp only [CollatzResearch.WordTrace]
  refine ⟨16229671863672542254976215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86558249939586892026539813 16229671863672542254976215)
  ·
    refine ⟨24344507795508813382464323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16229671863672542254976215 24344507795508813382464323)
    ·
      refine ⟨36516761693263220073696485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24344507795508813382464323 36516761693263220073696485)
      ·
        refine ⟨6846892817486853763818091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36516761693263220073696485 6846892817486853763818091)
        ·
          refine ⟨10270339226230280645727137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6846892817486853763818091 10270339226230280645727137)
          ·
            refine ⟨7702754419672710484295353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10270339226230280645727137 7702754419672710484295353)
            ·
              refine ⟨5777065814754532863221515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7702754419672710484295353 5777065814754532863221515)
              ·
                refine ⟨8665598722131799294832273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5777065814754532863221515 8665598722131799294832273)
                ·
                  refine ⟨6499199041598849471124205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8665598722131799294832273 6499199041598849471124205)
                  ·
                    refine ⟨2437199640599568551671577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6499199041598849471124205 2437199640599568551671577)
                    ·
                      refine ⟨1827899730449676413753683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437199640599568551671577 1827899730449676413753683)
                      ·
                        rfl

theorem cell23_3559822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3559822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559822 prefixEnd_3559822 := by exact prefixLift 3559822
  have htrace : WordTrace (prefixWord ++ tailWord_3559822) baseStart_3559822 baseEnd_3559822 := by
    simpa [prefixWord, tailWord_3559822, baseEnd_3559822] using wordTrace_append hprefix tailTrace_3559822
  have hstable : (prefixWord ++ tailWord_3559822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559822).length < 2 ^ (prefixWord ++ tailWord_3559822).sum := by decide
  have hdescent : baseEnd_3559822 < baseStart_3559822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559831 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_3559831 : Nat := 118140960795 + 3559831 * 2 ^ 59
def prefixEnd_3559831 : Nat := 4983230072969 + 3 ^ 40 * 3559831 * 2
def baseEnd_3559831 : Nat := 1827904351775566878541141

theorem tailTrace_3559831 : CollatzResearch.WordTrace tailWord_3559831 prefixEnd_3559831 1827904351775566878541141 := by
  unfold tailWord_3559831
  simp only [CollatzResearch.WordTrace]
  refine ⟨129837703166347732576887347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86558468777565155051258231 129837703166347732576887347)
  ·
    refine ⟨194756554749521598865331021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129837703166347732576887347 194756554749521598865331021)
    ·
      refine ⟨73033708031070599574499133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194756554749521598865331021 73033708031070599574499133)
      ·
        refine ⟨27387640511651474840437175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73033708031070599574499133 27387640511651474840437175)
        ·
          refine ⟨41081460767477212260655763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27387640511651474840437175 41081460767477212260655763)
          ·
            refine ⟨61622191151215818390983645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41081460767477212260655763 61622191151215818390983645)
            ·
              refine ⟨23108321681705931896618867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61622191151215818390983645 23108321681705931896618867)
              ·
                refine ⟨34662482522558897844928301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23108321681705931896618867 34662482522558897844928301)
                ·
                  refine ⟨12998430945959586691848113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34662482522558897844928301 12998430945959586691848113)
                  ·
                    refine ⟨9748823209469690018886085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12998430945959586691848113 9748823209469690018886085)
                    ·
                      refine ⟨1827904351775566878541141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9748823209469690018886085 1827904351775566878541141)
                      ·
                        rfl

theorem cell23_3559831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_3559831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559831 prefixEnd_3559831 := by exact prefixLift 3559831
  have htrace : WordTrace (prefixWord ++ tailWord_3559831) baseStart_3559831 baseEnd_3559831 := by
    simpa [prefixWord, tailWord_3559831, baseEnd_3559831] using wordTrace_append hprefix tailTrace_3559831
  have hstable : (prefixWord ++ tailWord_3559831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559831).length < 2 ^ (prefixWord ++ tailWord_3559831).sum := by decide
  have hdescent : baseEnd_3559831 < baseStart_3559831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559841 : List Nat := [1, 2, 3, 5, 12]
def baseStart_3559841 : Nat := 118140960795 + 3559841 * 2 ^ 59
def prefixEnd_3559841 : Nat := 4983230072969 + 3 ^ 40 * 3559841 * 2
def baseEnd_3559841 : Nat := 2507420420551593744055

theorem tailTrace_3559841 : CollatzResearch.WordTrace tailWord_3559841 prefixEnd_3559841 2507420420551593744055 := by
  unfold tailWord_3559841
  simp only [CollatzResearch.WordTrace]
  refine ⟨129838067896311504284751377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86558711930874336189834251 129838067896311504284751377)
  ·
    refine ⟨97378550922233628213563533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129838067896311504284751377 97378550922233628213563533)
    ·
      refine ⟨36516956595837610580086325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97378550922233628213563533 36516956595837610580086325)
      ·
        refine ⟨3423464680859775991883093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36516956595837610580086325 3423464680859775991883093)
        ·
          refine ⟨2507420420551593744055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3423464680859775991883093 2507420420551593744055)
          ·
            rfl

theorem cell23_3559841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 12].length) (baseStart_3559841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559841 prefixEnd_3559841 := by exact prefixLift 3559841
  have htrace : WordTrace (prefixWord ++ tailWord_3559841) baseStart_3559841 baseEnd_3559841 := by
    simpa [prefixWord, tailWord_3559841, baseEnd_3559841] using wordTrace_append hprefix tailTrace_3559841
  have hstable : (prefixWord ++ tailWord_3559841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559841).length < 2 ^ (prefixWord ++ tailWord_3559841).sum := by decide
  have hdescent : baseEnd_3559841 < baseStart_3559841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559873 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3559873 : Nat := 118140960795 + 3559873 * 2 ^ 59
def prefixEnd_3559873 : Nat := 4983230072969 + 3 ^ 40 * 3559873 * 2
def baseEnd_3559873 : Nat := 1827925917963055714215949

theorem tailTrace_3559873 : CollatzResearch.WordTrace tailWord_3559873 prefixEnd_3559873 1827925917963055714215949 := by
  unfold tailWord_3559873
  simp only [CollatzResearch.WordTrace]
  refine ⟨129839235032195573749916273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86559490021463715833277515 129839235032195573749916273)
  ·
    refine ⟨97379426274146680312437205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129839235032195573749916273 97379426274146680312437205)
    ·
      refine ⟨2282330303300312819822747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 97379426274146680312437205 2282330303300312819822747)
      ·
        refine ⟨3423495454950469229734121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282330303300312819822747 3423495454950469229734121)
        ·
          refine ⟨2567621591212851922300591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423495454950469229734121 2567621591212851922300591)
          ·
            refine ⟨3851432386819277883450887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567621591212851922300591 3851432386819277883450887)
            ·
              refine ⟨5777148580228916825176331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851432386819277883450887 5777148580228916825176331)
              ·
                refine ⟨8665722870343375237764497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5777148580228916825176331 8665722870343375237764497)
                ·
                  refine ⟨6499292152757531428323373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8665722870343375237764497 6499292152757531428323373)
                  ·
                    refine ⟨2437234557284074285621265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6499292152757531428323373 2437234557284074285621265)
                    ·
                      refine ⟨1827925917963055714215949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437234557284074285621265 1827925917963055714215949)
                      ·
                        rfl

theorem cell23_3559873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3559873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559873 prefixEnd_3559873 := by exact prefixLift 3559873
  have htrace : WordTrace (prefixWord ++ tailWord_3559873) baseStart_3559873 baseEnd_3559873 := by
    simpa [prefixWord, tailWord_3559873, baseEnd_3559873] using wordTrace_append hprefix tailTrace_3559873
  have hstable : (prefixWord ++ tailWord_3559873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559873).length < 2 ^ (prefixWord ++ tailWord_3559873).sum := by decide
  have hdescent : baseEnd_3559873 < baseStart_3559873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559908 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 2, 8, 2]
def baseStart_3559908 : Nat := 118140960795 + 3559908 * 2 ^ 59
def prefixEnd_3559908 : Nat := 4983230072969 + 3 ^ 40 * 3559908 * 2
def baseEnd_3559908 : Nat := 1827943889785963077278287

theorem tailTrace_3559908 : CollatzResearch.WordTrace tailWord_3559908 prefixEnd_3559908 1827943889785963077278287 := by
  unfold tailWord_3559908
  simp only [CollatzResearch.WordTrace]
  refine ⟨64920255793534387363720189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86560341058045849818293585 64920255793534387363720189)
  ·
    refine ⟨24345095922575395261395071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64920255793534387363720189 24345095922575395261395071)
    ·
      refine ⟨36517643883863092892092607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24345095922575395261395071 36517643883863092892092607)
      ·
        refine ⟨54776465825794639338138911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36517643883863092892092607 54776465825794639338138911)
        ·
          refine ⟨82164698738691959007208367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54776465825794639338138911 82164698738691959007208367)
          ·
            refine ⟨123247048108037938510812551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82164698738691959007208367 123247048108037938510812551)
            ·
              refine ⟨184870572162056907766218827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123247048108037938510812551 184870572162056907766218827)
              ·
                refine ⟨277305858243085361649328241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184870572162056907766218827 277305858243085361649328241)
                ·
                  refine ⟨207979393682314021236996181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277305858243085361649328241 207979393682314021236996181)
                  ·
                    refine ⟨2437258519714617436371049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 207979393682314021236996181 2437258519714617436371049)
                    ·
                      refine ⟨1827943889785963077278287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437258519714617436371049 1827943889785963077278287)
                      ·
                        rfl

theorem cell23_3559908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_3559908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559908 prefixEnd_3559908 := by exact prefixLift 3559908
  have htrace : WordTrace (prefixWord ++ tailWord_3559908) baseStart_3559908 baseEnd_3559908 := by
    simpa [prefixWord, tailWord_3559908, baseEnd_3559908] using wordTrace_append hprefix tailTrace_3559908
  have hstable : (prefixWord ++ tailWord_3559908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559908).length < 2 ^ (prefixWord ++ tailWord_3559908).sum := by decide
  have hdescent : baseEnd_3559908 < baseStart_3559908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559918 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_3559918 : Nat := 118140960795 + 3559918 * 2 ^ 59
def prefixEnd_3559918 : Nat := 4983230072969 + 3 ^ 40 * 3559918 * 2
def baseEnd_3559918 : Nat := 609316341530836012717747

theorem tailTrace_3559918 : CollatzResearch.WordTrace tailWord_3559918 prefixEnd_3559918 609316341530836012717747 := by
  unfold tailWord_3559918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16230109539629068304413051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86560584211355030956869605 16230109539629068304413051)
  ·
    refine ⟨24345164309443602456619577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16230109539629068304413051 24345164309443602456619577)
    ·
      refine ⟨18258873232082701842464683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24345164309443602456619577 18258873232082701842464683)
      ·
        refine ⟨27388309848124052763697025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18258873232082701842464683 27388309848124052763697025)
        ·
          refine ⟨20541232386093039572772769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27388309848124052763697025 20541232386093039572772769)
          ·
            refine ⟨15405924289569779679579577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20541232386093039572772769 15405924289569779679579577)
            ·
              refine ⟨11554443217177334759684683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15405924289569779679579577 11554443217177334759684683)
              ·
                refine ⟨17331664825766002139527025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11554443217177334759684683 17331664825766002139527025)
                ·
                  refine ⟨12998748619324501604645269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17331664825766002139527025 12998748619324501604645269)
                  ·
                    refine ⟨609316341530836012717747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12998748619324501604645269 609316341530836012717747)
                    ·
                      rfl

theorem cell23_3559918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_3559918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559918 prefixEnd_3559918 := by exact prefixLift 3559918
  have htrace : WordTrace (prefixWord ++ tailWord_3559918) baseStart_3559918 baseEnd_3559918 := by
    simpa [prefixWord, tailWord_3559918, baseEnd_3559918] using wordTrace_append hprefix tailTrace_3559918
  have hstable : (prefixWord ++ tailWord_3559918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559918).length < 2 ^ (prefixWord ++ tailWord_3559918).sum := by decide
  have hdescent : baseEnd_3559918 < baseStart_3559918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559965 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 7]
def baseStart_3559965 : Nat := 118140960795 + 3559965 * 2 ^ 59
def prefixEnd_3559965 : Nat := 4983230072969 + 3 ^ 40 * 3559965 * 2
def baseEnd_3559965 : Nat := 203108128687029928251725

theorem tailTrace_3559965 : CollatzResearch.WordTrace tailWord_3559965 prefixEnd_3559965 203108128687029928251725 := by
  unfold tailWord_3559965
  simp only [CollatzResearch.WordTrace]
  refine ⟨129842590547862273462265349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86561727031908182308176899 129842590547862273462265349)
  ·
    refine ⟨24345485727724176274174753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129842590547862273462265349 24345485727724176274174753)
    ·
      refine ⟨18259114295793132205631065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24345485727724176274174753 18259114295793132205631065)
      ·
        refine ⟨13694335721844849154223299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18259114295793132205631065 13694335721844849154223299)
        ·
          refine ⟨20541503582767273731334949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13694335721844849154223299 20541503582767273731334949)
          ·
            refine ⟨3851531921768863824625303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20541503582767273731334949 3851531921768863824625303)
            ·
              refine ⟨5777297882653295736937955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851531921768863824625303 5777297882653295736937955)
              ·
                refine ⟨8665946823979943605406933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5777297882653295736937955 8665946823979943605406933)
                ·
                  refine ⟨203108128687029928251725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8665946823979943605406933 203108128687029928251725)
                  ·
                    rfl

theorem cell23_3559965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_3559965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559965 prefixEnd_3559965 := by exact prefixLift 3559965
  have htrace : WordTrace (prefixWord ++ tailWord_3559965) baseStart_3559965 baseEnd_3559965 := by
    simpa [prefixWord, tailWord_3559965, baseEnd_3559965] using wordTrace_append hprefix tailTrace_3559965
  have hstable : (prefixWord ++ tailWord_3559965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559965).length < 2 ^ (prefixWord ++ tailWord_3559965).sum := by decide
  have hdescent : baseEnd_3559965 < baseStart_3559965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3559976 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_3559976 : Nat := 118140960795 + 3559976 * 2 ^ 59
def prefixEnd_3559976 : Nat := 4983230072969 + 3 ^ 40 * 3559976 * 2
def baseEnd_3559976 : Nat := 1827978806470468811227975

theorem tailTrace_3559976 : CollatzResearch.WordTrace tailWord_3559976 prefixEnd_3559976 1827978806470468811227975 := by
  unfold tailWord_3559976
  simp only [CollatzResearch.WordTrace]
  refine ⟨64921495875411211170457891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86561994500548281560610521 64921495875411211170457891)
  ·
    refine ⟨97382243813116816755686837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64921495875411211170457891 97382243813116816755686837)
    ·
      refine ⟨9129585357479701570845641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97382243813116816755686837 9129585357479701570845641)
      ·
        refine ⟨6847189018109776178134231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9129585357479701570845641 6847189018109776178134231)
        ·
          refine ⟨10270783527164664267201347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6847189018109776178134231 10270783527164664267201347)
          ·
            refine ⟨15406175290746996400802021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10270783527164664267201347 15406175290746996400802021)
            ·
              refine ⟨2888657867015061825150379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15406175290746996400802021 2888657867015061825150379)
              ·
                refine ⟨4332986800522592737725569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888657867015061825150379 4332986800522592737725569)
                ·
                  refine ⟨3249740100391944553294177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4332986800522592737725569 3249740100391944553294177)
                  ·
                    refine ⟨2437305075293958414970633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3249740100391944553294177 2437305075293958414970633)
                    ·
                      refine ⟨1827978806470468811227975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2437305075293958414970633 1827978806470468811227975)
                      ·
                        rfl

theorem cell23_3559976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_3559976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3559976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3559976 prefixEnd_3559976 := by exact prefixLift 3559976
  have htrace : WordTrace (prefixWord ++ tailWord_3559976) baseStart_3559976 baseEnd_3559976 := by
    simpa [prefixWord, tailWord_3559976, baseEnd_3559976] using wordTrace_append hprefix tailTrace_3559976
  have hstable : (prefixWord ++ tailWord_3559976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3559976).length < 2 ^ (prefixWord ++ tailWord_3559976).sum := by decide
  have hdescent : baseEnd_3559976 < baseStart_3559976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3559976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3560018 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3560018 : Nat := 118140960795 + 3560018 * 2 ^ 59
def prefixEnd_3560018 : Nat := 4983230072969 + 3 ^ 40 * 3560018 * 2
def baseEnd_3560018 : Nat := 1828000372657957646902781

theorem tailTrace_3560018 : CollatzResearch.WordTrace tailWord_3560018 prefixEnd_3560018 1828000372657957646902781 := by
  unfold tailWord_3560018
  simp only [CollatzResearch.WordTrace]
  refine ⟨32461130904167565878486177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86563015744446842342629805 32461130904167565878486177)
  ·
    refine ⟨24345848178125674408864633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32461130904167565878486177 24345848178125674408864633)
    ·
      refine ⟨18259386133594255806648475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24345848178125674408864633 18259386133594255806648475)
      ·
        refine ⟨27389079200391383709972713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18259386133594255806648475 27389079200391383709972713)
        ·
          refine ⟨20541809400293537782479535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27389079200391383709972713 20541809400293537782479535)
          ·
            refine ⟨30812714100440306673719303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20541809400293537782479535 30812714100440306673719303)
            ·
              refine ⟨46219071150660460010578955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30812714100440306673719303 46219071150660460010578955)
              ·
                refine ⟨69328606725990690015868433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46219071150660460010578955 69328606725990690015868433)
                ·
                  refine ⟨51996455044493017511901325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69328606725990690015868433 51996455044493017511901325)
                  ·
                    refine ⟨19498670641684881566962997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51996455044493017511901325 19498670641684881566962997)
                    ·
                      refine ⟨1828000372657957646902781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19498670641684881566962997 1828000372657957646902781)
                      ·
                        rfl

theorem cell23_3560018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3560018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3560018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3560018 prefixEnd_3560018 := by exact prefixLift 3560018
  have htrace : WordTrace (prefixWord ++ tailWord_3560018) baseStart_3560018 baseEnd_3560018 := by
    simpa [prefixWord, tailWord_3560018, baseEnd_3560018] using wordTrace_append hprefix tailTrace_3560018
  have hstable : (prefixWord ++ tailWord_3560018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3560018).length < 2 ^ (prefixWord ++ tailWord_3560018).sum := by decide
  have hdescent : baseEnd_3560018 < baseStart_3560018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3560018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
