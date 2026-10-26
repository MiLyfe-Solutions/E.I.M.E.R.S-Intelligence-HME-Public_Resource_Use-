import V185TrunkScan23Chunk0964

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5712794 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2]
def baseStart_5712794 : Nat := 118140960795 + 5712794 * 2 ^ 59
def prefixEnd_5712794 : Nat := 4983230072969 + 3 ^ 40 * 5712794 * 2
def baseEnd_5712794 : Nat := 2933409202121426900902345

theorem tailTrace_5712794 : CollatzResearch.WordTrace tailWord_5712794 prefixEnd_5712794 2933409202121426900902345 := by
  unfold tailWord_5712794
  simp only [CollatzResearch.WordTrace]
  refine ⟨52090678716382620095862359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138908476577020320255632957 52090678716382620095862359)
  ·
    refine ⟨78136018074573930143793539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52090678716382620095862359 78136018074573930143793539)
    ·
      refine ⟨117204027111860895215690309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78136018074573930143793539 117204027111860895215690309)
      ·
        refine ⟨21975755083473917852941933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117204027111860895215690309 21975755083473917852941933)
        ·
          refine ⟨8240908156302719194853225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21975755083473917852941933 8240908156302719194853225)
          ·
            refine ⟨6180681117227039396139919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8240908156302719194853225 6180681117227039396139919)
            ·
              refine ⟨9271021675840559094209879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6180681117227039396139919 9271021675840559094209879)
              ·
                refine ⟨13906532513760838641314819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9271021675840559094209879 13906532513760838641314819)
                ·
                  refine ⟨20859798770641257961972229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13906532513760838641314819 20859798770641257961972229)
                  ·
                    refine ⟨3911212269495235867869793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20859798770641257961972229 3911212269495235867869793)
                    ·
                      refine ⟨2933409202121426900902345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911212269495235867869793 2933409202121426900902345)
                      ·
                        rfl

theorem cell23_5712794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_5712794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712794 prefixEnd_5712794 := by exact prefixLift 5712794
  have htrace : WordTrace (prefixWord ++ tailWord_5712794) baseStart_5712794 baseEnd_5712794 := by
    simpa [prefixWord, tailWord_5712794, baseEnd_5712794] using wordTrace_append hprefix tailTrace_5712794
  have hstable : (prefixWord ++ tailWord_5712794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712794).length < 2 ^ (prefixWord ++ tailWord_5712794).sum := by decide
  have hdescent : baseEnd_5712794 < baseStart_5712794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712830 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_5712830 : Nat := 118140960795 + 5712830 * 2 ^ 59
def prefixEnd_5712830 : Nat := 4983230072969 + 3 ^ 40 * 5712830 * 2
def baseEnd_5712830 : Nat := 977809229141662920017393

theorem tailTrace_5712830 : CollatzResearch.WordTrace tailWord_5712830 prefixEnd_5712830 977809229141662920017393 := by
  unfold tailWord_5712830
  simp only [CollatzResearch.WordTrace]
  refine ⟨26045503486675007316469993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138909351928933372354506629 26045503486675007316469993)
  ·
    refine ⟨19534127615006255487352495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26045503486675007316469993 19534127615006255487352495)
    ·
      refine ⟨29301191422509383231028743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19534127615006255487352495 29301191422509383231028743)
      ·
        refine ⟨43951787133764074846543115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29301191422509383231028743 43951787133764074846543115)
        ·
          refine ⟨65927680700646112269814673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43951787133764074846543115 65927680700646112269814673)
          ·
            refine ⟨49445760525484584202361005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65927680700646112269814673 49445760525484584202361005)
            ·
              refine ⟨18542160197056719075885377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49445760525484584202361005 18542160197056719075885377)
              ·
                refine ⟨13906620147792539306914033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18542160197056719075885377 13906620147792539306914033)
                ·
                  refine ⟨10429965110844404480185525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13906620147792539306914033 10429965110844404480185525)
                  ·
                    refine ⟨977809229141662920017393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10429965110844404480185525 977809229141662920017393)
                    ·
                      rfl

theorem cell23_5712830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_5712830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712830 prefixEnd_5712830 := by exact prefixLift 5712830
  have htrace : WordTrace (prefixWord ++ tailWord_5712830) baseStart_5712830 baseEnd_5712830 := by
    simpa [prefixWord, tailWord_5712830, baseEnd_5712830] using wordTrace_append hprefix tailTrace_5712830
  have hstable : (prefixWord ++ tailWord_5712830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712830).length < 2 ^ (prefixWord ++ tailWord_5712830).sum := by decide
  have hdescent : baseEnd_5712830 < baseStart_5712830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712840 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_5712840 : Nat := 118140960795 + 5712840 * 2 ^ 59
def prefixEnd_5712840 : Nat := 4983230072969 + 3 ^ 40 * 5712840 * 2
def baseEnd_5712840 : Nat := 2933432822231533720927133

theorem tailTrace_5712840 : CollatzResearch.WordTrace tailWord_5712840 prefixEnd_5712840 2933432822231533720927133 := by
  unfold tailWord_5712840
  simp only [CollatzResearch.WordTrace]
  refine ⟨104182196311681915119811987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138909595082242553493082649 104182196311681915119811987)
  ·
    refine ⟨156273294467522872679717981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104182196311681915119811987 156273294467522872679717981)
    ·
      refine ⟨58602485425321077254894243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156273294467522872679717981 58602485425321077254894243)
      ·
        refine ⟨87903728137981615882341365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58602485425321077254894243 87903728137981615882341365)
        ·
          refine ⟨8240974512935776488969503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87903728137981615882341365 8240974512935776488969503)
          ·
            refine ⟨12361461769403664733454255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8240974512935776488969503 12361461769403664733454255)
            ·
              refine ⟨18542192654105497100181383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12361461769403664733454255 18542192654105497100181383)
              ·
                refine ⟨27813288981158245650272075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18542192654105497100181383 27813288981158245650272075)
                ·
                  refine ⟨41719933471737368475408113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27813288981158245650272075 41719933471737368475408113)
                  ·
                    refine ⟨31289950103803026356556085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41719933471737368475408113 31289950103803026356556085)
                    ·
                      refine ⟨2933432822231533720927133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31289950103803026356556085 2933432822231533720927133)
                      ·
                        rfl

theorem cell23_5712840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_5712840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712840 prefixEnd_5712840 := by exact prefixLift 5712840
  have htrace : WordTrace (prefixWord ++ tailWord_5712840) baseStart_5712840 baseEnd_5712840 := by
    simpa [prefixWord, tailWord_5712840, baseEnd_5712840] using wordTrace_append hprefix tailTrace_5712840
  have hstable : (prefixWord ++ tailWord_5712840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712840).length < 2 ^ (prefixWord ++ tailWord_5712840).sum := by decide
  have hdescent : baseEnd_5712840 < baseStart_5712840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712845 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5712845 : Nat := 118140960795 + 5712845 * 2 ^ 59
def prefixEnd_5712845 : Nat := 4983230072969 + 3 ^ 40 * 5712845 * 2
def baseEnd_5712845 : Nat := 2933435389634806201364611

theorem tailTrace_5712845 : CollatzResearch.WordTrace tailWord_5712845 prefixEnd_5712845 2933435389634806201364611 := by
  unfold tailWord_5712845
  simp only [CollatzResearch.WordTrace]
  refine ⟨208364574988345716093555989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138909716658897144062370659 208364574988345716093555989)
  ·
    refine ⟨9767089452578705441885437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 208364574988345716093555989 9767089452578705441885437)
    ·
      refine ⟨3662658544717014540707039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9767089452578705441885437 3662658544717014540707039)
      ·
        refine ⟨5493987817075521811060559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3662658544717014540707039 5493987817075521811060559)
        ·
          refine ⟨8240981725613282716590839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493987817075521811060559 8240981725613282716590839)
          ·
            refine ⟨12361472588419924074886259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8240981725613282716590839 12361472588419924074886259)
            ·
              refine ⟨18542208882629886112329389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12361472588419924074886259 18542208882629886112329389)
              ·
                refine ⟨6953328330986207292123521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18542208882629886112329389 6953328330986207292123521)
                ·
                  refine ⟨5214996248239655469092641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6953328330986207292123521 5214996248239655469092641)
                  ·
                    refine ⟨3911247186179741601819481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5214996248239655469092641 3911247186179741601819481)
                    ·
                      refine ⟨2933435389634806201364611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911247186179741601819481 2933435389634806201364611)
                      ·
                        rfl

theorem cell23_5712845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5712845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712845 prefixEnd_5712845 := by exact prefixLift 5712845
  have htrace : WordTrace (prefixWord ++ tailWord_5712845) baseStart_5712845 baseEnd_5712845 := by
    simpa [prefixWord, tailWord_5712845, baseEnd_5712845] using wordTrace_append hprefix tailTrace_5712845
  have hstable : (prefixWord ++ tailWord_5712845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712845).length < 2 ^ (prefixWord ++ tailWord_5712845).sum := by decide
  have hdescent : baseEnd_5712845 < baseStart_5712845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712893 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_5712893 : Nat := 118140960795 + 5712893 * 2 ^ 59
def prefixEnd_5712893 : Nat := 4983230072969 + 3 ^ 40 * 5712893 * 2
def baseEnd_5712893 : Nat := 2933460036706222013564389

theorem tailTrace_5712893 : CollatzResearch.WordTrace tailWord_5712893 prefixEnd_5712893 2933460036706222013564389 := by
  unfold tailWord_5712893
  simp only [CollatzResearch.WordTrace]
  refine ⟨208366325692171820291303333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138910883794781213527535555 208366325692171820291303333)
  ·
    refine ⟨39068686067282216304619375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208366325692171820291303333 39068686067282216304619375)
    ·
      refine ⟨58603029100923324456929063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39068686067282216304619375 58603029100923324456929063)
      ·
        refine ⟨87904543651384986685393595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58603029100923324456929063 87904543651384986685393595)
        ·
          refine ⟨131856815477077480028090393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87904543651384986685393595 131856815477077480028090393)
          ·
            refine ⟨98892611607808110021067795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131856815477077480028090393 98892611607808110021067795)
            ·
              refine ⟨148338917411712165031601693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98892611607808110021067795 148338917411712165031601693)
              ·
                refine ⟨55627094029392061886850635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148338917411712165031601693 55627094029392061886850635)
                ·
                  refine ⟨83440641044088092830275953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55627094029392061886850635 83440641044088092830275953)
                  ·
                    refine ⟨62580480783066069622706965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83440641044088092830275953 62580480783066069622706965)
                    ·
                      refine ⟨2933460036706222013564389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62580480783066069622706965 2933460036706222013564389)
                      ·
                        rfl

theorem cell23_5712893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_5712893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712893 prefixEnd_5712893 := by exact prefixLift 5712893
  have htrace : WordTrace (prefixWord ++ tailWord_5712893) baseStart_5712893 baseEnd_5712893 := by
    simpa [prefixWord, tailWord_5712893, baseEnd_5712893] using wordTrace_append hprefix tailTrace_5712893
  have hstable : (prefixWord ++ tailWord_5712893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712893).length < 2 ^ (prefixWord ++ tailWord_5712893).sum := by decide
  have hdescent : baseEnd_5712893 < baseStart_5712893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712917 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_5712917 : Nat := 118140960795 + 5712917 * 2 ^ 59
def prefixEnd_5712917 : Nat := 4983230072969 + 3 ^ 40 * 5712917 * 2
def baseEnd_5712917 : Nat := 2933472360241929919664279

theorem tailTrace_5712917 : CollatzResearch.WordTrace tailWord_5712917 prefixEnd_5712917 2933472360241929919664279 := by
  unfold tailWord_5712917
  simp only [CollatzResearch.WordTrace]
  refine ⟨208367201044084872390177005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138911467362723248260118003 208367201044084872390177005)
  ·
    refine ⟨78137700391531827146316377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208367201044084872390177005 78137700391531827146316377)
    ·
      refine ⟨58603275293648870359737283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78137700391531827146316377 58603275293648870359737283)
      ·
        refine ⟨87904912940473305539605925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58603275293648870359737283 87904912940473305539605925)
        ·
          refine ⟨16482171176338744788676111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87904912940473305539605925 16482171176338744788676111)
          ·
            refine ⟨24723256764508117183014167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16482171176338744788676111 24723256764508117183014167)
            ·
              refine ⟨37084885146762175774521251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24723256764508117183014167 37084885146762175774521251)
              ·
                refine ⟨55627327720143263661781877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37084885146762175774521251 55627327720143263661781877)
                ·
                  refine ⟨5215061973763430968292051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55627327720143263661781877 5215061973763430968292051)
                  ·
                    refine ⟨7822592960645146452438077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5215061973763430968292051 7822592960645146452438077)
                    ·
                      refine ⟨2933472360241929919664279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7822592960645146452438077 2933472360241929919664279)
                      ·
                        rfl

theorem cell23_5712917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_5712917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712917 prefixEnd_5712917 := by exact prefixLift 5712917
  have htrace : WordTrace (prefixWord ++ tailWord_5712917) baseStart_5712917 baseEnd_5712917 := by
    simpa [prefixWord, tailWord_5712917, baseEnd_5712917] using wordTrace_append hprefix tailTrace_5712917
  have hstable : (prefixWord ++ tailWord_5712917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712917).length < 2 ^ (prefixWord ++ tailWord_5712917).sum := by decide
  have hdescent : baseEnd_5712917 < baseStart_5712917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712920 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 3, 5]
def baseStart_5712920 : Nat := 118140960795 + 5712920 * 2 ^ 59
def prefixEnd_5712920 : Nat := 4983230072969 + 3 ^ 40 * 5712920 * 2
def baseEnd_5712920 : Nat := 977824633561297802642255

theorem tailTrace_5712920 : CollatzResearch.WordTrace tailWord_5712920 prefixEnd_5712920 977824633561297802642255 := by
  unfold tailWord_5712920
  simp only [CollatzResearch.WordTrace]
  refine ⟨104183655231537001951268107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138911540308716002601690809 104183655231537001951268107)
  ·
    refine ⟨156275482847305502926902161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104183655231537001951268107 156275482847305502926902161)
    ·
      refine ⟨117206612135479127195176621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156275482847305502926902161 117206612135479127195176621)
      ·
        refine ⟨43952479550804672698191233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117206612135479127195176621 43952479550804672698191233)
        ·
          refine ⟨32964359663103504523643425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43952479550804672698191233 32964359663103504523643425)
          ·
            refine ⟨24723269747327628392732569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32964359663103504523643425 24723269747327628392732569)
            ·
              refine ⟨18542452310495721294549427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24723269747327628392732569 18542452310495721294549427)
              ·
                refine ⟨27813678465743581941824141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18542452310495721294549427 27813678465743581941824141)
                ·
                  refine ⟨10430129424653843228184053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27813678465743581941824141 10430129424653843228184053)
                  ·
                    refine ⟨977824633561297802642255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10430129424653843228184053 977824633561297802642255)
                    ·
                      rfl

theorem cell23_5712920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_5712920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712920 prefixEnd_5712920 := by exact prefixLift 5712920
  have htrace : WordTrace (prefixWord ++ tailWord_5712920) baseStart_5712920 baseEnd_5712920 := by
    simpa [prefixWord, tailWord_5712920, baseEnd_5712920] using wordTrace_append hprefix tailTrace_5712920
  have hstable : (prefixWord ++ tailWord_5712920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712920).length < 2 ^ (prefixWord ++ tailWord_5712920).sum := by decide
  have hdescent : baseEnd_5712920 < baseStart_5712920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712927 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 1, 5, 2]
def baseStart_5712927 : Nat := 118140960795 + 5712927 * 2 ^ 59
def prefixEnd_5712927 : Nat := 4983230072969 + 3 ^ 40 * 5712927 * 2
def baseEnd_5712927 : Nat := 2933477495048474880539233

theorem tailTrace_5712927 : CollatzResearch.WordTrace tailWord_5712927 prefixEnd_5712927 2933477495048474880539233 := by
  unfold tailWord_5712927
  simp only [CollatzResearch.WordTrace]
  refine ⟨208367565774048644098041035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138911710516032429398694023 208367565774048644098041035)
  ·
    refine ⟨312551348661072966147061553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208367565774048644098041035 312551348661072966147061553)
    ·
      refine ⟨234413511495804724610296165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312551348661072966147061553 234413511495804724610296165)
      ·
        refine ⟨43952533405463385864430531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234413511495804724610296165 43952533405463385864430531)
        ·
          refine ⟨65928800108195078796645797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43952533405463385864430531 65928800108195078796645797)
          ·
            refine ⟨12361650020286577274371087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65928800108195078796645797 12361650020286577274371087)
            ·
              refine ⟨18542475030429865911556631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12361650020286577274371087 18542475030429865911556631)
              ·
                refine ⟨27813712545644798867334947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18542475030429865911556631 27813712545644798867334947)
                ·
                  refine ⟨41720568818467198301002421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27813712545644798867334947 41720568818467198301002421)
                  ·
                    refine ⟨3911303326731299840718977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41720568818467198301002421 3911303326731299840718977)
                    ·
                      refine ⟨2933477495048474880539233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911303326731299840718977 2933477495048474880539233)
                      ·
                        rfl

theorem cell23_5712927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_5712927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712927 prefixEnd_5712927 := by exact prefixLift 5712927
  have htrace : WordTrace (prefixWord ++ tailWord_5712927) baseStart_5712927 baseEnd_5712927 := by
    simpa [prefixWord, tailWord_5712927, baseEnd_5712927] using wordTrace_append hprefix tailTrace_5712927
  have hstable : (prefixWord ++ tailWord_5712927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712927).length < 2 ^ (prefixWord ++ tailWord_5712927).sum := by decide
  have hdescent : baseEnd_5712927 < baseStart_5712927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712960 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 5]
def baseStart_5712960 : Nat := 118140960795 + 5712960 * 2 ^ 59
def prefixEnd_5712960 : Nat := 4983230072969 + 3 ^ 40 * 5712960 * 2
def baseEnd_5712960 : Nat := 2933494439910073251426581

theorem tailTrace_5712960 : CollatzResearch.WordTrace tailWord_5712960 prefixEnd_5712960 2933494439910073251426581 := by
  unfold tailWord_5712960
  simp only [CollatzResearch.WordTrace]
  refine ⟨104184384691464545366996167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138912512921952727155994889 104184384691464545366996167)
  ·
    refine ⟨156276577037196818050494251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104184384691464545366996167 156276577037196818050494251)
    ·
      refine ⟨234414865555795227075741377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156276577037196818050494251 234414865555795227075741377)
      ·
        refine ⟨175811149166846420306806033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234414865555795227075741377 175811149166846420306806033)
        ·
          refine ⟨131858361875134815230104525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175811149166846420306806033 131858361875134815230104525)
          ·
            refine ⟨49446885703175555711289197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131858361875134815230104525 49446885703175555711289197)
            ·
              refine ⟨18542582138690833391733449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49446885703175555711289197 18542582138690833391733449)
              ·
                refine ⟨13906936604018125043800087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18542582138690833391733449 13906936604018125043800087)
                ·
                  refine ⟨20860404906027187565700131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13906936604018125043800087 20860404906027187565700131)
                  ·
                    refine ⟨31290607359040781348550197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20860404906027187565700131 31290607359040781348550197)
                    ·
                      refine ⟨2933494439910073251426581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31290607359040781348550197 2933494439910073251426581)
                      ·
                        rfl

theorem cell23_5712960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_5712960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712960 prefixEnd_5712960 := by exact prefixLift 5712960
  have htrace : WordTrace (prefixWord ++ tailWord_5712960) baseStart_5712960 baseEnd_5712960 := by
    simpa [prefixWord, tailWord_5712960, baseEnd_5712960] using wordTrace_append hprefix tailTrace_5712960
  have hstable : (prefixWord ++ tailWord_5712960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712960).length < 2 ^ (prefixWord ++ tailWord_5712960).sum := by decide
  have hdescent : baseEnd_5712960 < baseStart_5712960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712963 : List Nat := [1, 1, 1, 3, 1, 2, 4, 10]
def baseStart_5712963 : Nat := 118140960795 + 5712963 * 2 ^ 59
def prefixEnd_5712963 : Nat := 4983230072969 + 3 ^ 40 * 5712963 * 2
def baseEnd_5712963 : Nat := 108647999272297657025521

theorem tailTrace_5712963 : CollatzResearch.WordTrace tailWord_5712963 prefixEnd_5712963 108647999272297657025521 := by
  unfold tailWord_5712963
  simp only [CollatzResearch.WordTrace]
  refine ⟨208368878801918222246351543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138912585867945481497567695 208368878801918222246351543)
  ·
    refine ⟨312553318202877333369527315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208368878801918222246351543 312553318202877333369527315)
    ·
      refine ⟨468829977304316000054290973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312553318202877333369527315 468829977304316000054290973)
      ·
        refine ⟨175811241489118500020359115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468829977304316000054290973 175811241489118500020359115)
        ·
          refine ⟨263716862233677750030538673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175811241489118500020359115 263716862233677750030538673)
          ·
            refine ⟨197787646675258312522904005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263716862233677750030538673 197787646675258312522904005)
            ·
              refine ⟨37085183751610933598044501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197787646675258312522904005 37085183751610933598044501)
              ·
                refine ⟨108647999272297657025521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37085183751610933598044501 108647999272297657025521)
                ·
                  rfl

theorem cell23_5712963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 10].length) (baseStart_5712963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712963 prefixEnd_5712963 := by exact prefixLift 5712963
  have htrace : WordTrace (prefixWord ++ tailWord_5712963) baseStart_5712963 baseEnd_5712963 := by
    simpa [prefixWord, tailWord_5712963, baseEnd_5712963] using wordTrace_append hprefix tailTrace_5712963
  have hstable : (prefixWord ++ tailWord_5712963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712963).length < 2 ^ (prefixWord ++ tailWord_5712963).sum := by decide
  have hdescent : baseEnd_5712963 < baseStart_5712963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712967 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 1, 6]
def baseStart_5712967 : Nat := 118140960795 + 5712967 * 2 ^ 59
def prefixEnd_5712967 : Nat := 4983230072969 + 3 ^ 40 * 5712967 * 2
def baseEnd_5712967 : Nat := 977832678091551574679683

theorem tailTrace_5712967 : CollatzResearch.WordTrace tailWord_5712967 prefixEnd_5712967 977832678091551574679683 := by
  unfold tailWord_5712967
  simp only [CollatzResearch.WordTrace]
  refine ⟨208369024693903730929497155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138912683129269153952998103 208369024693903730929497155)
  ·
    refine ⟨312553537040855596394245733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208369024693903730929497155 312553537040855596394245733)
    ·
      refine ⟨58603788195160424323921075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312553537040855596394245733 58603788195160424323921075)
      ·
        refine ⟨87905682292740636485881613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58603788195160424323921075 87905682292740636485881613)
        ·
          refine ⟨32964630859777738682205605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87905682292740636485881613 32964630859777738682205605)
          ·
            refine ⟨6180868286208326002913551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32964630859777738682205605 6180868286208326002913551)
            ·
              refine ⟨9271302429312489004370327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6180868286208326002913551 9271302429312489004370327)
              ·
                refine ⟨13906953643968733506555491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9271302429312489004370327 13906953643968733506555491)
                ·
                  refine ⟨20860430465953100259833237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13906953643968733506555491 20860430465953100259833237)
                  ·
                    refine ⟨977832678091551574679683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20860430465953100259833237 977832678091551574679683)
                    ·
                      rfl

theorem cell23_5712967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_5712967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712967 prefixEnd_5712967 := by exact prefixLift 5712967
  have htrace : WordTrace (prefixWord ++ tailWord_5712967) baseStart_5712967 baseEnd_5712967 := by
    simpa [prefixWord, tailWord_5712967, baseEnd_5712967] using wordTrace_append hprefix tailTrace_5712967
  have hstable : (prefixWord ++ tailWord_5712967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712967).length < 2 ^ (prefixWord ++ tailWord_5712967).sum := by decide
  have hdescent : baseEnd_5712967 < baseStart_5712967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712974 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2]
def baseStart_5712974 : Nat := 118140960795 + 5712974 * 2 ^ 59
def prefixEnd_5712974 : Nat := 4983230072969 + 3 ^ 40 * 5712974 * 2
def baseEnd_5712974 : Nat := 2933501628639236196651517

theorem tailTrace_5712974 : CollatzResearch.WordTrace tailWord_5712974 prefixEnd_5712974 2933501628639236196651517 := by
  unfold tailWord_5712974
  simp only [CollatzResearch.WordTrace]
  refine ⟨26046160000609796390625247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138912853336585580750001317 26046160000609796390625247)
  ·
    refine ⟨39069240000914694585937871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26046160000609796390625247 39069240000914694585937871)
    ·
      refine ⟨58603860001372041878906807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39069240000914694585937871 58603860001372041878906807)
      ·
        refine ⟨87905790002058062818360211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58603860001372041878906807 87905790002058062818360211)
        ·
          refine ⟨131858685003087094227540317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87905790002058062818360211 131858685003087094227540317)
          ·
            refine ⟨49447006876157660335327619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131858685003087094227540317 49447006876157660335327619)
            ·
              refine ⟨74170510314236490502991429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49447006876157660335327619 74170510314236490502991429)
              ·
                refine ⟨13906970683919341969310893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74170510314236490502991429 13906970683919341969310893)
                ·
                  refine ⟨5215114006469753238491585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13906970683919341969310893 5215114006469753238491585)
                  ·
                    refine ⟨3911335504852314928868689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5215114006469753238491585 3911335504852314928868689)
                    ·
                      refine ⟨2933501628639236196651517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911335504852314928868689 2933501628639236196651517)
                      ·
                        rfl

theorem cell23_5712974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_5712974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712974 prefixEnd_5712974 := by exact prefixLift 5712974
  have htrace : WordTrace (prefixWord ++ tailWord_5712974) baseStart_5712974 baseEnd_5712974 := by
    simpa [prefixWord, tailWord_5712974, baseEnd_5712974] using wordTrace_append hprefix tailTrace_5712974
  have hstable : (prefixWord ++ tailWord_5712974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712974).length < 2 ^ (prefixWord ++ tailWord_5712974).sum := by decide
  have hdescent : baseEnd_5712974 < baseStart_5712974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712977 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 1, 2, 3]
def baseStart_5712977 : Nat := 118140960795 + 5712977 * 2 ^ 59
def prefixEnd_5712977 : Nat := 4983230072969 + 3 ^ 40 * 5712977 * 2
def baseEnd_5712977 : Nat := 2933503169081199684914003

theorem tailTrace_5712977 : CollatzResearch.WordTrace tailWord_5712977 prefixEnd_5712977 2933503169081199684914003 := by
  unfold tailWord_5712977
  simp only [CollatzResearch.WordTrace]
  refine ⟨208369389423867502637361185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138912926282578335091574123 208369389423867502637361185)
  ·
    refine ⟨156277042067900626978020889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208369389423867502637361185 156277042067900626978020889)
    ·
      refine ⟨117207781550925470233515667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156277042067900626978020889 117207781550925470233515667)
      ·
        refine ⟨175811672326388205350273501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117207781550925470233515667 175811672326388205350273501)
        ·
          refine ⟨65929377122395577006352563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175811672326388205350273501 65929377122395577006352563)
          ·
            refine ⟨98894065683593365509528845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65929377122395577006352563 98894065683593365509528845)
            ·
              refine ⟨37085274631347512066073317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98894065683593365509528845 37085274631347512066073317)
              ·
                refine ⟨6953488993377658512388747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37085274631347512066073317 6953488993377658512388747)
                ·
                  refine ⟨10430233490066487768583121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6953488993377658512388747 10430233490066487768583121)
                  ·
                    refine ⟨7822675117549865826437341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10430233490066487768583121 7822675117549865826437341)
                    ·
                      refine ⟨2933503169081199684914003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7822675117549865826437341 2933503169081199684914003)
                      ·
                        rfl

theorem cell23_5712977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_5712977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712977 prefixEnd_5712977 := by exact prefixLift 5712977
  have htrace : WordTrace (prefixWord ++ tailWord_5712977) baseStart_5712977 baseEnd_5712977 := by
    simpa [prefixWord, tailWord_5712977, baseEnd_5712977] using wordTrace_append hprefix tailTrace_5712977
  have hstable : (prefixWord ++ tailWord_5712977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712977).length < 2 ^ (prefixWord ++ tailWord_5712977).sum := by decide
  have hdescent : baseEnd_5712977 < baseStart_5712977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5712994 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5712994 : Nat := 118140960795 + 5712994 * 2 ^ 59
def prefixEnd_5712994 : Nat := 4983230072969 + 3 ^ 40 * 5712994 * 2
def baseEnd_5712994 : Nat := 2933511898252326118401425

theorem tailTrace_5712994 : CollatzResearch.WordTrace tailWord_5712994 prefixEnd_5712994 2933511898252326118401425 := by
  unfold tailWord_5712994
  simp only [CollatzResearch.WordTrace]
  refine ⟨52092502366201478635182509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138913339643203943027153357 52092502366201478635182509)
  ·
    refine ⟨19534688387325554488193441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52092502366201478635182509 19534688387325554488193441)
    ·
      refine ⟨14651016290494165866145081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19534688387325554488193441 14651016290494165866145081)
      ·
        refine ⟨10988262217870624399608811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14651016290494165866145081 10988262217870624399608811)
        ·
          refine ⟨16482393326805936599413217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10988262217870624399608811 16482393326805936599413217)
          ·
            refine ⟨12361794995104452449559913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16482393326805936599413217 12361794995104452449559913)
            ·
              refine ⟨9271346246328339337169935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12361794995104452449559913 9271346246328339337169935)
              ·
                refine ⟨13907019369492509005754903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9271346246328339337169935 13907019369492509005754903)
                ·
                  refine ⟨20860529054238763508632355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13907019369492509005754903 20860529054238763508632355)
                  ·
                    refine ⟨31290793581358145262948533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20860529054238763508632355 31290793581358145262948533)
                    ·
                      refine ⟨2933511898252326118401425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31290793581358145262948533 2933511898252326118401425)
                      ·
                        rfl

theorem cell23_5712994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5712994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5712994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5712994 prefixEnd_5712994 := by exact prefixLift 5712994
  have htrace : WordTrace (prefixWord ++ tailWord_5712994) baseStart_5712994 baseEnd_5712994 := by
    simpa [prefixWord, tailWord_5712994, baseEnd_5712994] using wordTrace_append hprefix tailTrace_5712994
  have hstable : (prefixWord ++ tailWord_5712994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5712994).length < 2 ^ (prefixWord ++ tailWord_5712994).sum := by decide
  have hdescent : baseEnd_5712994 < baseStart_5712994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5712994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713007 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 4, 1, 3]
def baseStart_5713007 : Nat := 118140960795 + 5713007 * 2 ^ 59
def prefixEnd_5713007 : Nat := 4983230072969 + 3 ^ 40 * 5713007 * 2
def baseEnd_5713007 : Nat := 2933518573500834567538865

theorem tailTrace_5713007 : CollatzResearch.WordTrace tailWord_5713007 prefixEnd_5713007 2933518573500834567538865 := by
  unfold tailWord_5713007
  simp only [CollatzResearch.WordTrace]
  refine ⟨208370483613758817760953275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138913655742505878507302183 208370483613758817760953275)
  ·
    refine ⟨312555725420638226641429913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208370483613758817760953275 312555725420638226641429913)
    ·
      refine ⟨234416794065478669981072435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312555725420638226641429913 234416794065478669981072435)
      ·
        refine ⟨351625191098218004971608653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234416794065478669981072435 351625191098218004971608653)
        ·
          refine ⟨131859446661831751864353245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351625191098218004971608653 131859446661831751864353245)
          ·
            refine ⟨49447292498186906949132467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131859446661831751864353245 49447292498186906949132467)
            ·
              refine ⟨74170938747280360423698701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49447292498186906949132467 74170938747280360423698701)
              ·
                refine ⟨27814102030230135158887013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74170938747280360423698701 27814102030230135158887013)
                ·
                  refine ⟨5215144130668150342291315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27814102030230135158887013 5215144130668150342291315)
                  ·
                    refine ⟨7822716196002225513436973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5215144130668150342291315 7822716196002225513436973)
                    ·
                      refine ⟨2933518573500834567538865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7822716196002225513436973 2933518573500834567538865)
                      ·
                        rfl

theorem cell23_5713007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 1, 3].length) (baseStart_5713007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713007 prefixEnd_5713007 := by exact prefixLift 5713007
  have htrace : WordTrace (prefixWord ++ tailWord_5713007) baseStart_5713007 baseEnd_5713007 := by
    simpa [prefixWord, tailWord_5713007, baseEnd_5713007] using wordTrace_append hprefix tailTrace_5713007
  have hstable : (prefixWord ++ tailWord_5713007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713007).length < 2 ^ (prefixWord ++ tailWord_5713007).sum := by decide
  have hdescent : baseEnd_5713007 < baseStart_5713007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713008 : List Nat := [2, 1, 1, 1, 5, 1, 5, 2, 1, 2, 2]
def baseStart_5713008 : Nat := 118140960795 + 5713008 * 2 ^ 59
def prefixEnd_5713008 : Nat := 4983230072969 + 3 ^ 40 * 5713008 * 2
def baseEnd_5713008 : Nat := 2933519086981489063626361

theorem tailTrace_5713008 : CollatzResearch.WordTrace tailWord_5713008 prefixEnd_5713008 2933519086981489063626361 := by
  unfold tailWord_5713008
  simp only [CollatzResearch.WordTrace]
  refine ⟨104185260043377597465869839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138913680057836796621159785 104185260043377597465869839)
  ·
    refine ⟨156277890065066396198804759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104185260043377597465869839 156277890065066396198804759)
    ·
      refine ⟨234416835097599594298207139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156277890065066396198804759 234416835097599594298207139)
      ·
        refine ⟨351625252646399391447310709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234416835097599594298207139 351625252646399391447310709)
        ·
          refine ⟨32964867435599942948185379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351625252646399391447310709 32964867435599942948185379)
          ·
            refine ⟨49447301153399914422278069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32964867435599942948185379 49447301153399914422278069)
            ·
              refine ⟨4635684483131241977088569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49447301153399914422278069 4635684483131241977088569)
              ·
                refine ⟨3476763362348431482816427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4635684483131241977088569 3476763362348431482816427)
                ·
                  refine ⟨5215145043522647224224641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476763362348431482816427 5215145043522647224224641)
                  ·
                    refine ⟨3911358782641985418168481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5215145043522647224224641 3911358782641985418168481)
                    ·
                      refine ⟨2933519086981489063626361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911358782641985418168481 2933519086981489063626361)
                      ·
                        rfl

theorem cell23_5713008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 1, 2, 2].length) (baseStart_5713008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713008 prefixEnd_5713008 := by exact prefixLift 5713008
  have htrace : WordTrace (prefixWord ++ tailWord_5713008) baseStart_5713008 baseEnd_5713008 := by
    simpa [prefixWord, tailWord_5713008, baseEnd_5713008] using wordTrace_append hprefix tailTrace_5713008
  have hstable : (prefixWord ++ tailWord_5713008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713008).length < 2 ^ (prefixWord ++ tailWord_5713008).sum := by decide
  have hdescent : baseEnd_5713008 < baseStart_5713008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713010 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_5713010 : Nat := 118140960795 + 5713010 * 2 ^ 59
def prefixEnd_5713010 : Nat := 4983230072969 + 3 ^ 40 * 5713010 * 2
def baseEnd_5713010 : Nat := 977840037980932685267117

theorem tailTrace_5713010 : CollatzResearch.WordTrace tailWord_5713010 prefixEnd_5713010 977840037980932685267117 := by
  unfold tailWord_5713010
  simp only [CollatzResearch.WordTrace]
  refine ⟨52092648258186987318328121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138913728688498632848874989 52092648258186987318328121)
  ·
    refine ⟨39069486193640240488746091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52092648258186987318328121 39069486193640240488746091)
    ·
      refine ⟨58604229290460360733119137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39069486193640240488746091 58604229290460360733119137)
      ·
        refine ⟨43953171967845270549839353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58604229290460360733119137 43953171967845270549839353)
        ·
          refine ⟨32964878975883952912379515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43953171967845270549839353 32964878975883952912379515)
          ·
            refine ⟨49447318463825929368569273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32964878975883952912379515 49447318463825929368569273)
            ·
              refine ⟨37085488847869447026426955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49447318463825929368569273 37085488847869447026426955)
              ·
                refine ⟨55628233271804170539640433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37085488847869447026426955 55628233271804170539640433)
                ·
                  refine ⟨41721174953853127904730325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55628233271804170539640433 41721174953853127904730325)
                  ·
                    refine ⟨977840037980932685267117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41721174953853127904730325 977840037980932685267117)
                    ·
                      rfl

theorem cell23_5713010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_5713010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713010 prefixEnd_5713010 := by exact prefixLift 5713010
  have htrace : WordTrace (prefixWord ++ tailWord_5713010) baseStart_5713010 baseEnd_5713010 := by
    simpa [prefixWord, tailWord_5713010, baseEnd_5713010] using wordTrace_append hprefix tailTrace_5713010
  have hstable : (prefixWord ++ tailWord_5713010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713010).length < 2 ^ (prefixWord ++ tailWord_5713010).sum := by decide
  have hdescent : baseEnd_5713010 < baseStart_5713010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713034 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2]
def baseStart_5713034 : Nat := 118140960795 + 5713034 * 2 ^ 59
def prefixEnd_5713034 : Nat := 4983230072969 + 3 ^ 40 * 5713034 * 2
def baseEnd_5713034 : Nat := 2933532437478505961901241

theorem tailTrace_5713034 : CollatzResearch.WordTrace tailWord_5713034 prefixEnd_5713034 2933532437478505961901241 := by
  unfold tailWord_5713034
  simp only [CollatzResearch.WordTrace]
  refine ⟨52092867096165250343046539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138914312256440667581457437 52092867096165250343046539)
  ·
    refine ⟨78139300644247875514569809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52092867096165250343046539 78139300644247875514569809)
    ·
      refine ⟨58604475483185906635927357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78139300644247875514569809 58604475483185906635927357)
      ·
        refine ⟨21976678306194714988472759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58604475483185906635927357 21976678306194714988472759)
        ·
          refine ⟨32965017459292072482709139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21976678306194714988472759 32965017459292072482709139)
          ·
            refine ⟨49447526188938108724063709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32965017459292072482709139 49447526188938108724063709)
            ·
              refine ⟨18542822320851790771523891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49447526188938108724063709 18542822320851790771523891)
              ·
                refine ⟨27814233481277686157285837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18542822320851790771523891 27814233481277686157285837)
                ·
                  refine ⟨10430337555479132308982189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27814233481277686157285837 10430337555479132308982189)
                  ·
                    refine ⟨3911376583304674615868321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10430337555479132308982189 3911376583304674615868321)
                    ·
                      refine ⟨2933532437478505961901241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911376583304674615868321 2933532437478505961901241)
                      ·
                        rfl

theorem cell23_5713034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_5713034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713034 prefixEnd_5713034 := by exact prefixLift 5713034
  have htrace : WordTrace (prefixWord ++ tailWord_5713034) baseStart_5713034 baseEnd_5713034 := by
    simpa [prefixWord, tailWord_5713034, baseEnd_5713034] using wordTrace_append hprefix tailTrace_5713034
  have hstable : (prefixWord ++ tailWord_5713034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713034).length < 2 ^ (prefixWord ++ tailWord_5713034).sum := by decide
  have hdescent : baseEnd_5713034 < baseStart_5713034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713058 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_5713058 : Nat := 118140960795 + 5713058 * 2 ^ 59
def prefixEnd_5713058 : Nat := 4983230072969 + 3 ^ 40 * 5713058 * 2
def baseEnd_5713058 : Nat := 2933544761014213868001131

theorem tailTrace_5713058 : CollatzResearch.WordTrace tailWord_5713058 prefixEnd_5713058 2933544761014213868001131 := by
  unfold tailWord_5713058
  simp only [CollatzResearch.WordTrace]
  refine ⟨52093085934143513367764957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138914895824382702314039885 52093085934143513367764957)
  ·
    refine ⟨19534907225303817512911859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52093085934143513367764957 19534907225303817512911859)
    ·
      refine ⟨29302360837955726269367789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19534907225303817512911859 29302360837955726269367789)
      ·
        refine ⟨10988385314233397351012921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29302360837955726269367789 10988385314233397351012921)
        ·
          refine ⟨8241288985675048013259691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10988385314233397351012921 8241288985675048013259691)
          ·
            refine ⟨12361933478512572019889537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8241288985675048013259691 12361933478512572019889537)
            ·
              refine ⟨9271450108884429014917153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12361933478512572019889537 9271450108884429014917153)
              ·
                refine ⟨6953587581663321761187865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9271450108884429014917153 6953587581663321761187865)
                ·
                  refine ⟨5215190686247491320890899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6953587581663321761187865 5215190686247491320890899)
                  ·
                    refine ⟨7822786029371236981336349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5215190686247491320890899 7822786029371236981336349)
                    ·
                      refine ⟨2933544761014213868001131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7822786029371236981336349 2933544761014213868001131)
                      ·
                        rfl

theorem cell23_5713058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_5713058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713058 prefixEnd_5713058 := by exact prefixLift 5713058
  have htrace : WordTrace (prefixWord ++ tailWord_5713058) baseStart_5713058 baseEnd_5713058 := by
    simpa [prefixWord, tailWord_5713058, baseEnd_5713058] using wordTrace_append hprefix tailTrace_5713058
  have hstable : (prefixWord ++ tailWord_5713058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713058).length < 2 ^ (prefixWord ++ tailWord_5713058).sum := by decide
  have hdescent : baseEnd_5713058 < baseStart_5713058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713081 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 2, 2, 2]
def baseStart_5713081 : Nat := 118140960795 + 5713081 * 2 ^ 59
def prefixEnd_5713081 : Nat := 4983230072969 + 3 ^ 40 * 5713081 * 2
def baseEnd_5713081 : Nat := 2933556571069267278013525

theorem tailTrace_5713081 : CollatzResearch.WordTrace tailWord_5713081 prefixEnd_5713081 2933556571069267278013525 := by
  unfold tailWord_5713081
  simp only [CollatzResearch.WordTrace]
  refine ⟨208373182615490728399147097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138915455076993818932764731 208373182615490728399147097)
  ·
    refine ⟨156279886961618046299360323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208373182615490728399147097 156279886961618046299360323)
    ·
      refine ⟨234419830442427069449040485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156279886961618046299360323 234419830442427069449040485)
      ·
        refine ⟨43953718207955075521695091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234419830442427069449040485 43953718207955075521695091)
        ·
          refine ⟨65930577311932613282542637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43953718207955075521695091 65930577311932613282542637)
          ·
            refine ⟨24723966491974729980953489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65930577311932613282542637 24723966491974729980953489)
            ·
              refine ⟨18542974868981047485715117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24723966491974729980953489 18542974868981047485715117)
              ·
                refine ⟨6953615575867892807143169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18542974868981047485715117 6953615575867892807143169)
                ·
                  refine ⟨5215211681900919605357377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6953615575867892807143169 5215211681900919605357377)
                  ·
                    refine ⟨3911408761425689704018033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5215211681900919605357377 3911408761425689704018033)
                    ·
                      refine ⟨2933556571069267278013525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911408761425689704018033 2933556571069267278013525)
                      ·
                        rfl

theorem cell23_5713081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_5713081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713081 prefixEnd_5713081 := by exact prefixLift 5713081
  have htrace : WordTrace (prefixWord ++ tailWord_5713081) baseStart_5713081 baseEnd_5713081 := by
    simpa [prefixWord, tailWord_5713081, baseEnd_5713081] using wordTrace_append hprefix tailTrace_5713081
  have hstable : (prefixWord ++ tailWord_5713081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713081).length < 2 ^ (prefixWord ++ tailWord_5713081).sum := by decide
  have hdescent : baseEnd_5713081 < baseStart_5713081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713107 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 4, 5, 2]
def baseStart_5713107 : Nat := 118140960795 + 5713107 * 2 ^ 59
def prefixEnd_5713107 : Nat := 4983230072969 + 3 ^ 40 * 5713107 * 2
def baseEnd_5713107 : Nat := 2933569921566284176288405

theorem tailTrace_5713107 : CollatzResearch.WordTrace tailWord_5713107 prefixEnd_5713107 2933569921566284176288405 := by
  unfold tailWord_5713107
  simp only [CollatzResearch.WordTrace]
  refine ⟨208374130913396534839593575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138916087275597689893062383 208374130913396534839593575)
  ·
    refine ⟨312561196370094802259390363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208374130913396534839593575 312561196370094802259390363)
    ·
      refine ⟨468841794555142203389085545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312561196370094802259390363 468841794555142203389085545)
      ·
        refine ⟨351631345916356652541814159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468841794555142203389085545 351631345916356652541814159)
        ·
          refine ⟨527447018874534978812721239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351631345916356652541814159 527447018874534978812721239)
          ·
            refine ⟨791170528311802468219081859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527447018874534978812721239 791170528311802468219081859)
            ·
              refine ⟨1186755792467703702328622789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791170528311802468219081859 1186755792467703702328622789)
              ·
                refine ⟨222516711087694444186616773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1186755792467703702328622789 222516711087694444186616773)
                ·
                  refine ⟨41721883328942708284990645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222516711087694444186616773 41721883328942708284990645)
                  ·
                    refine ⟨3911426562088378901717873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41721883328942708284990645 3911426562088378901717873)
                    ·
                      refine ⟨2933569921566284176288405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911426562088378901717873 2933569921566284176288405)
                      ·
                        rfl

theorem cell23_5713107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 5, 2].length) (baseStart_5713107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713107 prefixEnd_5713107 := by exact prefixLift 5713107
  have htrace : WordTrace (prefixWord ++ tailWord_5713107) baseStart_5713107 baseEnd_5713107 := by
    simpa [prefixWord, tailWord_5713107, baseEnd_5713107] using wordTrace_append hprefix tailTrace_5713107
  have hstable : (prefixWord ++ tailWord_5713107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713107).length < 2 ^ (prefixWord ++ tailWord_5713107).sum := by decide
  have hdescent : baseEnd_5713107 < baseStart_5713107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713157 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 1, 4, 3]
def baseStart_5713157 : Nat := 118140960795 + 5713157 * 2 ^ 59
def prefixEnd_5713157 : Nat := 4983230072969 + 3 ^ 40 * 5713157 * 2
def baseEnd_5713157 : Nat := 2933595595599008980663175

theorem tailTrace_5713157 : CollatzResearch.WordTrace tailWord_5713157 prefixEnd_5713157 2933595595599008980663175 := by
  unfold tailWord_5713157
  simp only [CollatzResearch.WordTrace]
  refine ⟨208375954563215393378913725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138917303042143595585942483 208375954563215393378913725)
  ·
    refine ⟨78140982961205772517092647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208375954563215393378913725 78140982961205772517092647)
    ·
      refine ⟨117211474441808658775638971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78140982961205772517092647 117211474441808658775638971)
      ·
        refine ⟨175817211662712988163458457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117211474441808658775638971 175817211662712988163458457)
        ·
          refine ⟨131862908747034741122593843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175817211662712988163458457 131862908747034741122593843)
          ·
            refine ⟨197794363120552111683890765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131862908747034741122593843 197794363120552111683890765)
            ·
              refine ⟨74172886170207041881459037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197794363120552111683890765 74172886170207041881459037)
              ·
                refine ⟨27814832313827640705547139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74172886170207041881459037 27814832313827640705547139)
                ·
                  refine ⟨41722248470741461058320709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27814832313827640705547139 41722248470741461058320709)
                  ·
                    refine ⟨7822921588264023948435133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41722248470741461058320709 7822921588264023948435133)
                    ·
                      refine ⟨2933595595599008980663175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7822921588264023948435133 2933595595599008980663175)
                      ·
                        rfl

theorem cell23_5713157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_5713157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713157 prefixEnd_5713157 := by exact prefixLift 5713157
  have htrace : WordTrace (prefixWord ++ tailWord_5713157) baseStart_5713157 baseEnd_5713157 := by
    simpa [prefixWord, tailWord_5713157, baseEnd_5713157] using wordTrace_append hprefix tailTrace_5713157
  have hstable : (prefixWord ++ tailWord_5713157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713157).length < 2 ^ (prefixWord ++ tailWord_5713157).sum := by decide
  have hdescent : baseEnd_5713157 < baseStart_5713157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713181 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_5713181 : Nat := 118140960795 + 5713181 * 2 ^ 59
def prefixEnd_5713181 : Nat := 4983230072969 + 3 ^ 40 * 5713181 * 2
def baseEnd_5713181 : Nat := 977869306378238962254355

theorem tailTrace_5713181 : CollatzResearch.WordTrace tailWord_5713181 prefixEnd_5713181 977869306378238962254355 := by
  unfold tailWord_5713181
  simp only [CollatzResearch.WordTrace]
  refine ⟨208376829915128445477787397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138917886610085630318524931 208376829915128445477787397)
  ·
    refine ⟨39070655609086583527085137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208376829915128445477787397 39070655609086583527085137)
    ·
      refine ⟨29302991706814937645313853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39070655609086583527085137 29302991706814937645313853)
      ·
        refine ⟨10988621890055601616992695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29302991706814937645313853 10988621890055601616992695)
        ·
          refine ⟨16482932835083402425489043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10988621890055601616992695 16482932835083402425489043)
          ·
            refine ⟨24724399252625103638233565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16482932835083402425489043 24724399252625103638233565)
            ·
              refine ⟨9271649719734413864337587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24724399252625103638233565 9271649719734413864337587)
              ·
                refine ⟨13907474579601620796506381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9271649719734413864337587 13907474579601620796506381)
                ·
                  refine ⟨5215302967350607798689893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13907474579601620796506381 5215302967350607798689893)
                  ·
                    refine ⟨977869306378238962254355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5215302967350607798689893 977869306378238962254355)
                    ·
                      rfl

theorem cell23_5713181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_5713181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713181 prefixEnd_5713181 := by exact prefixLift 5713181
  have htrace : WordTrace (prefixWord ++ tailWord_5713181) baseStart_5713181 baseEnd_5713181 := by
    simpa [prefixWord, tailWord_5713181, baseEnd_5713181] using wordTrace_append hprefix tailTrace_5713181
  have hstable : (prefixWord ++ tailWord_5713181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713181).length < 2 ^ (prefixWord ++ tailWord_5713181).sum := by decide
  have hdescent : baseEnd_5713181 < baseStart_5713181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713247 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_5713247 : Nat := 118140960795 + 5713247 * 2 ^ 59
def prefixEnd_5713247 : Nat := 4983230072969 + 3 ^ 40 * 5713247 * 2
def baseEnd_5713247 : Nat := 2933641808857913628537761

theorem tailTrace_5713247 : CollatzResearch.WordTrace tailWord_5713247 prefixEnd_5713247 2933641808857913628537761 := by
  unfold tailWord_5713247
  simp only [CollatzResearch.WordTrace]
  refine ⟨208379237132889338749689995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138919491421926225833126663 208379237132889338749689995)
  ·
    refine ⟨312568855699334008124534993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208379237132889338749689995 312568855699334008124534993)
    ·
      refine ⟨234426641774500506093401245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312568855699334008124534993 234426641774500506093401245)
      ·
        refine ⟨87909990665437689785025467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234426641774500506093401245 87909990665437689785025467)
        ·
          refine ⟨131864985998156534677538201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87909990665437689785025467 131864985998156534677538201)
          ·
            refine ⟨98898739498617401008153651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131864985998156534677538201 98898739498617401008153651)
            ·
              refine ⟨148348109247926101512230477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98898739498617401008153651 148348109247926101512230477)
              ·
                refine ⟨55630540967972288067086429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148348109247926101512230477 55630540967972288067086429)
                ·
                  refine ⟨20861452862989608025157411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55630540967972288067086429 20861452862989608025157411)
                  ·
                    refine ⟨31292179294484412037736117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20861452862989608025157411 31292179294484412037736117)
                    ·
                      refine ⟨2933641808857913628537761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31292179294484412037736117 2933641808857913628537761)
                      ·
                        rfl

theorem cell23_5713247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_5713247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713247 prefixEnd_5713247 := by exact prefixLift 5713247
  have htrace : WordTrace (prefixWord ++ tailWord_5713247) baseStart_5713247 baseEnd_5713247 := by
    simpa [prefixWord, tailWord_5713247, baseEnd_5713247] using wordTrace_append hprefix tailTrace_5713247
  have hstable : (prefixWord ++ tailWord_5713247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713247).length < 2 ^ (prefixWord ++ tailWord_5713247).sum := by decide
  have hdescent : baseEnd_5713247 < baseStart_5713247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713264 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 3]
def baseStart_5713264 : Nat := 118140960795 + 5713264 * 2 ^ 59
def prefixEnd_5713264 : Nat := 4983230072969 + 3 ^ 40 * 5713264 * 2
def baseEnd_5713264 : Nat := 2933650538029040062025183

theorem tailTrace_5713264 : CollatzResearch.WordTrace tailWord_5713264 prefixEnd_5713264 2933650538029040062025183 := by
  unfold tailWord_5713264
  simp only [CollatzResearch.WordTrace]
  refine ⟨104189928586913875326529423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138919904782551833768705897 104189928586913875326529423)
  ·
    refine ⟨156284892880370812989794135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104189928586913875326529423 156284892880370812989794135)
    ·
      refine ⟨234427339320556219484691203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156284892880370812989794135 234427339320556219484691203)
      ·
        refine ⟨351641008980834329227036805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234427339320556219484691203 351641008980834329227036805)
        ·
          refine ⟨65932689183906436730069401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 351641008980834329227036805 65932689183906436730069401)
          ·
            refine ⟨49449516887929827547552051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65932689183906436730069401 49449516887929827547552051)
            ·
              refine ⟨74174275331894741321328077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49449516887929827547552051 74174275331894741321328077)
              ·
                refine ⟨27815353249460527995498029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74174275331894741321328077 27815353249460527995498029)
                ·
                  refine ⟨10430757468547697998311761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27815353249460527995498029 10430757468547697998311761)
                  ·
                    refine ⟨7823068101410773498733821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10430757468547697998311761 7823068101410773498733821)
                    ·
                      refine ⟨2933650538029040062025183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7823068101410773498733821 2933650538029040062025183)
                      ·
                        rfl

theorem cell23_5713264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 3].length) (baseStart_5713264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713264 prefixEnd_5713264 := by exact prefixLift 5713264
  have htrace : WordTrace (prefixWord ++ tailWord_5713264) baseStart_5713264 baseEnd_5713264 := by
    simpa [prefixWord, tailWord_5713264, baseEnd_5713264] using wordTrace_append hprefix tailTrace_5713264
  have hstable : (prefixWord ++ tailWord_5713264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713264).length < 2 ^ (prefixWord ++ tailWord_5713264).sum := by decide
  have hdescent : baseEnd_5713264 < baseStart_5713264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713288 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 2, 4]
def baseStart_5713288 : Nat := 118140960795 + 5713288 * 2 ^ 59
def prefixEnd_5713288 : Nat := 4983230072969 + 3 ^ 40 * 5713288 * 2
def baseEnd_5713288 : Nat := 977887620521582656041691

theorem tailTrace_5713288 : CollatzResearch.WordTrace tailWord_5713288 prefixEnd_5713288 977887620521582656041691 := by
  unfold tailWord_5713288
  simp only [CollatzResearch.WordTrace]
  refine ⟨104190366262870401375966259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138920488350493868501288345 104190366262870401375966259)
  ·
    refine ⟨156285549394305602063949389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104190366262870401375966259 156285549394305602063949389)
    ·
      refine ⟨58607081022864600773981021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156285549394305602063949389 58607081022864600773981021)
      ·
        refine ⟨21977655383574225290242883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58607081022864600773981021 21977655383574225290242883)
        ·
          refine ⟨32966483075361337935364325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21977655383574225290242883 32966483075361337935364325)
          ·
            refine ⟨6181215576630250862880811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32966483075361337935364325 6181215576630250862880811)
            ·
              refine ⟨9271823364945376294321217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6181215576630250862880811 9271823364945376294321217)
              ·
                refine ⟨6953867523709032220740913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9271823364945376294321217 6953867523709032220740913)
                ·
                  refine ⟨5215400642781774165555685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6953867523709032220740913 5215400642781774165555685)
                  ·
                    refine ⟨977887620521582656041691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5215400642781774165555685 977887620521582656041691)
                    ·
                      rfl

theorem cell23_5713288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_5713288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713288 prefixEnd_5713288 := by exact prefixLift 5713288
  have htrace : WordTrace (prefixWord ++ tailWord_5713288) baseStart_5713288 baseEnd_5713288 := by
    simpa [prefixWord, tailWord_5713288, baseEnd_5713288] using wordTrace_append hprefix tailTrace_5713288
  have hstable : (prefixWord ++ tailWord_5713288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713288).length < 2 ^ (prefixWord ++ tailWord_5713288).sum := by decide
  have hdescent : baseEnd_5713288 < baseStart_5713288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713298 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5713298 : Nat := 118140960795 + 5713298 * 2 ^ 59
def prefixEnd_5713298 : Nat := 4983230072969 + 3 ^ 40 * 5713298 * 2
def baseEnd_5713298 : Nat := 2933667996371292929000027

theorem tailTrace_5713298 : CollatzResearch.WordTrace tailWord_5713298 prefixEnd_5713298 2933667996371292929000027 := by
  unfold tailWord_5713298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52095274313926143614949137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138920731503803049639864365 52095274313926143614949137)
  ·
    refine ⟨39071455735444607711211853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52095274313926143614949137 39071455735444607711211853)
    ·
      refine ⟨14651795900791727891704445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39071455735444607711211853 14651795900791727891704445)
      ·
        refine ⟨5494423462796897959389167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14651795900791727891704445 5494423462796897959389167)
        ·
          refine ⟨8241635194195346939083751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5494423462796897959389167 8241635194195346939083751)
          ·
            refine ⟨12362452791293020408625627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8241635194195346939083751 12362452791293020408625627)
            ·
              refine ⟨18543679186939530612938441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12362452791293020408625627 18543679186939530612938441)
              ·
                refine ⟨13907759390204647959703831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18543679186939530612938441 13907759390204647959703831)
                ·
                  refine ⟨20861639085306971939555747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13907759390204647959703831 20861639085306971939555747)
                  ·
                    refine ⟨31292458627960457909333621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20861639085306971939555747 31292458627960457909333621)
                    ·
                      refine ⟨2933667996371292929000027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31292458627960457909333621 2933667996371292929000027)
                      ·
                        rfl

theorem cell23_5713298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5713298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713298 prefixEnd_5713298 := by exact prefixLift 5713298
  have htrace : WordTrace (prefixWord ++ tailWord_5713298) baseStart_5713298 baseEnd_5713298 := by
    simpa [prefixWord, tailWord_5713298, baseEnd_5713298] using wordTrace_append hprefix tailTrace_5713298
  have hstable : (prefixWord ++ tailWord_5713298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713298).length < 2 ^ (prefixWord ++ tailWord_5713298).sum := by decide
  have hdescent : baseEnd_5713298 < baseStart_5713298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713311 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 3]
def baseStart_5713311 : Nat := 118140960795 + 5713311 * 2 ^ 59
def prefixEnd_5713311 : Nat := 4983230072969 + 3 ^ 40 * 5713311 * 2
def baseEnd_5713311 : Nat := 2933674671619801378137467

theorem tailTrace_5713311 : CollatzResearch.WordTrace tailWord_5713311 prefixEnd_5713311 2933674671619801378137467 := by
  unfold tailWord_5713311
  simp only [CollatzResearch.WordTrace]
  refine ⟨208381571404657477680019787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138921047603104985120013191 208381571404657477680019787)
  ·
    refine ⟨312572357106986216520029681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208381571404657477680019787 312572357106986216520029681)
    ·
      refine ⟨234429267830239662390022261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312572357106986216520029681 234429267830239662390022261)
      ·
        refine ⟨21977743859084968349064587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234429267830239662390022261 21977743859084968349064587)
        ·
          refine ⟨32966615788627452523596881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21977743859084968349064587 32966615788627452523596881)
          ·
            refine ⟨24724961841470589392697661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32966615788627452523596881 24724961841470589392697661)
            ·
              refine ⟨9271860690551471022261623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24724961841470589392697661 9271860690551471022261623)
              ·
                refine ⟨13907791035827206533392435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9271860690551471022261623 13907791035827206533392435)
                ·
                  refine ⟨20861686553740809800088653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13907791035827206533392435 20861686553740809800088653)
                  ·
                    refine ⟨7823132457652803675033245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20861686553740809800088653 7823132457652803675033245)
                    ·
                      refine ⟨2933674671619801378137467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7823132457652803675033245 2933674671619801378137467)
                      ·
                        rfl

theorem cell23_5713311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_5713311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713311 prefixEnd_5713311 := by exact prefixLift 5713311
  have htrace : WordTrace (prefixWord ++ tailWord_5713311) baseStart_5713311 baseEnd_5713311 := by
    simpa [prefixWord, tailWord_5713311, baseEnd_5713311] using wordTrace_append hprefix tailTrace_5713311
  have hstable : (prefixWord ++ tailWord_5713311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713311).length < 2 ^ (prefixWord ++ tailWord_5713311).sum := by decide
  have hdescent : baseEnd_5713311 < baseStart_5713311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713317 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_5713317 : Nat := 118140960795 + 5713317 * 2 ^ 59
def prefixEnd_5713317 : Nat := 4983230072969 + 3 ^ 40 * 5713317 * 2
def baseEnd_5713317 : Nat := 2933677752503728354662439

theorem tailTrace_5713317 : CollatzResearch.WordTrace tailWord_5713317 prefixEnd_5713317 2933677752503728354662439 := by
  unfold tailWord_5713317
  simp only [CollatzResearch.WordTrace]
  refine ⟨208381790242635740704738205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138921193495090493803158803 208381790242635740704738205)
  ·
    refine ⟨78143171340988402764276827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208381790242635740704738205 78143171340988402764276827)
    ·
      refine ⟨117214757011482604146415241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78143171340988402764276827 117214757011482604146415241)
      ·
        refine ⟨87911067758611953109811431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117214757011482604146415241 87911067758611953109811431)
        ·
          refine ⟨131866601637917929664717147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87911067758611953109811431 131866601637917929664717147)
          ·
            refine ⟨197799902456876894497075721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131866601637917929664717147 197799902456876894497075721)
            ·
              refine ⟨148349926842657670872806791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197799902456876894497075721 148349926842657670872806791)
              ·
                refine ⟨222524890263986506309210187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148349926842657670872806791 222524890263986506309210187)
                ·
                  refine ⟨333787335395979759463815281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222524890263986506309210187 333787335395979759463815281)
                  ·
                    refine ⟨250340501546984819597861461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 333787335395979759463815281 250340501546984819597861461)
                    ·
                      refine ⟨2933677752503728354662439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 250340501546984819597861461 2933677752503728354662439)
                      ·
                        rfl

theorem cell23_5713317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_5713317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713317 prefixEnd_5713317 := by exact prefixLift 5713317
  have htrace : WordTrace (prefixWord ++ tailWord_5713317) baseStart_5713317 baseEnd_5713317 := by
    simpa [prefixWord, tailWord_5713317, baseEnd_5713317] using wordTrace_append hprefix tailTrace_5713317
  have hstable : (prefixWord ++ tailWord_5713317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713317).length < 2 ^ (prefixWord ++ tailWord_5713317).sum := by decide
  have hdescent : baseEnd_5713317 < baseStart_5713317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713327 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 1, 8]
def baseStart_5713327 : Nat := 118140960795 + 5713327 * 2 ^ 59
def prefixEnd_5713327 : Nat := 4983230072969 + 3 ^ 40 * 5713327 * 2
def baseEnd_5713327 : Nat := 977894295770091105179131

theorem tailTrace_5713327 : CollatzResearch.WordTrace tailWord_5713327 prefixEnd_5713327 977894295770091105179131 := by
  unfold tailWord_5713327
  simp only [CollatzResearch.WordTrace]
  refine ⟨208382154972599512412602235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138921436648399674941734823 208382154972599512412602235)
  ·
    refine ⟨312573232458899268618903353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208382154972599512412602235 312573232458899268618903353)
    ·
      refine ⟨234429924344174451464177515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312573232458899268618903353 234429924344174451464177515)
      ·
        refine ⟨351644886516261677196266273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234429924344174451464177515 351644886516261677196266273)
        ·
          refine ⟨263733664887196257897199705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351644886516261677196266273 263733664887196257897199705)
          ·
            refine ⟨197800248665397193422899779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263733664887196257897199705 197800248665397193422899779)
            ·
              refine ⟨296700372998095790134349669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197800248665397193422899779 296700372998095790134349669)
              ·
                refine ⟨55631319937142960650190563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296700372998095790134349669 55631319937142960650190563)
                ·
                  refine ⟨83446979905714440975285845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55631319937142960650190563 83446979905714440975285845)
                  ·
                    refine ⟨977894295770091105179131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83446979905714440975285845 977894295770091105179131)
                    ·
                      rfl

theorem cell23_5713327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_5713327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713327 prefixEnd_5713327 := by exact prefixLift 5713327
  have htrace : WordTrace (prefixWord ++ tailWord_5713327) baseStart_5713327 baseEnd_5713327 := by
    simpa [prefixWord, tailWord_5713327, baseEnd_5713327] using wordTrace_append hprefix tailTrace_5713327
  have hstable : (prefixWord ++ tailWord_5713327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713327).length < 2 ^ (prefixWord ++ tailWord_5713327).sum := by decide
  have hdescent : baseEnd_5713327 < baseStart_5713327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713441 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_5713441 : Nat := 118140960795 + 5713441 * 2 ^ 59
def prefixEnd_5713441 : Nat := 4983230072969 + 3 ^ 40 * 5713441 * 2
def baseEnd_5713441 : Nat := 2933741424104885869511869

theorem tailTrace_5713441 : CollatzResearch.WordTrace tailWord_5713441 prefixEnd_5713441 2933741424104885869511869 := by
  unfold tailWord_5713441
  simp only [CollatzResearch.WordTrace]
  refine ⟨208386312894186509882252177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138924208596124339921501451 208386312894186509882252177)
  ·
    refine ⟨156289734670639882411689133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208386312894186509882252177 156289734670639882411689133)
    ·
      refine ⟨58608650501489955904383425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156289734670639882411689133 58608650501489955904383425)
      ·
        refine ⟨43956487876117466928287569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58608650501489955904383425 43956487876117466928287569)
        ·
          refine ⟨32967365907088100196215677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43956487876117466928287569 32967365907088100196215677)
          ·
            refine ⟨12362762215158037573580879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32967365907088100196215677 12362762215158037573580879)
            ·
              refine ⟨18544143322737056360371319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12362762215158037573580879 18544143322737056360371319)
              ·
                refine ⟨27816214984105584540556979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18544143322737056360371319 27816214984105584540556979)
                ·
                  refine ⟨41724322476158376810835469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27816214984105584540556979 41724322476158376810835469)
                  ·
                    refine ⟨15646620928559391304063301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41724322476158376810835469 15646620928559391304063301)
                    ·
                      refine ⟨2933741424104885869511869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15646620928559391304063301 2933741424104885869511869)
                      ·
                        rfl

theorem cell23_5713441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_5713441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713441 prefixEnd_5713441 := by exact prefixLift 5713441
  have htrace : WordTrace (prefixWord ++ tailWord_5713441) baseStart_5713441 baseEnd_5713441 := by
    simpa [prefixWord, tailWord_5713441, baseEnd_5713441] using wordTrace_append hprefix tailTrace_5713441
  have hstable : (prefixWord ++ tailWord_5713441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713441).length < 2 ^ (prefixWord ++ tailWord_5713441).sum := by decide
  have hdescent : baseEnd_5713441 < baseStart_5713441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713531 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 4]
def baseStart_5713531 : Nat := 118140960795 + 5713531 * 2 ^ 59
def prefixEnd_5713531 : Nat := 4983230072969 + 3 ^ 40 * 5713531 * 2
def baseEnd_5713531 : Nat := 2933787637363790517386455

theorem tailTrace_5713531 : CollatzResearch.WordTrace tailWord_5713531 prefixEnd_5713531 2933787637363790517386455 := by
  unfold tailWord_5713531
  simp only [CollatzResearch.WordTrace]
  refine ⟨208389595463860455253028447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138926396975906970168685631 208389595463860455253028447)
  ·
    refine ⟨312584393195790682879542671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208389595463860455253028447 312584393195790682879542671)
    ·
      refine ⟨468876589793686024319314007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312584393195790682879542671 468876589793686024319314007)
      ·
        refine ⟨703314884690529036478971011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468876589793686024319314007 703314884690529036478971011)
        ·
          refine ⟨1054972327035793554718456517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703314884690529036478971011 1054972327035793554718456517)
          ·
            refine ⟨197807311319211291509710597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1054972327035793554718456517 197807311319211291509710597)
            ·
              refine ⟨37088870872352117158070737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197807311319211291509710597 37088870872352117158070737)
              ·
                refine ⟨27816653154264087868553053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37088870872352117158070737 27816653154264087868553053)
                ·
                  refine ⟨10431244932849032950707395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27816653154264087868553053 10431244932849032950707395)
                  ·
                    refine ⟨15646867399273549426061093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10431244932849032950707395 15646867399273549426061093)
                    ·
                      refine ⟨2933787637363790517386455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15646867399273549426061093 2933787637363790517386455)
                      ·
                        rfl

theorem cell23_5713531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 4].length) (baseStart_5713531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713531 prefixEnd_5713531 := by exact prefixLift 5713531
  have htrace : WordTrace (prefixWord ++ tailWord_5713531) baseStart_5713531 baseEnd_5713531 := by
    simpa [prefixWord, tailWord_5713531, baseEnd_5713531] using wordTrace_append hprefix tailTrace_5713531
  have hstable : (prefixWord ++ tailWord_5713531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713531).length < 2 ^ (prefixWord ++ tailWord_5713531).sum := by decide
  have hdescent : baseEnd_5713531 < baseStart_5713531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713541 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_5713541 : Nat := 118140960795 + 5713541 * 2 ^ 59
def prefixEnd_5713541 : Nat := 4983230072969 + 3 ^ 40 * 5713541 * 2
def baseEnd_5713541 : Nat := 977930924056778492753803

theorem tailTrace_5713541 : CollatzResearch.WordTrace tailWord_5713541 prefixEnd_5713541 977930924056778492753803 := by
  unfold tailWord_5713541
  simp only [CollatzResearch.WordTrace]
  refine ⟨208389960193824226960892477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138926640129216151307261651 208389960193824226960892477)
  ·
    refine ⟨78146235072684085110334679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208389960193824226960892477 78146235072684085110334679)
    ·
      refine ⟨117219352609026127665502019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78146235072684085110334679 117219352609026127665502019)
      ·
        refine ⟨175829028913539191498253029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117219352609026127665502019 175829028913539191498253029)
        ·
          refine ⟨32967942921288598405922443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175829028913539191498253029 32967942921288598405922443)
          ·
            refine ⟨49451914381932897608883665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32967942921288598405922443 49451914381932897608883665)
            ·
              refine ⟨37088935786449673206662749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49451914381932897608883665 37088935786449673206662749)
              ·
                refine ⟨13908350919918627452498531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37088935786449673206662749 13908350919918627452498531)
                ·
                  refine ⟨20862526379877941178747797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13908350919918627452498531 20862526379877941178747797)
                  ·
                    refine ⟨977930924056778492753803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20862526379877941178747797 977930924056778492753803)
                    ·
                      rfl

theorem cell23_5713541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_5713541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713541 prefixEnd_5713541 := by exact prefixLift 5713541
  have htrace : WordTrace (prefixWord ++ tailWord_5713541) baseStart_5713541 baseEnd_5713541 := by
    simpa [prefixWord, tailWord_5713541, baseEnd_5713541] using wordTrace_append hprefix tailTrace_5713541
  have hstable : (prefixWord ++ tailWord_5713541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713541).length < 2 ^ (prefixWord ++ tailWord_5713541).sum := by decide
  have hdescent : baseEnd_5713541 < baseStart_5713541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713568 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 5]
def baseStart_5713568 : Nat := 118140960795 + 5713568 * 2 ^ 59
def prefixEnd_5713568 : Nat := 4983230072969 + 3 ^ 40 * 5713568 * 2
def baseEnd_5713568 : Nat := 2933806636148006872623785

theorem tailTrace_5713568 : CollatzResearch.WordTrace tailWord_5713568 prefixEnd_5713568 2933806636148006872623785 := by
  unfold tailWord_5713568
  simp only [CollatzResearch.WordTrace]
  refine ⟨104195472482363205286062679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138927296643150940381416905 104195472482363205286062679)
  ·
    refine ⟨156293208723544807929094019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104195472482363205286062679 156293208723544807929094019)
    ·
      refine ⟨234439813085317211893641029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156293208723544807929094019 234439813085317211893641029)
      ·
        refine ⟨43957464953496977230057693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234439813085317211893641029 43957464953496977230057693)
        ·
          refine ⟨16484049357561366461271635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43957464953496977230057693 16484049357561366461271635)
          ·
            refine ⟨24726074036342049691907453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16484049357561366461271635 24726074036342049691907453)
            ·
              refine ⟨9272277763628268634465295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24726074036342049691907453 9272277763628268634465295)
              ·
                refine ⟨13908416645442402951697943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9272277763628268634465295 13908416645442402951697943)
                ·
                  refine ⟨20862624968163604427546915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13908416645442402951697943 20862624968163604427546915)
                  ·
                    refine ⟨31293937452245406641320373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20862624968163604427546915 31293937452245406641320373)
                    ·
                      refine ⟨2933806636148006872623785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31293937452245406641320373 2933806636148006872623785)
                      ·
                        rfl

theorem cell23_5713568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_5713568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713568 prefixEnd_5713568 := by exact prefixLift 5713568
  have htrace : WordTrace (prefixWord ++ tailWord_5713568) baseStart_5713568 baseEnd_5713568 := by
    simpa [prefixWord, tailWord_5713568, baseEnd_5713568] using wordTrace_append hprefix tailTrace_5713568
  have hstable : (prefixWord ++ tailWord_5713568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713568).length < 2 ^ (prefixWord ++ tailWord_5713568).sum := by decide
  have hdescent : baseEnd_5713568 < baseStart_5713568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713631 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 4, 6]
def baseStart_5713631 : Nat := 118140960795 + 5713631 * 2 ^ 59
def prefixEnd_5713631 : Nat := 4983230072969 + 3 ^ 40 * 5713631 * 2
def baseEnd_5713631 : Nat := 977946328476413375378665

theorem tailTrace_5713631 : CollatzResearch.WordTrace tailWord_5713631 prefixEnd_5713631 977946328476413375378665 := by
  unfold tailWord_5713631
  simp only [CollatzResearch.WordTrace]
  refine ⟨208393242763498172331668747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138928828508998781554445831 208393242763498172331668747)
  ·
    refine ⟨312589864145247258497503121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208393242763498172331668747 312589864145247258497503121)
    ·
      refine ⟨234442398108935443873127341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312589864145247258497503121 234442398108935443873127341)
      ·
        refine ⟨87915899290850791452422753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234442398108935443873127341 87915899290850791452422753)
        ·
          refine ⟨65936924468138093589317065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87915899290850791452422753 65936924468138093589317065)
          ·
            refine ⟨49452693351103570191987799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65936924468138093589317065 49452693351103570191987799)
            ·
              refine ⟨74179040026655355287981699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49452693351103570191987799 74179040026655355287981699)
              ·
                refine ⟨111268560039983032931972549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74179040026655355287981699 111268560039983032931972549)
                ·
                  refine ⟨20862855007496818674744853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111268560039983032931972549 20862855007496818674744853)
                  ·
                    refine ⟨977946328476413375378665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20862855007496818674744853 977946328476413375378665)
                    ·
                      rfl

theorem cell23_5713631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_5713631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713631 prefixEnd_5713631 := by exact prefixLift 5713631
  have htrace : WordTrace (prefixWord ++ tailWord_5713631) baseStart_5713631 baseEnd_5713631 := by
    simpa [prefixWord, tailWord_5713631, baseEnd_5713631] using wordTrace_append hprefix tailTrace_5713631
  have hstable : (prefixWord ++ tailWord_5713631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713631).length < 2 ^ (prefixWord ++ tailWord_5713631).sum := by decide
  have hdescent : baseEnd_5713631 < baseStart_5713631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713641 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_5713641 : Nat := 118140960795 + 5713641 * 2 ^ 59
def prefixEnd_5713641 : Nat := 4983230072969 + 3 ^ 40 * 5713641 * 2
def baseEnd_5713641 : Nat := 2933844120235785087010949

theorem tailTrace_5713641 : CollatzResearch.WordTrace tailWord_5713641 prefixEnd_5713641 2933844120235785087010949 := by
  unfold tailWord_5713641
  simp only [CollatzResearch.WordTrace]
  refine ⟨208393607493461944039532777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138929071662307962693021851 208393607493461944039532777)
  ·
    refine ⟨156295205620096458029649583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208393607493461944039532777 156295205620096458029649583)
    ·
      refine ⟨234442808430144687044474375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156295205620096458029649583 234442808430144687044474375)
      ·
        refine ⟨351664212645217030566711563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234442808430144687044474375 351664212645217030566711563)
        ·
          refine ⟨527496318967825545850067345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351664212645217030566711563 527496318967825545850067345)
          ·
            refine ⟨395622239225869159387550509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527496318967825545850067345 395622239225869159387550509)
            ·
              refine ⟨148358339709700934770331441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395622239225869159387550509 148358339709700934770331441)
              ·
                refine ⟨111268754782275701077748581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148358339709700934770331441 111268754782275701077748581)
                ·
                  refine ⟨20862891521676693952077859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111268754782275701077748581 20862891521676693952077859)
                  ·
                    refine ⟨31294337282515040928116789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20862891521676693952077859 31294337282515040928116789)
                    ·
                      refine ⟨2933844120235785087010949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31294337282515040928116789 2933844120235785087010949)
                      ·
                        rfl

theorem cell23_5713641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_5713641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713641 prefixEnd_5713641 := by exact prefixLift 5713641
  have htrace : WordTrace (prefixWord ++ tailWord_5713641) baseStart_5713641 baseEnd_5713641 := by
    simpa [prefixWord, tailWord_5713641, baseEnd_5713641] using wordTrace_append hprefix tailTrace_5713641
  have hstable : (prefixWord ++ tailWord_5713641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713641).length < 2 ^ (prefixWord ++ tailWord_5713641).sum := by decide
  have hdescent : baseEnd_5713641 < baseStart_5713641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713655 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 1, 4, 2]
def baseStart_5713655 : Nat := 118140960795 + 5713655 * 2 ^ 59
def prefixEnd_5713655 : Nat := 4983230072969 + 3 ^ 40 * 5713655 * 2
def baseEnd_5713655 : Nat := 2933851308964948032235885

theorem tailTrace_5713655 : CollatzResearch.WordTrace tailWord_5713655 prefixEnd_5713655 2933851308964948032235885 := by
  unfold tailWord_5713655
  simp only [CollatzResearch.WordTrace]
  refine ⟨208394118115411224430542419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138929412076940816287028279 208394118115411224430542419)
  ·
    refine ⟨312591177173116836645813629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208394118115411224430542419 312591177173116836645813629)
    ·
      refine ⟨117221691439918813742180111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312591177173116836645813629 117221691439918813742180111)
      ·
        refine ⟨175832537159878220613270167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117221691439918813742180111 175832537159878220613270167)
        ·
          refine ⟨263748805739817330919905251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175832537159878220613270167 263748805739817330919905251)
          ·
            refine ⟨395623208609725996379857877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263748805739817330919905251 395623208609725996379857877)
            ·
              refine ⟨9272418951790453040152919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 395623208609725996379857877 9272418951790453040152919)
              ·
                refine ⟨13908628427685679560229379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9272418951790453040152919 13908628427685679560229379)
                ·
                  refine ⟨20862942641528519340344069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13908628427685679560229379 20862942641528519340344069)
                  ·
                    refine ⟨3911801745286597376314513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20862942641528519340344069 3911801745286597376314513)
                    ·
                      refine ⟨2933851308964948032235885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911801745286597376314513 2933851308964948032235885)
                      ·
                        rfl

theorem cell23_5713655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_5713655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713655 prefixEnd_5713655 := by exact prefixLift 5713655
  have htrace : WordTrace (prefixWord ++ tailWord_5713655) baseStart_5713655 baseEnd_5713655 := by
    simpa [prefixWord, tailWord_5713655, baseEnd_5713655] using wordTrace_append hprefix tailTrace_5713655
  have hstable : (prefixWord ++ tailWord_5713655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713655).length < 2 ^ (prefixWord ++ tailWord_5713655).sum := by decide
  have hdescent : baseEnd_5713655 < baseStart_5713655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713661 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 9]
def baseStart_5713661 : Nat := 118140960795 + 5713661 * 2 ^ 59
def prefixEnd_5713661 : Nat := 4983230072969 + 3 ^ 40 * 5713661 * 2
def baseEnd_5713661 : Nat := 325983821094319445417873

theorem tailTrace_5713661 : CollatzResearch.WordTrace tailWord_5713661 prefixEnd_5713661 325983821094319445417873 := by
  unfold tailWord_5713661
  simp only [CollatzResearch.WordTrace]
  refine ⟨208394336953389487455260837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138929557968926324970173891 208394336953389487455260837)
  ·
    refine ⟨39073938178760528897861407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208394336953389487455260837 39073938178760528897861407)
    ·
      refine ⟨58610907268140793346792111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39073938178760528897861407 58610907268140793346792111)
      ·
        refine ⟨87916360902211190020188167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58610907268140793346792111 87916360902211190020188167)
        ·
          refine ⟨131874541353316785030282251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87916360902211190020188167 131874541353316785030282251)
          ·
            refine ⟨197811812029975177545423377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131874541353316785030282251 197811812029975177545423377)
            ·
              refine ⟨148358859022481383159067533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197811812029975177545423377 148358859022481383159067533)
              ·
                refine ⟨55634572133430518684650325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148358859022481383159067533 55634572133430518684650325)
                ·
                  refine ⟨325983821094319445417873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55634572133430518684650325 325983821094319445417873)
                  ·
                    rfl

theorem cell23_5713661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_5713661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713661 prefixEnd_5713661 := by exact prefixLift 5713661
  have htrace : WordTrace (prefixWord ++ tailWord_5713661) baseStart_5713661 baseEnd_5713661 := by
    simpa [prefixWord, tailWord_5713661, baseEnd_5713661] using wordTrace_append hprefix tailTrace_5713661
  have hstable : (prefixWord ++ tailWord_5713661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713661).length < 2 ^ (prefixWord ++ tailWord_5713661).sum := by decide
  have hdescent : baseEnd_5713661 < baseStart_5713661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713688 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 4, 3, 3]
def baseStart_5713688 : Nat := 118140960795 + 5713688 * 2 ^ 59
def prefixEnd_5713688 : Nat := 4983230072969 + 3 ^ 40 * 5713688 * 2
def baseEnd_5713688 : Nat := 2933868253826546403123233

theorem tailTrace_5713688 : CollatzResearch.WordTrace tailWord_5713688 prefixEnd_5713688 2933868253826546403123233 := by
  unfold tailWord_5713688
  simp only [CollatzResearch.WordTrace]
  refine ⟨104197660862145835533246859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138930214482861114044329145 104197660862145835533246859)
  ·
    refine ⟨156296491293218753299870289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104197660862145835533246859 156296491293218753299870289)
    ·
      refine ⟨117222368469914064974902717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156296491293218753299870289 117222368469914064974902717)
      ·
        refine ⟨43958388176217774365588519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117222368469914064974902717 43958388176217774365588519)
        ·
          refine ⟨65937582264326661548382779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43958388176217774365588519 65937582264326661548382779)
          ·
            refine ⟨98906373396489992322574169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65937582264326661548382779 98906373396489992322574169)
            ·
              refine ⟨74179780047367494241930627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98906373396489992322574169 74179780047367494241930627)
              ·
                refine ⟨111269670071051241362895941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74179780047367494241930627 111269670071051241362895941)
                ·
                  refine ⟨20863063138322107755542989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111269670071051241362895941 20863063138322107755542989)
                  ·
                    refine ⟨7823648676870790408328621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20863063138322107755542989 7823648676870790408328621)
                    ·
                      refine ⟨2933868253826546403123233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7823648676870790408328621 2933868253826546403123233)
                      ·
                        rfl

theorem cell23_5713688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_5713688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713688 prefixEnd_5713688 := by exact prefixLift 5713688
  have htrace : WordTrace (prefixWord ++ tailWord_5713688) baseStart_5713688 baseEnd_5713688 := by
    simpa [prefixWord, tailWord_5713688, baseEnd_5713688] using wordTrace_append hprefix tailTrace_5713688
  have hstable : (prefixWord ++ tailWord_5713688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713688).length < 2 ^ (prefixWord ++ tailWord_5713688).sum := by decide
  have hdescent : baseEnd_5713688 < baseStart_5713688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713725 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_5713725 : Nat := 118140960795 + 5713725 * 2 ^ 59
def prefixEnd_5713725 : Nat := 4983230072969 + 3 ^ 40 * 5713725 * 2
def baseEnd_5713725 : Nat := 977962417536920919453521

theorem tailTrace_5713725 : CollatzResearch.WordTrace tailWord_5713725 prefixEnd_5713725 977962417536920919453521 := by
  unfold tailWord_5713725
  simp only [CollatzResearch.WordTrace]
  refine ⟨208396671225157626385590629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138931114150105084257060419 208396671225157626385590629)
  ·
    refine ⟨39074375854717054947298243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208396671225157626385590629 39074375854717054947298243)
    ·
      refine ⟨58611563782075582420947365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39074375854717054947298243 58611563782075582420947365)
      ·
        refine ⟨10989668209139171703927631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58611563782075582420947365 10989668209139171703927631)
        ·
          refine ⟨16484502313708757555891447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10989668209139171703927631 16484502313708757555891447)
          ·
            refine ⟨24726753470563136333837171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16484502313708757555891447 24726753470563136333837171)
            ·
              refine ⟨37090130205844704500755757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24726753470563136333837171 37090130205844704500755757)
              ·
                refine ⟨13908798827191764187783409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37090130205844704500755757 13908798827191764187783409)
                ·
                  refine ⟨10431599120393823140837557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13908798827191764187783409 10431599120393823140837557)
                  ·
                    refine ⟨977962417536920919453521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10431599120393823140837557 977962417536920919453521)
                    ·
                      rfl

theorem cell23_5713725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_5713725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713725 prefixEnd_5713725 := by exact prefixLift 5713725
  have htrace : WordTrace (prefixWord ++ tailWord_5713725) baseStart_5713725 baseEnd_5713725 := by
    simpa [prefixWord, tailWord_5713725, baseEnd_5713725] using wordTrace_append hprefix tailTrace_5713725
  have hstable : (prefixWord ++ tailWord_5713725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713725).length < 2 ^ (prefixWord ++ tailWord_5713725).sum := by decide
  have hdescent : baseEnd_5713725 < baseStart_5713725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713745 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_5713745 : Nat := 118140960795 + 5713745 * 2 ^ 59
def prefixEnd_5713745 : Nat := 4983230072969 + 3 ^ 40 * 5713745 * 2
def baseEnd_5713745 : Nat := 2933897522223852680110471

theorem tailTrace_5713745 : CollatzResearch.WordTrace tailWord_5713745 prefixEnd_5713745 2933897522223852680110471 := by
  unfold tailWord_5713745
  simp only [CollatzResearch.WordTrace]
  refine ⟨208397400685085169801318689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138931600456723446534212459 208397400685085169801318689)
  ·
    refine ⟨156298050513813877350989017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208397400685085169801318689 156298050513813877350989017)
    ·
      refine ⟨117223537885360408013241763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156298050513813877350989017 117223537885360408013241763)
      ·
        refine ⟨175835306828040612019862645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117223537885360408013241763 175835306828040612019862645)
        ·
          refine ⟨16484560015128807376862123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175835306828040612019862645 16484560015128807376862123)
          ·
            refine ⟨24726840022693211065293185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16484560015128807376862123 24726840022693211065293185)
            ·
              refine ⟨18545130017019908298969889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24726840022693211065293185 18545130017019908298969889)
              ·
                refine ⟨13908847512764931224227417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18545130017019908298969889 13908847512764931224227417)
                ·
                  refine ⟨10431635634573698418170563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13908847512764931224227417 10431635634573698418170563)
                  ·
                    refine ⟨15647453451860547627255845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10431635634573698418170563 15647453451860547627255845)
                    ·
                      refine ⟨2933897522223852680110471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15647453451860547627255845 2933897522223852680110471)
                      ·
                        rfl

theorem cell23_5713745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_5713745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713745 prefixEnd_5713745 := by exact prefixLift 5713745
  have htrace : WordTrace (prefixWord ++ tailWord_5713745) baseStart_5713745 baseEnd_5713745 := by
    simpa [prefixWord, tailWord_5713745, baseEnd_5713745] using wordTrace_append hprefix tailTrace_5713745
  have hstable : (prefixWord ++ tailWord_5713745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713745).length < 2 ^ (prefixWord ++ tailWord_5713745).sum := by decide
  have hdescent : baseEnd_5713745 < baseStart_5713745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713762 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_5713762 : Nat := 118140960795 + 5713762 * 2 ^ 59
def prefixEnd_5713762 : Nat := 4983230072969 + 3 ^ 40 * 5713762 * 2
def baseEnd_5713762 : Nat := 2933906251394979113597893

theorem tailTrace_5713762 : CollatzResearch.WordTrace tailWord_5713762 prefixEnd_5713762 2933906251394979113597893 := by
  unfold tailWord_5713762
  simp only [CollatzResearch.WordTrace]
  refine ⟨52099505181505895426171885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138932013817349054469791693 52099505181505895426171885)
  ·
    refine ⟨19537314443064710784814457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52099505181505895426171885 19537314443064710784814457)
    ·
      refine ⟨14652985832298533088610843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19537314443064710784814457 14652985832298533088610843)
      ·
        refine ⟨21979478748447799632916265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14652985832298533088610843 21979478748447799632916265)
        ·
          refine ⟨16484609061335849724687199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21979478748447799632916265 16484609061335849724687199)
          ·
            refine ⟨24726913592003774587030799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16484609061335849724687199 24726913592003774587030799)
            ·
              refine ⟨37090370388005661880546199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24726913592003774587030799 37090370388005661880546199)
              ·
                refine ⟨55635555582008492820819299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37090370388005661880546199 55635555582008492820819299)
                ·
                  refine ⟨83453333373012739231228949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55635555582008492820819299 83453333373012739231228949)
                  ·
                    refine ⟨3911875001859972151463857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83453333373012739231228949 3911875001859972151463857)
                    ·
                      refine ⟨2933906251394979113597893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3911875001859972151463857 2933906251394979113597893)
                      ·
                        rfl

theorem cell23_5713762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_5713762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713762 prefixEnd_5713762 := by exact prefixLift 5713762
  have htrace : WordTrace (prefixWord ++ tailWord_5713762) baseStart_5713762 baseEnd_5713762 := by
    simpa [prefixWord, tailWord_5713762, baseEnd_5713762] using wordTrace_append hprefix tailTrace_5713762
  have hstable : (prefixWord ++ tailWord_5713762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713762).length < 2 ^ (prefixWord ++ tailWord_5713762).sum := by decide
  have hdescent : baseEnd_5713762 < baseStart_5713762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713855 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 5]
def baseStart_5713855 : Nat := 118140960795 + 5713855 * 2 ^ 59
def prefixEnd_5713855 : Nat := 4983230072969 + 3 ^ 40 * 5713855 * 2
def baseEnd_5713855 : Nat := 2933954005095847249734965

theorem tailTrace_5713855 : CollatzResearch.WordTrace tailWord_5713855 prefixEnd_5713855 2933954005095847249734965 := by
  unfold tailWord_5713855
  simp only [CollatzResearch.WordTrace]
  refine ⟨208401412714686658587823019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138934275143124439058548679 208401412714686658587823019)
  ·
    refine ⟨312602119072029987881734529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208401412714686658587823019 312602119072029987881734529)
    ·
      refine ⟨234451589304022490911300897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312602119072029987881734529 234451589304022490911300897)
      ·
        refine ⟨175838691978016868183475673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234451589304022490911300897 175838691978016868183475673)
        ·
          refine ⟨131879018983512651137606755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175838691978016868183475673 131879018983512651137606755)
          ·
            refine ⟨197818528475268976706410133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131879018983512651137606755 197818528475268976706410133)
            ·
              refine ⟨9272743522278233283112975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197818528475268976706410133 9272743522278233283112975)
              ·
                refine ⟨13909115283417349924669463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9272743522278233283112975 13909115283417349924669463)
                ·
                  refine ⟨20863672925126024887004195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13909115283417349924669463 20863672925126024887004195)
                  ·
                    refine ⟨31295509387689037330506293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20863672925126024887004195 31295509387689037330506293)
                    ·
                      refine ⟨2933954005095847249734965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31295509387689037330506293 2933954005095847249734965)
                      ·
                        rfl

theorem cell23_5713855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_5713855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713855 prefixEnd_5713855 := by exact prefixLift 5713855
  have htrace : WordTrace (prefixWord ++ tailWord_5713855) baseStart_5713855 baseEnd_5713855 := by
    simpa [prefixWord, tailWord_5713855, baseEnd_5713855] using wordTrace_append hprefix tailTrace_5713855
  have hstable : (prefixWord ++ tailWord_5713855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713855).length < 2 ^ (prefixWord ++ tailWord_5713855).sum := by decide
  have hdescent : baseEnd_5713855 < baseStart_5713855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713902 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_5713902 : Nat := 118140960795 + 5713902 * 2 ^ 59
def prefixEnd_5713902 : Nat := 4983230072969 + 3 ^ 40 * 5713902 * 2
def baseEnd_5713902 : Nat := 2933978138686608565847249

theorem tailTrace_5713902 : CollatzResearch.WordTrace tailWord_5713902 prefixEnd_5713902 2933978138686608565847249 := by
  unfold tailWord_5713902
  simp only [CollatzResearch.WordTrace]
  refine ⟨26050390868189548201847995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138935417963677590409855973 26050390868189548201847995)
  ·
    refine ⟨39075586302284322302771993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26050390868189548201847995 39075586302284322302771993)
    ·
      refine ⟨29306689726713241727078995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39075586302284322302771993 29306689726713241727078995)
      ·
        refine ⟨43960034590069862590618493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29306689726713241727078995 43960034590069862590618493)
        ·
          refine ⟨16485012971276198471481935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43960034590069862590618493 16485012971276198471481935)
          ·
            refine ⟨24727519456914297707222903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16485012971276198471481935 24727519456914297707222903)
            ·
              refine ⟨37091279185371446560834355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24727519456914297707222903 37091279185371446560834355)
              ·
                refine ⟨55636918778057169841251533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37091279185371446560834355 55636918778057169841251533)
                ·
                  refine ⟨20863844541771438690469325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55636918778057169841251533 20863844541771438690469325)
                  ·
                    refine ⟨7823941703164289508925997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20863844541771438690469325 7823941703164289508925997)
                    ·
                      refine ⟨2933978138686608565847249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7823941703164289508925997 2933978138686608565847249)
                      ·
                        rfl

theorem cell23_5713902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_5713902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713902 prefixEnd_5713902 := by exact prefixLift 5713902
  have htrace : WordTrace (prefixWord ++ tailWord_5713902) baseStart_5713902 baseEnd_5713902 := by
    simpa [prefixWord, tailWord_5713902, baseEnd_5713902] using wordTrace_append hprefix tailTrace_5713902
  have hstable : (prefixWord ++ tailWord_5713902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713902).length < 2 ^ (prefixWord ++ tailWord_5713902).sum := by decide
  have hdescent : baseEnd_5713902 < baseStart_5713902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713925 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_5713925 : Nat := 118140960795 + 5713925 * 2 ^ 59
def prefixEnd_5713925 : Nat := 4983230072969 + 3 ^ 40 * 5713925 * 2
def baseEnd_5713925 : Nat := 2933989948741661975859643

theorem tailTrace_5713925 : CollatzResearch.WordTrace tailWord_5713925 prefixEnd_5713925 2933989948741661975859643 := by
  unfold tailWord_5713925
  simp only [CollatzResearch.WordTrace]
  refine ⟨208403965824433060542871229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138935977216288707028580819 208403965824433060542871229)
  ·
    refine ⟨78151487184162397703576711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208403965824433060542871229 78151487184162397703576711)
    ·
      refine ⟨117227230776243596555365067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78151487184162397703576711 117227230776243596555365067)
      ·
        refine ⟨175840846164365394833047601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117227230776243596555365067 175840846164365394833047601)
        ·
          refine ⟨131880634623274046124785701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175840846164365394833047601 131880634623274046124785701)
          ·
            refine ⟨24727618991863883648397319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131880634623274046124785701 24727618991863883648397319)
            ·
              refine ⟨37091428487795825472595979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24727618991863883648397319 37091428487795825472595979)
              ·
                refine ⟨55637142731693738208893969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37091428487795825472595979 55637142731693738208893969)
                ·
                  refine ⟨41727857048770303656670477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55637142731693738208893969 41727857048770303656670477)
                  ·
                    refine ⟨15647946393288863871251429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41727857048770303656670477 15647946393288863871251429)
                    ·
                      refine ⟨2933989948741661975859643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15647946393288863871251429 2933989948741661975859643)
                      ·
                        rfl

theorem cell23_5713925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_5713925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713925 prefixEnd_5713925 := by exact prefixLift 5713925
  have htrace : WordTrace (prefixWord ++ tailWord_5713925) baseStart_5713925 baseEnd_5713925 := by
    simpa [prefixWord, tailWord_5713925, baseEnd_5713925] using wordTrace_append hprefix tailTrace_5713925
  have hstable : (prefixWord ++ tailWord_5713925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713925).length < 2 ^ (prefixWord ++ tailWord_5713925).sum := by decide
  have hdescent : baseEnd_5713925 < baseStart_5713925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713933 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5713933 : Nat := 118140960795 + 5713933 * 2 ^ 59
def prefixEnd_5713933 : Nat := 4983230072969 + 3 ^ 40 * 5713933 * 2
def baseEnd_5713933 : Nat := 2933994056586897944559607

theorem tailTrace_5713933 : CollatzResearch.WordTrace tailWord_5713933 prefixEnd_5713933 2933994056586897944559607 := by
  unfold tailWord_5713933
  simp only [CollatzResearch.WordTrace]
  refine ⟨208404257608404077909162453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138936171738936051939441635 208404257608404077909162453)
  ·
    refine ⟨4884474787696970575995995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 208404257608404077909162453 4884474787696970575995995)
    ·
      refine ⟨7326712181545455863993993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4884474787696970575995995 7326712181545455863993993)
      ·
        refine ⟨5495034136159091897995495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7326712181545455863993993 5495034136159091897995495)
        ·
          refine ⟨8242551204238637846993243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5495034136159091897995495 8242551204238637846993243)
          ·
            refine ⟨12363826806357956770489865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8242551204238637846993243 12363826806357956770489865)
            ·
              refine ⟨9272870104768467577867399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12363826806357956770489865 9272870104768467577867399)
              ·
                refine ⟨13909305157152701366801099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9272870104768467577867399 13909305157152701366801099)
                ·
                  refine ⟨20863957735729052050201649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13909305157152701366801099 20863957735729052050201649)
                  ·
                    refine ⟨15647968301796789037651237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20863957735729052050201649 15647968301796789037651237)
                    ·
                      refine ⟨2933994056586897944559607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15647968301796789037651237 2933994056586897944559607)
                      ·
                        rfl

theorem cell23_5713933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5713933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713933 prefixEnd_5713933 := by exact prefixLift 5713933
  have htrace : WordTrace (prefixWord ++ tailWord_5713933) baseStart_5713933 baseEnd_5713933 := by
    simpa [prefixWord, tailWord_5713933, baseEnd_5713933] using wordTrace_append hprefix tailTrace_5713933
  have hstable : (prefixWord ++ tailWord_5713933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713933).length < 2 ^ (prefixWord ++ tailWord_5713933).sum := by decide
  have hdescent : baseEnd_5713933 < baseStart_5713933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713945 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 4, 4, 3]
def baseStart_5713945 : Nat := 118140960795 + 5713945 * 2 ^ 59
def prefixEnd_5713945 : Nat := 4983230072969 + 3 ^ 40 * 5713945 * 2
def baseEnd_5713945 : Nat := 2934000218354751897609551

theorem tailTrace_5713945 : CollatzResearch.WordTrace tailWord_5713945 prefixEnd_5713945 2934000218354751897609551 := by
  unfold tailWord_5713945
  simp only [CollatzResearch.WordTrace]
  refine ⟨208404695284360603958599289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138936463522907069305732859 208404695284360603958599289)
  ·
    refine ⟨156303521463270452968949467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208404695284360603958599289 156303521463270452968949467)
    ·
      refine ⟨234455282194905679453424201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156303521463270452968949467 234455282194905679453424201)
      ·
        refine ⟨175841461646179259590068151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234455282194905679453424201 175841461646179259590068151)
        ·
          refine ⟨263762192469268889385102227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175841461646179259590068151 263762192469268889385102227)
          ·
            refine ⟨395643288703903334077653341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263762192469268889385102227 395643288703903334077653341)
            ·
              refine ⟨148366233263963750279120003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395643288703903334077653341 148366233263963750279120003)
              ·
                refine ⟨222549349895945625418680005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148366233263963750279120003 222549349895945625418680005)
                ·
                  refine ⟨41728003105489804766002501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222549349895945625418680005 41728003105489804766002501)
                  ·
                    refine ⟨7824000582279338393625469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41728003105489804766002501 7824000582279338393625469)
                    ·
                      refine ⟨2934000218354751897609551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7824000582279338393625469 2934000218354751897609551)
                      ·
                        rfl

theorem cell23_5713945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_5713945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713945 prefixEnd_5713945 := by exact prefixLift 5713945
  have htrace : WordTrace (prefixWord ++ tailWord_5713945) baseStart_5713945 baseEnd_5713945 := by
    simpa [prefixWord, tailWord_5713945, baseEnd_5713945] using wordTrace_append hprefix tailTrace_5713945
  have hstable : (prefixWord ++ tailWord_5713945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713945).length < 2 ^ (prefixWord ++ tailWord_5713945).sum := by decide
  have hdescent : baseEnd_5713945 < baseStart_5713945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713955 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 4]
def baseStart_5713955 : Nat := 118140960795 + 5713955 * 2 ^ 59
def prefixEnd_5713955 : Nat := 4983230072969 + 3 ^ 40 * 5713955 * 2
def baseEnd_5713955 : Nat := 2934005353161296858484505

theorem tailTrace_5713955 : CollatzResearch.WordTrace tailWord_5713955 prefixEnd_5713955 2934005353161296858484505 := by
  unfold tailWord_5713955
  simp only [CollatzResearch.WordTrace]
  refine ⟨208405060014324375666463319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138936706676216250444308879 208405060014324375666463319)
  ·
    refine ⟨312607590021486563499694979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208405060014324375666463319 312607590021486563499694979)
    ·
      refine ⟨468911385032229845249542469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312607590021486563499694979 468911385032229845249542469)
      ·
        refine ⟨87920884693543095984289213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 468911385032229845249542469 87920884693543095984289213)
        ·
          refine ⟨32970331760078660994108455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87920884693543095984289213 32970331760078660994108455)
          ·
            refine ⟨49455497640117991491162683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32970331760078660994108455 49455497640117991491162683)
            ·
              refine ⟨74183246460176987236744025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49455497640117991491162683 74183246460176987236744025)
              ·
                refine ⟨55637434845132740427558019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74183246460176987236744025 55637434845132740427558019)
                ·
                  refine ⟨83456152267699110641337029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55637434845132740427558019 83456152267699110641337029)
                  ·
                    refine ⟨15648028550193583245250693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83456152267699110641337029 15648028550193583245250693)
                    ·
                      refine ⟨2934005353161296858484505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15648028550193583245250693 2934005353161296858484505)
                      ·
                        rfl

theorem cell23_5713955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_5713955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713955 prefixEnd_5713955 := by exact prefixLift 5713955
  have htrace : WordTrace (prefixWord ++ tailWord_5713955) baseStart_5713955 baseEnd_5713955 := by
    simpa [prefixWord, tailWord_5713955, baseEnd_5713955] using wordTrace_append hprefix tailTrace_5713955
  have hstable : (prefixWord ++ tailWord_5713955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713955).length < 2 ^ (prefixWord ++ tailWord_5713955).sum := by decide
  have hdescent : baseEnd_5713955 < baseStart_5713955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713976 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 4, 2, 2]
def baseStart_5713976 : Nat := 118140960795 + 5713976 * 2 ^ 59
def prefixEnd_5713976 : Nat := 4983230072969 + 3 ^ 40 * 5713976 * 2
def baseEnd_5713976 : Nat := 2934016136255041276321909

theorem tailTrace_5713976 : CollatzResearch.WordTrace tailWord_5713976 prefixEnd_5713976 2934016136255041276321909 := by
  unfold tailWord_5713976
  simp only [CollatzResearch.WordTrace]
  refine ⟨104202912973624148126488891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138937217298165530835318521 104202912973624148126488891)
  ·
    refine ⟨156304369460436222189733337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104202912973624148126488891 156304369460436222189733337)
    ·
      refine ⟨117228277095327166642300003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156304369460436222189733337 117228277095327166642300003)
      ·
        refine ⟨175842415642990749963450005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117228277095327166642300003 175842415642990749963450005)
        ·
          refine ⟨8242613233265191404536719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 175842415642990749963450005 8242613233265191404536719)
          ·
            refine ⟨12363919849897787106805079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8242613233265191404536719 12363919849897787106805079)
            ·
              refine ⟨18545879774846680660207619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12363919849897787106805079 18545879774846680660207619)
              ·
                refine ⟨27818819662270020990311429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18545879774846680660207619 27818819662270020990311429)
                ·
                  refine ⟨5216028686675628935683393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27818819662270020990311429 5216028686675628935683393)
                  ·
                    refine ⟨3912021515006721701762545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5216028686675628935683393 3912021515006721701762545)
                    ·
                      refine ⟨2934016136255041276321909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912021515006721701762545 2934016136255041276321909)
                      ·
                        rfl

theorem cell23_5713976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_5713976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713976 prefixEnd_5713976 := by exact prefixLift 5713976
  have htrace : WordTrace (prefixWord ++ tailWord_5713976) baseStart_5713976 baseEnd_5713976 := by
    simpa [prefixWord, tailWord_5713976, baseEnd_5713976] using wordTrace_append hprefix tailTrace_5713976
  have hstable : (prefixWord ++ tailWord_5713976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713976).length < 2 ^ (prefixWord ++ tailWord_5713976).sum := by decide
  have hdescent : baseEnd_5713976 < baseStart_5713976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5713995 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 4, 5]
def baseStart_5713995 : Nat := 118140960795 + 5713995 * 2 ^ 59
def prefixEnd_5713995 : Nat := 4983230072969 + 3 ^ 40 * 5713995 * 2
def baseEnd_5713995 : Nat := 978008630795825567328107

theorem tailTrace_5713995 : CollatzResearch.WordTrace tailWord_5713995 prefixEnd_5713995 978008630795825567328107 := by
  unfold tailWord_5713995
  simp only [CollatzResearch.WordTrace]
  refine ⟨208406518934179462497919439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138937679289452974998612959 208406518934179462497919439)
  ·
    refine ⟨312609778401269193746879159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208406518934179462497919439 312609778401269193746879159)
    ·
      refine ⟨468914667601903790620318739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312609778401269193746879159 468914667601903790620318739)
      ·
        refine ⟨703372001402855685930478109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468914667601903790620318739 703372001402855685930478109)
        ·
          refine ⟨263764500526070882223929291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 703372001402855685930478109 263764500526070882223929291)
          ·
            refine ⟨395646750789106323335893937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263764500526070882223929291 395646750789106323335893937)
            ·
              refine ⟨296735063091829742501920453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395646750789106323335893937 296735063091829742501920453)
              ·
                refine ⟨55637824329718076719110085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296735063091829742501920453 55637824329718076719110085)
                ·
                  refine ⟨10432092061822139384833141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55637824329718076719110085 10432092061822139384833141)
                  ·
                    refine ⟨978008630795825567328107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10432092061822139384833141 978008630795825567328107)
                    ·
                      rfl

theorem cell23_5713995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 5].length) (baseStart_5713995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5713995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5713995 prefixEnd_5713995 := by exact prefixLift 5713995
  have htrace : WordTrace (prefixWord ++ tailWord_5713995) baseStart_5713995 baseEnd_5713995 := by
    simpa [prefixWord, tailWord_5713995, baseEnd_5713995] using wordTrace_append hprefix tailTrace_5713995
  have hstable : (prefixWord ++ tailWord_5713995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5713995).length < 2 ^ (prefixWord ++ tailWord_5713995).sum := by decide
  have hdescent : baseEnd_5713995 < baseStart_5713995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5713995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714012 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_5714012 : Nat := 118140960795 + 5714012 * 2 ^ 59
def prefixEnd_5714012 : Nat := 4983230072969 + 3 ^ 40 * 5714012 * 2
def baseEnd_5714012 : Nat := 978011540519534378490581

theorem tailTrace_5714012 : CollatzResearch.WordTrace tailWord_5714012 prefixEnd_5714012 978011540519534378490581 := by
  unfold tailWord_5714012
  simp only [CollatzResearch.WordTrace]
  refine ⟨104203569487558937200644145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138938092650078582934192193 104203569487558937200644145)
  ·
    refine ⟨78152677115669202900483109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104203569487558937200644145 78152677115669202900483109)
    ·
      refine ⟨14653626959187975543840583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78152677115669202900483109 14653626959187975543840583)
      ·
        refine ⟨21980440438781963315760875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14653626959187975543840583 21980440438781963315760875)
        ·
          refine ⟨32970660658172944973641313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21980440438781963315760875 32970660658172944973641313)
          ·
            refine ⟨24727995493629708730230985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32970660658172944973641313 24727995493629708730230985)
            ·
              refine ⟨18545996620222281547673239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24727995493629708730230985 18545996620222281547673239)
              ·
                refine ⟨27818994930333422321509859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18545996620222281547673239 27818994930333422321509859)
                ·
                  refine ⟨41728492395500133482264789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27818994930333422321509859 41728492395500133482264789)
                  ·
                    refine ⟨978011540519534378490581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41728492395500133482264789 978011540519534378490581)
                    ·
                      rfl

theorem cell23_5714012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_5714012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714012 prefixEnd_5714012 := by exact prefixLift 5714012
  have htrace : WordTrace (prefixWord ++ tailWord_5714012) baseStart_5714012 baseEnd_5714012 := by
    simpa [prefixWord, tailWord_5714012, baseEnd_5714012] using wordTrace_append hprefix tailTrace_5714012
  have hstable : (prefixWord ++ tailWord_5714012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714012).length < 2 ^ (prefixWord ++ tailWord_5714012).sum := by decide
  have hdescent : baseEnd_5714012 < baseStart_5714012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714032 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 4]
def baseStart_5714032 : Nat := 118140960795 + 5714032 * 2 ^ 59
def prefixEnd_5714032 : Nat := 4983230072969 + 3 ^ 40 * 5714032 * 2
def baseEnd_5714032 : Nat := 2934044891171693057221651

theorem tailTrace_5714032 : CollatzResearch.WordTrace tailWord_5714032 prefixEnd_5714032 2934044891171693057221651 := by
  unfold tailWord_5714032
  simp only [CollatzResearch.WordTrace]
  refine ⟨104203934217522708908508175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138938578956696945211344233 104203934217522708908508175)
  ·
    refine ⟨156305901326284063362762263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104203934217522708908508175 156305901326284063362762263)
    ·
      refine ⟨234458851989426095044143395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156305901326284063362762263 234458851989426095044143395)
      ·
        refine ⟨351688277984139142566215093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234458851989426095044143395 351688277984139142566215093)
        ·
          refine ⟨32970776061013044615582665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351688277984139142566215093 32970776061013044615582665)
          ·
            refine ⟨24728082045759783461686999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32970776061013044615582665 24728082045759783461686999)
            ·
              refine ⟨37092123068639675192530499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24728082045759783461686999 37092123068639675192530499)
              ·
                refine ⟨55638184602959512788795749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37092123068639675192530499 55638184602959512788795749)
                ·
                  refine ⟨10432159613054908647899203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55638184602959512788795749 10432159613054908647899203)
                  ·
                    refine ⟨15648239419582362971848805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10432159613054908647899203 15648239419582362971848805)
                    ·
                      refine ⟨2934044891171693057221651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15648239419582362971848805 2934044891171693057221651)
                      ·
                        rfl

theorem cell23_5714032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_5714032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714032 prefixEnd_5714032 := by exact prefixLift 5714032
  have htrace : WordTrace (prefixWord ++ tailWord_5714032) baseStart_5714032 baseEnd_5714032 := by
    simpa [prefixWord, tailWord_5714032, baseEnd_5714032] using wordTrace_append hprefix tailTrace_5714032
  have hstable : (prefixWord ++ tailWord_5714032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714032).length < 2 ^ (prefixWord ++ tailWord_5714032).sum := by decide
  have hdescent : baseEnd_5714032 < baseStart_5714032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714069 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_5714069 : Nat := 118140960795 + 5714069 * 2 ^ 59
def prefixEnd_5714069 : Nat := 4983230072969 + 3 ^ 40 * 5714069 * 2
def baseEnd_5714069 : Nat := 2934063889955909412458981

theorem tailTrace_5714069 : CollatzResearch.WordTrace tailWord_5714069 prefixEnd_5714069 2934063889955909412458981 := by
  unfold tailWord_5714069
  simp only [CollatzResearch.WordTrace]
  refine ⟨208409217935911373136113261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138939478623940915424075507 208409217935911373136113261)
  ·
    refine ⟨78153456725966764926042473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208409217935911373136113261 78153456725966764926042473)
    ·
      refine ⟨58615092544475073694531855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78153456725966764926042473 58615092544475073694531855)
      ·
        refine ⟨87922638816712610541797783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58615092544475073694531855 87922638816712610541797783)
        ·
          refine ⟨131883958225068915812696675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87922638816712610541797783 131883958225068915812696675)
          ·
            refine ⟨197825937337603373719045013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131883958225068915812696675 197825937337603373719045013)
            ·
              refine ⟨9273090812700158143080235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197825937337603373719045013 9273090812700158143080235)
              ·
                refine ⟨13909636219050237214620353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9273090812700158143080235 13909636219050237214620353)
                ·
                  refine ⟨10432227164287677910965265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13909636219050237214620353 10432227164287677910965265)
                  ·
                    refine ⟨7824170373215758433223949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10432227164287677910965265 7824170373215758433223949)
                    ·
                      refine ⟨2934063889955909412458981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7824170373215758433223949 2934063889955909412458981)
                      ·
                        rfl

theorem cell23_5714069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_5714069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714069 prefixEnd_5714069 := by exact prefixLift 5714069
  have htrace : WordTrace (prefixWord ++ tailWord_5714069) baseStart_5714069 baseEnd_5714069 := by
    simpa [prefixWord, tailWord_5714069, baseEnd_5714069] using wordTrace_append hprefix tailTrace_5714069
  have hstable : (prefixWord ++ tailWord_5714069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714069).length < 2 ^ (prefixWord ++ tailWord_5714069).sum := by decide
  have hdescent : baseEnd_5714069 < baseStart_5714069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714075 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 6]
def baseStart_5714075 : Nat := 118140960795 + 5714075 * 2 ^ 59
def prefixEnd_5714075 : Nat := 4983230072969 + 3 ^ 40 * 5714075 * 2
def baseEnd_5714075 : Nat := 2934066970839836388983953

theorem tailTrace_5714075 : CollatzResearch.WordTrace tailWord_5714075 prefixEnd_5714075 2934066970839836388983953 := by
  unfold tailWord_5714075
  simp only [CollatzResearch.WordTrace]
  refine ⟨208409436773889636160831679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138939624515926424107221119 208409436773889636160831679)
  ·
    refine ⟨312614155160834454241247519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208409436773889636160831679 312614155160834454241247519)
    ·
      refine ⟨468921232741251681361871279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312614155160834454241247519 468921232741251681361871279)
      ·
        refine ⟨703381849111877522042806919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468921232741251681361871279 703381849111877522042806919)
        ·
          refine ⟨1055072773667816283064210379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703381849111877522042806919 1055072773667816283064210379)
          ·
            refine ⟨1582609160501724424596315569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055072773667816283064210379 1582609160501724424596315569)
            ·
              refine ⟨1186956870376293318447236677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582609160501724424596315569 1186956870376293318447236677)
              ·
                refine ⟨222554413195554997208856877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1186956870376293318447236677 222554413195554997208856877)
                ·
                  refine ⟨83457904948333123953321329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222554413195554997208856877 83457904948333123953321329)
                  ·
                    refine ⟨62593428711249842964990997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83457904948333123953321329 62593428711249842964990997)
                    ·
                      refine ⟨2934066970839836388983953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62593428711249842964990997 2934066970839836388983953)
                      ·
                        rfl

theorem cell23_5714075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_5714075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714075 prefixEnd_5714075 := by exact prefixLift 5714075
  have htrace : WordTrace (prefixWord ++ tailWord_5714075) baseStart_5714075 baseEnd_5714075 := by
    simpa [prefixWord, tailWord_5714075, baseEnd_5714075] using wordTrace_append hprefix tailTrace_5714075
  have hstable : (prefixWord ++ tailWord_5714075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714075).length < 2 ^ (prefixWord ++ tailWord_5714075).sum := by decide
  have hdescent : baseEnd_5714075 < baseStart_5714075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714076 : List Nat := [2, 2, 3, 2, 1, 1, 2, 5, 1, 4]
def baseStart_5714076 : Nat := 118140960795 + 5714076 * 2 ^ 59
def prefixEnd_5714076 : Nat := 4983230072969 + 3 ^ 40 * 5714076 * 2
def baseEnd_5714076 : Nat := 978022494773496961690483

theorem tailTrace_5714076 : CollatzResearch.WordTrace tailWord_5714076 prefixEnd_5714076 978022494773496961690483 := by
  unfold tailWord_5714076
  simp only [CollatzResearch.WordTrace]
  refine ⟨104204736623443006665809041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138939648831257342221078721 104204736623443006665809041)
  ·
    refine ⟨78153552467582254999356781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104204736623443006665809041 78153552467582254999356781)
    ·
      refine ⟨29307582175343345624758793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78153552467582254999356781 29307582175343345624758793)
      ·
        refine ⟨21980686631507509218569095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29307582175343345624758793 21980686631507509218569095)
        ·
          refine ⟨32971029947261263827853643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21980686631507509218569095 32971029947261263827853643)
          ·
            refine ⟨49456544920891895741780465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32971029947261263827853643 49456544920891895741780465)
            ·
              refine ⟨37092408690668921806335349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49456544920891895741780465 37092408690668921806335349)
              ·
                refine ⟨3477413314750211419343939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37092408690668921806335349 3477413314750211419343939)
                ·
                  refine ⟨5216119972125317129015909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477413314750211419343939 5216119972125317129015909)
                  ·
                    refine ⟨978022494773496961690483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5216119972125317129015909 978022494773496961690483)
                    ·
                      rfl

theorem cell23_5714076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_5714076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714076 prefixEnd_5714076 := by exact prefixLift 5714076
  have htrace : WordTrace (prefixWord ++ tailWord_5714076) baseStart_5714076 baseEnd_5714076 := by
    simpa [prefixWord, tailWord_5714076, baseEnd_5714076] using wordTrace_append hprefix tailTrace_5714076
  have hstable : (prefixWord ++ tailWord_5714076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714076).length < 2 ^ (prefixWord ++ tailWord_5714076).sum := by decide
  have hdescent : baseEnd_5714076 < baseStart_5714076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714093 : List Nat := [1, 5, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_5714093 : Nat := 118140960795 + 5714093 * 2 ^ 59
def prefixEnd_5714093 : Nat := 4983230072969 + 3 ^ 40 * 5714093 * 2
def baseEnd_5714093 : Nat := 978025404497205772852957

theorem tailTrace_5714093 : CollatzResearch.WordTrace tailWord_5714093 prefixEnd_5714093 978025404497205772852957 := by
  unfold tailWord_5714093
  simp only [CollatzResearch.WordTrace]
  refine ⟨208410093287824425234986933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138940062191882950156657955 208410093287824425234986933)
  ·
    refine ⟨19538446245733539865780025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208410093287824425234986933 19538446245733539865780025)
    ·
      refine ⟨14653834684300154899335019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19538446245733539865780025 14653834684300154899335019)
      ·
        refine ⟨21980752026450232349002529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14653834684300154899335019 21980752026450232349002529)
        ·
          refine ⟨16485564019837674261751897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21980752026450232349002529 16485564019837674261751897)
          ·
            refine ⟨12364173014878255696313923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16485564019837674261751897 12364173014878255696313923)
            ·
              refine ⟨18546259522317383544470885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12364173014878255696313923 18546259522317383544470885)
              ·
                refine ⟨3477423660434509414588291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18546259522317383544470885 3477423660434509414588291)
                ·
                  refine ⟨5216135490651764121882437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477423660434509414588291 5216135490651764121882437)
                  ·
                    refine ⟨978025404497205772852957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5216135490651764121882437 978025404497205772852957)
                    ·
                      rfl

theorem cell23_5714093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_5714093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714093 prefixEnd_5714093 := by exact prefixLift 5714093
  have htrace : WordTrace (prefixWord ++ tailWord_5714093) baseStart_5714093 baseEnd_5714093 := by
    simpa [prefixWord, tailWord_5714093, baseEnd_5714093] using wordTrace_append hprefix tailTrace_5714093
  have hstable : (prefixWord ++ tailWord_5714093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714093).length < 2 ^ (prefixWord ++ tailWord_5714093).sum := by decide
  have hdescent : baseEnd_5714093 < baseStart_5714093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714099 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 3, 1, 3]
def baseStart_5714099 : Nat := 118140960795 + 5714099 * 2 ^ 59
def prefixEnd_5714099 : Nat := 4983230072969 + 3 ^ 40 * 5714099 * 2
def baseEnd_5714099 : Nat := 2934079294375544295083843

theorem tailTrace_5714099 : CollatzResearch.WordTrace tailWord_5714099 prefixEnd_5714099 2934079294375544295083843 := by
  unfold tailWord_5714099
  simp only [CollatzResearch.WordTrace]
  refine ⟨208410312125802688259705351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138940208083868458839803567 208410312125802688259705351)
  ·
    refine ⟨312615468188704032389558027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208410312125802688259705351 312615468188704032389558027)
    ·
      refine ⟨468923202283056048584337041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312615468188704032389558027 468923202283056048584337041)
      ·
        refine ⟨351692401712292036438252781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468923202283056048584337041 351692401712292036438252781)
        ·
          refine ⟨131884650642109513664344793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351692401712292036438252781 131884650642109513664344793)
          ·
            refine ⟨98913487981582135248258595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131884650642109513664344793 98913487981582135248258595)
            ·
              refine ⟨148370231972373202872387893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98913487981582135248258595 148370231972373202872387893)
              ·
                refine ⟨13909709247409987769286365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148370231972373202872387893 13909709247409987769286365)
                ·
                  refine ⟨5216140967778745413482387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13909709247409987769286365 5216140967778745413482387)
                  ·
                    refine ⟨7824211451668118120223581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5216140967778745413482387 7824211451668118120223581)
                    ·
                      refine ⟨2934079294375544295083843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7824211451668118120223581 2934079294375544295083843)
                      ·
                        rfl

theorem cell23_5714099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 1, 3].length) (baseStart_5714099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714099 prefixEnd_5714099 := by exact prefixLift 5714099
  have htrace : WordTrace (prefixWord ++ tailWord_5714099) baseStart_5714099 baseEnd_5714099 := by
    simpa [prefixWord, tailWord_5714099, baseEnd_5714099] using wordTrace_append hprefix tailTrace_5714099
  have hstable : (prefixWord ++ tailWord_5714099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714099).length < 2 ^ (prefixWord ++ tailWord_5714099).sum := by decide
  have hdescent : baseEnd_5714099 < baseStart_5714099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714109 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 1, 5, 2]
def baseStart_5714109 : Nat := 118140960795 + 5714109 * 2 ^ 59
def prefixEnd_5714109 : Nat := 4983230072969 + 3 ^ 40 * 5714109 * 2
def baseEnd_5714109 : Nat := 2934084429182089255958797

theorem tailTrace_5714109 : CollatzResearch.WordTrace tailWord_5714109 prefixEnd_5714109 2934084429182089255958797 := by
  unfold tailWord_5714109
  simp only [CollatzResearch.WordTrace]
  refine ⟨208410676855766459967569381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138940451237177639978379587 208410676855766459967569381)
  ·
    refine ⟨39077001910456211243919259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208410676855766459967569381 39077001910456211243919259)
    ·
      refine ⟨58615502865684316865878889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39077001910456211243919259 58615502865684316865878889)
      ·
        refine ⟨43961627149263237649409167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58615502865684316865878889 43961627149263237649409167)
        ·
          refine ⟨65942440723894856474113751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43961627149263237649409167 65942440723894856474113751)
          ·
            refine ⟨98913661085842284711170627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65942440723894856474113751 98913661085842284711170627)
            ·
              refine ⟨148370491628763427066755941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98913661085842284711170627 148370491628763427066755941)
              ·
                refine ⟨27819467180393142575016739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148370491628763427066755941 27819467180393142575016739)
                ·
                  refine ⟨41729200770589713862525109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27819467180393142575016739 41729200770589713862525109)
                  ·
                    refine ⟨3912112572242785674611729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41729200770589713862525109 3912112572242785674611729)
                    ·
                      refine ⟨2934084429182089255958797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912112572242785674611729 2934084429182089255958797)
                      ·
                        rfl

theorem cell23_5714109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_5714109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714109 prefixEnd_5714109 := by exact prefixLift 5714109
  have htrace : WordTrace (prefixWord ++ tailWord_5714109) baseStart_5714109 baseEnd_5714109 := by
    simpa [prefixWord, tailWord_5714109, baseEnd_5714109] using wordTrace_append hprefix tailTrace_5714109
  have hstable : (prefixWord ++ tailWord_5714109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714109).length < 2 ^ (prefixWord ++ tailWord_5714109).sum := by decide
  have hdescent : baseEnd_5714109 < baseStart_5714109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714116 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_5714116 : Nat := 118140960795 + 5714116 * 2 ^ 59
def prefixEnd_5714116 : Nat := 4983230072969 + 3 ^ 40 * 5714116 * 2
def baseEnd_5714116 : Nat := 2934088023546670728571265

theorem tailTrace_5714116 : CollatzResearch.WordTrace tailWord_5714116 prefixEnd_5714116 2934088023546670728571265 := by
  unfold tailWord_5714116
  simp only [CollatzResearch.WordTrace]
  refine ⟨104205466083370550081537101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138940621444494066775382801 104205466083370550081537101)
  ·
    refine ⟨39077049781263956280576413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104205466083370550081537101 39077049781263956280576413)
    ·
      refine ⟨14653893667973983605216155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39077049781263956280576413 14653893667973983605216155)
      ·
        refine ⟨21980840501960975407824233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14653893667973983605216155 21980840501960975407824233)
        ·
          refine ⟨16485630376470731555868175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21980840501960975407824233 16485630376470731555868175)
          ·
            refine ⟨24728445564706097333802263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16485630376470731555868175 24728445564706097333802263)
            ·
              refine ⟨37092668347059146000703395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24728445564706097333802263 37092668347059146000703395)
              ·
                refine ⟨55639002520588719001055093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37092668347059146000703395 55639002520588719001055093)
                ·
                  refine ⟨5216156486305192406348915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55639002520588719001055093 5216156486305192406348915)
                  ·
                    refine ⟨7824234729457788609523373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5216156486305192406348915 7824234729457788609523373)
                    ·
                      refine ⟨2934088023546670728571265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7824234729457788609523373 2934088023546670728571265)
                      ·
                        rfl

theorem cell23_5714116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_5714116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714116 prefixEnd_5714116 := by exact prefixLift 5714116
  have htrace : WordTrace (prefixWord ++ tailWord_5714116) baseStart_5714116 baseEnd_5714116 := by
    simpa [prefixWord, tailWord_5714116, baseEnd_5714116] using wordTrace_append hprefix tailTrace_5714116
  have hstable : (prefixWord ++ tailWord_5714116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714116).length < 2 ^ (prefixWord ++ tailWord_5714116).sum := by decide
  have hdescent : baseEnd_5714116 < baseStart_5714116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714126 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2]
def baseStart_5714126 : Nat := 118140960795 + 5714126 * 2 ^ 59
def prefixEnd_5714126 : Nat := 4983230072969 + 3 ^ 40 * 5714126 * 2
def baseEnd_5714126 : Nat := 2934093158353215689446219

theorem tailTrace_5714126 : CollatzResearch.WordTrace tailWord_5714126 prefixEnd_5714126 2934093158353215689446219 := by
  unfold tailWord_5714126
  simp only [CollatzResearch.WordTrace]
  refine ⟨26051412112088108983867279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138940864597803247913958821 26051412112088108983867279)
  ·
    refine ⟨39077118168132163475800919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26051412112088108983867279 39077118168132163475800919)
    ·
      refine ⟨58615677252198245213701379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39077118168132163475800919 58615677252198245213701379)
      ·
        refine ⟨87923515878297367820552069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58615677252198245213701379 87923515878297367820552069)
        ·
          refine ⟨16485659227180756466353513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87923515878297367820552069 16485659227180756466353513)
          ·
            refine ⟨12364244420385567349765135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16485659227180756466353513 12364244420385567349765135)
            ·
              refine ⟨18546366630578351024647703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12364244420385567349765135 18546366630578351024647703)
              ·
                refine ⟨27819549945867526536971555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18546366630578351024647703 27819549945867526536971555)
                ·
                  refine ⟨41729324918801289805457333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27819549945867526536971555 41729324918801289805457333)
                  ·
                    refine ⟨3912124211137620919261625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41729324918801289805457333 3912124211137620919261625)
                    ·
                      refine ⟨2934093158353215689446219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912124211137620919261625 2934093158353215689446219)
                      ·
                        rfl

theorem cell23_5714126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_5714126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714126 prefixEnd_5714126 := by exact prefixLift 5714126
  have htrace : WordTrace (prefixWord ++ tailWord_5714126) baseStart_5714126 baseEnd_5714126 := by
    simpa [prefixWord, tailWord_5714126, baseEnd_5714126] using wordTrace_append hprefix tailTrace_5714126
  have hstable : (prefixWord ++ tailWord_5714126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714126).length < 2 ^ (prefixWord ++ tailWord_5714126).sum := by decide
  have hdescent : baseEnd_5714126 < baseStart_5714126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714136 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 1, 5]
def baseStart_5714136 : Nat := 118140960795 + 5714136 * 2 ^ 59
def prefixEnd_5714136 : Nat := 4983230072969 + 3 ^ 40 * 5714136 * 2
def baseEnd_5714136 : Nat := 978032764386586883440391

theorem tailTrace_5714136 : CollatzResearch.WordTrace tailWord_5714136 prefixEnd_5714136 978032764386586883440391 := by
  unfold tailWord_5714136
  simp only [CollatzResearch.WordTrace]
  refine ⟨104205830813334321789401131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138941107751112429052534841 104205830813334321789401131)
  ·
    refine ⟨156308746220001482684101697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104205830813334321789401131 156308746220001482684101697)
    ·
      refine ⟨117231559665001112013076273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156308746220001482684101697 117231559665001112013076273)
      ·
        refine ⟨87923669748750834009807205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117231559665001112013076273 87923669748750834009807205)
        ·
          refine ⟨16485688077890781376838851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87923669748750834009807205 16485688077890781376838851)
          ·
            refine ⟨24728532116836172065258277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16485688077890781376838851 24728532116836172065258277)
            ·
              refine ⟨4636599771906782262235927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24728532116836172065258277 4636599771906782262235927)
              ·
                refine ⟨6954899657860173393353891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4636599771906782262235927 6954899657860173393353891)
                ·
                  refine ⟨10432349486790260090030837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6954899657860173393353891 10432349486790260090030837)
                  ·
                    refine ⟨978032764386586883440391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10432349486790260090030837 978032764386586883440391)
                    ·
                      rfl

theorem cell23_5714136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_5714136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714136 prefixEnd_5714136 := by exact prefixLift 5714136
  have htrace : WordTrace (prefixWord ++ tailWord_5714136) baseStart_5714136 baseEnd_5714136 := by
    simpa [prefixWord, tailWord_5714136, baseEnd_5714136] using wordTrace_append hprefix tailTrace_5714136
  have hstable : (prefixWord ++ tailWord_5714136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714136).length < 2 ^ (prefixWord ++ tailWord_5714136).sum := by decide
  have hdescent : baseEnd_5714136 < baseStart_5714136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714140 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 6]
def baseStart_5714140 : Nat := 118140960795 + 5714140 * 2 ^ 59
def prefixEnd_5714140 : Nat := 4983230072969 + 3 ^ 40 * 5714140 * 2
def baseEnd_5714140 : Nat := 326011149675819848296795

theorem tailTrace_5714140 : CollatzResearch.WordTrace tailWord_5714140 prefixEnd_5714140 326011149675819848296795 := by
  unfold tailWord_5714140
  simp only [CollatzResearch.WordTrace]
  refine ⟨104205903759327076130973937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138941205012436101507965249 104205903759327076130973937)
  ·
    refine ⟨78154427819495307098230453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104205903759327076130973937 78154427819495307098230453)
    ·
      refine ⟨7326977608077685040459105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78154427819495307098230453 7326977608077685040459105)
      ·
        refine ⟨5495233206058263780344329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7326977608077685040459105 5495233206058263780344329)
        ·
          refine ⟨4121424904543697835258247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5495233206058263780344329 4121424904543697835258247)
          ·
            refine ⟨6182137356815546752887371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121424904543697835258247 6182137356815546752887371)
            ·
              refine ⟨9273206035223320129331057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6182137356815546752887371 9273206035223320129331057)
              ·
                refine ⟨6954904526417490096998293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9273206035223320129331057 6954904526417490096998293)
                ·
                  refine ⟨326011149675819848296795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6954904526417490096998293 326011149675819848296795)
                  ·
                    rfl

theorem cell23_5714140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_5714140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714140 prefixEnd_5714140 := by exact prefixLift 5714140
  have htrace : WordTrace (prefixWord ++ tailWord_5714140) baseStart_5714140 baseEnd_5714140 := by
    simpa [prefixWord, tailWord_5714140, baseEnd_5714140] using wordTrace_append hprefix tailTrace_5714140
  have hstable : (prefixWord ++ tailWord_5714140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714140).length < 2 ^ (prefixWord ++ tailWord_5714140).sum := by decide
  have hdescent : baseEnd_5714140 < baseStart_5714140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714159 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 5]
def baseStart_5714159 : Nat := 118140960795 + 5714159 * 2 ^ 59
def prefixEnd_5714159 : Nat := 4983230072969 + 3 ^ 40 * 5714159 * 2
def baseEnd_5714159 : Nat := 2934110103214814060333567

theorem tailTrace_5714159 : CollatzResearch.WordTrace tailWord_5714159 prefixEnd_5714159 2934110103214814060333567 := by
  unfold tailWord_5714159
  simp only [CollatzResearch.WordTrace]
  refine ⟨208412500505585318506889531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138941667003723545671259687 208412500505585318506889531)
  ·
    refine ⟨312618750758377977760334297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208412500505585318506889531 312618750758377977760334297)
    ·
      refine ⟨234464063068783483320250723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312618750758377977760334297 234464063068783483320250723)
      ·
        refine ⟨351696094603175224980376085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234464063068783483320250723 351696094603175224980376085)
        ·
          refine ⟨16485754434523838670955129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 351696094603175224980376085 16485754434523838670955129)
          ·
            refine ⟨12364315825892879003216347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16485754434523838670955129 12364315825892879003216347)
            ·
              refine ⟨18546473738839318504824521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12364315825892879003216347 18546473738839318504824521)
              ·
                refine ⟨13909855304129488878618391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18546473738839318504824521 13909855304129488878618391)
                ·
                  refine ⟨20864782956194233317927587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13909855304129488878618391 20864782956194233317927587)
                  ·
                    refine ⟨31297174434291349976891381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20864782956194233317927587 31297174434291349976891381)
                    ·
                      refine ⟨2934110103214814060333567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31297174434291349976891381 2934110103214814060333567)
                      ·
                        rfl

theorem cell23_5714159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_5714159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714159 prefixEnd_5714159 := by exact prefixLift 5714159
  have htrace : WordTrace (prefixWord ++ tailWord_5714159) baseStart_5714159 baseEnd_5714159 := by
    simpa [prefixWord, tailWord_5714159, baseEnd_5714159] using wordTrace_append hprefix tailTrace_5714159
  have hstable : (prefixWord ++ tailWord_5714159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714159).length < 2 ^ (prefixWord ++ tailWord_5714159).sum := by decide
  have hdescent : baseEnd_5714159 < baseStart_5714159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714166 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_5714166 : Nat := 118140960795 + 5714166 * 2 ^ 59
def prefixEnd_5714166 : Nat := 4983230072969 + 3 ^ 40 * 5714166 * 2
def baseEnd_5714166 : Nat := 978037899193131844315345

theorem tailTrace_5714166 : CollatzResearch.WordTrace tailWord_5714166 prefixEnd_5714166 978037899193131844315345 := by
  unfold tailWord_5714166
  simp only [CollatzResearch.WordTrace]
  refine ⟨13025797238534997418899647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138941837211039972468262901 13025797238534997418899647)
  ·
    refine ⟨19538695857802496128349471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13025797238534997418899647 19538695857802496128349471)
    ·
      refine ⟨29308043786703744192524207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19538695857802496128349471 29308043786703744192524207)
      ·
        refine ⟨43962065680055616288786311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29308043786703744192524207 43962065680055616288786311)
        ·
          refine ⟨65943098520083424433179467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43962065680055616288786311 65943098520083424433179467)
          ·
            refine ⟨98914647780125136649769201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65943098520083424433179467 98914647780125136649769201)
            ·
              refine ⟨74185985835093852487326901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98914647780125136649769201 74185985835093852487326901)
              ·
                refine ⟨6954936172040048670686897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74185985835093852487326901 6954936172040048670686897)
                ·
                  refine ⟨5216202129030036503015173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6954936172040048670686897 5216202129030036503015173)
                  ·
                    refine ⟨978037899193131844315345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5216202129030036503015173 978037899193131844315345)
                    ·
                      rfl

theorem cell23_5714166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_5714166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714166 prefixEnd_5714166 := by exact prefixLift 5714166
  have htrace : WordTrace (prefixWord ++ tailWord_5714166) baseStart_5714166 baseEnd_5714166 := by
    simpa [prefixWord, tailWord_5714166, baseEnd_5714166] using wordTrace_append hprefix tailTrace_5714166
  have hstable : (prefixWord ++ tailWord_5714166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714166).length < 2 ^ (prefixWord ++ tailWord_5714166).sum := by decide
  have hdescent : baseEnd_5714166 < baseStart_5714166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714207 : List Nat := [1, 1, 2, 4, 3, 2, 3, 2, 1, 2, 2]
def baseStart_5714207 : Nat := 118140960795 + 5714207 * 2 ^ 59
def prefixEnd_5714207 : Nat := 4983230072969 + 3 ^ 40 * 5714207 * 2
def baseEnd_5714207 : Nat := 2934134750286229872533347

theorem tailTrace_5714207 : CollatzResearch.WordTrace tailWord_5714207 prefixEnd_5714207 2934134750286229872533347 := by
  unfold tailWord_5714207
  simp only [CollatzResearch.WordTrace]
  refine ⟨208414251209411422704636875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138942834139607615136424583 208414251209411422704636875)
  ·
    refine ⟨312621376814117134056955313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208414251209411422704636875 312621376814117134056955313)
    ·
      refine ⟨234466032610587850542716485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312621376814117134056955313 234466032610587850542716485)
      ·
        refine ⟨43962381114485221976759341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234466032610587850542716485 43962381114485221976759341)
        ·
          refine ⟨16485892917931958241284753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43962381114485221976759341 16485892917931958241284753)
          ·
            refine ⟨12364419688448968680963565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16485892917931958241284753 12364419688448968680963565)
            ·
              refine ⟨4636657383168363255361337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12364419688448968680963565 4636657383168363255361337)
              ·
                refine ⟨3477493037376272441521003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4636657383168363255361337 3477493037376272441521003)
                ·
                  refine ⟨5216239556064408662281505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477493037376272441521003 5216239556064408662281505)
                  ·
                    refine ⟨3912179667048306496711129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5216239556064408662281505 3912179667048306496711129)
                    ·
                      refine ⟨2934134750286229872533347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912179667048306496711129 2934134750286229872533347)
                      ·
                        rfl

theorem cell23_5714207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_5714207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714207 prefixEnd_5714207 := by exact prefixLift 5714207
  have htrace : WordTrace (prefixWord ++ tailWord_5714207) baseStart_5714207 baseEnd_5714207 := by
    simpa [prefixWord, tailWord_5714207, baseEnd_5714207] using wordTrace_append hprefix tailTrace_5714207
  have hstable : (prefixWord ++ tailWord_5714207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714207).length < 2 ^ (prefixWord ++ tailWord_5714207).sum := by decide
  have hdescent : baseEnd_5714207 < baseStart_5714207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714223 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 2, 1, 3]
def baseStart_5714223 : Nat := 118140960795 + 5714223 * 2 ^ 59
def prefixEnd_5714223 : Nat := 4983230072969 + 3 ^ 40 * 5714223 * 2
def baseEnd_5714223 : Nat := 2934142965976701809933273

theorem tailTrace_5714223 : CollatzResearch.WordTrace tailWord_5714223 prefixEnd_5714223 2934142965976701809933273 := by
  unfold tailWord_5714223
  simp only [CollatzResearch.WordTrace]
  refine ⟨208414834777353457437219323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138943223184902304958146215 208414834777353457437219323)
  ·
    refine ⟨312622252166030186155828985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208414834777353457437219323 312622252166030186155828985)
    ·
      refine ⟨234466689124522639616871739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312622252166030186155828985 234466689124522639616871739)
      ·
        refine ⟨351700033686783959425307609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234466689124522639616871739 351700033686783959425307609)
        ·
          refine ⟨263775025265087969568980707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351700033686783959425307609 263775025265087969568980707)
          ·
            refine ⟨395662537897631954353471061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263775025265087969568980707 395662537897631954353471061)
            ·
              refine ⟨4636670365987874465079739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 395662537897631954353471061 4636670365987874465079739)
              ·
                refine ⟨6955005548981811697619609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4636670365987874465079739 6955005548981811697619609)
                ·
                  refine ⟨5216254161736358773214707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6955005548981811697619609 5216254161736358773214707)
                  ·
                    refine ⟨7824381242604538159822061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5216254161736358773214707 7824381242604538159822061)
                    ·
                      refine ⟨2934142965976701809933273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7824381242604538159822061 2934142965976701809933273)
                      ·
                        rfl

theorem cell23_5714223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 2, 1, 3].length) (baseStart_5714223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714223 prefixEnd_5714223 := by exact prefixLift 5714223
  have htrace : WordTrace (prefixWord ++ tailWord_5714223) baseStart_5714223 baseEnd_5714223 := by
    simpa [prefixWord, tailWord_5714223, baseEnd_5714223] using wordTrace_append hprefix tailTrace_5714223
  have hstable : (prefixWord ++ tailWord_5714223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714223).length < 2 ^ (prefixWord ++ tailWord_5714223).sum := by decide
  have hdescent : baseEnd_5714223 < baseStart_5714223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714233 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 3, 3, 2]
def baseStart_5714233 : Nat := 118140960795 + 5714233 * 2 ^ 59
def prefixEnd_5714233 : Nat := 4983230072969 + 3 ^ 40 * 5714233 * 2
def baseEnd_5714233 : Nat := 2934148100783246770808227

theorem tailTrace_5714233 : CollatzResearch.WordTrace tailWord_5714233 prefixEnd_5714233 2934148100783246770808227 := by
  unfold tailWord_5714233
  simp only [CollatzResearch.WordTrace]
  refine ⟨208415199507317229145083353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138943466338211486096722235 208415199507317229145083353)
  ·
    refine ⟨156311399630487921858812515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208415199507317229145083353 156311399630487921858812515)
    ·
      refine ⟨234467099445731882788218773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156311399630487921858812515 234467099445731882788218773)
      ·
        refine ⟨10990645286518682005697755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234467099445731882788218773 10990645286518682005697755)
        ·
          refine ⟨16485967929778023008546633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10990645286518682005697755 16485967929778023008546633)
          ·
            refine ⟨12364475947333517256409975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16485967929778023008546633 12364475947333517256409975)
            ·
              refine ⟨18546713921000275884614963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12364475947333517256409975 18546713921000275884614963)
              ·
                refine ⟨27820070881500413826922445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18546713921000275884614963 27820070881500413826922445)
                ·
                  refine ⟨10432526580562655185095917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27820070881500413826922445 10432526580562655185095917)
                  ·
                    refine ⟨3912197467710995694410969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10432526580562655185095917 3912197467710995694410969)
                    ·
                      refine ⟨2934148100783246770808227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912197467710995694410969 2934148100783246770808227)
                      ·
                        rfl

theorem cell23_5714233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_5714233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714233 prefixEnd_5714233 := by exact prefixLift 5714233
  have htrace : WordTrace (prefixWord ++ tailWord_5714233) baseStart_5714233 baseEnd_5714233 := by
    simpa [prefixWord, tailWord_5714233, baseEnd_5714233] using wordTrace_append hprefix tailTrace_5714233
  have hstable : (prefixWord ++ tailWord_5714233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714233).length < 2 ^ (prefixWord ++ tailWord_5714233).sum := by decide
  have hdescent : baseEnd_5714233 < baseStart_5714233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714280 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_5714280 : Nat := 118140960795 + 5714280 * 2 ^ 59
def prefixEnd_5714280 : Nat := 4983230072969 + 3 ^ 40 * 5714280 * 2
def baseEnd_5714280 : Nat := 2934172234374008086920511

theorem tailTrace_5714280 : CollatzResearch.WordTrace tailWord_5714280 prefixEnd_5714280 2934172234374008086920511 := by
  unfold tailWord_5714280
  simp only [CollatzResearch.WordTrace]
  refine ⟨104208456869073478086022147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138944609158764637448029529 104208456869073478086022147)
  ·
    refine ⟨156312685303610217129033221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104208456869073478086022147 156312685303610217129033221)
    ·
      refine ⟨29308628494426915711693729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156312685303610217129033221 29308628494426915711693729)
      ·
        refine ⟨21981471370820186783770297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29308628494426915711693729 21981471370820186783770297)
        ·
          refine ⟨16486103528115140087827723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21981471370820186783770297 16486103528115140087827723)
          ·
            refine ⟨24729155292172710131741585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16486103528115140087827723 24729155292172710131741585)
            ·
              refine ⟨18546866469129532598806189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24729155292172710131741585 18546866469129532598806189)
              ·
                refine ⟨6955074925923574724552321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18546866469129532598806189 6955074925923574724552321)
                ·
                  refine ⟨5216306194442681043414241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6955074925923574724552321 5216306194442681043414241)
                  ·
                    refine ⟨3912229645832010782560681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5216306194442681043414241 3912229645832010782560681)
                    ·
                      refine ⟨2934172234374008086920511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912229645832010782560681 2934172234374008086920511)
                      ·
                        rfl

theorem cell23_5714280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_5714280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714280 prefixEnd_5714280 := by exact prefixLift 5714280
  have htrace : WordTrace (prefixWord ++ tailWord_5714280) baseStart_5714280 baseEnd_5714280 := by
    simpa [prefixWord, tailWord_5714280, baseEnd_5714280] using wordTrace_append hprefix tailTrace_5714280
  have hstable : (prefixWord ++ tailWord_5714280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714280).length < 2 ^ (prefixWord ++ tailWord_5714280).sum := by decide
  have hdescent : baseEnd_5714280 < baseStart_5714280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714299 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 1, 7]
def baseStart_5714299 : Nat := 118140960795 + 5714299 * 2 ^ 59
def prefixEnd_5714299 : Nat := 4983230072969 + 3 ^ 40 * 5714299 * 2
def baseEnd_5714299 : Nat := 978060663502147837527641

theorem tailTrace_5714299 : CollatzResearch.WordTrace tailWord_5714299 prefixEnd_5714299 978060663502147837527641 := by
  unfold tailWord_5714299
  simp only [CollatzResearch.WordTrace]
  refine ⟨208417606725078122416985951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138945071150052081611323967 208417606725078122416985951)
  ·
    refine ⟨312626410087617183625478927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208417606725078122416985951 312626410087617183625478927)
    ·
      refine ⟨468939615131425775438218391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312626410087617183625478927 468939615131425775438218391)
      ·
        refine ⟨703409422697138663157327587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468939615131425775438218391 703409422697138663157327587)
        ·
          refine ⟨1055114134045707994735991381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703409422697138663157327587 1055114134045707994735991381)
          ·
            refine ⟨12364618758348140563312399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1055114134045707994735991381 12364618758348140563312399)
            ·
              refine ⟨18546928137522210844968599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12364618758348140563312399 18546928137522210844968599)
              ·
                refine ⟨27820392206283316267452899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18546928137522210844968599 27820392206283316267452899)
                ·
                  refine ⟨41730588309424974401179349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27820392206283316267452899 41730588309424974401179349)
                  ·
                    refine ⟨978060663502147837527641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41730588309424974401179349 978060663502147837527641)
                    ·
                      rfl

theorem cell23_5714299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 7].length) (baseStart_5714299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714299 prefixEnd_5714299 := by exact prefixLift 5714299
  have htrace : WordTrace (prefixWord ++ tailWord_5714299) baseStart_5714299 baseEnd_5714299 := by
    simpa [prefixWord, tailWord_5714299, baseEnd_5714299] using wordTrace_append hprefix tailTrace_5714299
  have hstable : (prefixWord ++ tailWord_5714299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714299).length < 2 ^ (prefixWord ++ tailWord_5714299).sum := by decide
  have hdescent : baseEnd_5714299 < baseStart_5714299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714314 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2]
def baseStart_5714314 : Nat := 118140960795 + 5714314 * 2 ^ 59
def prefixEnd_5714314 : Nat := 4983230072969 + 3 ^ 40 * 5714314 * 2
def baseEnd_5714314 : Nat := 2934189692716260953895355

theorem tailTrace_5714314 : CollatzResearch.WordTrace tailWord_5714314 prefixEnd_5714314 2934189692716260953895355 := by
  unfold tailWord_5714314
  simp only [CollatzResearch.WordTrace]
  refine ⟨52104538455005944994695499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138945435880015853319187997 52104538455005944994695499)
  ·
    refine ⟨78156807682508917492043249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52104538455005944994695499 78156807682508917492043249)
    ·
      refine ⟨58617605761881688119032437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78156807682508917492043249 58617605761881688119032437)
      ·
        refine ⟨5495400540176408261159291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58617605761881688119032437 5495400540176408261159291)
        ·
          refine ⟨8243100810264612391738937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5495400540176408261159291 8243100810264612391738937)
          ·
            refine ⟨6182325607698459293804203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8243100810264612391738937 6182325607698459293804203)
            ·
              refine ⟨9273488411547688940706305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6182325607698459293804203 9273488411547688940706305)
              ·
                refine ⟨6955116308660766705529729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9273488411547688940706305 6955116308660766705529729)
                ·
                  refine ⟨5216337231495575029147297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6955116308660766705529729 5216337231495575029147297)
                  ·
                    refine ⟨3912252923621681271860473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5216337231495575029147297 3912252923621681271860473)
                    ·
                      refine ⟨2934189692716260953895355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912252923621681271860473 2934189692716260953895355)
                      ·
                        rfl

theorem cell23_5714314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_5714314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714314 prefixEnd_5714314 := by exact prefixLift 5714314
  have htrace : WordTrace (prefixWord ++ tailWord_5714314) baseStart_5714314 baseEnd_5714314 := by
    simpa [prefixWord, tailWord_5714314, baseEnd_5714314] using wordTrace_append hprefix tailTrace_5714314
  have hstable : (prefixWord ++ tailWord_5714314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714314).length < 2 ^ (prefixWord ++ tailWord_5714314).sum := by decide
  have hdescent : baseEnd_5714314 < baseStart_5714314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714359 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 8]
def baseStart_5714359 : Nat := 118140960795 + 5714359 * 2 ^ 59
def prefixEnd_5714359 : Nat := 4983230072969 + 3 ^ 40 * 5714359 * 2
def baseEnd_5714359 : Nat := 326023644371745919759183

theorem tailTrace_5714359 : CollatzResearch.WordTrace tailWord_5714359 prefixEnd_5714359 326023644371745919759183 := by
  unfold tailWord_5714359
  simp only [CollatzResearch.WordTrace]
  refine ⟨208419795104860752664170131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138946530069907168442780087 208419795104860752664170131)
  ·
    refine ⟨312629692657291128996255197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208419795104860752664170131 312629692657291128996255197)
    ·
      refine ⟨117236134746484173373595699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312629692657291128996255197 117236134746484173373595699)
      ·
        refine ⟨175854202119726260060393549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117236134746484173373595699 175854202119726260060393549)
        ·
          refine ⟨65945325794897347522647581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175854202119726260060393549 65945325794897347522647581)
          ·
            refine ⟨24729497173086505320992843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65945325794897347522647581 24729497173086505320992843)
            ·
              refine ⟨37094245759629757981489265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24729497173086505320992843 37094245759629757981489265)
              ·
                refine ⟨27820684319722318486116949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37094245759629757981489265 27820684319722318486116949)
                ·
                  refine ⟨326023644371745919759183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27820684319722318486116949 326023644371745919759183)
                  ·
                    rfl

theorem cell23_5714359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 8].length) (baseStart_5714359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714359 prefixEnd_5714359 := by exact prefixLift 5714359
  have htrace : WordTrace (prefixWord ++ tailWord_5714359) baseStart_5714359 baseEnd_5714359 := by
    simpa [prefixWord, tailWord_5714359, baseEnd_5714359] using wordTrace_append hprefix tailTrace_5714359
  have hstable : (prefixWord ++ tailWord_5714359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714359).length < 2 ^ (prefixWord ++ tailWord_5714359).sum := by decide
  have hdescent : baseEnd_5714359 < baseStart_5714359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714380 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_5714380 : Nat := 118140960795 + 5714380 * 2 ^ 59
def prefixEnd_5714380 : Nat := 4983230072969 + 3 ^ 40 * 5714380 * 2
def baseEnd_5714380 : Nat := 978074527479819231890017

theorem tailTrace_5714380 : CollatzResearch.WordTrace tailWord_5714380 prefixEnd_5714380 978074527479819231890017 := by
  unfold tailWord_5714380
  simp only [CollatzResearch.WordTrace]
  refine ⟨104210280518892336625342297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138947040691856448833789729 104210280518892336625342297)
  ·
    refine ⟨78157710389169252469006723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104210280518892336625342297 78157710389169252469006723)
    ·
      refine ⟨117236565583753878703510085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78157710389169252469006723 117236565583753878703510085)
      ·
        refine ⟨21981856046953852256908141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117236565583753878703510085 21981856046953852256908141)
        ·
          refine ⟨8243196017607694596340553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21981856046953852256908141 8243196017607694596340553)
          ·
            refine ⟨6182397013205770947255415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8243196017607694596340553 6182397013205770947255415)
            ·
              refine ⟨9273595519808656420883123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6182397013205770947255415 9273595519808656420883123)
              ·
                refine ⟨13910393279712984631324685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9273595519808656420883123 13910393279712984631324685)
                ·
                  refine ⟨5216397479892369236746757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13910393279712984631324685 5216397479892369236746757)
                  ·
                    refine ⟨978074527479819231890017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5216397479892369236746757 978074527479819231890017)
                    ·
                      rfl

theorem cell23_5714380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_5714380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714380 prefixEnd_5714380 := by exact prefixLift 5714380
  have htrace : WordTrace (prefixWord ++ tailWord_5714380) baseStart_5714380 baseEnd_5714380 := by
    simpa [prefixWord, tailWord_5714380, baseEnd_5714380] using wordTrace_append hprefix tailTrace_5714380
  have hstable : (prefixWord ++ tailWord_5714380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714380).length < 2 ^ (prefixWord ++ tailWord_5714380).sum := by decide
  have hdescent : baseEnd_5714380 < baseStart_5714380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714437 : List Nat := [1, 3, 1, 1, 2, 2, 6, 2, 1, 1, 3]
def baseStart_5714437 : Nat := 118140960795 + 5714437 * 2 ^ 59
def prefixEnd_5714437 : Nat := 4983230072969 + 3 ^ 40 * 5714437 * 2
def baseEnd_5714437 : Nat := 2934252850836763972657289

theorem tailTrace_5714437 : CollatzResearch.WordTrace tailWord_5714437 prefixEnd_5714437 2934252850836763972657289 := by
  unfold tailWord_5714437
  simp only [CollatzResearch.WordTrace]
  refine ⟨208422639998578171985509565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138948426665718781323673043 208422639998578171985509565)
  ·
    refine ⟨78158489999466814494566087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208422639998578171985509565 78158489999466814494566087)
    ·
      refine ⟨117237734999200221741849131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78158489999466814494566087 117237734999200221741849131)
      ·
        refine ⟨175856602498800332612773697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117237734999200221741849131 175856602498800332612773697)
        ·
          refine ⟨131892451874100249459580273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175856602498800332612773697 131892451874100249459580273)
          ·
            refine ⟨98919338905575187094685205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131892451874100249459580273 98919338905575187094685205)
            ·
              refine ⟨4636844011198836895063369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98919338905575187094685205 4636844011198836895063369)
              ·
                refine ⟨3477633008399127671297527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4636844011198836895063369 3477633008399127671297527)
                ·
                  refine ⟨5216449512598691506946291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477633008399127671297527 5216449512598691506946291)
                  ·
                    refine ⟨7824674268898037260419437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5216449512598691506946291 7824674268898037260419437)
                    ·
                      refine ⟨2934252850836763972657289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7824674268898037260419437 2934252850836763972657289)
                      ·
                        rfl

theorem cell23_5714437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 1, 1, 3].length) (baseStart_5714437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714437 prefixEnd_5714437 := by exact prefixLift 5714437
  have htrace : WordTrace (prefixWord ++ tailWord_5714437) baseStart_5714437 baseEnd_5714437 := by
    simpa [prefixWord, tailWord_5714437, baseEnd_5714437] using wordTrace_append hprefix tailTrace_5714437
  have hstable : (prefixWord ++ tailWord_5714437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714437).length < 2 ^ (prefixWord ++ tailWord_5714437).sum := by decide
  have hdescent : baseEnd_5714437 < baseStart_5714437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714449 : List Nat := [1, 2, 2, 1, 1, 2, 2, 12]
def baseStart_5714449 : Nat := 118140960795 + 5714449 * 2 ^ 59
def prefixEnd_5714449 : Nat := 4983230072969 + 3 ^ 40 * 5714449 * 2
def baseEnd_5714449 : Nat := 108676259726096960211379

theorem tailTrace_5714449 : CollatzResearch.WordTrace tailWord_5714449 prefixEnd_5714449 108676259726096960211379 := by
  unfold tailWord_5714449
  simp only [CollatzResearch.WordTrace]
  refine ⟨208423077674534698034946401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138948718449689798689964267 208423077674534698034946401)
  ·
    refine ⟨156317308255901023526209801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208423077674534698034946401 156317308255901023526209801)
    ·
      refine ⟨117237981191925767644657351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156317308255901023526209801 117237981191925767644657351)
      ·
        refine ⟨175856971787888651466986027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117237981191925767644657351 175856971787888651466986027)
        ·
          refine ⟨263785457681832977200479041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175856971787888651466986027 263785457681832977200479041)
          ·
            refine ⟨197839093261374732900359281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263785457681832977200479041 197839093261374732900359281)
            ·
              refine ⟨148379319946031049675269461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197839093261374732900359281 148379319946031049675269461)
              ·
                refine ⟨108676259726096960211379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 148379319946031049675269461 108676259726096960211379)
                ·
                  rfl

theorem cell23_5714449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 12].length) (baseStart_5714449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714449 prefixEnd_5714449 := by exact prefixLift 5714449
  have htrace : WordTrace (prefixWord ++ tailWord_5714449) baseStart_5714449 baseEnd_5714449 := by
    simpa [prefixWord, tailWord_5714449, baseEnd_5714449] using wordTrace_append hprefix tailTrace_5714449
  have hstable : (prefixWord ++ tailWord_5714449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714449).length < 2 ^ (prefixWord ++ tailWord_5714449).sum := by decide
  have hdescent : baseEnd_5714449 < baseStart_5714449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714453 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_5714453 : Nat := 118140960795 + 5714453 * 2 ^ 59
def prefixEnd_5714453 : Nat := 4983230072969 + 3 ^ 40 * 5714453 * 2
def baseEnd_5714453 : Nat := 978087022175745303352405

theorem tailTrace_5714453 : CollatzResearch.WordTrace tailWord_5714453 prefixEnd_5714453 978087022175745303352405 := by
  unfold tailWord_5714453
  simp only [CollatzResearch.WordTrace]
  refine ⟨208423223566520206718092013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138948815711013471145394675 208423223566520206718092013)
  ·
    refine ⟨78158708837445077519284505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208423223566520206718092013 78158708837445077519284505)
    ·
      refine ⟨58619031628083808139463379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78158708837445077519284505 58619031628083808139463379)
      ·
        refine ⟨87928547442125712209195069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58619031628083808139463379 87928547442125712209195069)
        ·
          refine ⟨32973205290797142078448151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87928547442125712209195069 32973205290797142078448151)
          ·
            refine ⟨49459807936195713117672227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32973205290797142078448151 49459807936195713117672227)
            ·
              refine ⟨74189711904293569676508341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49459807936195713117672227 74189711904293569676508341)
              ·
                refine ⟨6955285491027522157172657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74189711904293569676508341 6955285491027522157172657)
                ·
                  refine ⟨5216464118270641617879493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6955285491027522157172657 5216464118270641617879493)
                  ·
                    refine ⟨978087022175745303352405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5216464118270641617879493 978087022175745303352405)
                    ·
                      rfl

theorem cell23_5714453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_5714453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714453 prefixEnd_5714453 := by exact prefixLift 5714453
  have htrace : WordTrace (prefixWord ++ tailWord_5714453) baseStart_5714453 baseEnd_5714453 := by
    simpa [prefixWord, tailWord_5714453, baseEnd_5714453] using wordTrace_append hprefix tailTrace_5714453
  have hstable : (prefixWord ++ tailWord_5714453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714453).length < 2 ^ (prefixWord ++ tailWord_5714453).sum := by decide
  have hdescent : baseEnd_5714453 < baseStart_5714453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714459 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 7]
def baseStart_5714459 : Nat := 118140960795 + 5714459 * 2 ^ 59
def prefixEnd_5714459 : Nat := 4983230072969 + 3 ^ 40 * 5714459 * 2
def baseEnd_5714459 : Nat := 2934264147411162886582187

theorem tailTrace_5714459 : CollatzResearch.WordTrace tailWord_5714459 prefixEnd_5714459 2934264147411162886582187 := by
  unfold tailWord_5714459
  simp only [CollatzResearch.WordTrace]
  refine ⟨208423442404498469742810431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138948961602998979828540287 208423442404498469742810431)
  ·
    refine ⟨312635163606747704614215647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208423442404498469742810431 312635163606747704614215647)
    ·
      refine ⟨468952745410121556921323471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312635163606747704614215647 468952745410121556921323471)
      ·
        refine ⟨703429118115182335381985207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468952745410121556921323471 703429118115182335381985207)
        ·
          refine ⟨1055143677172773503072977811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703429118115182335381985207 1055143677172773503072977811)
          ·
            refine ⟨1582715515759160254609466717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055143677172773503072977811 1582715515759160254609466717)
            ·
              refine ⟨593518318409685095478550019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1582715515759160254609466717 593518318409685095478550019)
              ·
                refine ⟨890277477614527643217825029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593518318409685095478550019 890277477614527643217825029)
                ·
                  refine ⟨166927027052723933103342193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890277477614527643217825029 166927027052723933103342193)
                  ·
                    refine ⟨125195270289542949827506645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166927027052723933103342193 125195270289542949827506645)
                    ·
                      refine ⟨2934264147411162886582187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125195270289542949827506645 2934264147411162886582187)
                      ·
                        rfl

theorem cell23_5714459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_5714459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714459 prefixEnd_5714459 := by exact prefixLift 5714459
  have htrace : WordTrace (prefixWord ++ tailWord_5714459) baseStart_5714459 baseEnd_5714459 := by
    simpa [prefixWord, tailWord_5714459, baseEnd_5714459] using wordTrace_append hprefix tailTrace_5714459
  have hstable : (prefixWord ++ tailWord_5714459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714459).length < 2 ^ (prefixWord ++ tailWord_5714459).sum := by decide
  have hdescent : baseEnd_5714459 < baseStart_5714459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714460 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_5714460 : Nat := 118140960795 + 5714460 * 2 ^ 59
def prefixEnd_5714460 : Nat := 4983230072969 + 3 ^ 40 * 5714460 * 2
def baseEnd_5714460 : Nat := 2934264660891817382669683

theorem tailTrace_5714460 : CollatzResearch.WordTrace tailWord_5714460 prefixEnd_5714460 2934264660891817382669683 := by
  unfold tailWord_5714460
  simp only [CollatzResearch.WordTrace]
  refine ⟨104211739438747423456798417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138948985918329897942397889 104211739438747423456798417)
  ·
    refine ⟨78158804579060567592598813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104211739438747423456798417 78158804579060567592598813)
    ·
      refine ⟨29309551717147712847224555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78158804579060567592598813 29309551717147712847224555)
      ·
        refine ⟨43964327575721569270836833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29309551717147712847224555 43964327575721569270836833)
        ·
          refine ⟨32973245681791176953127625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43964327575721569270836833 32973245681791176953127625)
          ·
            refine ⟨24729934261343382714845719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32973245681791176953127625 24729934261343382714845719)
            ·
              refine ⟨37094901392015074072268579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24729934261343382714845719 37094901392015074072268579)
              ·
                refine ⟨55642352088022611108402869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37094901392015074072268579 55642352088022611108402869)
                ·
                  refine ⟨5216470508252119791412769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55642352088022611108402869 5216470508252119791412769)
                  ·
                    refine ⟨3912352881189089843559577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5216470508252119791412769 3912352881189089843559577)
                    ·
                      refine ⟨2934264660891817382669683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912352881189089843559577 2934264660891817382669683)
                      ·
                        rfl

theorem cell23_5714460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_5714460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714460 prefixEnd_5714460 := by exact prefixLift 5714460
  have htrace : WordTrace (prefixWord ++ tailWord_5714460) baseStart_5714460 baseEnd_5714460 := by
    simpa [prefixWord, tailWord_5714460, baseEnd_5714460] using wordTrace_append hprefix tailTrace_5714460
  have hstable : (prefixWord ++ tailWord_5714460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714460).length < 2 ^ (prefixWord ++ tailWord_5714460).sum := by decide
  have hdescent : baseEnd_5714460 < baseStart_5714460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714463 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 1, 2, 3]
def baseStart_5714463 : Nat := 118140960795 + 5714463 * 2 ^ 59
def prefixEnd_5714463 : Nat := 4983230072969 + 3 ^ 40 * 5714463 * 2
def baseEnd_5714463 : Nat := 2934266201333780870932169

theorem tailTrace_5714463 : CollatzResearch.WordTrace tailWord_5714463 prefixEnd_5714463 2934266201333780870932169 := by
  unfold tailWord_5714463
  simp only [CollatzResearch.WordTrace]
  refine ⟨208423588296483978425956043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138949058864322652283970695 208423588296483978425956043)
  ·
    refine ⟨312635382444725967638934065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208423588296483978425956043 312635382444725967638934065)
    ·
      refine ⟨234476536833544475729200549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312635382444725967638934065 234476536833544475729200549)
      ·
        refine ⟨43964350656289589199225103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234476536833544475729200549 43964350656289589199225103)
        ·
          refine ⟨65946525984434383798837655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43964350656289589199225103 65946525984434383798837655)
          ·
            refine ⟨98919788976651575698256483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65946525984434383798837655 98919788976651575698256483)
            ·
              refine ⟨148379683464977363547384725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98919788976651575698256483 148379683464977363547384725)
              ·
                refine ⟨6955297662420813916283659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148379683464977363547384725 6955297662420813916283659)
                ·
                  refine ⟨10432946493631220874425489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955297662420813916283659 10432946493631220874425489)
                  ·
                    refine ⟨7824709870223415655819117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10432946493631220874425489 7824709870223415655819117)
                    ·
                      refine ⟨2934266201333780870932169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7824709870223415655819117 2934266201333780870932169)
                      ·
                        rfl

theorem cell23_5714463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_5714463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714463 prefixEnd_5714463 := by exact prefixLift 5714463
  have htrace : WordTrace (prefixWord ++ tailWord_5714463) baseStart_5714463 baseEnd_5714463 := by
    simpa [prefixWord, tailWord_5714463, baseEnd_5714463] using wordTrace_append hprefix tailTrace_5714463
  have hstable : (prefixWord ++ tailWord_5714463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714463).length < 2 ^ (prefixWord ++ tailWord_5714463).sum := by decide
  have hdescent : baseEnd_5714463 < baseStart_5714463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714464 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5714464 : Nat := 118140960795 + 5714464 * 2 ^ 59
def prefixEnd_5714464 : Nat := 4983230072969 + 3 ^ 40 * 5714464 * 2
def baseEnd_5714464 : Nat := 2934266714814435367019665

theorem tailTrace_5714464 : CollatzResearch.WordTrace tailWord_5714464 prefixEnd_5714464 2934266714814435367019665 := by
  unfold tailWord_5714464
  simp only [CollatzResearch.WordTrace]
  refine ⟨104211812384740177798371223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138949083179653570397828297 104211812384740177798371223)
  ·
    refine ⟨156317718577110266697556835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104211812384740177798371223 156317718577110266697556835)
    ·
      refine ⟨234476577865665400046335253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156317718577110266697556835 234476577865665400046335253)
      ·
        refine ⟨10991089587453065627171965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234476577865665400046335253 10991089587453065627171965)
        ·
          refine ⟨4121658595294899610189487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10991089587453065627171965 4121658595294899610189487)
          ·
            refine ⟨6182487892942349415284231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121658595294899610189487 6182487892942349415284231)
            ·
              refine ⟨9273731839413524122926347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6182487892942349415284231 9273731839413524122926347)
              ·
                refine ⟨13910597759120286184389521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9273731839413524122926347 13910597759120286184389521)
                ·
                  refine ⟨10432948319340214638292141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13910597759120286184389521 10432948319340214638292141)
                  ·
                    refine ⟨3912355619752580489359553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10432948319340214638292141 3912355619752580489359553)
                    ·
                      refine ⟨2934266714814435367019665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912355619752580489359553 2934266714814435367019665)
                      ·
                        rfl

theorem cell23_5714464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5714464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714464 prefixEnd_5714464 := by exact prefixLift 5714464
  have htrace : WordTrace (prefixWord ++ tailWord_5714464) baseStart_5714464 baseEnd_5714464 := by
    simpa [prefixWord, tailWord_5714464, baseEnd_5714464] using wordTrace_append hprefix tailTrace_5714464
  have hstable : (prefixWord ++ tailWord_5714464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714464).length < 2 ^ (prefixWord ++ tailWord_5714464).sum := by decide
  have hdescent : baseEnd_5714464 < baseStart_5714464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714471 : List Nat := [1, 1, 7, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5714471 : Nat := 118140960795 + 5714471 * 2 ^ 59
def prefixEnd_5714471 : Nat := 4983230072969 + 3 ^ 40 * 5714471 * 2
def baseEnd_5714471 : Nat := 2934270309179016839632133

theorem tailTrace_5714471 : CollatzResearch.WordTrace tailWord_5714471 prefixEnd_5714471 2934270309179016839632133 := by
  unfold tailWord_5714471
  simp only [CollatzResearch.WordTrace]
  refine ⟨208423880080454995792247267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138949253386969997194831511 208423880080454995792247267)
  ·
    refine ⟨312635820120682493688370901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208423880080454995792247267 312635820120682493688370901)
    ·
      refine ⟨7327402034078495945821193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 312635820120682493688370901 7327402034078495945821193)
      ·
        refine ⟨5495551525558871959365895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7327402034078495945821193 5495551525558871959365895)
        ·
          refine ⟨8243327288338307939048843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5495551525558871959365895 8243327288338307939048843)
          ·
            refine ⟨12364990932507461908573265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8243327288338307939048843 12364990932507461908573265)
            ·
              refine ⟨9273743199380596431429949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12364990932507461908573265 9273743199380596431429949)
              ·
                refine ⟨3477653699767723661786231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9273743199380596431429949 3477653699767723661786231)
                ·
                  refine ⟨5216480549651585492679347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477653699767723661786231 5216480549651585492679347)
                  ·
                    refine ⟨7824720824477378239019021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5216480549651585492679347 7824720824477378239019021)
                    ·
                      refine ⟨2934270309179016839632133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7824720824477378239019021 2934270309179016839632133)
                      ·
                        rfl

theorem cell23_5714471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5714471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714471 prefixEnd_5714471 := by exact prefixLift 5714471
  have htrace : WordTrace (prefixWord ++ tailWord_5714471) baseStart_5714471 baseEnd_5714471 := by
    simpa [prefixWord, tailWord_5714471, baseEnd_5714471] using wordTrace_append hprefix tailTrace_5714471
  have hstable : (prefixWord ++ tailWord_5714471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714471).length < 2 ^ (prefixWord ++ tailWord_5714471).sum := by decide
  have hdescent : baseEnd_5714471 < baseStart_5714471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714480 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 1, 2, 3]
def baseStart_5714480 : Nat := 118140960795 + 5714480 * 2 ^ 59
def prefixEnd_5714480 : Nat := 4983230072969 + 3 ^ 40 * 5714480 * 2
def baseEnd_5714480 : Nat := 2934274930504907304419591

theorem tailTrace_5714480 : CollatzResearch.WordTrace tailWord_5714480 prefixEnd_5714480 2934274930504907304419591 := by
  unfold tailWord_5714480
  simp only [CollatzResearch.WordTrace]
  refine ⟨104212104168711195164662447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138949472224948260219549929 104212104168711195164662447)
  ·
    refine ⟨156318156253066792746993671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104212104168711195164662447 156318156253066792746993671)
    ·
      refine ⟨234477234379600189120490507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156318156253066792746993671 234477234379600189120490507)
      ·
        refine ⟨351715851569400283680735761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234477234379600189120490507 351715851569400283680735761)
        ·
          refine ⟨263786888677050212760551821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351715851569400283680735761 263786888677050212760551821)
          ·
            refine ⟨98920083253893829785206933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263786888677050212760551821 98920083253893829785206933)
            ·
              refine ⟨4636878902526273271181575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98920083253893829785206933 4636878902526273271181575)
              ·
                refine ⟨6955318353789409906772363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4636878902526273271181575 6955318353789409906772363)
                ·
                  refine ⟨10432977530684114860158545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955318353789409906772363 10432977530684114860158545)
                  ·
                    refine ⟨7824733148013086145118909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10432977530684114860158545 7824733148013086145118909)
                    ·
                      refine ⟨2934274930504907304419591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7824733148013086145118909 2934274930504907304419591)
                      ·
                        rfl

theorem cell23_5714480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 2, 3].length) (baseStart_5714480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714480 prefixEnd_5714480 := by exact prefixLift 5714480
  have htrace : WordTrace (prefixWord ++ tailWord_5714480) baseStart_5714480 baseEnd_5714480 := by
    simpa [prefixWord, tailWord_5714480, baseEnd_5714480] using wordTrace_append hprefix tailTrace_5714480
  have hstable : (prefixWord ++ tailWord_5714480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714480).length < 2 ^ (prefixWord ++ tailWord_5714480).sum := by decide
  have hdescent : baseEnd_5714480 < baseStart_5714480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714510 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_5714510 : Nat := 118140960795 + 5714510 * 2 ^ 59
def prefixEnd_5714510 : Nat := 4983230072969 + 3 ^ 40 * 5714510 * 2
def baseEnd_5714510 : Nat := 2934290334924542187044453

theorem tailTrace_5714510 : CollatzResearch.WordTrace tailWord_5714510 prefixEnd_5714510 2934290334924542187044453 := by
  unfold tailWord_5714510
  simp only [CollatzResearch.WordTrace]
  refine ⟨26053162815914213181614623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138950201684875803635277989 26053162815914213181614623)
  ·
    refine ⟨39079744223871319772421935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26053162815914213181614623 39079744223871319772421935)
    ·
      refine ⟨58619616335806979658632903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39079744223871319772421935 58619616335806979658632903)
      ·
        refine ⟨87929424503710469487949355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58619616335806979658632903 87929424503710469487949355)
        ·
          refine ⟨131894136755565704231924033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87929424503710469487949355 131894136755565704231924033)
          ·
            refine ⟨98920602566674278173943025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131894136755565704231924033 98920602566674278173943025)
            ·
              refine ⟨74190451925005708630457269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98920602566674278173943025 74190451925005708630457269)
              ·
                refine ⟨6955354867969285184105369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74190451925005708630457269 6955354867969285184105369)
                ·
                  refine ⟨5216516150976963888079027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6955354867969285184105369 5216516150976963888079027)
                  ·
                    refine ⟨7824774226465445832118541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5216516150976963888079027 7824774226465445832118541)
                    ·
                      refine ⟨2934290334924542187044453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7824774226465445832118541 2934290334924542187044453)
                      ·
                        rfl

theorem cell23_5714510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_5714510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714510 prefixEnd_5714510 := by exact prefixLift 5714510
  have htrace : WordTrace (prefixWord ++ tailWord_5714510) baseStart_5714510 baseEnd_5714510 := by
    simpa [prefixWord, tailWord_5714510, baseEnd_5714510] using wordTrace_append hprefix tailTrace_5714510
  have hstable : (prefixWord ++ tailWord_5714510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714510).length < 2 ^ (prefixWord ++ tailWord_5714510).sum := by decide
  have hdescent : baseEnd_5714510 < baseStart_5714510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714520 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 1, 3, 2]
def baseStart_5714520 : Nat := 118140960795 + 5714520 * 2 ^ 59
def prefixEnd_5714520 : Nat := 4983230072969 + 3 ^ 40 * 5714520 * 2
def baseEnd_5714520 : Nat := 2934295469731087147919407

theorem tailTrace_5714520 : CollatzResearch.WordTrace tailWord_5714520 prefixEnd_5714520 2934295469731087147919407 := by
  unfold tailWord_5714520
  simp only [CollatzResearch.WordTrace]
  refine ⟨104212833628638738580390507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138950444838184984773854009 104212833628638738580390507)
  ·
    refine ⟨156319250442958107870585761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104212833628638738580390507 156319250442958107870585761)
    ·
      refine ⟨117239437832218580902939321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156319250442958107870585761 117239437832218580902939321)
      ·
        refine ⟨87929578374163935677204491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117239437832218580902939321 87929578374163935677204491)
        ·
          refine ⟨131894367561245903515806737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87929578374163935677204491 131894367561245903515806737)
          ·
            refine ⟨98920775670934427636855053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131894367561245903515806737 98920775670934427636855053)
            ·
              refine ⟨37095290876600410363820645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98920775670934427636855053 37095290876600410363820645)
              ·
                refine ⟨6955367039362576943216371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37095290876600410363820645 6955367039362576943216371)
                ·
                  refine ⟨10433050559043865414824557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955367039362576943216371 10433050559043865414824557)
                  ·
                    refine ⟨3912393959641449530559209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10433050559043865414824557 3912393959641449530559209)
                    ·
                      refine ⟨2934295469731087147919407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912393959641449530559209 2934295469731087147919407)
                      ·
                        rfl

theorem cell23_5714520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_5714520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714520 prefixEnd_5714520 := by exact prefixLift 5714520
  have htrace : WordTrace (prefixWord ++ tailWord_5714520) baseStart_5714520 baseEnd_5714520 := by
    simpa [prefixWord, tailWord_5714520, baseEnd_5714520] using wordTrace_append hprefix tailTrace_5714520
  have hstable : (prefixWord ++ tailWord_5714520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714520).length < 2 ^ (prefixWord ++ tailWord_5714520).sum := by decide
  have hdescent : baseEnd_5714520 < baseStart_5714520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714567 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 2, 2, 2]
def baseStart_5714567 : Nat := 118140960795 + 5714567 * 2 ^ 59
def prefixEnd_5714567 : Nat := 4983230072969 + 3 ^ 40 * 5714567 * 2
def baseEnd_5714567 : Nat := 2934319603321848464031691

theorem tailTrace_5714567 : CollatzResearch.WordTrace tailWord_5714567 prefixEnd_5714567 2934319603321848464031691 := by
  unfold tailWord_5714567
  simp only [CollatzResearch.WordTrace]
  refine ⟨208427381488107204187741955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138951587658738136125161303 208427381488107204187741955)
  ·
    refine ⟨312641072232160806281612933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208427381488107204187741955 312641072232160806281612933)
    ·
      refine ⟨58620201043530151177802425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312641072232160806281612933 58620201043530151177802425)
      ·
        refine ⟨43965150782647613383351819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58620201043530151177802425 43965150782647613383351819)
        ·
          refine ⟨65947726173971420075027729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43965150782647613383351819 65947726173971420075027729)
          ·
            refine ⟨49460794630478565056270797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65947726173971420075027729 49460794630478565056270797)
            ·
              refine ⟨18547797986429461896101549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49460794630478565056270797 18547797986429461896101549)
              ·
                refine ⟨6955424244911048211038081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18547797986429461896101549 6955424244911048211038081)
                ·
                  refine ⟨5216568183683286158278561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6955424244911048211038081 5216568183683286158278561)
                  ·
                    refine ⟨3912426137762464618708921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5216568183683286158278561 3912426137762464618708921)
                    ·
                      refine ⟨2934319603321848464031691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912426137762464618708921 2934319603321848464031691)
                      ·
                        rfl

theorem cell23_5714567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_5714567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714567 prefixEnd_5714567 := by exact prefixLift 5714567
  have htrace : WordTrace (prefixWord ++ tailWord_5714567) baseStart_5714567 baseEnd_5714567 := by
    simpa [prefixWord, tailWord_5714567, baseEnd_5714567] using wordTrace_append hprefix tailTrace_5714567
  have hstable : (prefixWord ++ tailWord_5714567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714567).length < 2 ^ (prefixWord ++ tailWord_5714567).sum := by decide
  have hdescent : baseEnd_5714567 < baseStart_5714567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714607 : List Nat := [1, 1, 2, 1, 2, 7, 2, 2, 5]
def baseStart_5714607 : Nat := 118140960795 + 5714607 * 2 ^ 59
def prefixEnd_5714607 : Nat := 4983230072969 + 3 ^ 40 * 5714607 * 2
def baseEnd_5714607 : Nat := 326037793616447589725723

theorem tailTrace_5714607 : CollatzResearch.WordTrace tailWord_5714607 prefixEnd_5714607 326037793616447589725723 := by
  unfold tailWord_5714607
  simp only [CollatzResearch.WordTrace]
  refine ⟨208428840407962291019198075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138952560271974860679465383 208428840407962291019198075)
  ·
    refine ⟨312643260611943436528797113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208428840407962291019198075 312643260611943436528797113)
    ·
      refine ⟨234482445458957577396597835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312643260611943436528797113 234482445458957577396597835)
      ·
        refine ⟨351723668188436366094896753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234482445458957577396597835 351723668188436366094896753)
        ·
          refine ⟨263792751141327274571172565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351723668188436366094896753 263792751141327274571172565)
          ·
            refine ⟨6182642604874857997761857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 263792751141327274571172565 6182642604874857997761857)
            ·
              refine ⟨4636981953656143498321393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6182642604874857997761857 4636981953656143498321393)
              ·
                refine ⟨3477736465242107623741045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4636981953656143498321393 3477736465242107623741045)
                ·
                  refine ⟨326037793616447589725723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3477736465242107623741045 326037793616447589725723)
                  ·
                    rfl

theorem cell23_5714607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 5].length) (baseStart_5714607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714607 prefixEnd_5714607 := by exact prefixLift 5714607
  have htrace : WordTrace (prefixWord ++ tailWord_5714607) baseStart_5714607 baseEnd_5714607 := by
    simpa [prefixWord, tailWord_5714607, baseEnd_5714607] using wordTrace_append hprefix tailTrace_5714607
  have hstable : (prefixWord ++ tailWord_5714607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714607).length < 2 ^ (prefixWord ++ tailWord_5714607).sum := by decide
  have hdescent : baseEnd_5714607 < baseStart_5714607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714616 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 4, 8]
def baseStart_5714616 : Nat := 118140960795 + 5714616 * 2 ^ 59
def prefixEnd_5714616 : Nat := 4983230072969 + 3 ^ 40 * 5714616 * 2
def baseEnd_5714616 : Nat := 978114921291306257439655

theorem tailTrace_5714616 : CollatzResearch.WordTrace tailWord_5714616 prefixEnd_5714616 978114921291306257439655 := by
  unfold tailWord_5714616
  simp only [CollatzResearch.WordTrace]
  refine ⟨104214584332464842778137851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138952779109953123704183801 104214584332464842778137851)
  ·
    refine ⟨156321876498697264167206777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104214584332464842778137851 156321876498697264167206777)
    ·
      refine ⟨117241407374022948125405083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156321876498697264167206777 117241407374022948125405083)
      ·
        refine ⟨175862111061034422188107625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117241407374022948125405083 175862111061034422188107625)
        ·
          refine ⟨131896583295775816641080719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175862111061034422188107625 131896583295775816641080719)
          ·
            refine ⟨197844874943663724961621079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131896583295775816641080719 197844874943663724961621079)
            ·
              refine ⟨296767312415495587442431619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197844874943663724961621079 296767312415495587442431619)
              ·
                refine ⟨445150968623243381163647429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296767312415495587442431619 445150968623243381163647429)
                ·
                  refine ⟨83465806616858133968183893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 445150968623243381163647429 83465806616858133968183893)
                  ·
                    refine ⟨978114921291306257439655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83465806616858133968183893 978114921291306257439655)
                    ·
                      rfl

theorem cell23_5714616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_5714616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714616 prefixEnd_5714616 := by exact prefixLift 5714616
  have htrace : WordTrace (prefixWord ++ tailWord_5714616) baseStart_5714616 baseEnd_5714616 := by
    simpa [prefixWord, tailWord_5714616, baseEnd_5714616] using wordTrace_append hprefix tailTrace_5714616
  have hstable : (prefixWord ++ tailWord_5714616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714616).length < 2 ^ (prefixWord ++ tailWord_5714616).sum := by decide
  have hdescent : baseEnd_5714616 < baseStart_5714616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714637 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_5714637 : Nat := 118140960795 + 5714637 * 2 ^ 59
def prefixEnd_5714637 : Nat := 4983230072969 + 3 ^ 40 * 5714637 * 2
def baseEnd_5714637 : Nat := 978118515655887730052123

theorem tailTrace_5714637 : CollatzResearch.WordTrace tailWord_5714637 prefixEnd_5714637 978118515655887730052123 := by
  unfold tailWord_5714637
  simp only [CollatzResearch.WordTrace]
  refine ⟨208429934597853606142790165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138953289731902404095193443 208429934597853606142790165)
  ·
    refine ⟨9770153184274387787943289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 208429934597853606142790165 9770153184274387787943289)
    ·
      refine ⟨7327614888205790840957467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9770153184274387787943289 7327614888205790840957467)
      ·
        refine ⟨10991422332308686261436201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7327614888205790840957467 10991422332308686261436201)
        ·
          refine ⟨8243566749231514696077151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10991422332308686261436201 8243566749231514696077151)
          ·
            refine ⟨12365350123847272044115727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8243566749231514696077151 12365350123847272044115727)
            ·
              refine ⟨18548025185770908066173591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12365350123847272044115727 18548025185770908066173591)
              ·
                refine ⟨27822037778656362099260387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18548025185770908066173591 27822037778656362099260387)
                ·
                  refine ⟨41733056667984543148890581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27822037778656362099260387 41733056667984543148890581)
                  ·
                    refine ⟨978118515655887730052123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41733056667984543148890581 978118515655887730052123)
                    ·
                      rfl

theorem cell23_5714637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_5714637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714637 prefixEnd_5714637 := by exact prefixLift 5714637
  have htrace : WordTrace (prefixWord ++ tailWord_5714637) baseStart_5714637 baseEnd_5714637 := by
    simpa [prefixWord, tailWord_5714637, baseEnd_5714637] using wordTrace_append hprefix tailTrace_5714637
  have hstable : (prefixWord ++ tailWord_5714637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714637).length < 2 ^ (prefixWord ++ tailWord_5714637).sum := by decide
  have hdescent : baseEnd_5714637 < baseStart_5714637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714680 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 6]
def baseStart_5714680 : Nat := 118140960795 + 5714680 * 2 ^ 59
def prefixEnd_5714680 : Nat := 4983230072969 + 3 ^ 40 * 5714680 * 2
def baseEnd_5714680 : Nat := 326041958515089613546519

theorem tailTrace_5714680 : CollatzResearch.WordTrace tailWord_5714680 prefixEnd_5714680 326041958515089613546519 := by
  unfold tailWord_5714680
  simp only [CollatzResearch.WordTrace]
  refine ⟨104215751468348912243302747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138954335291131882991070329 104215751468348912243302747)
  ·
    refine ⟨156323627202523368364954121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104215751468348912243302747 156323627202523368364954121)
    ·
      refine ⟨117242720401892526273715591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156323627202523368364954121 117242720401892526273715591)
      ·
        refine ⟨175864080602838789410573387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117242720401892526273715591 175864080602838789410573387)
        ·
          refine ⟨263796120904258184115860081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175864080602838789410573387 263796120904258184115860081)
          ·
            refine ⟨197847090678193638086895061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263796120904258184115860081 197847090678193638086895061)
            ·
              refine ⟨4637041187770163392661603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 197847090678193638086895061 4637041187770163392661603)
              ·
                refine ⟨6955561781655245088992405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4637041187770163392661603 6955561781655245088992405)
                ·
                  refine ⟨326041958515089613546519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6955561781655245088992405 326041958515089613546519)
                  ·
                    rfl

theorem cell23_5714680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 6].length) (baseStart_5714680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714680 prefixEnd_5714680 := by exact prefixLift 5714680
  have htrace : WordTrace (prefixWord ++ tailWord_5714680) baseStart_5714680 baseEnd_5714680 := by
    simpa [prefixWord, tailWord_5714680, baseEnd_5714680] using wordTrace_append hprefix tailTrace_5714680
  have hstable : (prefixWord ++ tailWord_5714680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714680).length < 2 ^ (prefixWord ++ tailWord_5714680).sum := by decide
  have hdescent : baseEnd_5714680 < baseStart_5714680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714693 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_5714693 : Nat := 118140960795 + 5714693 * 2 ^ 59
def prefixEnd_5714693 : Nat := 4983230072969 + 3 ^ 40 * 5714693 * 2
def baseEnd_5714693 : Nat := 978128100628104990352037

theorem tailTrace_5714693 : CollatzResearch.WordTrace tailWord_5714693 prefixEnd_5714693 978128100628104990352037 := by
  unfold tailWord_5714693
  simp only [CollatzResearch.WordTrace]
  refine ⟨208431977085650727706828733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138954651390433818471219155 208431977085650727706828733)
  ·
    refine ⟨78161991407119022890060775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208431977085650727706828733 78161991407119022890060775)
    ·
      refine ⟨117242987110678534335091163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78161991407119022890060775 117242987110678534335091163)
      ·
        refine ⟨175864480666017801502636745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117242987110678534335091163 175864480666017801502636745)
        ·
          refine ⟨131898360499513351126977559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175864480666017801502636745 131898360499513351126977559)
          ·
            refine ⟨197847540749270026690466339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131898360499513351126977559 197847540749270026690466339)
            ·
              refine ⟨296771311123905040035699509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197847540749270026690466339 296771311123905040035699509)
              ·
                refine ⟨27822310417866097503346829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 296771311123905040035699509 27822310417866097503346829)
                ·
                  refine ⟨10433366406699786563755061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27822310417866097503346829 10433366406699786563755061)
                  ·
                    refine ⟨978128100628104990352037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10433366406699786563755061 978128100628104990352037)
                    ·
                      rfl

theorem cell23_5714693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_5714693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714693 prefixEnd_5714693 := by exact prefixLift 5714693
  have htrace : WordTrace (prefixWord ++ tailWord_5714693) baseStart_5714693 baseEnd_5714693 := by
    simpa [prefixWord, tailWord_5714693, baseEnd_5714693] using wordTrace_append hprefix tailTrace_5714693
  have hstable : (prefixWord ++ tailWord_5714693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714693).length < 2 ^ (prefixWord ++ tailWord_5714693).sum := by decide
  have hdescent : baseEnd_5714693 < baseStart_5714693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714743 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_5714743 : Nat := 118140960795 + 5714743 * 2 ^ 59
def prefixEnd_5714743 : Nat := 4983230072969 + 3 ^ 40 * 5714743 * 2
def baseEnd_5714743 : Nat := 2934409975917039775430881

theorem tailTrace_5714743 : CollatzResearch.WordTrace tailWord_5714743 prefixEnd_5714743 2934409975917039775430881 := by
  unfold tailWord_5714743
  simp only [CollatzResearch.WordTrace]
  refine ⟨208433800735469586246148883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138955867156979724164099255 208433800735469586246148883)
  ·
    refine ⟨312650701103204379369223325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208433800735469586246148883 312650701103204379369223325)
    ·
      refine ⟨117244012913701642263458747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312650701103204379369223325 117244012913701642263458747)
      ·
        refine ⟨175866019370552463395188121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117244012913701642263458747 175866019370552463395188121)
        ·
          refine ⟨131899514527914347546391091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175866019370552463395188121 131899514527914347546391091)
          ·
            refine ⟨197849271791871521319586637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131899514527914347546391091 197849271791871521319586637)
            ·
              refine ⟨74193476921951820494844989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197849271791871521319586637 74193476921951820494844989)
              ·
                refine ⟨27822553845731932685566871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74193476921951820494844989 27822553845731932685566871)
                ·
                  refine ⟨41733830768597899028350307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27822553845731932685566871 41733830768597899028350307)
                  ·
                    refine ⟨62600746152896848542525461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41733830768597899028350307 62600746152896848542525461)
                    ·
                      refine ⟨2934409975917039775430881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62600746152896848542525461 2934409975917039775430881)
                      ·
                        rfl

theorem cell23_5714743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_5714743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714743 prefixEnd_5714743 := by exact prefixLift 5714743
  have htrace : WordTrace (prefixWord ++ tailWord_5714743) baseStart_5714743 baseEnd_5714743 := by
    simpa [prefixWord, tailWord_5714743, baseEnd_5714743] using wordTrace_append hprefix tailTrace_5714743
  have hstable : (prefixWord ++ tailWord_5714743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714743).length < 2 ^ (prefixWord ++ tailWord_5714743).sum := by decide
  have hdescent : baseEnd_5714743 < baseStart_5714743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714760 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_5714760 : Nat := 118140960795 + 5714760 * 2 ^ 59
def prefixEnd_5714760 : Nat := 4983230072969 + 3 ^ 40 * 5714760 * 2
def baseEnd_5714760 : Nat := 2934418705088166208918303

theorem tailTrace_5714760 : CollatzResearch.WordTrace tailWord_5714760 prefixEnd_5714760 2934418705088166208918303 := by
  unfold tailWord_5714760
  simp only [CollatzResearch.WordTrace]
  refine ⟨104217210388203999074758867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138956280517605332099678489 104217210388203999074758867)
  ·
    refine ⟨156325815582305998612138301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104217210388203999074758867 156325815582305998612138301)
    ·
      refine ⟨58622180843364749479551863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156325815582305998612138301 58622180843364749479551863)
      ·
        refine ⟨87933271265047124219327795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58622180843364749479551863 87933271265047124219327795)
        ·
          refine ⟨131899906897570686328991693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87933271265047124219327795 131899906897570686328991693)
          ·
            refine ⟨49462465086589007373371885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131899906897570686328991693 49462465086589007373371885)
            ·
              refine ⟨18548424407470877765014457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49462465086589007373371885 18548424407470877765014457)
              ·
                refine ⟨13911318305603158323760843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18548424407470877765014457 13911318305603158323760843)
                ·
                  refine ⟨20866977458404737485641265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13911318305603158323760843 20866977458404737485641265)
                  ·
                    refine ⟨15650233093803553114230949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20866977458404737485641265 15650233093803553114230949)
                    ·
                      refine ⟨2934418705088166208918303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15650233093803553114230949 2934418705088166208918303)
                      ·
                        rfl

theorem cell23_5714760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_5714760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714760 prefixEnd_5714760 := by exact prefixLift 5714760
  have htrace : WordTrace (prefixWord ++ tailWord_5714760) baseStart_5714760 baseEnd_5714760 := by
    simpa [prefixWord, tailWord_5714760, baseEnd_5714760] using wordTrace_append hprefix tailTrace_5714760
  have hstable : (prefixWord ++ tailWord_5714760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714760).length < 2 ^ (prefixWord ++ tailWord_5714760).sum := by decide
  have hdescent : baseEnd_5714760 < baseStart_5714760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714764 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 1, 1, 4]
def baseStart_5714764 : Nat := 118140960795 + 5714764 * 2 ^ 59
def prefixEnd_5714764 : Nat := 4983230072969 + 3 ^ 40 * 5714764 * 2
def baseEnd_5714764 : Nat := 2934420759010784193268285

theorem tailTrace_5714764 : CollatzResearch.WordTrace tailWord_5714764 prefixEnd_5714764 2934420759010784193268285 := by
  unfold tailWord_5714764
  simp only [CollatzResearch.WordTrace]
  refine ⟨104217283334196753416331673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138956377778929004555108897 104217283334196753416331673)
  ·
    refine ⟨78162962500647565062248755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104217283334196753416331673 78162962500647565062248755)
    ·
      refine ⟨117244443750971347593373133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78162962500647565062248755 117244443750971347593373133)
      ·
        refine ⟨43966666406614255347514925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117244443750971347593373133 43966666406614255347514925)
        ·
          refine ⟨16487499902480345755318097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43966666406614255347514925 16487499902480345755318097)
          ·
            refine ⟨12365624926860259316488573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16487499902480345755318097 12365624926860259316488573)
            ·
              refine ⟨4637109347572597243683215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12365624926860259316488573 4637109347572597243683215)
              ·
                refine ⟨6955664021358895865524823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4637109347572597243683215 6955664021358895865524823)
                ·
                  refine ⟨10433496032038343798287235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955664021358895865524823 10433496032038343798287235)
                  ·
                    refine ⟨15650244048057515697430853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10433496032038343798287235 15650244048057515697430853)
                    ·
                      refine ⟨2934420759010784193268285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15650244048057515697430853 2934420759010784193268285)
                      ·
                        rfl

theorem cell23_5714764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_5714764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714764 prefixEnd_5714764 := by exact prefixLift 5714764
  have htrace : WordTrace (prefixWord ++ tailWord_5714764) baseStart_5714764 baseEnd_5714764 := by
    simpa [prefixWord, tailWord_5714764, baseEnd_5714764] using wordTrace_append hprefix tailTrace_5714764
  have hstable : (prefixWord ++ tailWord_5714764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714764).length < 2 ^ (prefixWord ++ tailWord_5714764).sum := by decide
  have hdescent : baseEnd_5714764 < baseStart_5714764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714783 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 1, 9]
def baseStart_5714783 : Nat := 118140960795 + 5714783 * 2 ^ 59
def prefixEnd_5714783 : Nat := 4983230072969 + 3 ^ 40 * 5714783 * 2
def baseEnd_5714783 : Nat := 978143505047739872976899

theorem tailTrace_5714783 : CollatzResearch.WordTrace tailWord_5714783 prefixEnd_5714783 978143505047739872976899 := by
  unfold tailWord_5714783
  simp only [CollatzResearch.WordTrace]
  refine ⟨208435259655324673077605003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138956839770216448718403335 208435259655324673077605003)
  ·
    refine ⟨312652889482987009616407505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208435259655324673077605003 312652889482987009616407505)
    ·
      refine ⟨234489667112240257212305629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312652889482987009616407505 234489667112240257212305629)
      ·
        refine ⟨87933625167090096454614611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234489667112240257212305629 87933625167090096454614611)
        ·
          refine ⟨131900437750635144681921917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87933625167090096454614611 131900437750635144681921917)
          ·
            refine ⟨49462664156488179255720719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131900437750635144681921917 49462664156488179255720719)
            ·
              refine ⟨74193996234732268883581079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49462664156488179255720719 74193996234732268883581079)
              ·
                refine ⟨111290994352098403325371619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74193996234732268883581079 111290994352098403325371619)
                ·
                  refine ⟨166936491528147604988057429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111290994352098403325371619 166936491528147604988057429)
                  ·
                    refine ⟨978143505047739872976899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 166936491528147604988057429 978143505047739872976899)
                    ·
                      rfl

theorem cell23_5714783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_5714783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714783 prefixEnd_5714783 := by exact prefixLift 5714783
  have htrace : WordTrace (prefixWord ++ tailWord_5714783) baseStart_5714783 baseEnd_5714783 := by
    simpa [prefixWord, tailWord_5714783, baseEnd_5714783] using wordTrace_append hprefix tailTrace_5714783
  have hstable : (prefixWord ++ tailWord_5714783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714783).length < 2 ^ (prefixWord ++ tailWord_5714783).sum := by decide
  have hdescent : baseEnd_5714783 < baseStart_5714783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714793 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_5714793 : Nat := 118140960795 + 5714793 * 2 ^ 59
def prefixEnd_5714793 : Nat := 4983230072969 + 3 ^ 40 * 5714793 * 2
def baseEnd_5714793 : Nat := 2934435649949764579805651

theorem tailTrace_5714793 : CollatzResearch.WordTrace tailWord_5714793 prefixEnd_5714793 2934435649949764579805651 := by
  unfold tailWord_5714793
  simp only [CollatzResearch.WordTrace]
  refine ⟨208435624385288444785469033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138957082923525629856979355 208435624385288444785469033)
  ·
    refine ⟨156326718288966333589101775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208435624385288444785469033 156326718288966333589101775)
    ·
      refine ⟨234490077433449500383652663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156326718288966333589101775 234490077433449500383652663)
      ·
        refine ⟨351735116150174250575478995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234490077433449500383652663 351735116150174250575478995)
        ·
          refine ⟨527602674225261375863218493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351735116150174250575478995 527602674225261375863218493)
          ·
            refine ⟨197851002834473015948706935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 527602674225261375863218493 197851002834473015948706935)
            ·
              refine ⟨296776504251709523923060403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197851002834473015948706935 296776504251709523923060403)
              ·
                refine ⟨445164756377564285884590605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296776504251709523923060403 445164756377564285884590605)
                ·
                  refine ⟨166936783641586607206721477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445164756377564285884590605 166936783641586607206721477)
                  ·
                    refine ⟨31300646932797488851260277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 166936783641586607206721477 31300646932797488851260277)
                    ·
                      refine ⟨2934435649949764579805651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31300646932797488851260277 2934435649949764579805651)
                      ·
                        rfl

theorem cell23_5714793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_5714793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714793 prefixEnd_5714793 := by exact prefixLift 5714793
  have htrace : WordTrace (prefixWord ++ tailWord_5714793) baseStart_5714793 baseEnd_5714793 := by
    simpa [prefixWord, tailWord_5714793, baseEnd_5714793] using wordTrace_append hprefix tailTrace_5714793
  have hstable : (prefixWord ++ tailWord_5714793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714793).length < 2 ^ (prefixWord ++ tailWord_5714793).sum := by decide
  have hdescent : baseEnd_5714793 < baseStart_5714793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714797 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_5714797 : Nat := 118140960795 + 5714797 * 2 ^ 59
def prefixEnd_5714797 : Nat := 4983230072969 + 3 ^ 40 * 5714797 * 2
def baseEnd_5714797 : Nat := 2934437703872382564155633

theorem tailTrace_5714797 : CollatzResearch.WordTrace tailWord_5714797 prefixEnd_5714797 2934437703872382564155633 := by
  unfold tailWord_5714797
  simp only [CollatzResearch.WordTrace]
  refine ⟨208435770277273953468614645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138957180184849302312409763 208435770277273953468614645)
  ·
    refine ⟨19540853463494433137682623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208435770277273953468614645 19540853463494433137682623)
    ·
      refine ⟨29311280195241649706523935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19540853463494433137682623 29311280195241649706523935)
      ·
        refine ⟨43966920292862474559785903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29311280195241649706523935 43966920292862474559785903)
        ·
          refine ⟨65950380439293711839678855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43966920292862474559785903 65950380439293711839678855)
          ·
            refine ⟨98925570658940567759518283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65950380439293711839678855 98925570658940567759518283)
            ·
              refine ⟨148388355988410851639277425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98925570658940567759518283 148388355988410851639277425)
              ·
                refine ⟨111291266991308138729458069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148388355988410851639277425 111291266991308138729458069)
                ·
                  refine ⟨5216778140217569002943347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111291266991308138729458069 5216778140217569002943347)
                  ·
                    refine ⟨7825167210326353504415021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5216778140217569002943347 7825167210326353504415021)
                    ·
                      refine ⟨2934437703872382564155633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7825167210326353504415021 2934437703872382564155633)
                      ·
                        rfl

theorem cell23_5714797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_5714797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714797 prefixEnd_5714797 := by exact prefixLift 5714797
  have htrace : WordTrace (prefixWord ++ tailWord_5714797) baseStart_5714797 baseEnd_5714797 := by
    simpa [prefixWord, tailWord_5714797, baseEnd_5714797] using wordTrace_append hprefix tailTrace_5714797
  have hstable : (prefixWord ++ tailWord_5714797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714797).length < 2 ^ (prefixWord ++ tailWord_5714797).sum := by decide
  have hdescent : baseEnd_5714797 < baseStart_5714797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714818 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5714818 : Nat := 118140960795 + 5714818 * 2 ^ 59
def prefixEnd_5714818 : Nat := 4983230072969 + 3 ^ 40 * 5714818 * 2
def baseEnd_5714818 : Nat := 2934448486966126981993037

theorem tailTrace_5714818 : CollatzResearch.WordTrace tailWord_5714818 prefixEnd_5714818 2934448486966126981993037 := by
  unfold tailWord_5714818
  simp only [CollatzResearch.WordTrace]
  refine ⟨52109134052549468513782277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138957690806798582703419405 52109134052549468513782277)
  ·
    refine ⟨9770462634853025346334177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52109134052549468513782277 9770462634853025346334177)
    ·
      refine ⟨7327846976139769009750633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9770462634853025346334177 7327846976139769009750633)
      ·
        refine ⟨5495885232104826757312975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7327846976139769009750633 5495885232104826757312975)
        ·
          refine ⟨8243827848157240135969463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5495885232104826757312975 8243827848157240135969463)
          ·
            refine ⟨12365741772235860203954195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8243827848157240135969463 12365741772235860203954195)
            ·
              refine ⟨18548612658353790305931293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12365741772235860203954195 18548612658353790305931293)
              ·
                refine ⟨6955729746882671364724235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18548612658353790305931293 6955729746882671364724235)
                ·
                  refine ⟨10433594620324007047086353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955729746882671364724235 10433594620324007047086353)
                  ·
                    refine ⟨7825195965243005285314765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10433594620324007047086353 7825195965243005285314765)
                    ·
                      refine ⟨2934448486966126981993037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7825195965243005285314765 2934448486966126981993037)
                      ·
                        rfl

theorem cell23_5714818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5714818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714818 prefixEnd_5714818 := by exact prefixLift 5714818
  have htrace : WordTrace (prefixWord ++ tailWord_5714818) baseStart_5714818 baseEnd_5714818 := by
    simpa [prefixWord, tailWord_5714818, baseEnd_5714818] using wordTrace_append hprefix tailTrace_5714818
  have hstable : (prefixWord ++ tailWord_5714818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714818).length < 2 ^ (prefixWord ++ tailWord_5714818).sum := by decide
  have hdescent : baseEnd_5714818 < baseStart_5714818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714897 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 2, 5, 2]
def baseStart_5714897 : Nat := 118140960795 + 5714897 * 2 ^ 59
def prefixEnd_5714897 : Nat := 4983230072969 + 3 ^ 40 * 5714897 * 2
def baseEnd_5714897 : Nat := 2934489051937832172905173

theorem tailTrace_5714897 : CollatzResearch.WordTrace tailWord_5714897 prefixEnd_5714897 2934489051937832172905173 := by
  unfold tailWord_5714897
  simp only [CollatzResearch.WordTrace]
  refine ⟨208439417576911670547254945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138959611717941113698169963 208439417576911670547254945)
  ·
    refine ⟨156329563182683752910441209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208439417576911670547254945 156329563182683752910441209)
    ·
      refine ⟨117247172387012814682830907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156329563182683752910441209 117247172387012814682830907)
      ·
        refine ⟨175870758580519222024246361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117247172387012814682830907 175870758580519222024246361)
        ·
          refine ⟨131903068935389416518184771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175870758580519222024246361 131903068935389416518184771)
          ·
            refine ⟨197854603403084124777277157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131903068935389416518184771 197854603403084124777277157)
            ·
              refine ⟨37097738138078273395739467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197854603403084124777277157 37097738138078273395739467)
              ·
                refine ⟨55646607207117410093609201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37097738138078273395739467 55646607207117410093609201)
                ·
                  refine ⟨41734955405338057570206901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55646607207117410093609201 41734955405338057570206901)
                  ·
                    refine ⟨3912652069250442897206897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41734955405338057570206901 3912652069250442897206897)
                    ·
                      refine ⟨2934489051937832172905173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912652069250442897206897 2934489051937832172905173)
                      ·
                        rfl

theorem cell23_5714897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_5714897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714897 prefixEnd_5714897 := by exact prefixLift 5714897
  have htrace : WordTrace (prefixWord ++ tailWord_5714897) baseStart_5714897 baseEnd_5714897 := by
    simpa [prefixWord, tailWord_5714897, baseEnd_5714897] using wordTrace_append hprefix tailTrace_5714897
  have hstable : (prefixWord ++ tailWord_5714897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714897).length < 2 ^ (prefixWord ++ tailWord_5714897).sum := by decide
  have hdescent : baseEnd_5714897 < baseStart_5714897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714920 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 2, 8]
def baseStart_5714920 : Nat := 118140960795 + 5714920 * 2 ^ 59
def prefixEnd_5714920 : Nat := 4983230072969 + 3 ^ 40 * 5714920 * 2
def baseEnd_5714920 : Nat := 978166953997628527639189

theorem tailTrace_5714920 : CollatzResearch.WordTrace tailWord_5714920 prefixEnd_5714920 978166953997628527639189 := by
  unfold tailWord_5714920
  simp only [CollatzResearch.WordTrace]
  refine ⟨104220128227914172737671107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138960170970552230316894809 104220128227914172737671107)
  ·
    refine ⟨156330192341871259106506661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104220128227914172737671107 156330192341871259106506661)
    ·
      refine ⟨29311911064100861082469999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156330192341871259106506661 29311911064100861082469999)
      ·
        refine ⟨43967866596151291623704999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29311911064100861082469999 43967866596151291623704999)
        ·
          refine ⟨65951799894226937435557499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43967866596151291623704999 65951799894226937435557499)
          ·
            refine ⟨98927699841340406153336249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65951799894226937435557499 98927699841340406153336249)
            ·
              refine ⟨74195774881005304615002187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98927699841340406153336249 74195774881005304615002187)
              ·
                refine ⟨111293662321507956922503281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74195774881005304615002187 111293662321507956922503281)
                ·
                  refine ⟨83470246741130967691877461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111293662321507956922503281 83470246741130967691877461)
                  ·
                    refine ⟨978166953997628527639189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83470246741130967691877461 978166953997628527639189)
                    ·
                      rfl

theorem cell23_5714920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_5714920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714920 prefixEnd_5714920 := by exact prefixLift 5714920
  have htrace : WordTrace (prefixWord ++ tailWord_5714920) baseStart_5714920 baseEnd_5714920 := by
    simpa [prefixWord, tailWord_5714920, baseEnd_5714920] using wordTrace_append hprefix tailTrace_5714920
  have hstable : (prefixWord ++ tailWord_5714920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714920).length < 2 ^ (prefixWord ++ tailWord_5714920).sum := by decide
  have hdescent : baseEnd_5714920 < baseStart_5714920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714927 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 4]
def baseStart_5714927 : Nat := 118140960795 + 5714927 * 2 ^ 59
def prefixEnd_5714927 : Nat := 4983230072969 + 3 ^ 40 * 5714927 * 2
def baseEnd_5714927 : Nat := 2934504456357467055530035

theorem tailTrace_5714927 : CollatzResearch.WordTrace tailWord_5714927 prefixEnd_5714927 2934504456357467055530035 := by
  unfold tailWord_5714927
  simp only [CollatzResearch.WordTrace]
  refine ⟨208440511766802985670847035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138960341177868657113898023 208440511766802985670847035)
  ·
    refine ⟨312660767650204478506270553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208440511766802985670847035 312660767650204478506270553)
    ·
      refine ⟨234495575737653358879702915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312660767650204478506270553 234495575737653358879702915)
      ·
        refine ⟨351743363606480038319554373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234495575737653358879702915 351743363606480038319554373)
        ·
          refine ⟨65951880676215007184916445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 351743363606480038319554373 65951880676215007184916445)
          ·
            refine ⟨24731955253580627694343667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65951880676215007184916445 24731955253580627694343667)
            ·
              refine ⟨37097932880370941541515501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24731955253580627694343667 37097932880370941541515501)
              ·
                refine ⟨13911724830139103078068313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37097932880370941541515501 13911724830139103078068313)
                ·
                  refine ⟨10433793622604327308551235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13911724830139103078068313 10433793622604327308551235)
                  ·
                    refine ⟨15650690433906490962826853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10433793622604327308551235 15650690433906490962826853)
                    ·
                      refine ⟨2934504456357467055530035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15650690433906490962826853 2934504456357467055530035)
                      ·
                        rfl

theorem cell23_5714927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_5714927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714927 prefixEnd_5714927 := by exact prefixLift 5714927
  have htrace : WordTrace (prefixWord ++ tailWord_5714927) baseStart_5714927 baseEnd_5714927 := by
    simpa [prefixWord, tailWord_5714927, baseEnd_5714927] using wordTrace_append hprefix tailTrace_5714927
  have hstable : (prefixWord ++ tailWord_5714927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714927).length < 2 ^ (prefixWord ++ tailWord_5714927).sum := by decide
  have hdescent : baseEnd_5714927 < baseStart_5714927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5714994 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_5714994 : Nat := 118140960795 + 5714994 * 2 ^ 59
def prefixEnd_5714994 : Nat := 4983230072969 + 3 ^ 40 * 5714994 * 2
def baseEnd_5714994 : Nat := 2934538859561318293392227

theorem tailTrace_5714994 : CollatzResearch.WordTrace tailWord_5714994 prefixEnd_5714994 2934538859561318293392227 := by
  unfold tailWord_5714994
  simp only [CollatzResearch.WordTrace]
  refine ⟨52110738864390064028384009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138961970305040170742357357 52110738864390064028384009)
  ·
    refine ⟨39083054148292548021288007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52110738864390064028384009 39083054148292548021288007)
    ·
      refine ⟨58624581222438822031932011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39083054148292548021288007 58624581222438822031932011)
      ·
        refine ⟨87936871833658233047898017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58624581222438822031932011 87936871833658233047898017)
        ·
          refine ⟨65952653875243674785923513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87936871833658233047898017 65952653875243674785923513)
          ·
            refine ⟨49464490406432756089442635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65952653875243674785923513 49464490406432756089442635)
            ·
              refine ⟨74196735609649134134163953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49464490406432756089442635 74196735609649134134163953)
              ·
                refine ⟨55647551707236850600622965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74196735609649134134163953 55647551707236850600622965)
                ·
                  refine ⟨5216957972553454743808403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55647551707236850600622965 5216957972553454743808403)
                  ·
                    refine ⟨7825436958830182115712605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5216957972553454743808403 7825436958830182115712605)
                    ·
                      refine ⟨2934538859561318293392227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7825436958830182115712605 2934538859561318293392227)
                      ·
                        rfl

theorem cell23_5714994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_5714994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5714994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5714994 prefixEnd_5714994 := by exact prefixLift 5714994
  have htrace : WordTrace (prefixWord ++ tailWord_5714994) baseStart_5714994 baseEnd_5714994 := by
    simpa [prefixWord, tailWord_5714994, baseEnd_5714994] using wordTrace_append hprefix tailTrace_5714994
  have hstable : (prefixWord ++ tailWord_5714994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5714994).length < 2 ^ (prefixWord ++ tailWord_5714994).sum := by decide
  have hdescent : baseEnd_5714994 < baseStart_5714994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5714994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715011 : List Nat := [1, 1, 1, 3, 1, 2, 3, 6, 1, 1, 3]
def baseStart_5715011 : Nat := 118140960795 + 5715011 * 2 ^ 59
def prefixEnd_5715011 : Nat := 4983230072969 + 3 ^ 40 * 5715011 * 2
def baseEnd_5715011 : Nat := 2934547588732444726879649

theorem tailTrace_5715011 : CollatzResearch.WordTrace tailWord_5715011 prefixEnd_5715011 2934547588732444726879649 := by
  unfold tailWord_5715011
  simp only [CollatzResearch.WordTrace]
  refine ⟨208443575498498668016904887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138962383665665778677936591 208443575498498668016904887)
  ·
    refine ⟨312665363247748002025357331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208443575498498668016904887 312665363247748002025357331)
    ·
      refine ⟨468998044871622003038035997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312665363247748002025357331 468998044871622003038035997)
      ·
        refine ⟨175874266826858251139263499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468998044871622003038035997 175874266826858251139263499)
        ·
          refine ⟨263811400240287376708895249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175874266826858251139263499 263811400240287376708895249)
          ·
            refine ⟨197858550180215532531671437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263811400240287376708895249 197858550180215532531671437)
            ·
              refine ⟨74196956317580824699376789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197858550180215532531671437 74196956317580824699376789)
              ·
                refine ⟨3477982327386601157783287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74196956317580824699376789 3477982327386601157783287)
                ·
                  refine ⟨5216973491079901736674931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477982327386601157783287 5216973491079901736674931)
                  ·
                    refine ⟨7825460236619852605012397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5216973491079901736674931 7825460236619852605012397)
                    ·
                      refine ⟨2934547588732444726879649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7825460236619852605012397 2934547588732444726879649)
                      ·
                        rfl

theorem cell23_5715011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 1, 1, 3].length) (baseStart_5715011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715011 prefixEnd_5715011 := by exact prefixLift 5715011
  have htrace : WordTrace (prefixWord ++ tailWord_5715011) baseStart_5715011 baseEnd_5715011 := by
    simpa [prefixWord, tailWord_5715011, baseEnd_5715011] using wordTrace_append hprefix tailTrace_5715011
  have hstable : (prefixWord ++ tailWord_5715011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715011).length < 2 ^ (prefixWord ++ tailWord_5715011).sum := by decide
  have hdescent : baseEnd_5715011 < baseStart_5715011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715017 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 4]
def baseStart_5715017 : Nat := 118140960795 + 5715017 * 2 ^ 59
def prefixEnd_5715017 : Nat := 4983230072969 + 3 ^ 40 * 5715017 * 2
def baseEnd_5715017 : Nat := 2934550669616371703404621

theorem tailTrace_5715017 : CollatzResearch.WordTrace tailWord_5715017 prefixEnd_5715017 2934550669616371703404621 := by
  unfold tailWord_5715017
  simp only [CollatzResearch.WordTrace]
  refine ⟨208443794336476931041623305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138962529557651287361082203 208443794336476931041623305)
  ·
    refine ⟨156332845752357698281217479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208443794336476931041623305 156332845752357698281217479)
    ·
      refine ⟨234499268628536547421826219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156332845752357698281217479 234499268628536547421826219)
      ·
        refine ⟨351748902942804821132739329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234499268628536547421826219 351748902942804821132739329)
        ·
          refine ⟨263811677207103615849554497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351748902942804821132739329 263811677207103615849554497)
          ·
            refine ⟨197858757905327711887165873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263811677207103615849554497 197858757905327711887165873)
            ·
              refine ⟨148394068428995783915374405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197858757905327711887165873 148394068428995783915374405)
              ·
                refine ⟨27823887830436709484132701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148394068428995783915374405 27823887830436709484132701)
                ·
                  refine ⟨10433957936413766056549763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27823887830436709484132701 10433957936413766056549763)
                  ·
                    refine ⟨15650936904620649084824645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10433957936413766056549763 15650936904620649084824645)
                    ·
                      refine ⟨2934550669616371703404621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15650936904620649084824645 2934550669616371703404621)
                      ·
                        rfl

theorem cell23_5715017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_5715017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715017 prefixEnd_5715017 := by exact prefixLift 5715017
  have htrace : WordTrace (prefixWord ++ tailWord_5715017) baseStart_5715017 baseEnd_5715017 := by
    simpa [prefixWord, tailWord_5715017, baseEnd_5715017] using wordTrace_append hprefix tailTrace_5715017
  have hstable : (prefixWord ++ tailWord_5715017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715017).length < 2 ^ (prefixWord ++ tailWord_5715017).sum := by decide
  have hdescent : baseEnd_5715017 < baseStart_5715017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715021 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_5715021 : Nat := 118140960795 + 5715021 * 2 ^ 59
def prefixEnd_5715021 : Nat := 4983230072969 + 3 ^ 40 * 5715021 * 2
def baseEnd_5715021 : Nat := 2934552723538989687754603

theorem tailTrace_5715021 : CollatzResearch.WordTrace tailWord_5715021 prefixEnd_5715021 2934552723538989687754603 := by
  unfold tailWord_5715021
  simp only [CollatzResearch.WordTrace]
  refine ⟨208443940228462439724768917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138962626818974959816512611 208443940228462439724768917)
  ·
    refine ⟨9770809698209176862098543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 208443940228462439724768917 9770809698209176862098543)
    ·
      refine ⟨14656214547313765293147815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9770809698209176862098543 14656214547313765293147815)
      ·
        refine ⟨21984321820970647939721723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14656214547313765293147815 21984321820970647939721723)
        ·
          refine ⟨32976482731455971909582585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21984321820970647939721723 32976482731455971909582585)
          ·
            refine ⟨24732362048591978932186939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32976482731455971909582585 24732362048591978932186939)
            ·
              refine ⟨37098543072887968398280409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24732362048591978932186939 37098543072887968398280409)
              ·
                refine ⟨27823907304665976298710307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37098543072887968398280409 27823907304665976298710307)
                ·
                  refine ⟨41735860956998964448065461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27823907304665976298710307 41735860956998964448065461)
                  ·
                    refine ⟨3912736964718652917006137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41735860956998964448065461 3912736964718652917006137)
                    ·
                      refine ⟨2934552723538989687754603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912736964718652917006137 2934552723538989687754603)
                      ·
                        rfl

theorem cell23_5715021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_5715021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715021 prefixEnd_5715021 := by exact prefixLift 5715021
  have htrace : WordTrace (prefixWord ++ tailWord_5715021) baseStart_5715021 baseEnd_5715021 := by
    simpa [prefixWord, tailWord_5715021, baseEnd_5715021] using wordTrace_append hprefix tailTrace_5715021
  have hstable : (prefixWord ++ tailWord_5715021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715021).length < 2 ^ (prefixWord ++ tailWord_5715021).sum := by decide
  have hdescent : baseEnd_5715021 < baseStart_5715021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715027 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 6, 4]
def baseStart_5715027 : Nat := 118140960795 + 5715027 * 2 ^ 59
def prefixEnd_5715027 : Nat := 4983230072969 + 3 ^ 40 * 5715027 * 2
def baseEnd_5715027 : Nat := 978185268140972221426525

theorem tailTrace_5715027 : CollatzResearch.WordTrace tailWord_5715027 prefixEnd_5715027 978185268140972221426525 := by
  unfold tailWord_5715027
  simp only [CollatzResearch.WordTrace]
  refine ⟨208444159066440702749487335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138962772710960468499658223 208444159066440702749487335)
  ·
    refine ⟨312666238599661054124231003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208444159066440702749487335 312666238599661054124231003)
    ·
      refine ⟨468999357899491581186346505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312666238599661054124231003 468999357899491581186346505)
      ·
        refine ⟨351749518424618685889759879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468999357899491581186346505 351749518424618685889759879)
        ·
          refine ⟨527624277636928028834639819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351749518424618685889759879 527624277636928028834639819)
          ·
            refine ⟨791436416455392043251959729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527624277636928028834639819 791436416455392043251959729)
            ·
              refine ⟨593577312341544032438969797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791436416455392043251959729 593577312341544032438969797)
              ·
                refine ⟨111295746064039506082306837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 593577312341544032438969797 111295746064039506082306837)
                ·
                  refine ⟨5216988096751851847608133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111295746064039506082306837 5216988096751851847608133)
                  ·
                    refine ⟨978185268140972221426525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5216988096751851847608133 978185268140972221426525)
                    ·
                      rfl

theorem cell23_5715027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 4].length) (baseStart_5715027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715027 prefixEnd_5715027 := by exact prefixLift 5715027
  have htrace : WordTrace (prefixWord ++ tailWord_5715027) baseStart_5715027 baseEnd_5715027 := by
    simpa [prefixWord, tailWord_5715027, baseEnd_5715027] using wordTrace_append hprefix tailTrace_5715027
  have hstable : (prefixWord ++ tailWord_5715027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715027).length < 2 ^ (prefixWord ++ tailWord_5715027).sum := by decide
  have hdescent : baseEnd_5715027 < baseStart_5715027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715054 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_5715054 : Nat := 118140960795 + 5715054 * 2 ^ 59
def prefixEnd_5715054 : Nat := 4983230072969 + 3 ^ 40 * 5715054 * 2
def baseEnd_5715054 : Nat := 2934569668400588058641951

theorem tailTrace_5715054 : CollatzResearch.WordTrace tailWord_5715054 prefixEnd_5715054 2934569668400588058641951 := by
  unfold tailWord_5715054
  simp only [CollatzResearch.WordTrace]
  refine ⟨26055642979667860795090027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138963429224895257573813477 26055642979667860795090027)
  ·
    refine ⟨39083464469501791192635041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26055642979667860795090027 39083464469501791192635041)
    ·
      refine ⟨29312598352126343394476281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39083464469501791192635041 29312598352126343394476281)
      ·
        refine ⟨21984448764094757545857211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29312598352126343394476281 21984448764094757545857211)
        ·
          refine ⟨32976673146142136318785817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21984448764094757545857211 32976673146142136318785817)
          ·
            refine ⟨24732504859606602239089363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32976673146142136318785817 24732504859606602239089363)
            ·
              refine ⟨37098757289409903358634045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24732504859606602239089363 37098757289409903358634045)
              ·
                refine ⟨13912033983528713759487767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37098757289409903358634045 13912033983528713759487767)
                ·
                  refine ⟨20868050975293070639231651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13912033983528713759487767 20868050975293070639231651)
                  ·
                    refine ⟨31302076462939605958847477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20868050975293070639231651 31302076462939605958847477)
                    ·
                      refine ⟨2934569668400588058641951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31302076462939605958847477 2934569668400588058641951)
                      ·
                        rfl

theorem cell23_5715054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_5715054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715054 prefixEnd_5715054 := by exact prefixLift 5715054
  have htrace : WordTrace (prefixWord ++ tailWord_5715054) baseStart_5715054 baseEnd_5715054 := by
    simpa [prefixWord, tailWord_5715054, baseEnd_5715054] using wordTrace_append hprefix tailTrace_5715054
  have hstable : (prefixWord ++ tailWord_5715054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715054).length < 2 ^ (prefixWord ++ tailWord_5715054).sum := by decide
  have hdescent : baseEnd_5715054 < baseStart_5715054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715107 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 4]
def baseStart_5715107 : Nat := 118140960795 + 5715107 * 2 ^ 59
def prefixEnd_5715107 : Nat := 4983230072969 + 3 ^ 40 * 5715107 * 2
def baseEnd_5715107 : Nat := 2934596882875276351279207

theorem tailTrace_5715107 : CollatzResearch.WordTrace tailWord_5715107 prefixEnd_5715107 2934596882875276351279207 := by
  unfold tailWord_5715107
  simp only [CollatzResearch.WordTrace]
  refine ⟨208447076906150876412399575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138964717937433917608266383 208447076906150876412399575)
  ·
    refine ⟨312670615359226314618599363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208447076906150876412399575 312670615359226314618599363)
    ·
      refine ⟨469005923038839471927899045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312670615359226314618599363 469005923038839471927899045)
      ·
        refine ⟨87938610569782400986481071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 469005923038839471927899045 87938610569782400986481071)
        ·
          refine ⟨131907915854673601479721607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87938610569782400986481071 131907915854673601479721607)
          ·
            refine ⟨197861873782010402219582411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131907915854673601479721607 197861873782010402219582411)
            ·
              refine ⟨296792810673015603329373617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197861873782010402219582411 296792810673015603329373617)
              ·
                refine ⟨222594608004761702497030213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296792810673015603329373617 222594608004761702497030213)
                ·
                  refine ⟨41736489000892819218193165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222594608004761702497030213 41736489000892819218193165)
                  ·
                    refine ⟨15651183375334807206822437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41736489000892819218193165 15651183375334807206822437)
                    ·
                      refine ⟨2934596882875276351279207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15651183375334807206822437 2934596882875276351279207)
                      ·
                        rfl

theorem cell23_5715107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_5715107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715107 prefixEnd_5715107 := by exact prefixLift 5715107
  have htrace : WordTrace (prefixWord ++ tailWord_5715107) baseStart_5715107 baseEnd_5715107 := by
    simpa [prefixWord, tailWord_5715107, baseEnd_5715107] using wordTrace_append hprefix tailTrace_5715107
  have hstable : (prefixWord ++ tailWord_5715107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715107).length < 2 ^ (prefixWord ++ tailWord_5715107).sum := by decide
  have hdescent : baseEnd_5715107 < baseStart_5715107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715134 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_5715134 : Nat := 118140960795 + 5715134 * 2 ^ 59
def prefixEnd_5715134 : Nat := 4983230072969 + 3 ^ 40 * 5715134 * 2
def baseEnd_5715134 : Nat := 978203582284315915213861

theorem tailTrace_5715134 : CollatzResearch.WordTrace tailWord_5715134 prefixEnd_5715134 978203582284315915213861 := by
  unfold tailWord_5715134
  simp only [CollatzResearch.WordTrace]
  refine ⟨26056007709631632502954057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138965374451368706682421637 26056007709631632502954057)
  ·
    refine ⟨19542005782223724377215543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26056007709631632502954057 19542005782223724377215543)
    ·
      refine ⟨29313008673335586565823315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19542005782223724377215543 29313008673335586565823315)
      ·
        refine ⟨43969513010003379848734973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29313008673335586565823315 43969513010003379848734973)
        ·
          refine ⟨16488567378751267443275615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43969513010003379848734973 16488567378751267443275615)
          ·
            refine ⟨24732851068126901164913423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16488567378751267443275615 24732851068126901164913423)
            ·
              refine ⟨37099276602190351747370135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24732851068126901164913423 37099276602190351747370135)
              ·
                refine ⟨55648914903285527621055203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37099276602190351747370135 55648914903285527621055203)
                ·
                  refine ⟨83473372354928291431582805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55648914903285527621055203 83473372354928291431582805)
                  ·
                    refine ⟨978203582284315915213861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83473372354928291431582805 978203582284315915213861)
                    ·
                      rfl

theorem cell23_5715134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_5715134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715134 prefixEnd_5715134 := by exact prefixLift 5715134
  have htrace : WordTrace (prefixWord ++ tailWord_5715134) baseStart_5715134 baseEnd_5715134 := by
    simpa [prefixWord, tailWord_5715134, baseEnd_5715134] using wordTrace_append hprefix tailTrace_5715134
  have hstable : (prefixWord ++ tailWord_5715134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715134).length < 2 ^ (prefixWord ++ tailWord_5715134).sum := by decide
  have hdescent : baseEnd_5715134 < baseStart_5715134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715141 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 6, 2, 2]
def baseStart_5715141 : Nat := 118140960795 + 5715141 * 2 ^ 59
def prefixEnd_5715141 : Nat := 4983230072969 + 3 ^ 40 * 5715141 * 2
def baseEnd_5715141 : Nat := 2934614341217529218254051

theorem tailTrace_5715141 : CollatzResearch.WordTrace tailWord_5715141 prefixEnd_5715141 2934614341217529218254051 := by
  unfold tailWord_5715141
  simp only [CollatzResearch.WordTrace]
  refine ⟨208448316988027700219137277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138965544658685133479424851 208448316988027700219137277)
  ·
    refine ⟨78168118870510387582176479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208448316988027700219137277 78168118870510387582176479)
    ·
      refine ⟨117252178305765581373264719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78168118870510387582176479 117252178305765581373264719)
      ·
        refine ⟨175878267458648372059897079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117252178305765581373264719 175878267458648372059897079)
        ·
          refine ⟨263817401187972558089845619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175878267458648372059897079 263817401187972558089845619)
          ·
            refine ⟨395726101781958837134768429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263817401187972558089845619 395726101781958837134768429)
            ·
              refine ⟨148397288168234563925538161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395726101781958837134768429 148397288168234563925538161)
              ·
                refine ⟨111297966126175922944153621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148397288168234563925538161 111297966126175922944153621)
                ·
                  refine ⟨5217092162164496388007201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111297966126175922944153621 5217092162164496388007201)
                  ·
                    refine ⟨3912819121623372291005401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5217092162164496388007201 3912819121623372291005401)
                    ·
                      refine ⟨2934614341217529218254051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912819121623372291005401 2934614341217529218254051)
                      ·
                        rfl

theorem cell23_5715141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_5715141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715141 prefixEnd_5715141 := by exact prefixLift 5715141
  have htrace : WordTrace (prefixWord ++ tailWord_5715141) baseStart_5715141 baseEnd_5715141 := by
    simpa [prefixWord, tailWord_5715141, baseEnd_5715141] using wordTrace_append hprefix tailTrace_5715141
  have hstable : (prefixWord ++ tailWord_5715141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715141).length < 2 ^ (prefixWord ++ tailWord_5715141).sum := by decide
  have hdescent : baseEnd_5715141 < baseStart_5715141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715154 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_5715154 : Nat := 118140960795 + 5715154 * 2 ^ 59
def prefixEnd_5715154 : Nat := 4983230072969 + 3 ^ 40 * 5715154 * 2
def baseEnd_5715154 : Nat := 2934621016466037667391491

theorem tailTrace_5715154 : CollatzResearch.WordTrace tailWord_5715154 prefixEnd_5715154 2934621016466037667391491 := by
  unfold tailWord_5715154
  simp only [CollatzResearch.WordTrace]
  refine ⟨52112197784245150859840129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138965860757987068959573677 52112197784245150859840129)
  ·
    refine ⟨39084148338183863144880097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52112197784245150859840129 39084148338183863144880097)
    ·
      refine ⟨29313111253637897358660073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39084148338183863144880097 29313111253637897358660073)
      ·
        refine ⟨21984833440228423018995055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29313111253637897358660073 21984833440228423018995055)
        ·
          refine ⟨32977250160342634528492583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21984833440228423018995055 32977250160342634528492583)
          ·
            refine ⟨49465875240513951792738875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32977250160342634528492583 49465875240513951792738875)
            ·
              refine ⟨74198812860770927689108313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49465875240513951792738875 74198812860770927689108313)
              ·
                refine ⟨55649109645578195766831235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74198812860770927689108313 55649109645578195766831235)
                ·
                  refine ⟨83473664468367293650246853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55649109645578195766831235 83473664468367293650246853)
                  ·
                    refine ⟨15651312087818867559421285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83473664468367293650246853 15651312087818867559421285)
                    ·
                      refine ⟨2934621016466037667391491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15651312087818867559421285 2934621016466037667391491)
                      ·
                        rfl

theorem cell23_5715154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_5715154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715154 prefixEnd_5715154 := by exact prefixLift 5715154
  have htrace : WordTrace (prefixWord ++ tailWord_5715154) baseStart_5715154 baseEnd_5715154 := by
    simpa [prefixWord, tailWord_5715154, baseEnd_5715154] using wordTrace_append hprefix tailTrace_5715154
  have hstable : (prefixWord ++ tailWord_5715154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715154).length < 2 ^ (prefixWord ++ tailWord_5715154).sum := by decide
  have hdescent : baseEnd_5715154 < baseStart_5715154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715175 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5715175 : Nat := 118140960795 + 5715175 * 2 ^ 59
def prefixEnd_5715175 : Nat := 4983230072969 + 3 ^ 40 * 5715175 * 2
def baseEnd_5715175 : Nat := 2934631799559782085228895

theorem tailTrace_5715175 : CollatzResearch.WordTrace tailWord_5715175 prefixEnd_5715175 2934631799559782085228895 := by
  unfold tailWord_5715175
  simp only [CollatzResearch.WordTrace]
  refine ⟨208449557069904524025874979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138966371379936349350583319 208449557069904524025874979)
  ·
    refine ⟨312674335604856786038812469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208449557069904524025874979 312674335604856786038812469)
    ·
      refine ⟨29313218962955323691138669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 312674335604856786038812469 29313218962955323691138669)
      ·
        refine ⟨10992457111108246384177001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29313218962955323691138669 10992457111108246384177001)
        ·
          refine ⟨8244342833331184788132751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10992457111108246384177001 8244342833331184788132751)
          ·
            refine ⟨12366514249996777182199127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8244342833331184788132751 12366514249996777182199127)
            ·
              refine ⟨18549771374995165773298691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12366514249996777182199127 18549771374995165773298691)
              ·
                refine ⟨27824657062492748659948037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18549771374995165773298691 27824657062492748659948037)
                ·
                  refine ⟨5217123199217390373740257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27824657062492748659948037 5217123199217390373740257)
                  ·
                    refine ⟨3912842399413042780305193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5217123199217390373740257 3912842399413042780305193)
                    ·
                      refine ⟨2934631799559782085228895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3912842399413042780305193 2934631799559782085228895)
                      ·
                        rfl

theorem cell23_5715175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5715175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715175 prefixEnd_5715175 := by exact prefixLift 5715175
  have htrace : WordTrace (prefixWord ++ tailWord_5715175) baseStart_5715175 baseEnd_5715175 := by
    simpa [prefixWord, tailWord_5715175, baseEnd_5715175] using wordTrace_append hprefix tailTrace_5715175
  have hstable : (prefixWord ++ tailWord_5715175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715175).length < 2 ^ (prefixWord ++ tailWord_5715175).sum := by decide
  have hdescent : baseEnd_5715175 < baseStart_5715175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715177 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 5, 7]
def baseStart_5715177 : Nat := 118140960795 + 5715177 * 2 ^ 59
def prefixEnd_5715177 : Nat := 4983230072969 + 3 ^ 40 * 5715177 * 2
def baseEnd_5715177 : Nat := 978210942173697025801295

theorem tailTrace_5715177 : CollatzResearch.WordTrace tailWord_5715177 prefixEnd_5715177 978210942173697025801295 := by
  unfold tailWord_5715177
  simp only [CollatzResearch.WordTrace]
  refine ⟨208449630015897278367447785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138966420010598185578298523 208449630015897278367447785)
  ·
    refine ⟨156337222511922958775585839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208449630015897278367447785 156337222511922958775585839)
    ·
      refine ⟨234505833767884438163378759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156337222511922958775585839 234505833767884438163378759)
      ·
        refine ⟨351758750651826657245068139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234505833767884438163378759 351758750651826657245068139)
        ·
          refine ⟨527638125977739985867602209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351758750651826657245068139 527638125977739985867602209)
          ·
            refine ⟨395728594483304989400701657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527638125977739985867602209 395728594483304989400701657)
            ·
              refine ⟨296796445862478742050526243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395728594483304989400701657 296796445862478742050526243)
              ·
                refine ⟨445194668793718113075789365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296796445862478742050526243 445194668793718113075789365)
                ·
                  refine ⟨41737000199411073100855253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 445194668793718113075789365 41737000199411073100855253)
                  ·
                    refine ⟨978210942173697025801295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41737000199411073100855253 978210942173697025801295)
                    ·
                      rfl

theorem cell23_5715177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_5715177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715177 prefixEnd_5715177 := by exact prefixLift 5715177
  have htrace : WordTrace (prefixWord ++ tailWord_5715177) baseStart_5715177 baseEnd_5715177 := by
    simpa [prefixWord, tailWord_5715177, baseEnd_5715177] using wordTrace_append hprefix tailTrace_5715177
  have hstable : (prefixWord ++ tailWord_5715177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715177).length < 2 ^ (prefixWord ++ tailWord_5715177).sum := by decide
  have hdescent : baseEnd_5715177 < baseStart_5715177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715181 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 7]
def baseStart_5715181 : Nat := 118140960795 + 5715181 * 2 ^ 59
def prefixEnd_5715181 : Nat := 4983230072969 + 3 ^ 40 * 5715181 * 2
def baseEnd_5715181 : Nat := 326070542271523229083763

theorem tailTrace_5715181 : CollatzResearch.WordTrace tailWord_5715181 prefixEnd_5715181 326070542271523229083763 := by
  unfold tailWord_5715181
  simp only [CollatzResearch.WordTrace]
  refine ⟨208449775907882787050593397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138966517271921858033728931 208449775907882787050593397)
  ·
    refine ⟨19542166491364011285993131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208449775907882787050593397 19542166491364011285993131)
    ·
      refine ⟨29313249737046016928989697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19542166491364011285993131 29313249737046016928989697)
      ·
        refine ⟨21984937302784512696742273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29313249737046016928989697 21984937302784512696742273)
        ·
          refine ⟨16488702977088384522556705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21984937302784512696742273 16488702977088384522556705)
          ·
            refine ⟨12366527232816288391917529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16488702977088384522556705 12366527232816288391917529)
            ·
              refine ⟨9274895424612216293938147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12366527232816288391917529 9274895424612216293938147)
              ·
                refine ⟨13912343136918324440907221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9274895424612216293938147 13912343136918324440907221)
                ·
                  refine ⟨326070542271523229083763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13912343136918324440907221 326070542271523229083763)
                  ·
                    rfl

theorem cell23_5715181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_5715181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715181 prefixEnd_5715181 := by exact prefixLift 5715181
  have htrace : WordTrace (prefixWord ++ tailWord_5715181) baseStart_5715181 baseEnd_5715181 := by
    simpa [prefixWord, tailWord_5715181, baseEnd_5715181] using wordTrace_append hprefix tailTrace_5715181
  have hstable : (prefixWord ++ tailWord_5715181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715181).length < 2 ^ (prefixWord ++ tailWord_5715181).sum := by decide
  have hdescent : baseEnd_5715181 < baseStart_5715181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715321 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 4]
def baseStart_5715321 : Nat := 118140960795 + 5715321 * 2 ^ 59
def prefixEnd_5715321 : Nat := 4983230072969 + 3 ^ 40 * 5715321 * 2
def baseEnd_5715321 : Nat := 2934706767735338514003223

theorem tailTrace_5715321 : CollatzResearch.WordTrace tailWord_5715321 prefixEnd_5715321 2934706767735338514003223 := by
  unfold tailWord_5715321
  simp only [CollatzResearch.WordTrace]
  refine ⟨208454882127375590960689817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138969921418250393973793211 208454882127375590960689817)
  ·
    refine ⟨156341161595531693220517363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208454882127375590960689817 156341161595531693220517363)
    ·
      refine ⟨234511742393297539830776045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156341161595531693220517363 234511742393297539830776045)
      ·
        refine ⟨87941903397486577436541017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234511742393297539830776045 87941903397486577436541017)
        ·
          refine ⟨65956427548114933077405763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87941903397486577436541017 65956427548114933077405763)
          ·
            refine ⟨98934641322172399616108645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65956427548114933077405763 98934641322172399616108645)
            ·
              refine ⟨18550245247907324928020371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98934641322172399616108645 18550245247907324928020371)
              ·
                refine ⟨27825367871860987392030557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18550245247907324928020371 27825367871860987392030557)
                ·
                  refine ⟨10434512951947870272011459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27825367871860987392030557 10434512951947870272011459)
                  ·
                    refine ⟨15651769427921805408017189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10434512951947870272011459 15651769427921805408017189)
                    ·
                      refine ⟨2934706767735338514003223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15651769427921805408017189 2934706767735338514003223)
                      ·
                        rfl

theorem cell23_5715321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_5715321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715321 prefixEnd_5715321 := by exact prefixLift 5715321
  have htrace : WordTrace (prefixWord ++ tailWord_5715321) baseStart_5715321 baseEnd_5715321 := by
    simpa [prefixWord, tailWord_5715321, baseEnd_5715321] using wordTrace_append hprefix tailTrace_5715321
  have hstable : (prefixWord ++ tailWord_5715321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715321).length < 2 ^ (prefixWord ++ tailWord_5715321).sum := by decide
  have hdescent : baseEnd_5715321 < baseStart_5715321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715331 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 1, 6]
def baseStart_5715331 : Nat := 118140960795 + 5715331 * 2 ^ 59
def prefixEnd_5715331 : Nat := 4983230072969 + 3 ^ 40 * 5715331 * 2
def baseEnd_5715331 : Nat := 978237300847294491626059

theorem tailTrace_5715331 : CollatzResearch.WordTrace tailWord_5715331 prefixEnd_5715331 978237300847294491626059 := by
  unfold tailWord_5715331
  simp only [CollatzResearch.WordTrace]
  refine ⟨208455246857339362668553847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138970164571559575112369231 208455246857339362668553847)
  ·
    refine ⟨312682870286009044002830771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208455246857339362668553847 312682870286009044002830771)
    ·
      refine ⟨469024305429013566004246157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312682870286009044002830771 469024305429013566004246157)
      ·
        refine ⟨175884114535880087251592309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 469024305429013566004246157 175884114535880087251592309)
        ·
          refine ⟨16489135737738758179836779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175884114535880087251592309 16489135737738758179836779)
          ·
            refine ⟨24733703606608137269755169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16489135737738758179836779 24733703606608137269755169)
            ·
              refine ⟨18550277704956102952316377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24733703606608137269755169 18550277704956102952316377)
              ·
                refine ⟨13912708278717077214237283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18550277704956102952316377 13912708278717077214237283)
                ·
                  refine ⟨20869062418075615821355925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13912708278717077214237283 20869062418075615821355925)
                  ·
                    refine ⟨978237300847294491626059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20869062418075615821355925 978237300847294491626059)
                    ·
                      rfl

theorem cell23_5715331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 6].length) (baseStart_5715331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715331 prefixEnd_5715331 := by exact prefixLift 5715331
  have htrace : WordTrace (prefixWord ++ tailWord_5715331) baseStart_5715331 baseEnd_5715331 := by
    simpa [prefixWord, tailWord_5715331, baseEnd_5715331] using wordTrace_append hprefix tailTrace_5715331
  have hstable : (prefixWord ++ tailWord_5715331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715331).length < 2 ^ (prefixWord ++ tailWord_5715331).sum := by decide
  have hdescent : baseEnd_5715331 < baseStart_5715331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715332 : List Nat := [2, 3, 2, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_5715332 : Nat := 118140960795 + 5715332 * 2 ^ 59
def prefixEnd_5715332 : Nat := 4983230072969 + 3 ^ 40 * 5715332 * 2
def baseEnd_5715332 : Nat := 2934712416022537970965673

theorem tailTrace_5715332 : CollatzResearch.WordTrace tailWord_5715332 prefixEnd_5715332 2934712416022537970965673 := by
  unfold tailWord_5715332
  simp only [CollatzResearch.WordTrace]
  refine ⟨104227641665167869919670125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138970188886890493226226833 104227641665167869919670125)
  ·
    refine ⟨39085365624437951219876297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104227641665167869919670125 39085365624437951219876297)
    ·
      refine ⟨29314024218328463414907223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39085365624437951219876297 29314024218328463414907223)
      ·
        refine ⟨43971036327492695122360835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29314024218328463414907223 43971036327492695122360835)
        ·
          refine ⟨65956554491239042683541253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43971036327492695122360835 65956554491239042683541253)
          ·
            refine ⟨12366853967107320503163985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65956554491239042683541253 12366853967107320503163985)
            ·
              refine ⟨9275140475330490377372989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12366853967107320503163985 9275140475330490377372989)
              ·
                refine ⟨3478177678248933891514871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9275140475330490377372989 3478177678248933891514871)
                ·
                  refine ⟨5217266517373400837272307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478177678248933891514871 5217266517373400837272307)
                  ·
                    refine ⟨7825899776060101255908461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5217266517373400837272307 7825899776060101255908461)
                    ·
                      refine ⟨2934712416022537970965673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7825899776060101255908461 2934712416022537970965673)
                      ·
                        rfl

theorem cell23_5715332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_5715332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715332 prefixEnd_5715332 := by exact prefixLift 5715332
  have htrace : WordTrace (prefixWord ++ tailWord_5715332) baseStart_5715332 baseEnd_5715332 := by
    simpa [prefixWord, tailWord_5715332, baseEnd_5715332] using wordTrace_append hprefix tailTrace_5715332
  have hstable : (prefixWord ++ tailWord_5715332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715332).length < 2 ^ (prefixWord ++ tailWord_5715332).sum := by decide
  have hdescent : baseEnd_5715332 < baseStart_5715332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715335 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 1, 5]
def baseStart_5715335 : Nat := 118140960795 + 5715335 * 2 ^ 59
def prefixEnd_5715335 : Nat := 4983230072969 + 3 ^ 40 * 5715335 * 2
def baseEnd_5715335 : Nat := 978237985488167153076053

theorem tailTrace_5715335 : CollatzResearch.WordTrace tailWord_5715335 prefixEnd_5715335 978237985488167153076053 := by
  unfold tailWord_5715335
  simp only [CollatzResearch.WordTrace]
  refine ⟨208455392749324871351699459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138970261832883247567799639 208455392749324871351699459)
  ·
    refine ⟨312683089123987307027549189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208455392749324871351699459 312683089123987307027549189)
    ·
      refine ⟨58628079210747620067665473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312683089123987307027549189 58628079210747620067665473)
      ·
        refine ⟨43971059408060715050749105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58628079210747620067665473 43971059408060715050749105)
        ·
          refine ⟨32978294556045536288061829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43971059408060715050749105 32978294556045536288061829)
          ·
            refine ⟨6183430229258538054011593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32978294556045536288061829 6183430229258538054011593)
            ·
              refine ⟨4637572671943903540508695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6183430229258538054011593 4637572671943903540508695)
              ·
                refine ⟨6956359007915855310763043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4637572671943903540508695 6956359007915855310763043)
                ·
                  refine ⟨10434538511873782966144565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6956359007915855310763043 10434538511873782966144565)
                  ·
                    refine ⟨978237985488167153076053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10434538511873782966144565 978237985488167153076053)
                    ·
                      rfl

theorem cell23_5715335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_5715335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715335 prefixEnd_5715335 := by exact prefixLift 5715335
  have htrace : WordTrace (prefixWord ++ tailWord_5715335) baseStart_5715335 baseEnd_5715335 := by
    simpa [prefixWord, tailWord_5715335, baseEnd_5715335] using wordTrace_append hprefix tailTrace_5715335
  have hstable : (prefixWord ++ tailWord_5715335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715335).length < 2 ^ (prefixWord ++ tailWord_5715335).sum := by decide
  have hdescent : baseEnd_5715335 < baseStart_5715335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715428 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 5, 4, 2]
def baseStart_5715428 : Nat := 118140960795 + 5715428 * 2 ^ 59
def prefixEnd_5715428 : Nat := 4983230072969 + 3 ^ 40 * 5715428 * 2
def baseEnd_5715428 : Nat := 2934761710165369595365231

theorem tailTrace_5715428 : CollatzResearch.WordTrace tailWord_5715428 prefixEnd_5715428 2934761710165369595365231 := by
  unfold tailWord_5715428
  simp only [CollatzResearch.WordTrace]
  refine ⟨104229392368993974117417469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138972523158658632156556625 104229392368993974117417469)
  ·
    refine ⟨39086022138372740294031551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104229392368993974117417469 39086022138372740294031551)
    ·
      refine ⟨58629033207559110441047327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39086022138372740294031551 58629033207559110441047327)
      ·
        refine ⟨87943549811338665661570991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58629033207559110441047327 87943549811338665661570991)
        ·
          refine ⟨131915324717007998492356487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87943549811338665661570991 131915324717007998492356487)
          ·
            refine ⟨197872987075511997738534731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131915324717007998492356487 197872987075511997738534731)
            ·
              refine ⟨296809480613267996607802097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197872987075511997738534731 296809480613267996607802097)
              ·
                refine ⟨222607110459950997455851573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296809480613267996607802097 222607110459950997455851573)
                ·
                  refine ⟨20869416605620406011486085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222607110459950997455851573 20869416605620406011486085)
                  ·
                    refine ⟨3913015613553826127153641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20869416605620406011486085 3913015613553826127153641)
                    ·
                      refine ⟨2934761710165369595365231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913015613553826127153641 2934761710165369595365231)
                      ·
                        rfl

theorem cell23_5715428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_5715428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715428 prefixEnd_5715428 := by exact prefixLift 5715428
  have htrace : WordTrace (prefixWord ++ tailWord_5715428) baseStart_5715428 baseEnd_5715428 := by
    simpa [prefixWord, tailWord_5715428, baseEnd_5715428] using wordTrace_append hprefix tailTrace_5715428
  have hstable : (prefixWord ++ tailWord_5715428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715428).length < 2 ^ (prefixWord ++ tailWord_5715428).sum := by decide
  have hdescent : baseEnd_5715428 < baseStart_5715428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715498 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_5715498 : Nat := 118140960795 + 5715498 * 2 ^ 59
def prefixEnd_5715498 : Nat := 4983230072969 + 3 ^ 40 * 5715498 * 2
def baseEnd_5715498 : Nat := 978265884603728107163303

theorem tailTrace_5715498 : CollatzResearch.WordTrace tailWord_5715498 prefixEnd_5715498 978265884603728107163303 := by
  unfold tailWord_5715498
  simp only [CollatzResearch.WordTrace]
  refine ⟨52115334461933587547470787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138974225231822900126588765 52115334461933587547470787)
  ·
    refine ⟨78173001692900381321206181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52115334461933587547470787 78173001692900381321206181)
    ·
      refine ⟨14657437817418821497726159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78173001692900381321206181 14657437817418821497726159)
      ·
        refine ⟨21986156726128232246589239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14657437817418821497726159 21986156726128232246589239)
        ·
          refine ⟨32979235089192348369883859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21986156726128232246589239 32979235089192348369883859)
          ·
            refine ⟨49468852633788522554825789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32979235089192348369883859 49468852633788522554825789)
            ·
              refine ⟨18550819737670695958059671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49468852633788522554825789 18550819737670695958059671)
              ·
                refine ⟨27826229606506043937089507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18550819737670695958059671 27826229606506043937089507)
                ·
                  refine ⟨41739344409759065905634261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27826229606506043937089507 41739344409759065905634261)
                  ·
                    refine ⟨978265884603728107163303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41739344409759065905634261 978265884603728107163303)
                    ·
                      rfl

theorem cell23_5715498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_5715498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715498 prefixEnd_5715498 := by exact prefixLift 5715498
  have htrace : WordTrace (prefixWord ++ tailWord_5715498) baseStart_5715498 baseEnd_5715498 := by
    simpa [prefixWord, tailWord_5715498, baseEnd_5715498] using wordTrace_append hprefix tailTrace_5715498
  have hstable : (prefixWord ++ tailWord_5715498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715498).length < 2 ^ (prefixWord ++ tailWord_5715498).sum := by decide
  have hdescent : baseEnd_5715498 < baseStart_5715498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715502 : List Nat := [4, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_5715502 : Nat := 118140960795 + 5715502 * 2 ^ 59
def prefixEnd_5715502 : Nat := 4983230072969 + 3 ^ 40 * 5715502 * 2
def baseEnd_5715502 : Nat := 326088856414866922871099

theorem tailTrace_5715502 : CollatzResearch.WordTrace tailWord_5715502 prefixEnd_5715502 326088856414866922871099 := by
  unfold tailWord_5715502
  simp only [CollatzResearch.WordTrace]
  refine ⟨26057685467464982359128595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138974322493146572582019173 26057685467464982359128595)
  ·
    refine ⟨39086528201197473538692893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26057685467464982359128595 39086528201197473538692893)
    ·
      refine ⟨14657448075449052577009835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39086528201197473538692893 14657448075449052577009835)
      ·
        refine ⟨21986172113173578865514753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14657448075449052577009835 21986172113173578865514753)
        ·
          refine ⟨16489629084880184149136065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21986172113173578865514753 16489629084880184149136065)
          ·
            refine ⟨12367221813660138111852049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16489629084880184149136065 12367221813660138111852049)
            ·
              refine ⟨9275416360245103583889037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12367221813660138111852049 9275416360245103583889037)
              ·
                refine ⟨3478281135091913843958389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9275416360245103583889037 3478281135091913843958389)
                ·
                  refine ⟨326088856414866922871099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3478281135091913843958389 326088856414866922871099)
                  ·
                    rfl

theorem cell23_5715502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_5715502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715502 prefixEnd_5715502 := by exact prefixLift 5715502
  have htrace : WordTrace (prefixWord ++ tailWord_5715502) baseStart_5715502 baseEnd_5715502 := by
    simpa [prefixWord, tailWord_5715502, baseEnd_5715502] using wordTrace_append hprefix tailTrace_5715502
  have hstable : (prefixWord ++ tailWord_5715502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715502).length < 2 ^ (prefixWord ++ tailWord_5715502).sum := by decide
  have hdescent : baseEnd_5715502 < baseStart_5715502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715531 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 6]
def baseStart_5715531 : Nat := 118140960795 + 5715531 * 2 ^ 59
def prefixEnd_5715531 : Nat := 4983230072969 + 3 ^ 40 * 5715531 * 2
def baseEnd_5715531 : Nat := 2934814598672782692377257

theorem tailTrace_5715531 : CollatzResearch.WordTrace tailWord_5715531 prefixEnd_5715531 2934814598672782692377257 := by
  unfold tailWord_5715531
  simp only [CollatzResearch.WordTrace]
  refine ⟨208462541456614796825834447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138975027637743197883889631 208462541456614796825834447)
  ·
    refine ⟨312693812184922195238751671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208462541456614796825834447 312693812184922195238751671)
    ·
      refine ⟨469040718277383292858127507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312693812184922195238751671 469040718277383292858127507)
      ·
        refine ⟨703561077416074939287191261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469040718277383292858127507 703561077416074939287191261)
        ·
          refine ⟨263835404031028102232696723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 703561077416074939287191261 263835404031028102232696723)
          ·
            refine ⟨395753106046542153349045085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263835404031028102232696723 395753106046542153349045085)
            ·
              refine ⟨148407414767453307505891907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395753106046542153349045085 148407414767453307505891907)
              ·
                refine ⟨222611122151179961258837861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148407414767453307505891907 222611122151179961258837861)
                ·
                  refine ⟨41739585403346242736032099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222611122151179961258837861 41739585403346242736032099)
                  ·
                    refine ⟨62609378105019364104048149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41739585403346242736032099 62609378105019364104048149)
                    ·
                      refine ⟨2934814598672782692377257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62609378105019364104048149 2934814598672782692377257)
                      ·
                        rfl

theorem cell23_5715531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_5715531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715531 prefixEnd_5715531 := by exact prefixLift 5715531
  have htrace : WordTrace (prefixWord ++ tailWord_5715531) baseStart_5715531 baseEnd_5715531 := by
    simpa [prefixWord, tailWord_5715531, baseEnd_5715531] using wordTrace_append hprefix tailTrace_5715531
  have hstable : (prefixWord ++ tailWord_5715531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715531).length < 2 ^ (prefixWord ++ tailWord_5715531).sum := by decide
  have hdescent : baseEnd_5715531 < baseStart_5715531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715551 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_5715551 : Nat := 118140960795 + 5715551 * 2 ^ 59
def prefixEnd_5715551 : Nat := 4983230072969 + 3 ^ 40 * 5715551 * 2
def baseEnd_5715551 : Nat := 2934824868285872614127165

theorem tailTrace_5715551 : CollatzResearch.WordTrace tailWord_5715551 prefixEnd_5715551 2934824868285872614127165 := by
  unfold tailWord_5715551
  simp only [CollatzResearch.WordTrace]
  refine ⟨208463270916542340241562507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138975513944361560161041671 208463270916542340241562507)
  ·
    refine ⟨312694906374813510362343761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208463270916542340241562507 312694906374813510362343761)
    ·
      refine ⟨234521179781110132771757821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312694906374813510362343761 234521179781110132771757821)
      ·
        refine ⟨87945442417916299789409183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234521179781110132771757821 87945442417916299789409183)
        ·
          refine ⟨131918163626874449684113775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87945442417916299789409183 131918163626874449684113775)
          ·
            refine ⟨197877245440311674526170663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131918163626874449684113775 197877245440311674526170663)
            ·
              refine ⟨296815868160467511789255995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197877245440311674526170663 296815868160467511789255995)
              ·
                refine ⟨445223802240701267683883993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296815868160467511789255995 445223802240701267683883993)
                ·
                  refine ⟨333917851680525950762912995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445223802240701267683883993 333917851680525950762912995)
                  ·
                    refine ⟨500876777520788926144369493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 333917851680525950762912995 500876777520788926144369493)
                    ·
                      refine ⟨2934824868285872614127165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 500876777520788926144369493 2934824868285872614127165)
                      ·
                        rfl

theorem cell23_5715551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_5715551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715551 prefixEnd_5715551 := by exact prefixLift 5715551
  have htrace : WordTrace (prefixWord ++ tailWord_5715551) baseStart_5715551 baseEnd_5715551 := by
    simpa [prefixWord, tailWord_5715551, baseEnd_5715551] using wordTrace_append hprefix tailTrace_5715551
  have hstable : (prefixWord ++ tailWord_5715551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715551).length < 2 ^ (prefixWord ++ tailWord_5715551).sum := by decide
  have hdescent : baseEnd_5715551 < baseStart_5715551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715571 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 1, 11]
def baseStart_5715571 : Nat := 118140960795 + 5715571 * 2 ^ 59
def prefixEnd_5715571 : Nat := 4983230072969 + 3 ^ 40 * 5715571 * 2
def baseEnd_5715571 : Nat := 978278379299654178625691

theorem tailTrace_5715571 : CollatzResearch.WordTrace tailWord_5715571 prefixEnd_5715571 978278379299654178625691 := by
  unfold tailWord_5715571
  simp only [CollatzResearch.WordTrace]
  refine ⟨208464000376469883657290567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138976000250979922438193711 208464000376469883657290567)
  ·
    refine ⟨312696000564704825485935851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208464000376469883657290567 312696000564704825485935851)
    ·
      refine ⟨469044000847057238228903777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312696000564704825485935851 469044000847057238228903777)
      ·
        refine ⟨351783000635292928671677833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469044000847057238228903777 351783000635292928671677833)
        ·
          refine ⟨263837250476469696503758375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351783000635292928671677833 263837250476469696503758375)
          ·
            refine ⟨395755875714704544755637563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263837250476469696503758375 395755875714704544755637563)
            ·
              refine ⟨593633813572056817133456345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395755875714704544755637563 593633813572056817133456345)
              ·
                refine ⟨445225360179042612850092259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593633813572056817133456345 445225360179042612850092259)
                ·
                  refine ⟨667838040268563919275138389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445225360179042612850092259 667838040268563919275138389)
                  ·
                    refine ⟨978278379299654178625691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 667838040268563919275138389 978278379299654178625691)
                    ·
                      rfl

theorem cell23_5715571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 11].length) (baseStart_5715571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715571 prefixEnd_5715571 := by exact prefixLift 5715571
  have htrace : WordTrace (prefixWord ++ tailWord_5715571) baseStart_5715571 baseEnd_5715571 := by
    simpa [prefixWord, tailWord_5715571, baseEnd_5715571] using wordTrace_append hprefix tailTrace_5715571
  have hstable : (prefixWord ++ tailWord_5715571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715571).length < 2 ^ (prefixWord ++ tailWord_5715571).sum := by decide
  have hdescent : baseEnd_5715571 < baseStart_5715571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715592 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 6]
def baseStart_5715592 : Nat := 118140960795 + 5715592 * 2 ^ 59
def prefixEnd_5715592 : Nat := 4983230072969 + 3 ^ 40 * 5715592 * 2
def baseEnd_5715592 : Nat := 326093991221411883746053

theorem tailTrace_5715592 : CollatzResearch.WordTrace tailWord_5715592 prefixEnd_5715592 326093991221411883746053 := by
  unfold tailWord_5715592
  simp only [CollatzResearch.WordTrace]
  refine ⟨104232383154696902121902515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138976510872929202829203353 104232383154696902121902515)
  ·
    refine ⟨156348574732045353182853773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104232383154696902121902515 156348574732045353182853773)
    ·
      refine ⟨58630715524517007443570165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156348574732045353182853773 58630715524517007443570165)
      ·
        refine ⟨5496629580423469447834703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58630715524517007443570165 5496629580423469447834703)
        ·
          refine ⟨8244944370635204171752055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496629580423469447834703 8244944370635204171752055)
          ·
            refine ⟨12367416555952806257628083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8244944370635204171752055 12367416555952806257628083)
            ·
              refine ⟨18551124833929209386442125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12367416555952806257628083 18551124833929209386442125)
              ·
                refine ⟨6956671812723453519915797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18551124833929209386442125 6956671812723453519915797)
                ·
                  refine ⟨326093991221411883746053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6956671812723453519915797 326093991221411883746053)
                  ·
                    rfl

theorem cell23_5715592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 6].length) (baseStart_5715592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715592 prefixEnd_5715592 := by exact prefixLift 5715592
  have htrace : WordTrace (prefixWord ++ tailWord_5715592) baseStart_5715592 baseEnd_5715592 := by
    simpa [prefixWord, tailWord_5715592, baseEnd_5715592] using wordTrace_append hprefix tailTrace_5715592
  have hstable : (prefixWord ++ tailWord_5715592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715592).length < 2 ^ (prefixWord ++ tailWord_5715592).sum := by decide
  have hdescent : baseEnd_5715592 < baseStart_5715592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715595 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 4, 3, 2]
def baseStart_5715595 : Nat := 118140960795 + 5715595 * 2 ^ 59
def prefixEnd_5715595 : Nat := 4983230072969 + 3 ^ 40 * 5715595 * 2
def baseEnd_5715595 : Nat := 2934847461434670441976963

theorem tailTrace_5715595 : CollatzResearch.WordTrace tailWord_5715595 prefixEnd_5715595 2934847461434670441976963 := by
  unfold tailWord_5715595
  simp only [CollatzResearch.WordTrace]
  refine ⟨208464875728382935756164239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138976583818921957170776159 208464875728382935756164239)
  ·
    refine ⟨312697313592574403634246359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208464875728382935756164239 312697313592574403634246359)
    ·
      refine ⟨469045970388861605451369539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312697313592574403634246359 469045970388861605451369539)
      ·
        refine ⟨703568955583292408177054309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469045970388861605451369539 703568955583292408177054309)
        ·
          refine ⟨131919179171867326533197683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 703568955583292408177054309 131919179171867326533197683)
          ·
            refine ⟨197878768757800989799796525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131919179171867326533197683 197878768757800989799796525)
            ·
              refine ⟨74204538284175371174923697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197878768757800989799796525 74204538284175371174923697)
              ·
                refine ⟨55653403713131528381192773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74204538284175371174923697 55653403713131528381192773)
                ·
                  refine ⟨10435013196212161571473645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55653403713131528381192773 10435013196212161571473645)
                  ·
                    refine ⟨3913129948579560589302617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10435013196212161571473645 3913129948579560589302617)
                    ·
                      refine ⟨2934847461434670441976963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913129948579560589302617 2934847461434670441976963)
                      ·
                        rfl

theorem cell23_5715595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 3, 2].length) (baseStart_5715595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715595 prefixEnd_5715595 := by exact prefixLift 5715595
  have htrace : WordTrace (prefixWord ++ tailWord_5715595) baseStart_5715595 baseEnd_5715595 := by
    simpa [prefixWord, tailWord_5715595, baseEnd_5715595] using wordTrace_append hprefix tailTrace_5715595
  have hstable : (prefixWord ++ tailWord_5715595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715595).length < 2 ^ (prefixWord ++ tailWord_5715595).sum := by decide
  have hdescent : baseEnd_5715595 < baseStart_5715595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715630 : List Nat := [4, 1, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_5715630 : Nat := 118140960795 + 5715630 * 2 ^ 59
def prefixEnd_5715630 : Nat := 4983230072969 + 3 ^ 40 * 5715630 * 2
def baseEnd_5715630 : Nat := 978288477752525935013101

theorem tailTrace_5715630 : CollatzResearch.WordTrace tailWord_5715630 prefixEnd_5715630 978288477752525935013101 := by
  unfold tailWord_5715630
  simp only [CollatzResearch.WordTrace]
  refine ⟨26058269035407017091711043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138977434855504091155792229 26058269035407017091711043)
  ·
    refine ⟨39087403553110525637566565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26058269035407017091711043 39087403553110525637566565)
    ·
      refine ⟨7328888166208223557043731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39087403553110525637566565 7328888166208223557043731)
      ·
        refine ⟨10993332249312335335565597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7328888166208223557043731 10993332249312335335565597)
        ·
          refine ⟨4122499593492125750837099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10993332249312335335565597 4122499593492125750837099)
          ·
            refine ⟨6183749390238188626255649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122499593492125750837099 6183749390238188626255649)
            ·
              refine ⟨4637812042678641469691737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6183749390238188626255649 4637812042678641469691737)
              ·
                refine ⟨3478359032008981102268803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4637812042678641469691737 3478359032008981102268803)
                ·
                  refine ⟨5217538548013471653403205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478359032008981102268803 5217538548013471653403205)
                  ·
                    refine ⟨978288477752525935013101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5217538548013471653403205 978288477752525935013101)
                    ·
                      rfl

theorem cell23_5715630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_5715630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715630 prefixEnd_5715630 := by exact prefixLift 5715630
  have htrace : WordTrace (prefixWord ++ tailWord_5715630) baseStart_5715630 baseEnd_5715630 := by
    simpa [prefixWord, tailWord_5715630, baseEnd_5715630] using wordTrace_append hprefix tailTrace_5715630
  have hstable : (prefixWord ++ tailWord_5715630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715630).length < 2 ^ (prefixWord ++ tailWord_5715630).sum := by decide
  have hdescent : baseEnd_5715630 < baseStart_5715630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715645 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_5715645 : Nat := 118140960795 + 5715645 * 2 ^ 59
def prefixEnd_5715645 : Nat := 4983230072969 + 3 ^ 40 * 5715645 * 2
def baseEnd_5715645 : Nat := 2934873135467395246351733

theorem tailTrace_5715645 : CollatzResearch.WordTrace tailWord_5715645 prefixEnd_5715645 2934873135467395246351733 := by
  unfold tailWord_5715645
  simp only [CollatzResearch.WordTrace]
  refine ⟨208466699378201794295484389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138977799585467862863656259 208466699378201794295484389)
  ·
    refine ⟨39087506133412836430403323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208466699378201794295484389 39087506133412836430403323)
    ·
      refine ⟨58631259200119254645604985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39087506133412836430403323 58631259200119254645604985)
      ·
        refine ⟨43973444400089440984203739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58631259200119254645604985 43973444400089440984203739)
        ·
          refine ⟨65960166600134161476305609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43973444400089440984203739 65960166600134161476305609)
          ·
            refine ⟨49470124950100621107229207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65960166600134161476305609 49470124950100621107229207)
            ·
              refine ⟨74205187425150931660843811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49470124950100621107229207 74205187425150931660843811)
              ·
                refine ⟨111307781137726397491265717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74205187425150931660843811 111307781137726397491265717)
                ·
                  refine ⟨10435104481661849764806161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111307781137726397491265717 10435104481661849764806161)
                  ·
                    refine ⟨7826328361246387323604621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10435104481661849764806161 7826328361246387323604621)
                    ·
                      refine ⟨2934873135467395246351733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7826328361246387323604621 2934873135467395246351733)
                      ·
                        rfl

theorem cell23_5715645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_5715645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715645 prefixEnd_5715645 := by exact prefixLift 5715645
  have htrace : WordTrace (prefixWord ++ tailWord_5715645) baseStart_5715645 baseEnd_5715645 := by
    simpa [prefixWord, tailWord_5715645, baseEnd_5715645] using wordTrace_append hprefix tailTrace_5715645
  have hstable : (prefixWord ++ tailWord_5715645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715645).length < 2 ^ (prefixWord ++ tailWord_5715645).sum := by decide
  have hdescent : baseEnd_5715645 < baseStart_5715645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715652 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_5715652 : Nat := 118140960795 + 5715652 * 2 ^ 59
def prefixEnd_5715652 : Nat := 4983230072969 + 3 ^ 40 * 5715652 * 2
def baseEnd_5715652 : Nat := 978292243277325572988067

theorem tailTrace_5715652 : CollatzResearch.WordTrace tailWord_5715652 prefixEnd_5715652 978292243277325572988067 := by
  unfold tailWord_5715652
  simp only [CollatzResearch.WordTrace]
  refine ⟨104233477344588217245494605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138977969792784289660659473 104233477344588217245494605)
  ·
    refine ⟨39087554004220581467060477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104233477344588217245494605 39087554004220581467060477)
    ·
      refine ⟨14657832751582718050147679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39087554004220581467060477 14657832751582718050147679)
      ·
        refine ⟨21986749127374077075221519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14657832751582718050147679 21986749127374077075221519)
        ·
          refine ⟨32980123691061115612832279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21986749127374077075221519 32980123691061115612832279)
          ·
            refine ⟨49470185536591673419248419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32980123691061115612832279 49470185536591673419248419)
            ·
              refine ⟨74205278304887510128872629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49470185536591673419248419 74205278304887510128872629)
              ·
                refine ⟨6956744841083204074581809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74205278304887510128872629 6956744841083204074581809)
                ·
                  refine ⟨5217558630812403055936357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6956744841083204074581809 5217558630812403055936357)
                  ·
                    refine ⟨978292243277325572988067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5217558630812403055936357 978292243277325572988067)
                    ·
                      rfl

theorem cell23_5715652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_5715652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715652 prefixEnd_5715652 := by exact prefixLift 5715652
  have htrace : WordTrace (prefixWord ++ tailWord_5715652) baseStart_5715652 baseEnd_5715652 := by
    simpa [prefixWord, tailWord_5715652, baseEnd_5715652] using wordTrace_append hprefix tailTrace_5715652
  have hstable : (prefixWord ++ tailWord_5715652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715652).length < 2 ^ (prefixWord ++ tailWord_5715652).sum := by decide
  have hdescent : baseEnd_5715652 < baseStart_5715652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715655 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_5715655 : Nat := 118140960795 + 5715655 * 2 ^ 59
def prefixEnd_5715655 : Nat := 4983230072969 + 3 ^ 40 * 5715655 * 2
def baseEnd_5715655 : Nat := 2934878270273940207226687

theorem tailTrace_5715655 : CollatzResearch.WordTrace tailWord_5715655 prefixEnd_5715655 2934878270273940207226687 := by
  unfold tailWord_5715655
  simp only [CollatzResearch.WordTrace]
  refine ⟨208467064108165566003348419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138978042738777044002232279 208467064108165566003348419)
  ·
    refine ⟨312700596162248349005022629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208467064108165566003348419 312700596162248349005022629)
    ·
      refine ⟨58631361780421565438441743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312700596162248349005022629 58631361780421565438441743)
      ·
        refine ⟨87947042670632348157662615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58631361780421565438441743 87947042670632348157662615)
        ·
          refine ⟨131920564005948522236493923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87947042670632348157662615 131920564005948522236493923)
          ·
            refine ⟨197880846008922783354740885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131920564005948522236493923 197880846008922783354740885)
            ·
              refine ⟨9275664656668255469753479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197880846008922783354740885 9275664656668255469753479)
              ·
                refine ⟨13913496985002383204630219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9275664656668255469753479 13913496985002383204630219)
                ·
                  refine ⟨20870245477503574806945329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13913496985002383204630219 20870245477503574806945329)
                  ·
                    refine ⟨15652684108127681105208997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20870245477503574806945329 15652684108127681105208997)
                    ·
                      refine ⟨2934878270273940207226687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15652684108127681105208997 2934878270273940207226687)
                      ·
                        rfl

theorem cell23_5715655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_5715655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715655 prefixEnd_5715655 := by exact prefixLift 5715655
  have htrace : WordTrace (prefixWord ++ tailWord_5715655) baseStart_5715655 baseEnd_5715655 := by
    simpa [prefixWord, tailWord_5715655, baseEnd_5715655] using wordTrace_append hprefix tailTrace_5715655
  have hstable : (prefixWord ++ tailWord_5715655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715655).length < 2 ^ (prefixWord ++ tailWord_5715655).sum := by decide
  have hdescent : baseEnd_5715655 < baseStart_5715655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715662 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_5715662 : Nat := 118140960795 + 5715662 * 2 ^ 59
def prefixEnd_5715662 : Nat := 4983230072969 + 3 ^ 40 * 5715662 * 2
def baseEnd_5715662 : Nat := 2934881864638521679839155

theorem tailTrace_5715662 : CollatzResearch.WordTrace tailWord_5715662 prefixEnd_5715662 2934881864638521679839155 := by
  unfold tailWord_5715662
  simp only [CollatzResearch.WordTrace]
  refine ⟨26058414927392525774856655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138978212946093470799235493 26058414927392525774856655)
  ·
    refine ⟨39087622391088788662284983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26058414927392525774856655 39087622391088788662284983)
    ·
      refine ⟨58631433586633182993427475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39087622391088788662284983 58631433586633182993427475)
      ·
        refine ⟨87947150379949774490141213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58631433586633182993427475 87947150379949774490141213)
        ·
          refine ⟨32980181392481165433802955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87947150379949774490141213 32980181392481165433802955)
          ·
            refine ⟨49470272088721748150704433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32980181392481165433802955 49470272088721748150704433)
            ·
              refine ⟨37102704066541311113028325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49470272088721748150704433 37102704066541311113028325)
              ·
                refine ⟨6956757012476495833692811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37102704066541311113028325 6956757012476495833692811)
                ·
                  refine ⟨10435135518714743750539217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6956757012476495833692811 10435135518714743750539217)
                  ·
                    refine ⟨7826351639036057812904413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10435135518714743750539217 7826351639036057812904413)
                    ·
                      refine ⟨2934881864638521679839155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7826351639036057812904413 2934881864638521679839155)
                      ·
                        rfl

theorem cell23_5715662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_5715662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715662 prefixEnd_5715662 := by exact prefixLift 5715662
  have htrace : WordTrace (prefixWord ++ tailWord_5715662) baseStart_5715662 baseEnd_5715662 := by
    simpa [prefixWord, tailWord_5715662, baseEnd_5715662] using wordTrace_append hprefix tailTrace_5715662
  have hstable : (prefixWord ++ tailWord_5715662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715662).length < 2 ^ (prefixWord ++ tailWord_5715662).sum := by decide
  have hdescent : baseEnd_5715662 < baseStart_5715662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715665 : List Nat := [1, 2, 2, 1, 2, 5, 3, 7]
def baseStart_5715665 : Nat := 118140960795 + 5715665 * 2 ^ 59
def prefixEnd_5715665 : Nat := 4983230072969 + 3 ^ 40 * 5715665 * 2
def baseEnd_5715665 : Nat := 108699385373351302522283

theorem tailTrace_5715665 : CollatzResearch.WordTrace tailWord_5715665 prefixEnd_5715665 108699385373351302522283 := by
  unfold tailWord_5715665
  simp only [CollatzResearch.WordTrace]
  refine ⟨208467428838129337711212449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138978285892086225140808299 208467428838129337711212449)
  ·
    refine ⟨156350571628597003283409337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208467428838129337711212449 156350571628597003283409337)
    ·
      refine ⟨117262928721447752462557003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156350571628597003283409337 117262928721447752462557003)
      ·
        refine ⟨175894393082171628693835505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117262928721447752462557003 175894393082171628693835505)
        ·
          refine ⟨131920794811628721520376629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175894393082171628693835505 131920794811628721520376629)
          ·
            refine ⟨12367574513590192642535309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131920794811628721520376629 12367574513590192642535309)
            ·
              refine ⟨4637840442596322240950741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12367574513590192642535309 4637840442596322240950741)
              ·
                refine ⟨108699385373351302522283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4637840442596322240950741 108699385373351302522283)
                ·
                  rfl

theorem cell23_5715665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 7].length) (baseStart_5715665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715665 prefixEnd_5715665 := by exact prefixLift 5715665
  have htrace : WordTrace (prefixWord ++ tailWord_5715665) baseStart_5715665 baseEnd_5715665 := by
    simpa [prefixWord, tailWord_5715665, baseEnd_5715665] using wordTrace_append hprefix tailTrace_5715665
  have hstable : (prefixWord ++ tailWord_5715665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715665).length < 2 ^ (prefixWord ++ tailWord_5715665).sum := by decide
  have hdescent : baseEnd_5715665 < baseStart_5715665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715670 : List Nat := [5, 2, 1, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5715670 : Nat := 118140960795 + 5715670 * 2 ^ 59
def prefixEnd_5715670 : Nat := 4983230072969 + 3 ^ 40 * 5715670 * 2
def baseEnd_5715670 : Nat := 2934885972483757648539119

theorem tailTrace_5715670 : CollatzResearch.WordTrace tailWord_5715670 prefixEnd_5715670 2934885972483757648539119 := by
  unfold tailWord_5715670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13029225700194451472821529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138978407468740815710096309 13029225700194451472821529)
  ·
    refine ⟨9771919275145838604616147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13029225700194451472821529 9771919275145838604616147)
    ·
      refine ⟨14657878912718757906924221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9771919275145838604616147 14657878912718757906924221)
      ·
        refine ⟨5496704592269534215096583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14657878912718757906924221 5496704592269534215096583)
        ·
          refine ⟨8245056888404301322644875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496704592269534215096583 8245056888404301322644875)
          ·
            refine ⟨12367585332606451983967313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8245056888404301322644875 12367585332606451983967313)
            ·
              refine ⟨9275688999454838987975485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12367585332606451983967313 9275688999454838987975485)
              ·
                refine ⟨3478383374795564620490807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9275688999454838987975485 3478383374795564620490807)
                ·
                  refine ⟨5217575062193346930736211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478383374795564620490807 5217575062193346930736211)
                  ·
                    refine ⟨7826362593290020396104317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5217575062193346930736211 7826362593290020396104317)
                    ·
                      refine ⟨2934885972483757648539119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7826362593290020396104317 2934885972483757648539119)
                      ·
                        rfl

theorem cell23_5715670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5715670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715670 prefixEnd_5715670 := by exact prefixLift 5715670
  have htrace : WordTrace (prefixWord ++ tailWord_5715670) baseStart_5715670 baseEnd_5715670 := by
    simpa [prefixWord, tailWord_5715670, baseEnd_5715670] using wordTrace_append hprefix tailTrace_5715670
  have hstable : (prefixWord ++ tailWord_5715670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715670).length < 2 ^ (prefixWord ++ tailWord_5715670).sum := by decide
  have hdescent : baseEnd_5715670 < baseStart_5715670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715735 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_5715735 : Nat := 118140960795 + 5715735 * 2 ^ 59
def prefixEnd_5715735 : Nat := 4983230072969 + 3 ^ 40 * 5715735 * 2
def baseEnd_5715735 : Nat := 2934919348726299894226319

theorem tailTrace_5715735 : CollatzResearch.WordTrace tailWord_5715735 prefixEnd_5715735 2934919348726299894226319 := by
  unfold tailWord_5715735
  simp only [CollatzResearch.WordTrace]
  refine ⟨208469981947875739666260659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138979987965250493110840439 208469981947875739666260659)
  ·
    refine ⟨312704972921813609499390989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208469981947875739666260659 312704972921813609499390989)
    ·
      refine ⟨117264364845680103562271621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312704972921813609499390989 117264364845680103562271621)
      ·
        refine ⟨21987068408565019417925929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117264364845680103562271621 21987068408565019417925929)
        ·
          refine ⟨16490301306423764563444447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21987068408565019417925929 16490301306423764563444447)
          ·
            refine ⟨24735451959635646845166671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16490301306423764563444447 24735451959635646845166671)
            ·
              refine ⟨37103177939453470267750007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24735451959635646845166671 37103177939453470267750007)
              ·
                refine ⟨55654766909180205401625011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37103177939453470267750007 55654766909180205401625011)
                ·
                  refine ⟨83482150363770308102437517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55654766909180205401625011 83482150363770308102437517)
                  ·
                    refine ⟨31305806386413865538414069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83482150363770308102437517 31305806386413865538414069)
                    ·
                      refine ⟨2934919348726299894226319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31305806386413865538414069 2934919348726299894226319)
                      ·
                        rfl

theorem cell23_5715735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_5715735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715735 prefixEnd_5715735 := by exact prefixLift 5715735
  have htrace : WordTrace (prefixWord ++ tailWord_5715735) baseStart_5715735 baseEnd_5715735 := by
    simpa [prefixWord, tailWord_5715735, baseEnd_5715735] using wordTrace_append hprefix tailTrace_5715735
  have hstable : (prefixWord ++ tailWord_5715735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715735).length < 2 ^ (prefixWord ++ tailWord_5715735).sum := by decide
  have hdescent : baseEnd_5715735 < baseStart_5715735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715749 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 4, 2, 2]
def baseStart_5715749 : Nat := 118140960795 + 5715749 * 2 ^ 59
def prefixEnd_5715749 : Nat := 4983230072969 + 3 ^ 40 * 5715749 * 2
def baseEnd_5715749 : Nat := 2934926537455462839451255

theorem tailTrace_5715749 : CollatzResearch.WordTrace tailWord_5715749 prefixEnd_5715749 2934926537455462839451255 := by
  unfold tailWord_5715749
  simp only [CollatzResearch.WordTrace]
  refine ⟨208470492569825020057270301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138980328379883346704846867 208470492569825020057270301)
  ·
    refine ⟨78176434713684382521476363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208470492569825020057270301 78176434713684382521476363)
    ·
      refine ⟨117264652070526573782214545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78176434713684382521476363 117264652070526573782214545)
      ·
        refine ⟨87948489052894930336660909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117264652070526573782214545 87948489052894930336660909)
        ·
          refine ⟨32980683394835598876247841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87948489052894930336660909 32980683394835598876247841)
          ·
            refine ⟨24735512546126699157185881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32980683394835598876247841 24735512546126699157185881)
            ·
              refine ⟨18551634409595024367889411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24735512546126699157185881 18551634409595024367889411)
              ·
                refine ⟨27827451614392536551834117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18551634409595024367889411 27827451614392536551834117)
                ·
                  refine ⟨5217647177698600603468897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27827451614392536551834117 5217647177698600603468897)
                  ·
                    refine ⟨3913235383273950452601673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5217647177698600603468897 3913235383273950452601673)
                    ·
                      refine ⟨2934926537455462839451255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913235383273950452601673 2934926537455462839451255)
                      ·
                        rfl

theorem cell23_5715749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_5715749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715749 prefixEnd_5715749 := by exact prefixLift 5715749
  have htrace : WordTrace (prefixWord ++ tailWord_5715749) baseStart_5715749 baseEnd_5715749 := by
    simpa [prefixWord, tailWord_5715749, baseEnd_5715749] using wordTrace_append hprefix tailTrace_5715749
  have hstable : (prefixWord ++ tailWord_5715749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715749).length < 2 ^ (prefixWord ++ tailWord_5715749).sum := by decide
  have hdescent : baseEnd_5715749 < baseStart_5715749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715845 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 8]
def baseStart_5715845 : Nat := 118140960795 + 5715845 * 2 ^ 59
def prefixEnd_5715845 : Nat := 4983230072969 + 3 ^ 40 * 5715845 * 2
def baseEnd_5715845 : Nat := 326108425733143829316757

theorem tailTrace_5715845 : CollatzResearch.WordTrace tailWord_5715845 prefixEnd_5715845 326108425733143829316757 := by
  unfold tailWord_5715845
  simp only [CollatzResearch.WordTrace]
  refine ⟨208473993977477228452764989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138982662651651485635176659 208473993977477228452764989)
  ·
    refine ⟨78177747741553960669786871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208473993977477228452764989 78177747741553960669786871)
    ·
      refine ⟨117266621612330941004680307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78177747741553960669786871 117266621612330941004680307)
      ·
        refine ⟨175899932418496411507020461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117266621612330941004680307 175899932418496411507020461)
        ·
          refine ⟨65962474656936154315132673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175899932418496411507020461 65962474656936154315132673)
          ·
            refine ⟨49471855992702115736349505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65962474656936154315132673 49471855992702115736349505)
            ·
              refine ⟨37103891994526586802262129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49471855992702115736349505 37103891994526586802262129)
              ·
                refine ⟨27827918995894940101696597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37103891994526586802262129 27827918995894940101696597)
                ·
                  refine ⟨326108425733143829316757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27827918995894940101696597 326108425733143829316757)
                  ·
                    rfl

theorem cell23_5715845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_5715845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715845 prefixEnd_5715845 := by exact prefixLift 5715845
  have htrace : WordTrace (prefixWord ++ tailWord_5715845) baseStart_5715845 baseEnd_5715845 := by
    simpa [prefixWord, tailWord_5715845, baseEnd_5715845] using wordTrace_append hprefix tailTrace_5715845
  have hstable : (prefixWord ++ tailWord_5715845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715845).length < 2 ^ (prefixWord ++ tailWord_5715845).sum := by decide
  have hdescent : baseEnd_5715845 < baseStart_5715845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715865 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_5715865 : Nat := 118140960795 + 5715865 * 2 ^ 59
def prefixEnd_5715865 : Nat := 4983230072969 + 3 ^ 40 * 5715865 * 2
def baseEnd_5715865 : Nat := 2934986101211384385600721

theorem tailTrace_5715865 : CollatzResearch.WordTrace tailWord_5715865 prefixEnd_5715865 2934986101211384385600721 := by
  unfold tailWord_5715865
  simp only [CollatzResearch.WordTrace]
  refine ⟨208474723437404771868493049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138983148958269847912328699 208474723437404771868493049)
  ·
    refine ⟨156356042578053578901369787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208474723437404771868493049 156356042578053578901369787)
    ·
      refine ⟨234534063867080368352054681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156356042578053578901369787 234534063867080368352054681)
      ·
        refine ⟨175900547900310276264041011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234534063867080368352054681 175900547900310276264041011)
        ·
          refine ⟨263850821850465414396061517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175900547900310276264041011 263850821850465414396061517)
          ·
            refine ⟨98944058193924530398523069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263850821850465414396061517 98944058193924530398523069)
            ·
              refine ⟨37104021822721698899446151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98944058193924530398523069 37104021822721698899446151)
              ·
                refine ⟨55656032734082548349169227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37104021822721698899446151 55656032734082548349169227)
                ·
                  refine ⟨83484049101123822523753841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55656032734082548349169227 83484049101123822523753841)
                  ·
                    refine ⟨62613036825842866892815381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83484049101123822523753841 62613036825842866892815381)
                    ·
                      refine ⟨2934986101211384385600721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62613036825842866892815381 2934986101211384385600721)
                      ·
                        rfl

theorem cell23_5715865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_5715865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715865 prefixEnd_5715865 := by exact prefixLift 5715865
  have htrace : WordTrace (prefixWord ++ tailWord_5715865) baseStart_5715865 baseEnd_5715865 := by
    simpa [prefixWord, tailWord_5715865, baseEnd_5715865] using wordTrace_append hprefix tailTrace_5715865
  have hstable : (prefixWord ++ tailWord_5715865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715865).length < 2 ^ (prefixWord ++ tailWord_5715865).sum := by decide
  have hdescent : baseEnd_5715865 < baseStart_5715865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715866 : List Nat := [3, 1, 1, 4, 2, 1, 2, 4, 1, 4]
def baseStart_5715866 : Nat := 118140960795 + 5715866 * 2 ^ 59
def prefixEnd_5715866 : Nat := 4983230072969 + 3 ^ 40 * 5715866 * 2
def baseEnd_5715866 : Nat := 978328871564012960562739

theorem tailTrace_5715866 : CollatzResearch.WordTrace tailWord_5715866 prefixEnd_5715866 978328871564012960562739 := by
  unfold tailWord_5715866
  simp only [CollatzResearch.WordTrace]
  refine ⟨52118689977600287259819863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138983173273600766026186301 52118689977600287259819863)
  ·
    refine ⟨78178034966400430889729795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52118689977600287259819863 78178034966400430889729795)
    ·
      refine ⟨117267052449600646334594693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78178034966400430889729795 117267052449600646334594693)
      ·
        refine ⟨21987572334300121187736505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117267052449600646334594693 21987572334300121187736505)
        ·
          refine ⟨16490679250725090890802379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21987572334300121187736505 16490679250725090890802379)
          ·
            refine ⟨24736018876087636336203569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16490679250725090890802379 24736018876087636336203569)
            ·
              refine ⟨18552014157065727252152677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24736018876087636336203569 18552014157065727252152677)
              ·
                refine ⟨3478502654449823859778627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18552014157065727252152677 3478502654449823859778627)
                ·
                  refine ⟨5217753981674735789667941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478502654449823859778627 5217753981674735789667941)
                  ·
                    refine ⟨978328871564012960562739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5217753981674735789667941 978328871564012960562739)
                    ·
                      rfl

theorem cell23_5715866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_5715866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715866 prefixEnd_5715866 := by exact prefixLift 5715866
  have htrace : WordTrace (prefixWord ++ tailWord_5715866) baseStart_5715866 baseEnd_5715866 := by
    simpa [prefixWord, tailWord_5715866, baseEnd_5715866] using wordTrace_append hprefix tailTrace_5715866
  have hstable : (prefixWord ++ tailWord_5715866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715866).length < 2 ^ (prefixWord ++ tailWord_5715866).sum := by decide
  have hdescent : baseEnd_5715866 < baseStart_5715866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715900 : List Nat := [2, 2, 2, 5, 1, 2, 1, 3, 1, 4]
def baseStart_5715900 : Nat := 118140960795 + 5715900 * 2 ^ 59
def prefixEnd_5715900 : Nat := 4983230072969 + 3 ^ 40 * 5715900 * 2
def baseEnd_5715900 : Nat := 978334691011430582887687

theorem tailTrace_5715900 : CollatzResearch.WordTrace tailWord_5715900 prefixEnd_5715900 978334691011430582887687 := by
  unfold tailWord_5715900
  simp only [CollatzResearch.WordTrace]
  refine ⟨104237999996138986423008577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138983999994851981897344769 104237999996138986423008577)
  ·
    refine ⟨78178499997104239817256433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104237999996138986423008577 78178499997104239817256433)
    ·
      refine ⟨58633874997828179862942325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78178499997104239817256433 58633874997828179862942325)
      ·
        refine ⟨5496925781046391862150843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58633874997828179862942325 5496925781046391862150843)
        ·
          refine ⟨8245388671569587793226265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496925781046391862150843 8245388671569587793226265)
          ·
            refine ⟨6184041503677190844919699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8245388671569587793226265 6184041503677190844919699)
            ·
              refine ⟨9276062255515786267379549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6184041503677190844919699 9276062255515786267379549)
              ·
                refine ⟨3478523345818419850267331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9276062255515786267379549 3478523345818419850267331)
                ·
                  refine ⟨5217785018727629775400997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478523345818419850267331 5217785018727629775400997)
                  ·
                    refine ⟨978334691011430582887687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5217785018727629775400997 978334691011430582887687)
                    ·
                      rfl

theorem cell23_5715900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_5715900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715900 prefixEnd_5715900 := by exact prefixLift 5715900
  have htrace : WordTrace (prefixWord ++ tailWord_5715900) baseStart_5715900 baseEnd_5715900 := by
    simpa [prefixWord, tailWord_5715900, baseEnd_5715900] using wordTrace_append hprefix tailTrace_5715900
  have hstable : (prefixWord ++ tailWord_5715900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715900).length < 2 ^ (prefixWord ++ tailWord_5715900).sum := by decide
  have hdescent : baseEnd_5715900 < baseStart_5715900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715916 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 2, 3, 2]
def baseStart_5715916 : Nat := 118140960795 + 5715916 * 2 ^ 59
def prefixEnd_5715916 : Nat := 4983230072969 + 3 ^ 40 * 5715916 * 2
def baseEnd_5715916 : Nat := 2935012288724763686062987

theorem tailTrace_5715916 : CollatzResearch.WordTrace tailWord_5715916 prefixEnd_5715916 2935012288724763686062987 := by
  unfold tailWord_5715916
  simp only [CollatzResearch.WordTrace]
  refine ⟨104238291780110003789299801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138984389040146671719066401 104238291780110003789299801)
  ·
    refine ⟨78178718835082502841974851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104238291780110003789299801 78178718835082502841974851)
    ·
      refine ⟨117268078252623754262962277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78178718835082502841974851 117268078252623754262962277)
      ·
        refine ⟨21987764672366953924305427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117268078252623754262962277 21987764672366953924305427)
        ·
          refine ⟨32981647008550430886458141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21987764672366953924305427 32981647008550430886458141)
          ·
            refine ⟨12368117628206411582421803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32981647008550430886458141 12368117628206411582421803)
            ·
              refine ⟨18552176442309617373632705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12368117628206411582421803 18552176442309617373632705)
              ·
                refine ⟨13914132331732213030224529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18552176442309617373632705 13914132331732213030224529)
                ·
                  refine ⟨10435599248799159772668397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13914132331732213030224529 10435599248799159772668397)
                  ·
                    refine ⟨3913349718299684914750649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10435599248799159772668397 3913349718299684914750649)
                    ·
                      refine ⟨2935012288724763686062987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913349718299684914750649 2935012288724763686062987)
                      ·
                        rfl

theorem cell23_5715916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_5715916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715916 prefixEnd_5715916 := by exact prefixLift 5715916
  have htrace : WordTrace (prefixWord ++ tailWord_5715916) baseStart_5715916 baseEnd_5715916 := by
    simpa [prefixWord, tailWord_5715916, baseEnd_5715916] using wordTrace_append hprefix tailTrace_5715916
  have hstable : (prefixWord ++ tailWord_5715916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715916).length < 2 ^ (prefixWord ++ tailWord_5715916).sum := by decide
  have hdescent : baseEnd_5715916 < baseStart_5715916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715943 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 1, 5]
def baseStart_5715943 : Nat := 118140960795 + 5715943 * 2 ^ 59
def prefixEnd_5715943 : Nat := 4983230072969 + 3 ^ 40 * 5715943 * 2
def baseEnd_5715943 : Nat := 978342050900811693475121

theorem tailTrace_5715943 : CollatzResearch.WordTrace tailWord_5715943 prefixEnd_5715943 978342050900811693475121 := by
  unfold tailWord_5715943
  simp only [CollatzResearch.WordTrace]
  refine ⟨208477568331122191189832483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138985045554081460793221655 208477568331122191189832483)
  ·
    refine ⟨312716352496683286784748725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208477568331122191189832483 312716352496683286784748725)
    ·
      refine ⟨29317158046564058136070193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 312716352496683286784748725 29317158046564058136070193)
      ·
        refine ⟨21987868534923043602052645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29317158046564058136070193 21987868534923043602052645)
        ·
          refine ⟨4122725350298070675384871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21987868534923043602052645 4122725350298070675384871)
          ·
            refine ⟨6184088025447106013077307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122725350298070675384871 6184088025447106013077307)
            ·
              refine ⟨9276132038170659019615961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6184088025447106013077307 9276132038170659019615961)
              ·
                refine ⟨6957099028627994264711971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9276132038170659019615961 6957099028627994264711971)
                ·
                  refine ⟨10435648542941991397067957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6957099028627994264711971 10435648542941991397067957)
                  ·
                    refine ⟨978342050900811693475121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10435648542941991397067957 978342050900811693475121)
                    ·
                      rfl

theorem cell23_5715943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_5715943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715943 prefixEnd_5715943 := by exact prefixLift 5715943
  have htrace : WordTrace (prefixWord ++ tailWord_5715943) baseStart_5715943 baseEnd_5715943 := by
    simpa [prefixWord, tailWord_5715943, baseEnd_5715943] using wordTrace_append hprefix tailTrace_5715943
  have hstable : (prefixWord ++ tailWord_5715943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715943).length < 2 ^ (prefixWord ++ tailWord_5715943).sum := by decide
  have hdescent : baseEnd_5715943 < baseStart_5715943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715946 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_5715946 : Nat := 118140960795 + 5715946 * 2 ^ 59
def prefixEnd_5715946 : Nat := 4983230072969 + 3 ^ 40 * 5715946 * 2
def baseEnd_5715946 : Nat := 2935027693144398568687849

theorem tailTrace_5715946 : CollatzResearch.WordTrace tailWord_5715946 prefixEnd_5715946 2935027693144398568687849 := by
  unfold tailWord_5715946
  simp only [CollatzResearch.WordTrace]
  refine ⟨52119419437527830675547923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138985118500074215134794461 52119419437527830675547923)
  ·
    refine ⟨78179129156291746013321885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52119419437527830675547923 78179129156291746013321885)
    ·
      refine ⟨29317173433609404754995707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78179129156291746013321885 29317173433609404754995707)
      ·
        refine ⟨43975760150414107132493561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29317173433609404754995707 43975760150414107132493561)
        ·
          refine ⟨32981820112810580349370171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43975760150414107132493561 32981820112810580349370171)
          ·
            refine ⟨49472730169215870524055257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32981820112810580349370171 49472730169215870524055257)
            ·
              refine ⟨37104547626911902893041443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49472730169215870524055257 37104547626911902893041443)
              ·
                refine ⟨55656821440367854339562165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37104547626911902893041443 55656821440367854339562165)
                ·
                  refine ⟨5217827010034486344333953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55656821440367854339562165 5217827010034486344333953)
                  ·
                    refine ⟨3913370257525864758250465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5217827010034486344333953 3913370257525864758250465)
                    ·
                      refine ⟨2935027693144398568687849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913370257525864758250465 2935027693144398568687849)
                      ·
                        rfl

theorem cell23_5715946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_5715946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715946 prefixEnd_5715946 := by exact prefixLift 5715946
  have htrace : WordTrace (prefixWord ++ tailWord_5715946) baseStart_5715946 baseEnd_5715946 := by
    simpa [prefixWord, tailWord_5715946, baseEnd_5715946] using wordTrace_append hprefix tailTrace_5715946
  have hstable : (prefixWord ++ tailWord_5715946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715946).length < 2 ^ (prefixWord ++ tailWord_5715946).sum := by decide
  have hdescent : baseEnd_5715946 < baseStart_5715946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715966 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5715966 : Nat := 118140960795 + 5715966 * 2 ^ 59
def prefixEnd_5715966 : Nat := 4983230072969 + 3 ^ 40 * 5715966 * 2
def baseEnd_5715966 : Nat := 2935037962757488490437757

theorem tailTrace_5715966 : CollatzResearch.WordTrace tailWord_5715966 prefixEnd_5715966 2935037962757488490437757 := by
  unfold tailWord_5715966
  simp only [CollatzResearch.WordTrace]
  refine ⟨26059800901254858264739969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138985604806692577411946501 26059800901254858264739969)
  ·
    refine ⟨19544850675941143698554977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26059800901254858264739969 19544850675941143698554977)
    ·
      refine ⟨14658638006955857773916233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19544850675941143698554977 14658638006955857773916233)
      ·
        refine ⟨10993978505216893330437175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14658638006955857773916233 10993978505216893330437175)
        ·
          refine ⟨16490967757825339995655763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10993978505216893330437175 16490967757825339995655763)
          ·
            refine ⟨24736451636738009993483645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16490967757825339995655763 24736451636738009993483645)
            ·
              refine ⟨9276169363776753747556367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24736451636738009993483645 9276169363776753747556367)
              ·
                refine ⟨13914254045665130621334551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9276169363776753747556367 13914254045665130621334551)
                ·
                  refine ⟨20871381068497695932001827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13914254045665130621334551 20871381068497695932001827)
                  ·
                    refine ⟨31307071602746543898002741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20871381068497695932001827 31307071602746543898002741)
                    ·
                      refine ⟨2935037962757488490437757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31307071602746543898002741 2935037962757488490437757)
                      ·
                        rfl

theorem cell23_5715966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5715966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715966 prefixEnd_5715966 := by exact prefixLift 5715966
  have htrace : WordTrace (prefixWord ++ tailWord_5715966) baseStart_5715966 baseEnd_5715966 := by
    simpa [prefixWord, tailWord_5715966, baseEnd_5715966] using wordTrace_append hprefix tailTrace_5715966
  have hstable : (prefixWord ++ tailWord_5715966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715966).length < 2 ^ (prefixWord ++ tailWord_5715966).sum := by decide
  have hdescent : baseEnd_5715966 < baseStart_5715966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715982 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_5715982 : Nat := 118140960795 + 5715982 * 2 ^ 59
def prefixEnd_5715982 : Nat := 4983230072969 + 3 ^ 40 * 5715982 * 2
def baseEnd_5715982 : Nat := 978348726149320142612561

theorem tailTrace_5715982 : CollatzResearch.WordTrace tailWord_5715982 prefixEnd_5715982 978348726149320142612561 := by
  unfold tailWord_5715982
  simp only [CollatzResearch.WordTrace]
  refine ⟨26059873847247612606312775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138985993851987267233668133 26059873847247612606312775)
  ·
    refine ⟨39089810770871418909469163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26059873847247612606312775 39089810770871418909469163)
    ·
      refine ⟨58634716156307128364203745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39089810770871418909469163 58634716156307128364203745)
      ·
        refine ⟨43976037117230346273152809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58634716156307128364203745 43976037117230346273152809)
        ·
          refine ⟨32982027837922759704864607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43976037117230346273152809 32982027837922759704864607)
          ·
            refine ⟨49473041756884139557296911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32982027837922759704864607 49473041756884139557296911)
            ·
              refine ⟨74209562635326209335945367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49473041756884139557296911 74209562635326209335945367)
              ·
                refine ⟨111314343952989314003918051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74209562635326209335945367 111314343952989314003918051)
                ·
                  refine ⟨166971515929483971005877077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111314343952989314003918051 166971515929483971005877077)
                  ·
                    refine ⟨978348726149320142612561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 166971515929483971005877077 978348726149320142612561)
                    ·
                      rfl

theorem cell23_5715982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_5715982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715982 prefixEnd_5715982 := by exact prefixLift 5715982
  have htrace : WordTrace (prefixWord ++ tailWord_5715982) baseStart_5715982 baseEnd_5715982 := by
    simpa [prefixWord, tailWord_5715982, baseEnd_5715982] using wordTrace_append hprefix tailTrace_5715982
  have hstable : (prefixWord ++ tailWord_5715982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715982).length < 2 ^ (prefixWord ++ tailWord_5715982).sum := by decide
  have hdescent : baseEnd_5715982 < baseStart_5715982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5715996 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_5715996 : Nat := 118140960795 + 5715996 * 2 ^ 59
def prefixEnd_5715996 : Nat := 4983230072969 + 3 ^ 40 * 5715996 * 2
def baseEnd_5715996 : Nat := 2935053367177123373062619

theorem tailTrace_5715996 : CollatzResearch.WordTrace tailWord_5715996 prefixEnd_5715996 2935053367177123373062619 := by
  unfold tailWord_5715996
  simp only [CollatzResearch.WordTrace]
  refine ⟨104239750699965090620755921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138986334266620120827674561 104239750699965090620755921)
  ·
    refine ⟨78179813024973817965566941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104239750699965090620755921 78179813024973817965566941)
    ·
      refine ⟨29317429884365181737087603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78179813024973817965566941 29317429884365181737087603)
      ·
        refine ⟨43976144826547772605631405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29317429884365181737087603 43976144826547772605631405)
        ·
          refine ⟨16491054309955414727111777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43976144826547772605631405 16491054309955414727111777)
          ·
            refine ⟨12368290732466561045333833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16491054309955414727111777 12368290732466561045333833)
            ·
              refine ⟨9276218049349920784000375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12368290732466561045333833 9276218049349920784000375)
              ·
                refine ⟨13914327074024881176000563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9276218049349920784000375 13914327074024881176000563)
                ·
                  refine ⟨20871490611037321764000845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13914327074024881176000563 20871490611037321764000845)
                  ·
                    refine ⟨7826808979138995661500317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20871490611037321764000845 7826808979138995661500317)
                    ·
                      refine ⟨2935053367177123373062619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7826808979138995661500317 2935053367177123373062619)
                      ·
                        rfl

theorem cell23_5715996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_5715996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5715996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5715996 prefixEnd_5715996 := by exact prefixLift 5715996
  have htrace : WordTrace (prefixWord ++ tailWord_5715996) baseStart_5715996 baseEnd_5715996 := by
    simpa [prefixWord, tailWord_5715996, baseEnd_5715996] using wordTrace_append hprefix tailTrace_5715996
  have hstable : (prefixWord ++ tailWord_5715996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5715996).length < 2 ^ (prefixWord ++ tailWord_5715996).sum := by decide
  have hdescent : baseEnd_5715996 < baseStart_5715996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5715996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716023 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 1, 3, 2]
def baseStart_5716023 : Nat := 118140960795 + 5716023 * 2 ^ 59
def prefixEnd_5716023 : Nat := 4983230072969 + 3 ^ 40 * 5716023 * 2
def baseEnd_5716023 : Nat := 2935067231154794767424995

theorem tailTrace_5716023 : CollatzResearch.WordTrace tailWord_5716023 prefixEnd_5716023 2935067231154794767424995 := by
  unfold tailWord_5716023
  simp only [CollatzResearch.WordTrace]
  refine ⟨208480486170832364852744723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138986990780554909901829815 208480486170832364852744723)
  ·
    refine ⟨312720729256248547279117085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208480486170832364852744723 312720729256248547279117085)
    ·
      refine ⟨117270273471093205229668907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312720729256248547279117085 117270273471093205229668907)
      ·
        refine ⟨175905410206639807844503361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117270273471093205229668907 175905410206639807844503361)
        ·
          refine ⟨131929057654979855883377521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175905410206639807844503361 131929057654979855883377521)
          ·
            refine ⟨98946793241234891912533141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131929057654979855883377521 98946793241234891912533141)
            ·
              refine ⟨4638130933182885558399991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98946793241234891912533141 4638130933182885558399991)
              ·
                refine ⟨6957196399774328337599987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4638130933182885558399991 6957196399774328337599987)
                ·
                  refine ⟨10435794599661492506399981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6957196399774328337599987 10435794599661492506399981)
                  ·
                    refine ⟨3913422974873059689899993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10435794599661492506399981 3913422974873059689899993)
                    ·
                      refine ⟨2935067231154794767424995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913422974873059689899993 2935067231154794767424995)
                      ·
                        rfl

theorem cell23_5716023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_5716023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716023 prefixEnd_5716023 := by exact prefixLift 5716023
  have htrace : WordTrace (prefixWord ++ tailWord_5716023) baseStart_5716023 baseEnd_5716023 := by
    simpa [prefixWord, tailWord_5716023, baseEnd_5716023] using wordTrace_append hprefix tailTrace_5716023
  have hstable : (prefixWord ++ tailWord_5716023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716023).length < 2 ^ (prefixWord ++ tailWord_5716023).sum := by decide
  have hdescent : baseEnd_5716023 < baseStart_5716023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716053 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 1, 4, 2]
def baseStart_5716053 : Nat := 118140960795 + 5716053 * 2 ^ 59
def prefixEnd_5716053 : Nat := 4983230072969 + 3 ^ 40 * 5716053 * 2
def baseEnd_5716053 : Nat := 2935082635574429650049857

theorem tailTrace_5716053 : CollatzResearch.WordTrace tailWord_5716053 prefixEnd_5716053 2935082635574429650049857 := by
  unfold tailWord_5716053
  simp only [CollatzResearch.WordTrace]
  refine ⟨208481580360723679976336813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138987720240482453317557875 208481580360723679976336813)
  ·
    refine ⟨78180592635271379991126305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208481580360723679976336813 78180592635271379991126305)
    ·
      refine ⟨58635444476453534993344729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78180592635271379991126305 58635444476453534993344729)
      ·
        refine ⟨43976583357340151245008547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58635444476453534993344729 43976583357340151245008547)
        ·
          refine ⟨65964875036010226867512821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43976583357340151245008547 65964875036010226867512821)
          ·
            refine ⟨6184207034625958768829327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65964875036010226867512821 6184207034625958768829327)
            ·
              refine ⟨9276310551938938153243991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6184207034625958768829327 9276310551938938153243991)
              ·
                refine ⟨13914465827908407229865987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9276310551938938153243991 13914465827908407229865987)
                ·
                  refine ⟨20871698741862610844798981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13914465827908407229865987 20871698741862610844798981)
                  ·
                    refine ⟨3913443514099239533399809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20871698741862610844798981 3913443514099239533399809)
                    ·
                      refine ⟨2935082635574429650049857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913443514099239533399809 2935082635574429650049857)
                      ·
                        rfl

theorem cell23_5716053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_5716053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716053 prefixEnd_5716053 := by exact prefixLift 5716053
  have htrace : WordTrace (prefixWord ++ tailWord_5716053) baseStart_5716053 baseEnd_5716053 := by
    simpa [prefixWord, tailWord_5716053, baseEnd_5716053] using wordTrace_append hprefix tailTrace_5716053
  have hstable : (prefixWord ++ tailWord_5716053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716053).length < 2 ^ (prefixWord ++ tailWord_5716053).sum := by decide
  have hdescent : baseEnd_5716053 < baseStart_5716053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716076 : List Nat := [2, 2, 1, 1, 3, 3, 3, 3, 5]
def baseStart_5716076 : Nat := 118140960795 + 5716076 * 2 ^ 59
def prefixEnd_5716076 : Nat := 4983230072969 + 3 ^ 40 * 5716076 * 2
def baseEnd_5716076 : Nat := 326121605069942562229139

theorem tailTrace_5716076 : CollatzResearch.WordTrace tailWord_5716076 prefixEnd_5716076 326121605069942562229139 := by
  unfold tailWord_5716076
  simp only [CollatzResearch.WordTrace]
  refine ⟨104241209619820177452212041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138988279493093569936282721 104241209619820177452212041)
  ·
    refine ⟨78180907214865133089159031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104241209619820177452212041 78180907214865133089159031)
    ·
      refine ⟨117271360822297699633738547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78180907214865133089159031 117271360822297699633738547)
      ·
        refine ⟨175907041233446549450607821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117271360822297699633738547 175907041233446549450607821)
        ·
          refine ⟨65965140462542456043977933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175907041233446549450607821 65965140462542456043977933)
          ·
            refine ⟨24736927673453421016491725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65965140462542456043977933 24736927673453421016491725)
            ·
              refine ⟨9276347877545032881184397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24736927673453421016491725 9276347877545032881184397)
              ·
                refine ⟨3478630454079387330444149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9276347877545032881184397 3478630454079387330444149)
                ·
                  refine ⟨326121605069942562229139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3478630454079387330444149 326121605069942562229139)
                  ·
                    rfl

theorem cell23_5716076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_5716076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716076 prefixEnd_5716076 := by exact prefixLift 5716076
  have htrace : WordTrace (prefixWord ++ tailWord_5716076) baseStart_5716076 baseEnd_5716076 := by
    simpa [prefixWord, tailWord_5716076, baseEnd_5716076] using wordTrace_append hprefix tailTrace_5716076
  have hstable : (prefixWord ++ tailWord_5716076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716076).length < 2 ^ (prefixWord ++ tailWord_5716076).sum := by decide
  have hdescent : baseEnd_5716076 < baseStart_5716076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716089 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 4, 5]
def baseStart_5716089 : Nat := 118140960795 + 5716089 * 2 ^ 59
def prefixEnd_5716089 : Nat := 4983230072969 + 3 ^ 40 * 5716089 * 2
def baseEnd_5716089 : Nat := 978367040292663836399897

theorem tailTrace_5716089 : CollatzResearch.WordTrace tailWord_5716089 prefixEnd_5716089 978367040292663836399897 := by
  unfold tailWord_5716089
  simp only [CollatzResearch.WordTrace]
  refine ⟨208482893388593258124647321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138988595592395505416431547 208482893388593258124647321)
  ·
    refine ⟨156362170041444943593485491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208482893388593258124647321 156362170041444943593485491)
    ·
      refine ⟨234543255062167415390228237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156362170041444943593485491 234543255062167415390228237)
      ·
        refine ⟨87953720648312780771335589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234543255062167415390228237 87953720648312780771335589)
        ·
          refine ⟨16491322621558646394625423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87953720648312780771335589 16491322621558646394625423)
          ·
            refine ⟨24736983932337969591938135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16491322621558646394625423 24736983932337969591938135)
            ·
              refine ⟨37105475898506954387907203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24736983932337969591938135 37105475898506954387907203)
              ·
                refine ⟨55658213847760431581860805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37105475898506954387907203 55658213847760431581860805)
                ·
                  refine ⟨10435915096455080921598901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55658213847760431581860805 10435915096455080921598901)
                  ·
                    refine ⟨978367040292663836399897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10435915096455080921598901 978367040292663836399897)
                    ·
                      rfl

theorem cell23_5716089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_5716089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716089 prefixEnd_5716089 := by exact prefixLift 5716089
  have htrace : WordTrace (prefixWord ++ tailWord_5716089) baseStart_5716089 baseEnd_5716089 := by
    simpa [prefixWord, tailWord_5716089, baseEnd_5716089] using wordTrace_append hprefix tailTrace_5716089
  have hstable : (prefixWord ++ tailWord_5716089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716089).length < 2 ^ (prefixWord ++ tailWord_5716089).sum := by decide
  have hdescent : baseEnd_5716089 < baseStart_5716089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716093 : List Nat := [1, 4, 1, 1, 3, 3, 3, 2, 5]
def baseStart_5716093 : Nat := 118140960795 + 5716093 * 2 ^ 59
def prefixEnd_5716093 : Nat := 4983230072969 + 3 ^ 40 * 5716093 * 2
def baseEnd_5716093 : Nat := 326122574977845499283297

theorem tailTrace_5716093 : CollatzResearch.WordTrace tailWord_5716093 prefixEnd_5716093 326122574977845499283297 := by
  unfold tailWord_5716093
  simp only [CollatzResearch.WordTrace]
  refine ⟨208483039280578766807792933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138988692853719177871861955 208483039280578766807792933)
  ·
    refine ⟨39090569865108518776461175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208483039280578766807792933 39090569865108518776461175)
    ·
      refine ⟨58635854797662778164691763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39090569865108518776461175 58635854797662778164691763)
      ·
        refine ⟨87953782196494167247037645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58635854797662778164691763 87953782196494167247037645)
        ·
          refine ⟨32982668323685312717639117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87953782196494167247037645 32982668323685312717639117)
          ·
            refine ⟨12368500621381992269114669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32982668323685312717639117 12368500621381992269114669)
            ·
              refine ⟨4638187733018247100918001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12368500621381992269114669 4638187733018247100918001)
              ·
                refine ⟨3478640799763685325688501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4638187733018247100918001 3478640799763685325688501)
                ·
                  refine ⟨326122574977845499283297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3478640799763685325688501 326122574977845499283297)
                  ·
                    rfl

theorem cell23_5716093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_5716093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716093 prefixEnd_5716093 := by exact prefixLift 5716093
  have htrace : WordTrace (prefixWord ++ tailWord_5716093) baseStart_5716093 baseEnd_5716093 := by
    simpa [prefixWord, tailWord_5716093, baseEnd_5716093] using wordTrace_append hprefix tailTrace_5716093
  have hstable : (prefixWord ++ tailWord_5716093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716093).length < 2 ^ (prefixWord ++ tailWord_5716093).sum := by decide
  have hdescent : baseEnd_5716093 < baseStart_5716093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716099 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 5]
def baseStart_5716099 : Nat := 118140960795 + 5716099 * 2 ^ 59
def prefixEnd_5716099 : Nat := 4983230072969 + 3 ^ 40 * 5716099 * 2
def baseEnd_5716099 : Nat := 2935106255684536470074645

theorem tailTrace_5716099 : CollatzResearch.WordTrace tailWord_5716099 prefixEnd_5716099 2935106255684536470074645 := by
  unfold tailWord_5716099
  simp only [CollatzResearch.WordTrace]
  refine ⟨208483258118557029832511351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138988838745704686555007567 208483258118557029832511351)
  ·
    refine ⟨312724887177835544748767027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208483258118557029832511351 312724887177835544748767027)
    ·
      refine ⟨469087330766753317123150541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312724887177835544748767027 469087330766753317123150541)
      ·
        refine ⟨175907749037532493921181453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 469087330766753317123150541 175907749037532493921181453)
        ·
          refine ⟨65965405889074685220443045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175907749037532493921181453 65965405889074685220443045)
          ·
            refine ⟨12368513604201503478833071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65965405889074685220443045 12368513604201503478833071)
            ·
              refine ⟨18552770406302255218249607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12368513604201503478833071 18552770406302255218249607)
              ·
                refine ⟨27829155609453382827374411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18552770406302255218249607 27829155609453382827374411)
                ·
                  refine ⟨41743733414180074241061617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27829155609453382827374411 41743733414180074241061617)
                  ·
                    refine ⟨31307800060635055680796213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41743733414180074241061617 31307800060635055680796213)
                    ·
                      refine ⟨2935106255684536470074645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31307800060635055680796213 2935106255684536470074645)
                      ·
                        rfl

theorem cell23_5716099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_5716099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716099 prefixEnd_5716099 := by exact prefixLift 5716099
  have htrace : WordTrace (prefixWord ++ tailWord_5716099) baseStart_5716099 baseEnd_5716099 := by
    simpa [prefixWord, tailWord_5716099, baseEnd_5716099] using wordTrace_append hprefix tailTrace_5716099
  have hstable : (prefixWord ++ tailWord_5716099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716099).length < 2 ^ (prefixWord ++ tailWord_5716099).sum := by decide
  have hdescent : baseEnd_5716099 < baseStart_5716099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716146 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_5716146 : Nat := 118140960795 + 5716146 * 2 ^ 59
def prefixEnd_5716146 : Nat := 4983230072969 + 3 ^ 40 * 5716146 * 2
def baseEnd_5716146 : Nat := 2935130389275297786186929

theorem tailTrace_5716146 : CollatzResearch.WordTrace tailWord_5716146 prefixEnd_5716146 2935130389275297786186929 := by
  unfold tailWord_5716146
  simp only [CollatzResearch.WordTrace]
  refine ⟨52121243087346689214868073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138989981566257837906314861 52121243087346689214868073)
  ·
    refine ⟨39090932315510016911151055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52121243087346689214868073 39090932315510016911151055)
    ·
      refine ⟨58636398473265025366726583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39090932315510016911151055 58636398473265025366726583)
      ·
        refine ⟨87954597709897538050089875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58636398473265025366726583 87954597709897538050089875)
        ·
          refine ⟨131931896564846307075134813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87954597709897538050089875 131931896564846307075134813)
          ·
            refine ⟨49474461211817365153175555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131931896564846307075134813 49474461211817365153175555)
            ·
              refine ⟨74211691817726047729763333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49474461211817365153175555 74211691817726047729763333)
              ·
                refine ⟨13914692215823633949330625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74211691817726047729763333 13914692215823633949330625)
                ·
                  refine ⟨10436019161867725461997969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13914692215823633949330625 10436019161867725461997969)
                  ·
                    refine ⟨7827014371400794096498477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10436019161867725461997969 7827014371400794096498477)
                    ·
                      refine ⟨2935130389275297786186929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7827014371400794096498477 2935130389275297786186929)
                      ·
                        rfl

theorem cell23_5716146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_5716146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716146 prefixEnd_5716146 := by exact prefixLift 5716146
  have htrace : WordTrace (prefixWord ++ tailWord_5716146) baseStart_5716146 baseEnd_5716146 := by
    simpa [prefixWord, tailWord_5716146, baseEnd_5716146] using wordTrace_append hprefix tailTrace_5716146
  have hstable : (prefixWord ++ tailWord_5716146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716146).length < 2 ^ (prefixWord ++ tailWord_5716146).sum := by decide
  have hdescent : baseEnd_5716146 < baseStart_5716146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716153 : List Nat := [1, 2, 1, 4, 1, 2, 3, 4, 1, 4]
def baseStart_5716153 : Nat := 118140960795 + 5716153 * 2 ^ 59
def prefixEnd_5716153 : Nat := 4983230072969 + 3 ^ 40 * 5716153 * 2
def baseEnd_5716153 : Nat := 978377994546626419599799

theorem tailTrace_5716153 : CollatzResearch.WordTrace tailWord_5716153 prefixEnd_5716153 978377994546626419599799 := by
  unfold tailWord_5716153
  simp only [CollatzResearch.WordTrace]
  refine ⟨208485227660361397054977113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138990151773574264703318075 208485227660361397054977113)
  ·
    refine ⟨156363920745271047791232835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208485227660361397054977113 156363920745271047791232835)
    ·
      refine ⟨234545881117906571686849253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156363920745271047791232835 234545881117906571686849253)
      ·
        refine ⟨43977352709607482191284235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234545881117906571686849253 43977352709607482191284235)
        ·
          refine ⟨65966029064411223286926353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43977352709607482191284235 65966029064411223286926353)
          ·
            refine ⟨49474521798308417465194765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65966029064411223286926353 49474521798308417465194765)
            ·
              refine ⟨18552945674365656549448037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49474521798308417465194765 18552945674365656549448037)
              ·
                refine ⟨3478677313943560603021507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18552945674365656549448037 3478677313943560603021507)
                ·
                  refine ⟨5218015970915340904532261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478677313943560603021507 5218015970915340904532261)
                  ·
                    refine ⟨978377994546626419599799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5218015970915340904532261 978377994546626419599799)
                    ·
                      rfl

theorem cell23_5716153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 1, 4].length) (baseStart_5716153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716153 prefixEnd_5716153 := by exact prefixLift 5716153
  have htrace : WordTrace (prefixWord ++ tailWord_5716153) baseStart_5716153 baseEnd_5716153 := by
    simpa [prefixWord, tailWord_5716153, baseEnd_5716153] using wordTrace_append hprefix tailTrace_5716153
  have hstable : (prefixWord ++ tailWord_5716153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716153).length < 2 ^ (prefixWord ++ tailWord_5716153).sum := by decide
  have hdescent : baseEnd_5716153 < baseStart_5716153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716159 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 3]
def baseStart_5716159 : Nat := 118140960795 + 5716159 * 2 ^ 59
def prefixEnd_5716159 : Nat := 4983230072969 + 3 ^ 40 * 5716159 * 2
def baseEnd_5716159 : Nat := 2935137064523806235324369

theorem tailTrace_5716159 : CollatzResearch.WordTrace tailWord_5716159 prefixEnd_5716159 2935137064523806235324369 := by
  unfold tailWord_5716159
  simp only [CollatzResearch.WordTrace]
  refine ⟨208485446498339660079695531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138990297665559773386463687 208485446498339660079695531)
  ·
    refine ⟨312728169747509490119543297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208485446498339660079695531 312728169747509490119543297)
    ·
      refine ⟨234546127310632117589657473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312728169747509490119543297 234546127310632117589657473)
      ·
        refine ⟨175909595482974088192243105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234546127310632117589657473 175909595482974088192243105)
        ·
          refine ⟨131932196612230566144182329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175909595482974088192243105 131932196612230566144182329)
          ·
            refine ⟨98949147459172924608136747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131932196612230566144182329 98949147459172924608136747)
            ·
              refine ⟨148423721188759386912205121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98949147459172924608136747 148423721188759386912205121)
              ·
                refine ⟨111317790891569540184153841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148423721188759386912205121 111317790891569540184153841)
                ·
                  refine ⟨83488343168677155138115381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111317790891569540184153841 83488343168677155138115381)
                  ·
                    refine ⟨7827032172063483294198317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83488343168677155138115381 7827032172063483294198317)
                    ·
                      refine ⟨2935137064523806235324369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7827032172063483294198317 2935137064523806235324369)
                      ·
                        rfl

theorem cell23_5716159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_5716159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716159 prefixEnd_5716159 := by exact prefixLift 5716159
  have htrace : WordTrace (prefixWord ++ tailWord_5716159) baseStart_5716159 baseEnd_5716159 := by
    simpa [prefixWord, tailWord_5716159, baseEnd_5716159] using wordTrace_append hprefix tailTrace_5716159
  have hstable : (prefixWord ++ tailWord_5716159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716159).length < 2 ^ (prefixWord ++ tailWord_5716159).sum := by decide
  have hdescent : baseEnd_5716159 < baseStart_5716159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716209 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 3, 6]
def baseStart_5716209 : Nat := 118140960795 + 5716209 * 2 ^ 59
def prefixEnd_5716209 : Nat := 4983230072969 + 3 ^ 40 * 5716209 * 2
def baseEnd_5716209 : Nat := 978387579518843679899713

theorem tailTrace_5716209 : CollatzResearch.WordTrace tailWord_5716209 prefixEnd_5716209 978387579518843679899713 := by
  unfold tailWord_5716209
  simp only [CollatzResearch.WordTrace]
  refine ⟨208487270148158518619015681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138991513432105679079343787 208487270148158518619015681)
  ·
    refine ⟨156365452611118888964261761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208487270148158518619015681 156365452611118888964261761)
    ·
      refine ⟨117274089458339166723196321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156365452611118888964261761 117274089458339166723196321)
      ·
        refine ⟨87955567093754375042397241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117274089458339166723196321 87955567093754375042397241)
        ·
          refine ⟨65966675320315781281797931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87955567093754375042397241 65966675320315781281797931)
          ·
            refine ⟨98950012980473671922696897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65966675320315781281797931 98950012980473671922696897)
            ·
              refine ⟨74212509735355253942022673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98950012980473671922696897 74212509735355253942022673)
              ·
                refine ⟨55659382301516440456517005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74212509735355253942022673 55659382301516440456517005)
                ·
                  refine ⟨20872268363068665171193877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55659382301516440456517005 20872268363068665171193877)
                  ·
                    refine ⟨978387579518843679899713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20872268363068665171193877 978387579518843679899713)
                    ·
                      rfl

theorem cell23_5716209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_5716209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716209 prefixEnd_5716209 := by exact prefixLift 5716209
  have htrace : WordTrace (prefixWord ++ tailWord_5716209) baseStart_5716209 baseEnd_5716209 := by
    simpa [prefixWord, tailWord_5716209, baseEnd_5716209] using wordTrace_append hprefix tailTrace_5716209
  have hstable : (prefixWord ++ tailWord_5716209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716209).length < 2 ^ (prefixWord ++ tailWord_5716209).sum := by decide
  have hdescent : baseEnd_5716209 < baseStart_5716209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716210 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_5716210 : Nat := 118140960795 + 5716210 * 2 ^ 59
def prefixEnd_5716210 : Nat := 4983230072969 + 3 ^ 40 * 5716210 * 2
def baseEnd_5716210 : Nat := 2935163252037185535786635

theorem tailTrace_5716210 : CollatzResearch.WordTrace tailWord_5716210 prefixEnd_5716210 2935163252037185535786635 := by
  unfold tailWord_5716210
  simp only [CollatzResearch.WordTrace]
  refine ⟨52121826655288723947450521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138991537747436597193201389 52121826655288723947450521)
  ·
    refine ⟨39091369991466542960587891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52121826655288723947450521 39091369991466542960587891)
    ·
      refine ⟨58637054987199814440881837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39091369991466542960587891 58637054987199814440881837)
      ·
        refine ⟨21988895620199930415330689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58637054987199814440881837 21988895620199930415330689)
        ·
          refine ⟨16491671715149947811498017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21988895620199930415330689 16491671715149947811498017)
          ·
            refine ⟨12368753786362460858623513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16491671715149947811498017 12368753786362460858623513)
            ·
              refine ⟨9276565339771845643967635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12368753786362460858623513 9276565339771845643967635)
              ·
                refine ⟨13914848009657768465951453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9276565339771845643967635 13914848009657768465951453)
                ·
                  refine ⟨5218068003621663174731795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13914848009657768465951453 5218068003621663174731795)
                  ·
                    refine ⟨7827102005432494762097693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5218068003621663174731795 7827102005432494762097693)
                    ·
                      refine ⟨2935163252037185535786635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7827102005432494762097693 2935163252037185535786635)
                      ·
                        rfl

theorem cell23_5716210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_5716210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716210 prefixEnd_5716210 := by exact prefixLift 5716210
  have htrace : WordTrace (prefixWord ++ tailWord_5716210) baseStart_5716210 baseEnd_5716210 := by
    simpa [prefixWord, tailWord_5716210, baseEnd_5716210] using wordTrace_append hprefix tailTrace_5716210
  have hstable : (prefixWord ++ tailWord_5716210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716210).length < 2 ^ (prefixWord ++ tailWord_5716210).sum := by decide
  have hdescent : baseEnd_5716210 < baseStart_5716210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716233 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 4]
def baseStart_5716233 : Nat := 118140960795 + 5716233 * 2 ^ 59
def prefixEnd_5716233 : Nat := 4983230072969 + 3 ^ 40 * 5716233 * 2
def baseEnd_5716233 : Nat := 2935175062092238945799029

theorem tailTrace_5716233 : CollatzResearch.WordTrace tailWord_5716233 prefixEnd_5716233 2935175062092238945799029 := by
  unfold tailWord_5716233
  simp only [CollatzResearch.WordTrace]
  refine ⟨208488145500071570717889353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138992097000047713811926235 208488145500071570717889353)
  ·
    refine ⟨156366109125053678038417015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208488145500071570717889353 156366109125053678038417015)
    ·
      refine ⟨234549163687580517057625523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156366109125053678038417015 234549163687580517057625523)
      ·
        refine ⟨351823745531370775586438285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234549163687580517057625523 351823745531370775586438285)
        ·
          refine ⟨131933904574264040844914357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351823745531370775586438285 131933904574264040844914357)
          ·
            refine ⟨12368803553837253829210721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131933904574264040844914357 12368803553837253829210721)
            ·
              refine ⟨9276602665377940371908041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12368803553837253829210721 9276602665377940371908041)
              ·
                refine ⟨6957451999033455278931031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9276602665377940371908041 6957451999033455278931031)
                ·
                  refine ⟨10436177998550182918396547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6957451999033455278931031 10436177998550182918396547)
                  ·
                    refine ⟨15654266997825274377594821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10436177998550182918396547 15654266997825274377594821)
                    ·
                      refine ⟨2935175062092238945799029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15654266997825274377594821 2935175062092238945799029)
                      ·
                        rfl

theorem cell23_5716233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 4].length) (baseStart_5716233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716233 prefixEnd_5716233 := by exact prefixLift 5716233
  have htrace : WordTrace (prefixWord ++ tailWord_5716233) baseStart_5716233 baseEnd_5716233 := by
    simpa [prefixWord, tailWord_5716233, baseEnd_5716233] using wordTrace_append hprefix tailTrace_5716233
  have hstable : (prefixWord ++ tailWord_5716233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716233).length < 2 ^ (prefixWord ++ tailWord_5716233).sum := by decide
  have hdescent : baseEnd_5716233 < baseStart_5716233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716256 : List Nat := [2, 1, 1, 5, 2, 3, 9]
def baseStart_5716256 : Nat := 118140960795 + 5716256 * 2 ^ 59
def prefixEnd_5716256 : Nat := 4983230072969 + 3 ^ 40 * 5716256 * 2
def baseEnd_5716256 : Nat := 36236874964781387108783

theorem tailTrace_5716256 : CollatzResearch.WordTrace tailWord_5716256 prefixEnd_5716256 36236874964781387108783 := by
  unfold tailWord_5716256
  simp only [CollatzResearch.WordTrace]
  refine ⟨104244492189494122822988311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138992656252658830430651081 104244492189494122822988311)
  ·
    refine ⟨156366738284241184234482467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104244492189494122822988311 156366738284241184234482467)
    ·
      refine ⟨234550107426361776351723701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156366738284241184234482467 234550107426361776351723701)
      ·
        refine ⟨21989072571221416532974097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234550107426361776351723701 21989072571221416532974097)
        ·
          refine ⟨16491804428416062399730573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21989072571221416532974097 16491804428416062399730573)
          ·
            refine ⟨6184426660656023399898965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16491804428416062399730573 6184426660656023399898965)
            ·
              refine ⟨36236874964781387108783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6184426660656023399898965 36236874964781387108783)
              ·
                rfl

theorem cell23_5716256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 9].length) (baseStart_5716256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716256 prefixEnd_5716256 := by exact prefixLift 5716256
  have htrace : WordTrace (prefixWord ++ tailWord_5716256) baseStart_5716256 baseEnd_5716256 := by
    simpa [prefixWord, tailWord_5716256, baseEnd_5716256] using wordTrace_append hprefix tailTrace_5716256
  have hstable : (prefixWord ++ tailWord_5716256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716256).length < 2 ^ (prefixWord ++ tailWord_5716256).sum := by decide
  have hdescent : baseEnd_5716256 < baseStart_5716256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716299 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 3, 8]
def baseStart_5716299 : Nat := 118140960795 + 5716299 * 2 ^ 59
def prefixEnd_5716299 : Nat := 4983230072969 + 3 ^ 40 * 5716299 * 2
def baseEnd_5716299 : Nat := 978402983938478562524575

theorem tailTrace_5716299 : CollatzResearch.WordTrace tailWord_5716299 prefixEnd_5716299 978402983938478562524575 := by
  unfold tailWord_5716299
  simp only [CollatzResearch.WordTrace]
  refine ⟨208490552717832463989791951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138993701811888309326527967 208490552717832463989791951)
  ·
    refine ⟨312735829076748695984687927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208490552717832463989791951 312735829076748695984687927)
    ·
      refine ⟨469103743615123043977031891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312735829076748695984687927 469103743615123043977031891)
      ·
        refine ⟨703655615422684565965547837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469103743615123043977031891 703655615422684565965547837)
        ·
          refine ⟨263870855783506712237080439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 703655615422684565965547837 263870855783506712237080439)
          ·
            refine ⟨395806283675260068355620659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263870855783506712237080439 395806283675260068355620659)
            ·
              refine ⟨593709425512890102533430989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395806283675260068355620659 593709425512890102533430989)
              ·
                refine ⟨222641034567333788450036621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 593709425512890102533430989 222641034567333788450036621)
                ·
                  refine ⟨83490387962750170668763733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222641034567333788450036621 83490387962750170668763733)
                  ·
                    refine ⟨978402983938478562524575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83490387962750170668763733 978402983938478562524575)
                    ·
                      rfl

theorem cell23_5716299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 8].length) (baseStart_5716299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716299 prefixEnd_5716299 := by exact prefixLift 5716299
  have htrace : WordTrace (prefixWord ++ tailWord_5716299) baseStart_5716299 baseEnd_5716299 := by
    simpa [prefixWord, tailWord_5716299, baseEnd_5716299] using wordTrace_append hprefix tailTrace_5716299
  have hstable : (prefixWord ++ tailWord_5716299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716299).length < 2 ^ (prefixWord ++ tailWord_5716299).sum := by decide
  have hdescent : baseEnd_5716299 < baseStart_5716299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716323 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 3, 4, 2]
def baseStart_5716323 : Nat := 118140960795 + 5716323 * 2 ^ 59
def prefixEnd_5716323 : Nat := 4983230072969 + 3 ^ 40 * 5716323 * 2
def baseEnd_5716323 : Nat := 2935221275351143593673615

theorem tailTrace_5716323 : CollatzResearch.WordTrace tailWord_5716323 prefixEnd_5716323 2935221275351143593673615 := by
  unfold tailWord_5716323
  simp only [CollatzResearch.WordTrace]
  refine ⟨208491428069745516088665623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138994285379830344059110415 208491428069745516088665623)
  ·
    refine ⟨312737142104618274132998435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208491428069745516088665623 312737142104618274132998435)
    ·
      refine ⟨469105713156927411199497653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312737142104618274132998435 469105713156927411199497653)
      ·
        refine ⟨43978660608461944799952905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 469105713156927411199497653 43978660608461944799952905)
        ·
          refine ⟨32983995456346458599964679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43978660608461944799952905 32983995456346458599964679)
          ·
            refine ⟨49475993184519687899947019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32983995456346458599964679 49475993184519687899947019)
            ·
              refine ⟨74213989776779531849920529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49475993184519687899947019 74213989776779531849920529)
              ·
                refine ⟨55660492332584648887440397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74213989776779531849920529 55660492332584648887440397)
                ·
                  refine ⟨20872684624719243332790149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55660492332584648887440397 20872684624719243332790149)
                  ·
                    refine ⟨3913628367134858124898153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20872684624719243332790149 3913628367134858124898153)
                    ·
                      refine ⟨2935221275351143593673615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913628367134858124898153 2935221275351143593673615)
                      ·
                        rfl

theorem cell23_5716323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_5716323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716323 prefixEnd_5716323 := by exact prefixLift 5716323
  have htrace : WordTrace (prefixWord ++ tailWord_5716323) baseStart_5716323 baseEnd_5716323 := by
    simpa [prefixWord, tailWord_5716323, baseEnd_5716323] using wordTrace_append hprefix tailTrace_5716323
  have hstable : (prefixWord ++ tailWord_5716323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716323).length < 2 ^ (prefixWord ++ tailWord_5716323).sum := by decide
  have hdescent : baseEnd_5716323 < baseStart_5716323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716336 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_5716336 : Nat := 118140960795 + 5716336 * 2 ^ 59
def prefixEnd_5716336 : Nat := 4983230072969 + 3 ^ 40 * 5716336 * 2
def baseEnd_5716336 : Nat := 2935227950599652042811055

theorem tailTrace_5716336 : CollatzResearch.WordTrace tailWord_5716336 prefixEnd_5716336 2935227950599652042811055 := by
  unfold tailWord_5716336
  simp only [CollatzResearch.WordTrace]
  refine ⟨104245951109349209654444431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138994601479132279539259241 104245951109349209654444431)
  ·
    refine ⟨156368926664023814481666647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104245951109349209654444431 156368926664023814481666647)
    ·
      refine ⟨234553389996035721722499971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156368926664023814481666647 234553389996035721722499971)
      ·
        refine ⟨351830084994053582583749957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234553389996035721722499971 351830084994053582583749957)
        ·
          refine ⟨65968140936385046734453117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 351830084994053582583749957 65968140936385046734453117)
          ·
            refine ⟨24738052851144392525419919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65968140936385046734453117 24738052851144392525419919)
            ·
              refine ⟨37107079276716588788129879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24738052851144392525419919 37107079276716588788129879)
              ·
                refine ⟨55660618915074883182194819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37107079276716588788129879 55660618915074883182194819)
                ·
                  refine ⟨83490928372612324773292229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55660618915074883182194819 83490928372612324773292229)
                  ·
                    refine ⟨15654549069864810894992293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83490928372612324773292229 15654549069864810894992293)
                    ·
                      refine ⟨2935227950599652042811055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15654549069864810894992293 2935227950599652042811055)
                      ·
                        rfl

theorem cell23_5716336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_5716336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716336 prefixEnd_5716336 := by exact prefixLift 5716336
  have htrace : WordTrace (prefixWord ++ tailWord_5716336) baseStart_5716336 baseEnd_5716336 := by
    simpa [prefixWord, tailWord_5716336, baseEnd_5716336] using wordTrace_append hprefix tailTrace_5716336
  have hstable : (prefixWord ++ tailWord_5716336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716336).length < 2 ^ (prefixWord ++ tailWord_5716336).sum := by decide
  have hdescent : baseEnd_5716336 < baseStart_5716336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716363 : List Nat := [1, 1, 1, 1, 4, 4, 1, 5, 5]
def baseStart_5716363 : Nat := 118140960795 + 5716363 * 2 ^ 59
def prefixEnd_5716363 : Nat := 4983230072969 + 3 ^ 40 * 5716363 * 2
def baseEnd_5716363 : Nat := 326137979397480381908159

theorem tailTrace_5716363 : CollatzResearch.WordTrace tailWord_5716363 prefixEnd_5716363 326137979397480381908159 := by
  unfold tailWord_5716363
  simp only [CollatzResearch.WordTrace]
  refine ⟨208492886989600602920121743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138995257993067068613414495 208492886989600602920121743)
  ·
    refine ⟨312739330484400904380182615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208492886989600602920121743 312739330484400904380182615)
    ·
      refine ⟨469108995726601356570273923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312739330484400904380182615 469108995726601356570273923)
      ·
        refine ⟨703663493589902034855410885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469108995726601356570273923 703663493589902034855410885)
        ·
          refine ⟨131936905048106631535389541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 703663493589902034855410885 131936905048106631535389541)
          ·
            refine ⟨24738169696519993412885539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131936905048106631535389541 24738169696519993412885539)
            ·
              refine ⟨37107254544779990119328309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24738169696519993412885539 37107254544779990119328309)
              ·
                refine ⟨3478805113573124073687029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37107254544779990119328309 3478805113573124073687029)
                ·
                  refine ⟨326137979397480381908159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3478805113573124073687029 326137979397480381908159)
                  ·
                    rfl

theorem cell23_5716363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 5].length) (baseStart_5716363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716363 prefixEnd_5716363 := by exact prefixLift 5716363
  have htrace : WordTrace (prefixWord ++ tailWord_5716363) baseStart_5716363 baseEnd_5716363 := by
    simpa [prefixWord, tailWord_5716363, baseEnd_5716363] using wordTrace_append hprefix tailTrace_5716363
  have hstable : (prefixWord ++ tailWord_5716363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716363).length < 2 ^ (prefixWord ++ tailWord_5716363).sum := by decide
  have hdescent : baseEnd_5716363 < baseStart_5716363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716413 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_5716413 : Nat := 118140960795 + 5716413 * 2 ^ 59
def prefixEnd_5716413 : Nat := 4983230072969 + 3 ^ 40 * 5716413 * 2
def baseEnd_5716413 : Nat := 2935267488610048241548201

theorem tailTrace_5716413 : CollatzResearch.WordTrace tailWord_5716413 prefixEnd_5716413 2935267488610048241548201 := by
  unfold tailWord_5716413
  simp only [CollatzResearch.WordTrace]
  refine ⟨208494710639419461459441893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138996473759612974306294595 208494710639419461459441893)
  ·
    refine ⟨39092758244891149023645355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208494710639419461459441893 39092758244891149023645355)
    ·
      refine ⟨58639137367336723535468033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39092758244891149023645355 58639137367336723535468033)
      ·
        refine ⟨43979353025502542651601025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58639137367336723535468033 43979353025502542651601025)
        ·
          refine ⟨32984514769126906988700769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43979353025502542651601025 32984514769126906988700769)
          ·
            refine ⟨24738386076845180241525577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32984514769126906988700769 24738386076845180241525577)
            ·
              refine ⟨18553789557633885181144183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24738386076845180241525577 18553789557633885181144183)
              ·
                refine ⟨27830684336450827771716275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18553789557633885181144183 27830684336450827771716275)
                ·
                  refine ⟨41746026504676241657574413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27830684336450827771716275 41746026504676241657574413)
                  ·
                    refine ⟨15654759939253590621590405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41746026504676241657574413 15654759939253590621590405)
                    ·
                      refine ⟨2935267488610048241548201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15654759939253590621590405 2935267488610048241548201)
                      ·
                        rfl

theorem cell23_5716413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_5716413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716413 prefixEnd_5716413 := by exact prefixLift 5716413
  have htrace : WordTrace (prefixWord ++ tailWord_5716413) baseStart_5716413 baseEnd_5716413 := by
    simpa [prefixWord, tailWord_5716413, baseEnd_5716413] using wordTrace_append hprefix tailTrace_5716413
  have hstable : (prefixWord ++ tailWord_5716413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716413).length < 2 ^ (prefixWord ++ tailWord_5716413).sum := by decide
  have hdescent : baseEnd_5716413 < baseStart_5716413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716416 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_5716416 : Nat := 118140960795 + 5716416 * 2 ^ 59
def prefixEnd_5716416 : Nat := 4983230072969 + 3 ^ 40 * 5716416 * 2
def baseEnd_5716416 : Nat := 2935269029052011729810687

theorem tailTrace_5716416 : CollatzResearch.WordTrace tailWord_5716416 prefixEnd_5716416 2935269029052011729810687 := by
  unfold tailWord_5716416
  simp only [CollatzResearch.WordTrace]
  refine ⟨104247410029204296485900551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138996546705605728647867401 104247410029204296485900551)
  ·
    refine ⟨156371115043806444728850827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104247410029204296485900551 156371115043806444728850827)
    ·
      refine ⟨234556672565709667093276241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156371115043806444728850827 234556672565709667093276241)
      ·
        refine ⟨175917504424282250319957181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234556672565709667093276241 175917504424282250319957181)
        ·
          refine ⟨65969064159105843869983943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175917504424282250319957181 65969064159105843869983943)
          ·
            refine ⟨98953596238658765804975915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65969064159105843869983943 98953596238658765804975915)
            ·
              refine ⟨148430394357988148707463873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98953596238658765804975915 148430394357988148707463873)
              ·
                refine ⟨111322795768491111530597905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148430394357988148707463873 111322795768491111530597905)
                ·
                  refine ⟨83492096826368333647948429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111322795768491111530597905 83492096826368333647948429)
                  ·
                    refine ⟨31309536309888125117980661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83492096826368333647948429 31309536309888125117980661)
                    ·
                      refine ⟨2935269029052011729810687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31309536309888125117980661 2935269029052011729810687)
                      ·
                        rfl

theorem cell23_5716416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_5716416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716416 prefixEnd_5716416 := by exact prefixLift 5716416
  have htrace : WordTrace (prefixWord ++ tailWord_5716416) baseStart_5716416 baseEnd_5716416 := by
    simpa [prefixWord, tailWord_5716416, baseEnd_5716416] using wordTrace_append hprefix tailTrace_5716416
  have hstable : (prefixWord ++ tailWord_5716416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716416).length < 2 ^ (prefixWord ++ tailWord_5716416).sum := by decide
  have hdescent : baseEnd_5716416 < baseStart_5716416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716534 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_5716534 : Nat := 118140960795 + 5716534 * 2 ^ 59
def prefixEnd_5716534 : Nat := 4983230072969 + 3 ^ 40 * 5716534 * 2
def baseEnd_5716534 : Nat := 978443206589747422711715

theorem tailTrace_5716534 : CollatzResearch.WordTrace tailWord_5716534 prefixEnd_5716534 978443206589747422711715 := by
  unfold tailWord_5716534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13031195241998818695287291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138999415914654066083064437 13031195241998818695287291)
  ·
    refine ⟨19546792862998228042930937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13031195241998818695287291 19546792862998228042930937)
    ·
      refine ⟨14660094647248671032198203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19546792862998228042930937 14660094647248671032198203)
      ·
        refine ⟨21990141970873006548297305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14660094647248671032198203 21990141970873006548297305)
        ·
          refine ⟨16492606478154754911222979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21990141970873006548297305 16492606478154754911222979)
          ·
            refine ⟨24738909717232132366834469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16492606478154754911222979 24738909717232132366834469)
            ·
              refine ⟨4638545571981024818781463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24738909717232132366834469 4638545571981024818781463)
              ·
                refine ⟨6957818357971537228172195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4638545571981024818781463 6957818357971537228172195)
                ·
                  refine ⟨10436727536957305842258293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6957818357971537228172195 10436727536957305842258293)
                  ·
                    refine ⟨978443206589747422711715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10436727536957305842258293 978443206589747422711715)
                    ·
                      rfl

theorem cell23_5716534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_5716534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716534 prefixEnd_5716534 := by exact prefixLift 5716534
  have htrace : WordTrace (prefixWord ++ tailWord_5716534) baseStart_5716534 baseEnd_5716534 := by
    simpa [prefixWord, tailWord_5716534, baseEnd_5716534] using wordTrace_append hprefix tailTrace_5716534
  have hstable : (prefixWord ++ tailWord_5716534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716534).length < 2 ^ (prefixWord ++ tailWord_5716534).sum := by decide
  have hdescent : baseEnd_5716534 < baseStart_5716534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716537 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 5, 2, 2]
def baseStart_5716537 : Nat := 118140960795 + 5716537 * 2 ^ 59
def prefixEnd_5716537 : Nat := 4983230072969 + 3 ^ 40 * 5716537 * 2
def baseEnd_5716537 : Nat := 2935331160211205756397631

theorem tailTrace_5716537 : CollatzResearch.WordTrace tailWord_5716537 prefixEnd_5716537 2935331160211205756397631 := by
  unfold tailWord_5716537
  simp only [CollatzResearch.WordTrace]
  refine ⟨208499233290970230636955865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138999488860646820424637243 208499233290970230636955865)
  ·
    refine ⟨156374424968227672977716899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208499233290970230636955865 156374424968227672977716899)
    ·
      refine ⟨234561637452341509466575349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156374424968227672977716899 234561637452341509466575349)
      ·
        refine ⟨21990153511157016512491439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234561637452341509466575349 21990153511157016512491439)
        ·
          refine ⟨32985230266735524768737159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21990153511157016512491439 32985230266735524768737159)
          ·
            refine ⟨49477845400103287153105739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32985230266735524768737159 49477845400103287153105739)
            ·
              refine ⟨74216768100154930729658609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49477845400103287153105739 74216768100154930729658609)
              ·
                refine ⟨55662576075116198047243957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74216768100154930729658609 55662576075116198047243957)
                ·
                  refine ⟨5218366507042143566929121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55662576075116198047243957 5218366507042143566929121)
                  ·
                    refine ⟨3913774880281607675196841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5218366507042143566929121 3913774880281607675196841)
                    ·
                      refine ⟨2935331160211205756397631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913774880281607675196841 2935331160211205756397631)
                      ·
                        rfl

theorem cell23_5716537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_5716537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716537 prefixEnd_5716537 := by exact prefixLift 5716537
  have htrace : WordTrace (prefixWord ++ tailWord_5716537) baseStart_5716537 baseEnd_5716537 := by
    simpa [prefixWord, tailWord_5716537, baseEnd_5716537] using wordTrace_append hprefix tailTrace_5716537
  have hstable : (prefixWord ++ tailWord_5716537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716537).length < 2 ^ (prefixWord ++ tailWord_5716537).sum := by decide
  have hdescent : baseEnd_5716537 < baseStart_5716537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716548 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_5716548 : Nat := 118140960795 + 5716548 * 2 ^ 59
def prefixEnd_5716548 : Nat := 4983230072969 + 3 ^ 40 * 5716548 * 2
def baseEnd_5716548 : Nat := 2935336808498405213360081

theorem tailTrace_5716548 : CollatzResearch.WordTrace tailWord_5716548 prefixEnd_5716548 2935336808498405213360081 := by
  unfold tailWord_5716548
  simp only [CollatzResearch.WordTrace]
  refine ⟨104249817246965189757803149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138999756329286919677070865 104249817246965189757803149)
  ·
    refine ⟨39093681467611946159176181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104249817246965189757803149 39093681467611946159176181)
    ·
      refine ⟨3665032637588619952422767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39093681467611946159176181 3665032637588619952422767)
      ·
        refine ⟨5497548956382929928634151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665032637588619952422767 5497548956382929928634151)
        ·
          refine ⟨8246323434574394892951227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497548956382929928634151 8246323434574394892951227)
          ·
            refine ⟨12369485151861592339426841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8246323434574394892951227 12369485151861592339426841)
            ·
              refine ⟨9277113863896194254570131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12369485151861592339426841 9277113863896194254570131)
              ·
                refine ⟨13915670795844291381855197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9277113863896194254570131 13915670795844291381855197)
                ·
                  refine ⟨5218376548441609268195699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13915670795844291381855197 5218376548441609268195699)
                  ·
                    refine ⟨7827564822662413902293549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5218376548441609268195699 7827564822662413902293549)
                    ·
                      refine ⟨2935336808498405213360081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7827564822662413902293549 2935336808498405213360081)
                      ·
                        rfl

theorem cell23_5716548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_5716548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716548 prefixEnd_5716548 := by exact prefixLift 5716548
  have htrace : WordTrace (prefixWord ++ tailWord_5716548) baseStart_5716548 baseEnd_5716548 := by
    simpa [prefixWord, tailWord_5716548, baseEnd_5716548] using wordTrace_append hprefix tailTrace_5716548
  have hstable : (prefixWord ++ tailWord_5716548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716548).length < 2 ^ (prefixWord ++ tailWord_5716548).sum := by decide
  have hdescent : baseEnd_5716548 < baseStart_5716548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716553 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 2, 7, 3]
def baseStart_5716553 : Nat := 118140960795 + 5716553 * 2 ^ 59
def prefixEnd_5716553 : Nat := 4983230072969 + 3 ^ 40 * 5716553 * 2
def baseEnd_5716553 : Nat := 2935339375901677693797557

theorem tailTrace_5716553 : CollatzResearch.WordTrace tailWord_5716553 prefixEnd_5716553 2935339375901677693797557 := by
  unfold tailWord_5716553
  simp only [CollatzResearch.WordTrace]
  refine ⟨208499816858912265369538313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138999877905941510246358875 208499816858912265369538313)
  ·
    refine ⟨156374862644184199027153735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208499816858912265369538313 156374862644184199027153735)
    ·
      refine ⟨234562293966276298540730603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156374862644184199027153735 234562293966276298540730603)
      ·
        refine ⟨351843440949414447811095905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234562293966276298540730603 351843440949414447811095905)
        ·
          refine ⟨263882580712060835858321929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351843440949414447811095905 263882580712060835858321929)
          ·
            refine ⟨197911935534045626893741447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263882580712060835858321929 197911935534045626893741447)
            ·
              refine ⟨296867903301068440340612171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197911935534045626893741447 296867903301068440340612171)
              ·
                refine ⟨445301854951602660510918257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296867903301068440340612171 445301854951602660510918257)
                ·
                  refine ⟨333976391213701995383188693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445301854951602660510918257 333976391213701995383188693)
                  ·
                    refine ⟨7827571669071140516793485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 333976391213701995383188693 7827571669071140516793485)
                    ·
                      refine ⟨2935339375901677693797557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7827571669071140516793485 2935339375901677693797557)
                      ·
                        rfl

theorem cell23_5716553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7, 3].length) (baseStart_5716553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716553 prefixEnd_5716553 := by exact prefixLift 5716553
  have htrace : WordTrace (prefixWord ++ tailWord_5716553) baseStart_5716553 baseEnd_5716553 := by
    simpa [prefixWord, tailWord_5716553, baseEnd_5716553] using wordTrace_append hprefix tailTrace_5716553
  have hstable : (prefixWord ++ tailWord_5716553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716553).length < 2 ^ (prefixWord ++ tailWord_5716553).sum := by decide
  have hdescent : baseEnd_5716553 < baseStart_5716553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716554 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2]
def baseStart_5716554 : Nat := 118140960795 + 5716554 * 2 ^ 59
def prefixEnd_5716554 : Nat := 4983230072969 + 3 ^ 40 * 5716554 * 2
def baseEnd_5716554 : Nat := 2935339889382332189885053

theorem tailTrace_5716554 : CollatzResearch.WordTrace tailWord_5716554 prefixEnd_5716554 2935339889382332189885053 := by
  unfold tailWord_5716554
  simp only [CollatzResearch.WordTrace]
  refine ⟨52124963332977160635081179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138999902221272428360216477 52124963332977160635081179)
  ·
    refine ⟨78187444999465740952621769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52124963332977160635081179 78187444999465740952621769)
    ·
      refine ⟨58640583749599305714466327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78187444999465740952621769 58640583749599305714466327)
      ·
        refine ⟨87960875624398958571699491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58640583749599305714466327 87960875624398958571699491)
        ·
          refine ⟨131941313436598437857549237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87960875624398958571699491 131941313436598437857549237)
          ·
            refine ⟨12369498134681103549145241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131941313436598437857549237 12369498134681103549145241)
            ·
              refine ⟨9277123601010827661858931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12369498134681103549145241 9277123601010827661858931)
              ·
                refine ⟨13915685401516241492788397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9277123601010827661858931 13915685401516241492788397)
                ·
                  refine ⟨5218382025568590559795649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13915685401516241492788397 5218382025568590559795649)
                  ·
                    refine ⟨3913786519176442919846737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5218382025568590559795649 3913786519176442919846737)
                    ·
                      refine ⟨2935339889382332189885053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913786519176442919846737 2935339889382332189885053)
                      ·
                        rfl

theorem cell23_5716554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_5716554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716554 prefixEnd_5716554 := by exact prefixLift 5716554
  have htrace : WordTrace (prefixWord ++ tailWord_5716554) baseStart_5716554 baseEnd_5716554 := by
    simpa [prefixWord, tailWord_5716554, baseEnd_5716554] using wordTrace_append hprefix tailTrace_5716554
  have hstable : (prefixWord ++ tailWord_5716554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716554).length < 2 ^ (prefixWord ++ tailWord_5716554).sum := by decide
  have hdescent : baseEnd_5716554 < baseStart_5716554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716557 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_5716557 : Nat := 118140960795 + 5716557 * 2 ^ 59
def prefixEnd_5716557 : Nat := 4983230072969 + 3 ^ 40 * 5716557 * 2
def baseEnd_5716557 : Nat := 2935341429824295678147539

theorem tailTrace_5716557 : CollatzResearch.WordTrace tailWord_5716557 prefixEnd_5716557 2935341429824295678147539 := by
  unfold tailWord_5716557
  simp only [CollatzResearch.WordTrace]
  refine ⟨208499962750897774052683925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138999975167265182701789283 208499962750897774052683925)
  ·
    refine ⟨9773435753948333158719559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 208499962750897774052683925 9773435753948333158719559)
    ·
      refine ⟨14660153630922499738079339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9773435753948333158719559 14660153630922499738079339)
      ·
        refine ⟨21990230446383749607119009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14660153630922499738079339 21990230446383749607119009)
        ·
          refine ⟨16492672834787812205339257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21990230446383749607119009 16492672834787812205339257)
          ·
            refine ⟨12369504626090859154004443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16492672834787812205339257 12369504626090859154004443)
            ·
              refine ⟨18554256939136288731006665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12369504626090859154004443 18554256939136288731006665)
              ·
                refine ⟨13915692704352216548254999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18554256939136288731006665 13915692704352216548254999)
                ·
                  refine ⟨20873539056528324822382499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13915692704352216548254999 20873539056528324822382499)
                  ·
                    refine ⟨31310308584792487233573749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20873539056528324822382499 31310308584792487233573749)
                    ·
                      refine ⟨2935341429824295678147539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31310308584792487233573749 2935341429824295678147539)
                      ·
                        rfl

theorem cell23_5716557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_5716557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716557 prefixEnd_5716557 := by exact prefixLift 5716557
  have htrace : WordTrace (prefixWord ++ tailWord_5716557) baseStart_5716557 baseEnd_5716557 := by
    simpa [prefixWord, tailWord_5716557, baseEnd_5716557] using wordTrace_append hprefix tailTrace_5716557
  have hstable : (prefixWord ++ tailWord_5716557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716557).length < 2 ^ (prefixWord ++ tailWord_5716557).sum := by decide
  have hdescent : baseEnd_5716557 < baseStart_5716557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716564 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_5716564 : Nat := 118140960795 + 5716564 * 2 ^ 59
def prefixEnd_5716564 : Nat := 4983230072969 + 3 ^ 40 * 5716564 * 2
def baseEnd_5716564 : Nat := 978448341396292383586669

theorem tailTrace_5716564 : CollatzResearch.WordTrace tailWord_5716564 prefixEnd_5716564 978448341396292383586669 := by
  unfold tailWord_5716564
  simp only [CollatzResearch.WordTrace]
  refine ⟨104250109030936207124094373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139000145374581609498792497 104250109030936207124094373)
  ·
    refine ⟨19546895443300538835767695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104250109030936207124094373 19546895443300538835767695)
    ·
      refine ⟨29320343164950808253651543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19546895443300538835767695 29320343164950808253651543)
      ·
        refine ⟨43980514747426212380477315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29320343164950808253651543 43980514747426212380477315)
        ·
          refine ⟨65970772121139318570715973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43980514747426212380477315 65970772121139318570715973)
          ·
            refine ⟨12369519772713622232009245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65970772121139318570715973 12369519772713622232009245)
            ·
              refine ⟨4638569914767608337003467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12369519772713622232009245 4638569914767608337003467)
              ·
                refine ⟨6957854872151412505505201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4638569914767608337003467 6957854872151412505505201)
                ·
                  refine ⟨5218391154113559379128901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6957854872151412505505201 5218391154113559379128901)
                  ·
                    refine ⟨978448341396292383586669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5218391154113559379128901 978448341396292383586669)
                    ·
                      rfl

theorem cell23_5716564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_5716564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716564 prefixEnd_5716564 := by exact prefixLift 5716564
  have htrace : WordTrace (prefixWord ++ tailWord_5716564) baseStart_5716564 baseEnd_5716564 := by
    simpa [prefixWord, tailWord_5716564, baseEnd_5716564] using wordTrace_append hprefix tailTrace_5716564
  have hstable : (prefixWord ++ tailWord_5716564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716564).length < 2 ^ (prefixWord ++ tailWord_5716564).sum := by decide
  have hdescent : baseEnd_5716564 < baseStart_5716564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716593 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_5716593 : Nat := 118140960795 + 5716593 * 2 ^ 59
def prefixEnd_5716593 : Nat := 4983230072969 + 3 ^ 40 * 5716593 * 2
def baseEnd_5716593 : Nat := 2935359915127857537297373

theorem tailTrace_5716593 : CollatzResearch.WordTrace tailWord_5716593 prefixEnd_5716593 2935359915127857537297373 := by
  unfold tailWord_5716593
  simp only [CollatzResearch.WordTrace]
  refine ⟨208501275778767352200994433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139000850519178234800662955 208501275778767352200994433)
  ·
    refine ⟨156375956834075514150745825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208501275778767352200994433 156375956834075514150745825)
    ·
      refine ⟨117281967625556635613059369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156375956834075514150745825 117281967625556635613059369)
      ·
        refine ⟨87961475719167476709794527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117281967625556635613059369 87961475719167476709794527)
        ·
          refine ⟨131942213578751215064691791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87961475719167476709794527 131942213578751215064691791)
          ·
            refine ⟨197913320368126822597037687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131942213578751215064691791 197913320368126822597037687)
            ·
              refine ⟨296869980552190233895556531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197913320368126822597037687 296869980552190233895556531)
              ·
                refine ⟨445304970828285350843334797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296869980552190233895556531 445304970828285350843334797)
                ·
                  refine ⟨166989364060607006566250549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445304970828285350843334797 166989364060607006566250549)
                  ·
                    refine ⟨15655252880681906865585989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 166989364060607006566250549 15655252880681906865585989)
                    ·
                      refine ⟨2935359915127857537297373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15655252880681906865585989 2935359915127857537297373)
                      ·
                        rfl

theorem cell23_5716593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_5716593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716593 prefixEnd_5716593 := by exact prefixLift 5716593
  have htrace : WordTrace (prefixWord ++ tailWord_5716593) baseStart_5716593 baseEnd_5716593 := by
    simpa [prefixWord, tailWord_5716593, baseEnd_5716593] using wordTrace_append hprefix tailTrace_5716593
  have hstable : (prefixWord ++ tailWord_5716593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716593).length < 2 ^ (prefixWord ++ tailWord_5716593).sum := by decide
  have hdescent : baseEnd_5716593 < baseStart_5716593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716603 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 2, 6]
def baseStart_5716603 : Nat := 118140960795 + 5716603 * 2 ^ 59
def prefixEnd_5716603 : Nat := 4983230072969 + 3 ^ 40 * 5716603 * 2
def baseEnd_5716603 : Nat := 978455016644800832724109

theorem tailTrace_5716603 : CollatzResearch.WordTrace tailWord_5716603 prefixEnd_5716603 978455016644800832724109 := by
  unfold tailWord_5716603
  simp only [CollatzResearch.WordTrace]
  refine ⟨208501640508731123908858463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139001093672487415939238975 208501640508731123908858463)
  ·
    refine ⟨312752460763096685863287695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208501640508731123908858463 312752460763096685863287695)
    ·
      refine ⟨469128691144645028794931543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312752460763096685863287695 469128691144645028794931543)
      ·
        refine ⟨703693036716967543192397315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469128691144645028794931543 703693036716967543192397315)
        ·
          refine ⟨1055539555075451314788595973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703693036716967543192397315 1055539555075451314788595973)
          ·
            refine ⟨197913666576647121522861745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1055539555075451314788595973 197913666576647121522861745)
            ·
              refine ⟨148435249932485341142146309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197913666576647121522861745 148435249932485341142146309)
              ·
                refine ⟨27831609362341001464152433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148435249932485341142146309 27831609362341001464152433)
                ·
                  refine ⟨20873707021755751098114325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27831609362341001464152433 20873707021755751098114325)
                  ·
                    refine ⟨978455016644800832724109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20873707021755751098114325 978455016644800832724109)
                    ·
                      rfl

theorem cell23_5716603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 6].length) (baseStart_5716603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716603 prefixEnd_5716603 := by exact prefixLift 5716603
  have htrace : WordTrace (prefixWord ++ tailWord_5716603) baseStart_5716603 baseEnd_5716603 := by
    simpa [prefixWord, tailWord_5716603, baseEnd_5716603] using wordTrace_append hprefix tailTrace_5716603
  have hstable : (prefixWord ++ tailWord_5716603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716603).length < 2 ^ (prefixWord ++ tailWord_5716603).sum := by decide
  have hdescent : baseEnd_5716603 < baseStart_5716603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716633 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 9]
def baseStart_5716633 : Nat := 118140960795 + 5716633 * 2 ^ 59
def prefixEnd_5716633 : Nat := 4983230072969 + 3 ^ 40 * 5716633 * 2
def baseEnd_5716633 : Nat := 326153383817115264533021

theorem tailTrace_5716633 : CollatzResearch.WordTrace tailWord_5716633 prefixEnd_5716633 326153383817115264533021 := by
  unfold tailWord_5716633
  simp only [CollatzResearch.WordTrace]
  refine ⟨208502734698622439032450553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139001823132414959354967035 208502734698622439032450553)
  ·
    refine ⟨156377051023966829274337915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208502734698622439032450553 156377051023966829274337915)
    ·
      refine ⟨234565576535950243911506873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156377051023966829274337915 234565576535950243911506873)
      ·
        refine ⟨175924182401962682933630155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234565576535950243911506873 175924182401962682933630155)
        ·
          refine ⟨263886273602944024400445233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175924182401962682933630155 263886273602944024400445233)
          ·
            refine ⟨197914705202208018300333925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263886273602944024400445233 197914705202208018300333925)
            ·
              refine ⟨37109007225414003431312611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197914705202208018300333925 37109007225414003431312611)
              ·
                refine ⟨55663510838121005146968917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37109007225414003431312611 55663510838121005146968917)
                ·
                  refine ⟨326153383817115264533021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55663510838121005146968917 326153383817115264533021)
                  ·
                    rfl

theorem cell23_5716633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 9].length) (baseStart_5716633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716633 prefixEnd_5716633 := by exact prefixLift 5716633
  have htrace : WordTrace (prefixWord ++ tailWord_5716633) baseStart_5716633 baseEnd_5716633 := by
    simpa [prefixWord, tailWord_5716633, baseEnd_5716633] using wordTrace_append hprefix tailTrace_5716633
  have hstable : (prefixWord ++ tailWord_5716633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716633).length < 2 ^ (prefixWord ++ tailWord_5716633).sum := by decide
  have hdescent : baseEnd_5716633 < baseStart_5716633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716643 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 7]
def baseStart_5716643 : Nat := 118140960795 + 5716643 * 2 ^ 59
def prefixEnd_5716643 : Nat := 4983230072969 + 3 ^ 40 * 5716643 * 2
def baseEnd_5716643 : Nat := 2935385589160582341672143

theorem tailTrace_5716643 : CollatzResearch.WordTrace tailWord_5716643 prefixEnd_5716643 2935385589160582341672143 := by
  unfold tailWord_5716643
  simp only [CollatzResearch.WordTrace]
  refine ⟨208503099428586210740314583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139002066285724140493543055 208503099428586210740314583)
  ·
    refine ⟨312754649142879316110471875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208503099428586210740314583 312754649142879316110471875)
    ·
      refine ⟨469131973714318974165707813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312754649142879316110471875 469131973714318974165707813)
      ·
        refine ⟨87962245071434807656070215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 469131973714318974165707813 87962245071434807656070215)
        ·
          refine ⟨131943367607152211484105323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87962245071434807656070215 131943367607152211484105323)
          ·
            refine ⟨197915051410728317226157985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131943367607152211484105323 197915051410728317226157985)
            ·
              refine ⟨148436288558046237919618489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197915051410728317226157985 148436288558046237919618489)
              ·
                refine ⟨111327216418534678439713867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148436288558046237919618489 111327216418534678439713867)
                ·
                  refine ⟨166990824627802017659570801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111327216418534678439713867 166990824627802017659570801)
                  ·
                    refine ⟨125243118470851513244678101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166990824627802017659570801 125243118470851513244678101)
                    ·
                      refine ⟨2935385589160582341672143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125243118470851513244678101 2935385589160582341672143)
                      ·
                        rfl

theorem cell23_5716643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_5716643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716643 prefixEnd_5716643 := by exact prefixLift 5716643
  have htrace : WordTrace (prefixWord ++ tailWord_5716643) baseStart_5716643 baseEnd_5716643 := by
    simpa [prefixWord, tailWord_5716643, baseEnd_5716643] using wordTrace_append hprefix tailTrace_5716643
  have hstable : (prefixWord ++ tailWord_5716643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716643).length < 2 ^ (prefixWord ++ tailWord_5716643).sum := by decide
  have hdescent : baseEnd_5716643 < baseStart_5716643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716661 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_5716661 : Nat := 118140960795 + 5716661 * 2 ^ 59
def prefixEnd_5716661 : Nat := 4983230072969 + 3 ^ 40 * 5716661 * 2
def baseEnd_5716661 : Nat := 2935394831812363271247061

theorem tailTrace_5716661 : CollatzResearch.WordTrace tailWord_5716661 prefixEnd_5716661 2935394831812363271247061 := by
  unfold tailWord_5716661
  simp only [CollatzResearch.WordTrace]
  refine ⟨208503755942520999814469837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139002503961680666542979891 208503755942520999814469837)
  ·
    refine ⟨78188908478445374930426189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208503755942520999814469837 78188908478445374930426189)
    ·
      refine ⟨29320840679417015598909821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78188908478445374930426189 29320840679417015598909821)
      ·
        refine ⟨10995315254781380849591183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29320840679417015598909821 10995315254781380849591183)
        ·
          refine ⟨16492972882172071274386775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10995315254781380849591183 16492972882172071274386775)
          ·
            refine ⟨24739459323258106911580163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16492972882172071274386775 24739459323258106911580163)
            ·
              refine ⟨37109188984887160367370245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24739459323258106911580163 37109188984887160367370245)
              ·
                refine ⟨6957972934666342568881921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37109188984887160367370245 6957972934666342568881921)
                ·
                  refine ⟨5218479700999756926661441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6957972934666342568881921 5218479700999756926661441)
                  ·
                    refine ⟨3913859775749817694996081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5218479700999756926661441 3913859775749817694996081)
                    ·
                      refine ⟨2935394831812363271247061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913859775749817694996081 2935394831812363271247061)
                      ·
                        rfl

theorem cell23_5716661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_5716661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716661 prefixEnd_5716661 := by exact prefixLift 5716661
  have htrace : WordTrace (prefixWord ++ tailWord_5716661) baseStart_5716661 baseEnd_5716661 := by
    simpa [prefixWord, tailWord_5716661, baseEnd_5716661] using wordTrace_append hprefix tailTrace_5716661
  have hstable : (prefixWord ++ tailWord_5716661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716661).length < 2 ^ (prefixWord ++ tailWord_5716661).sum := by decide
  have hdescent : baseEnd_5716661 < baseStart_5716661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716717 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5716717 : Nat := 118140960795 + 5716717 * 2 ^ 59
def prefixEnd_5716717 : Nat := 4983230072969 + 3 ^ 40 * 5716717 * 2
def baseEnd_5716717 : Nat := 2935423586729015052146803

theorem tailTrace_5716717 : CollatzResearch.WordTrace tailWord_5716717 prefixEnd_5716717 2935423586729015052146803 := by
  unfold tailWord_5716717
  simp only [CollatzResearch.WordTrace]
  refine ⟨208505798430318121378508405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139003865620212080919005603 208505798430318121378508405)
  ·
    refine ⟨19547418602842323879235163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208505798430318121378508405 19547418602842323879235163)
    ·
      refine ⟨29321127904263485818852745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19547418602842323879235163 29321127904263485818852745)
      ·
        refine ⟨21990845928197614364139559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29321127904263485818852745 21990845928197614364139559)
        ·
          refine ⟨32986268892296421546209339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21990845928197614364139559 32986268892296421546209339)
          ·
            refine ⟨49479403338444632319314009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32986268892296421546209339 49479403338444632319314009)
            ·
              refine ⟨37109552503833474239485507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49479403338444632319314009 37109552503833474239485507)
              ·
                refine ⟨55664328755750211359228261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37109552503833474239485507 55664328755750211359228261)
                ·
                  refine ⟨10437061641703164629855299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55664328755750211359228261 10437061641703164629855299)
                  ·
                    refine ⟨15655592462554746944782949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10437061641703164629855299 15655592462554746944782949)
                    ·
                      refine ⟨2935423586729015052146803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15655592462554746944782949 2935423586729015052146803)
                      ·
                        rfl

theorem cell23_5716717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5716717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716717 prefixEnd_5716717 := by exact prefixLift 5716717
  have htrace : WordTrace (prefixWord ++ tailWord_5716717) baseStart_5716717 baseEnd_5716717 := by
    simpa [prefixWord, tailWord_5716717, baseEnd_5716717] using wordTrace_append hprefix tailTrace_5716717
  have hstable : (prefixWord ++ tailWord_5716717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716717).length < 2 ^ (prefixWord ++ tailWord_5716717).sum := by decide
  have hdescent : baseEnd_5716717 < baseStart_5716717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716778 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_5716778 : Nat := 118140960795 + 5716778 * 2 ^ 59
def prefixEnd_5716778 : Nat := 4983230072969 + 3 ^ 40 * 5716778 * 2
def baseEnd_5716778 : Nat := 978484969682979771161341

theorem tailTrace_5716778 : CollatzResearch.WordTrace tailWord_5716778 prefixEnd_5716778 978484969682979771161341 := by
  unfold tailWord_5716778
  simp only [CollatzResearch.WordTrace]
  refine ⟨52127005820774282199119747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139005348855398085864319325 52127005820774282199119747)
  ·
    refine ⟨78190508731161423298679621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52127005820774282199119747 78190508731161423298679621)
    ·
      refine ⟨14660720387092766868502429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78190508731161423298679621 14660720387092766868502429)
      ·
        refine ⟨5497770145159787575688411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14660720387092766868502429 5497770145159787575688411)
        ·
          refine ⟨8246655217739681363532617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497770145159787575688411 8246655217739681363532617)
          ·
            refine ⟨6184991413304761022649463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8246655217739681363532617 6184991413304761022649463)
            ·
              refine ⟨9277487119957141533974195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6184991413304761022649463 9277487119957141533974195)
              ·
                refine ⟨13916230679935712300961293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9277487119957141533974195 13916230679935712300961293)
                ·
                  refine ⟨5218586504975892112860485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13916230679935712300961293 5218586504975892112860485)
                  ·
                    refine ⟨978484969682979771161341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5218586504975892112860485 978484969682979771161341)
                    ·
                      rfl

theorem cell23_5716778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_5716778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716778 prefixEnd_5716778 := by exact prefixLift 5716778
  have htrace : WordTrace (prefixWord ++ tailWord_5716778) baseStart_5716778 baseEnd_5716778 := by
    simpa [prefixWord, tailWord_5716778, baseEnd_5716778] using wordTrace_append hprefix tailTrace_5716778
  have hstable : (prefixWord ++ tailWord_5716778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716778).length < 2 ^ (prefixWord ++ tailWord_5716778).sum := by decide
  have hdescent : baseEnd_5716778 < baseStart_5716778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716800 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 5, 6]
def baseStart_5716800 : Nat := 118140960795 + 5716800 * 2 ^ 59
def prefixEnd_5716800 : Nat := 4983230072969 + 3 ^ 40 * 5716800 * 2
def baseEnd_5716800 : Nat := 978488735207779409136307

theorem tailTrace_5716800 : CollatzResearch.WordTrace tailWord_5716800 prefixEnd_5716800 978488735207779409136307 := by
  unfold tailWord_5716800
  simp only [CollatzResearch.WordTrace]
  refine ⟨104254412844508713276889927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139005883792678284369186569 104254412844508713276889927)
  ·
    refine ⟨156381619266763069915334891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104254412844508713276889927 156381619266763069915334891)
    ·
      refine ⟨234572428900144604873002337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156381619266763069915334891 234572428900144604873002337)
      ·
        refine ⟨175929321675108453654751753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234572428900144604873002337 175929321675108453654751753)
        ·
          refine ⟨131946991256331340241063815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175929321675108453654751753 131946991256331340241063815)
          ·
            refine ⟨197920486884497010361595723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131946991256331340241063815 197920486884497010361595723)
            ·
              refine ⟨296880730326745515542393585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197920486884497010361595723 296880730326745515542393585)
              ·
                refine ⟨222660547745059136656795189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296880730326745515542393585 222660547745059136656795189)
                ·
                  refine ⟨20874426351099294061574549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222660547745059136656795189 20874426351099294061574549)
                  ·
                    refine ⟨978488735207779409136307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20874426351099294061574549 978488735207779409136307)
                    ·
                      rfl

theorem cell23_5716800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_5716800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716800 prefixEnd_5716800 := by exact prefixLift 5716800
  have htrace : WordTrace (prefixWord ++ tailWord_5716800) baseStart_5716800 baseEnd_5716800 := by
    simpa [prefixWord, tailWord_5716800, baseEnd_5716800] using wordTrace_append hprefix tailTrace_5716800
  have hstable : (prefixWord ++ tailWord_5716800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716800).length < 2 ^ (prefixWord ++ tailWord_5716800).sum := by decide
  have hdescent : baseEnd_5716800 < baseStart_5716800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716835 : List Nat := [1, 1, 1, 5, 3, 3, 2, 2, 1, 1, 3]
def baseStart_5716835 : Nat := 118140960795 + 5716835 * 2 ^ 59
def prefixEnd_5716835 : Nat := 4983230072969 + 3 ^ 40 * 5716835 * 2
def baseEnd_5716835 : Nat := 2935484177446245590471261

theorem tailTrace_5716835 : CollatzResearch.WordTrace tailWord_5716835 prefixEnd_5716835 2935484177446245590471261 := by
  unfold tailWord_5716835
  simp only [CollatzResearch.WordTrace]
  refine ⟨208510102243890627531303959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139006734829260418354202639 208510102243890627531303959)
  ·
    refine ⟨312765153365835941296955939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208510102243890627531303959 312765153365835941296955939)
    ·
      refine ⟨469147730048753911945433909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312765153365835941296955939 469147730048753911945433909)
      ·
        refine ⟨43982599692070679244884429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 469147730048753911945433909 43982599692070679244884429)
        ·
          refine ⟨16493474884526504716831661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43982599692070679244884429 16493474884526504716831661)
          ·
            refine ⟨6185053081697439268811873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16493474884526504716831661 6185053081697439268811873)
            ·
              refine ⟨4638789811273079451608905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6185053081697439268811873 4638789811273079451608905)
              ·
                refine ⟨3479092358454809588706679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4638789811273079451608905 3479092358454809588706679)
                ·
                  refine ⟨5218638537682214383060019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479092358454809588706679 5218638537682214383060019)
                  ·
                    refine ⟨7827957806523321574590029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5218638537682214383060019 7827957806523321574590029)
                    ·
                      refine ⟨2935484177446245590471261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7827957806523321574590029 2935484177446245590471261)
                      ·
                        rfl

theorem cell23_5716835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_5716835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716835 prefixEnd_5716835 := by exact prefixLift 5716835
  have htrace : WordTrace (prefixWord ++ tailWord_5716835) baseStart_5716835 baseEnd_5716835 := by
    simpa [prefixWord, tailWord_5716835, baseEnd_5716835] using wordTrace_append hprefix tailTrace_5716835
  have hstable : (prefixWord ++ tailWord_5716835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716835).length < 2 ^ (prefixWord ++ tailWord_5716835).sum := by decide
  have hdescent : baseEnd_5716835 < baseStart_5716835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716862 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5716862 : Nat := 118140960795 + 5716862 * 2 ^ 59
def prefixEnd_5716862 : Nat := 4983230072969 + 3 ^ 40 * 5716862 * 2
def baseEnd_5716862 : Nat := 2935498041423916984833637

theorem tailTrace_5716862 : CollatzResearch.WordTrace tailWord_5716862 prefixEnd_5716862 2935498041423916984833637 := by
  unfold tailWord_5716862
  simp only [CollatzResearch.WordTrace]
  refine ⟨26063885876849101392817105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139007391343195207428357893 26063885876849101392817105)
  ·
    refine ⟨19547914407636826044612829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26063885876849101392817105 19547914407636826044612829)
    ·
      refine ⟨7330467902863809766729811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19547914407636826044612829 7330467902863809766729811)
      ·
        refine ⟨10995701854295714650094717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7330467902863809766729811 10995701854295714650094717)
        ·
          refine ⟨4123388195360892993785519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10995701854295714650094717 4123388195360892993785519)
          ·
            refine ⟨6185082293041339490678279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123388195360892993785519 6185082293041339490678279)
            ·
              refine ⟨9277623439562009236017419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6185082293041339490678279 9277623439562009236017419)
              ·
                refine ⟨13916435159343013854026129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9277623439562009236017419 13916435159343013854026129)
                ·
                  refine ⟨10437326369507260390519597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13916435159343013854026129 10437326369507260390519597)
                  ·
                    refine ⟨3913997388565222646444849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10437326369507260390519597 3913997388565222646444849)
                    ·
                      refine ⟨2935498041423916984833637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3913997388565222646444849 2935498041423916984833637)
                      ·
                        rfl

theorem cell23_5716862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5716862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716862 prefixEnd_5716862 := by exact prefixLift 5716862
  have htrace : WordTrace (prefixWord ++ tailWord_5716862) baseStart_5716862 baseEnd_5716862 := by
    simpa [prefixWord, tailWord_5716862, baseEnd_5716862] using wordTrace_append hprefix tailTrace_5716862
  have hstable : (prefixWord ++ tailWord_5716862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716862).length < 2 ^ (prefixWord ++ tailWord_5716862).sum := by decide
  have hdescent : baseEnd_5716862 < baseStart_5716862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716927 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_5716927 : Nat := 118140960795 + 5716927 * 2 ^ 59
def prefixEnd_5716927 : Nat := 4983230072969 + 3 ^ 40 * 5716927 * 2
def baseEnd_5716927 : Nat := 2935531417666459230520837

theorem tailTrace_5716927 : CollatzResearch.WordTrace tailWord_5716927 prefixEnd_5716927 2935531417666459230520837 := by
  unfold tailWord_5716927
  simp only [CollatzResearch.WordTrace]
  refine ⟨208513457759557327243653035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139008971839704884829102023 208513457759557327243653035)
  ·
    refine ⟨312770186639335990865479553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208513457759557327243653035 312770186639335990865479553)
    ·
      refine ⟨234577639979501993149109665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312770186639335990865479553 234577639979501993149109665)
      ·
        refine ⟨175933229984626494861832249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234577639979501993149109665 175933229984626494861832249)
        ·
          refine ⟨131949922488469871146374187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175933229984626494861832249 131949922488469871146374187)
          ·
            refine ⟨197924883732704806719561281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131949922488469871146374187 197924883732704806719561281)
            ·
              refine ⟨148443662799528605039670961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197924883732704806719561281 148443662799528605039670961)
              ·
                refine ⟨111332747099646453779753221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148443662799528605039670961 111332747099646453779753221)
                ·
                  refine ⟨20874890081183710083703729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111332747099646453779753221 20874890081183710083703729)
                  ·
                    refine ⟨15656167560887782562777797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20874890081183710083703729 15656167560887782562777797)
                    ·
                      refine ⟨2935531417666459230520837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15656167560887782562777797 2935531417666459230520837)
                      ·
                        rfl

theorem cell23_5716927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_5716927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716927 prefixEnd_5716927 := by exact prefixLift 5716927
  have htrace : WordTrace (prefixWord ++ tailWord_5716927) baseStart_5716927 baseEnd_5716927 := by
    simpa [prefixWord, tailWord_5716927, baseEnd_5716927] using wordTrace_append hprefix tailTrace_5716927
  have hstable : (prefixWord ++ tailWord_5716927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716927).length < 2 ^ (prefixWord ++ tailWord_5716927).sum := by decide
  have hdescent : baseEnd_5716927 < baseStart_5716927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716948 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_5716948 : Nat := 118140960795 + 5716948 * 2 ^ 59
def prefixEnd_5716948 : Nat := 4983230072969 + 3 ^ 40 * 5716948 * 2
def baseEnd_5716948 : Nat := 2935542200760203648358241

theorem tailTrace_5716948 : CollatzResearch.WordTrace tailWord_5716948 prefixEnd_5716948 2935542200760203648358241 := by
  unfold tailWord_5716948
  simp only [CollatzResearch.WordTrace]
  refine ⟨104257111846240623915083749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139009482461654165220111665 104257111846240623915083749)
  ·
    refine ⟨19548208471170116984078203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104257111846240623915083749 19548208471170116984078203)
    ·
      refine ⟨29322312706755175476117305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19548208471170116984078203 29322312706755175476117305)
      ·
        refine ⟨21991734530066381607087979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29322312706755175476117305 21991734530066381607087979)
        ·
          refine ⟨32987601795099572410631969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21991734530066381607087979 32987601795099572410631969)
          ·
            refine ⟨24740701346324679307973977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32987601795099572410631969 24740701346324679307973977)
            ·
              refine ⟨18555526009743509480980483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24740701346324679307973977 18555526009743509480980483)
              ·
                refine ⟨27833289014615264221470725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18555526009743509480980483 27833289014615264221470725)
                ·
                  refine ⟨5218741690240362041525761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27833289014615264221470725 5218741690240362041525761)
                  ·
                    refine ⟨3914056267680271531144321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5218741690240362041525761 3914056267680271531144321)
                    ·
                      refine ⟨2935542200760203648358241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914056267680271531144321 2935542200760203648358241)
                      ·
                        rfl

theorem cell23_5716948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_5716948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716948 prefixEnd_5716948 := by exact prefixLift 5716948
  have htrace : WordTrace (prefixWord ++ tailWord_5716948) baseStart_5716948 baseEnd_5716948 := by
    simpa [prefixWord, tailWord_5716948, baseEnd_5716948] using wordTrace_append hprefix tailTrace_5716948
  have hstable : (prefixWord ++ tailWord_5716948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716948).length < 2 ^ (prefixWord ++ tailWord_5716948).sum := by decide
  have hdescent : baseEnd_5716948 < baseStart_5716948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5716954 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 7]
def baseStart_5716954 : Nat := 118140960795 + 5716954 * 2 ^ 59
def prefixEnd_5716954 : Nat := 4983230072969 + 3 ^ 40 * 5716954 * 2
def baseEnd_5716954 : Nat := 326171697960458958320357

theorem tailTrace_5716954 : CollatzResearch.WordTrace tailWord_5716954 prefixEnd_5716954 326171697960458958320357 := by
  unfold tailWord_5716954
  simp only [CollatzResearch.WordTrace]
  refine ⟨52128610632614877713721479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139009628353639673903257277 52128610632614877713721479)
  ·
    refine ⟨78192915948922316570582219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52128610632614877713721479 78192915948922316570582219)
    ·
      refine ⟨117289373923383474855873329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78192915948922316570582219 117289373923383474855873329)
      ·
        refine ⟨87967030442537606141904997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117289373923383474855873329 87967030442537606141904997)
        ·
          refine ⟨16493818207975801151607187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87967030442537606141904997 16493818207975801151607187)
          ·
            refine ⟨24740727311963701727410781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16493818207975801151607187 24740727311963701727410781)
            ·
              refine ⟨9277772741986388147779043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24740727311963701727410781 9277772741986388147779043)
              ·
                refine ⟨13916659112979582221668565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9277772741986388147779043 13916659112979582221668565)
                ·
                  refine ⟨326171697960458958320357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13916659112979582221668565 326171697960458958320357)
                  ·
                    rfl

theorem cell23_5716954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_5716954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5716954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5716954 prefixEnd_5716954 := by exact prefixLift 5716954
  have htrace : WordTrace (prefixWord ++ tailWord_5716954) baseStart_5716954 baseEnd_5716954 := by
    simpa [prefixWord, tailWord_5716954, baseEnd_5716954] using wordTrace_append hprefix tailTrace_5716954
  have hstable : (prefixWord ++ tailWord_5716954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5716954).length < 2 ^ (prefixWord ++ tailWord_5716954).sum := by decide
  have hdescent : baseEnd_5716954 < baseStart_5716954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5716954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717048 : List Nat := [2, 1, 2, 1, 5, 1, 1, 5, 1, 4]
def baseStart_5717048 : Nat := 118140960795 + 5717048 * 2 ^ 59
def prefixEnd_5717048 : Nat := 4983230072969 + 3 ^ 40 * 5717048 * 2
def baseEnd_5717048 : Nat := 978531182941884419035927

theorem tailTrace_5717048 : CollatzResearch.WordTrace tailWord_5717048 prefixEnd_5717048 978531182941884419035927 := by
  unfold tailWord_5717048
  simp only [CollatzResearch.WordTrace]
  refine ⟨104258935496059482454403899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139011913994745976605871865 104258935496059482454403899)
  ·
    refine ⟨156388403244089223681605849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104258935496059482454403899 156388403244089223681605849)
    ·
      refine ⟨117291302433066917761204387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156388403244089223681605849 117291302433066917761204387)
      ·
        refine ⟨175936953649600376641806581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117291302433066917761204387 175936953649600376641806581)
        ·
          refine ⟨16494089404650035310169367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175936953649600376641806581 16494089404650035310169367)
          ·
            refine ⟨24741134106975052965254051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16494089404650035310169367 24741134106975052965254051)
            ·
              refine ⟨37111701160462579447881077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24741134106975052965254051 37111701160462579447881077)
              ·
                refine ⟨3479221983793366823238851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37111701160462579447881077 3479221983793366823238851)
                ·
                  refine ⟨5218832975690050234858277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479221983793366823238851 5218832975690050234858277)
                  ·
                    refine ⟨978531182941884419035927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5218832975690050234858277 978531182941884419035927)
                    ·
                      rfl

theorem cell23_5717048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_5717048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717048 prefixEnd_5717048 := by exact prefixLift 5717048
  have htrace : WordTrace (prefixWord ++ tailWord_5717048) baseStart_5717048 baseEnd_5717048 := by
    simpa [prefixWord, tailWord_5717048, baseEnd_5717048] using wordTrace_append hprefix tailTrace_5717048
  have hstable : (prefixWord ++ tailWord_5717048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717048).length < 2 ^ (prefixWord ++ tailWord_5717048).sum := by decide
  have hdescent : baseEnd_5717048 < baseStart_5717048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717081 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 6, 3, 2]
def baseStart_5717081 : Nat := 118140960795 + 5717081 * 2 ^ 59
def prefixEnd_5717081 : Nat := 4983230072969 + 3 ^ 40 * 5717081 * 2
def baseEnd_5717081 : Nat := 2935610493687251627995129

theorem tailTrace_5717081 : CollatzResearch.WordTrace tailWord_5717081 prefixEnd_5717081 2935610493687251627995129 := by
  unfold tailWord_5717081
  simp only [CollatzResearch.WordTrace]
  refine ⟨208519074600999411544759097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139012716400666274363172731 208519074600999411544759097)
  ·
    refine ⟨156389305950749558658569323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208519074600999411544759097 156389305950749558658569323)
    ·
      refine ⟨234583958926124337987853985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156389305950749558658569323 234583958926124337987853985)
      ·
        refine ⟨175937969194593253490890489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234583958926124337987853985 175937969194593253490890489)
        ·
          refine ⟨131953476895944940118167867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175937969194593253490890489 131953476895944940118167867)
          ·
            refine ⟨197930215343917410177251801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131953476895944940118167867 197930215343917410177251801)
            ·
              refine ⟨148447661507938057632938851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197930215343917410177251801 148447661507938057632938851)
              ·
                refine ⟨222671492261907086449408277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148447661507938057632938851 222671492261907086449408277)
                ·
                  refine ⟨10437726199776894677316013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 222671492261907086449408277 10437726199776894677316013)
                  ·
                    refine ⟨3914147324916335503993505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10437726199776894677316013 3914147324916335503993505)
                    ·
                      refine ⟨2935610493687251627995129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914147324916335503993505 2935610493687251627995129)
                      ·
                        rfl

theorem cell23_5717081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_5717081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717081 prefixEnd_5717081 := by exact prefixLift 5717081
  have htrace : WordTrace (prefixWord ++ tailWord_5717081) baseStart_5717081 baseEnd_5717081 := by
    simpa [prefixWord, tailWord_5717081, baseEnd_5717081] using wordTrace_append hprefix tailTrace_5717081
  have hstable : (prefixWord ++ tailWord_5717081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717081).length < 2 ^ (prefixWord ++ tailWord_5717081).sum := by decide
  have hdescent : baseEnd_5717081 < baseStart_5717081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717098 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_5717098 : Nat := 118140960795 + 5717098 * 2 ^ 59
def prefixEnd_5717098 : Nat := 4983230072969 + 3 ^ 40 * 5717098 * 2
def baseEnd_5717098 : Nat := 2935619222858378061482551

theorem tailTrace_5717098 : CollatzResearch.WordTrace tailWord_5717098 prefixEnd_5717098 2935619222858378061482551 := by
  unfold tailWord_5717098
  simp only [CollatzResearch.WordTrace]
  refine ⟨52129923660484455862031987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139013129761291882298751965 52129923660484455862031987)
  ·
    refine ⟨78194885490726683793047981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52129923660484455862031987 78194885490726683793047981)
    ·
      refine ⟨29323082059022506422392993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78194885490726683793047981 29323082059022506422392993)
      ·
        refine ⟨21992311544266879816794745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29323082059022506422392993 21992311544266879816794745)
        ·
          refine ⟨16494233658200159862596059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21992311544266879816794745 16494233658200159862596059)
          ·
            refine ⟨24741350487300239793894089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16494233658200159862596059 24741350487300239793894089)
            ·
              refine ⟨18556012865475179845420567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24741350487300239793894089 18556012865475179845420567)
              ·
                refine ⟨27834019298212769768130851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18556012865475179845420567 27834019298212769768130851)
                ·
                  refine ⟨41751028947319154652196277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27834019298212769768130851 41751028947319154652196277)
                  ·
                    refine ⟨3914158963811170748643401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41751028947319154652196277 3914158963811170748643401)
                    ·
                      refine ⟨2935619222858378061482551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914158963811170748643401 2935619222858378061482551)
                      ·
                        rfl

theorem cell23_5717098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_5717098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717098 prefixEnd_5717098 := by exact prefixLift 5717098
  have htrace : WordTrace (prefixWord ++ tailWord_5717098) baseStart_5717098 baseEnd_5717098 := by
    simpa [prefixWord, tailWord_5717098, baseEnd_5717098] using wordTrace_append hprefix tailTrace_5717098
  have hstable : (prefixWord ++ tailWord_5717098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717098).length < 2 ^ (prefixWord ++ tailWord_5717098).sum := by decide
  have hdescent : baseEnd_5717098 < baseStart_5717098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717104 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 3, 6]
def baseStart_5717104 : Nat := 118140960795 + 5717104 * 2 ^ 59
def prefixEnd_5717104 : Nat := 4983230072969 + 3 ^ 40 * 5717104 * 2
def baseEnd_5717104 : Nat := 978540767914101679335841

theorem tailTrace_5717104 : CollatzResearch.WordTrace tailWord_5717104 prefixEnd_5717104 978540767914101679335841 := by
  unfold tailWord_5717104
  simp only [CollatzResearch.WordTrace]
  refine ⟨104259956739958043236423183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139013275653277390981897577 104259956739958043236423183)
  ·
    refine ⟨156389935109937064854634775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104259956739958043236423183 156389935109937064854634775)
    ·
      refine ⟨234584902664905597281952163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156389935109937064854634775 234584902664905597281952163)
      ·
        refine ⟨351877353997358395922928245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234584902664905597281952163 351877353997358395922928245)
        ·
          refine ⟨32988501937252349617774523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351877353997358395922928245 32988501937252349617774523)
          ·
            refine ⟨49482752905878524426661785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32988501937252349617774523 49482752905878524426661785)
            ·
              refine ⟨37112064679408893319996339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49482752905878524426661785 37112064679408893319996339)
              ·
                refine ⟨55668097019113339979994509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37112064679408893319996339 55668097019113339979994509)
                ·
                  refine ⟨20875536382167502492497941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55668097019113339979994509 20875536382167502492497941)
                  ·
                    refine ⟨978540767914101679335841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20875536382167502492497941 978540767914101679335841)
                    ·
                      rfl

theorem cell23_5717104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_5717104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717104 prefixEnd_5717104 := by exact prefixLift 5717104
  have htrace : WordTrace (prefixWord ++ tailWord_5717104) baseStart_5717104 baseEnd_5717104 := by
    simpa [prefixWord, tailWord_5717104, baseEnd_5717104] using wordTrace_append hprefix tailTrace_5717104
  have hstable : (prefixWord ++ tailWord_5717104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717104).length < 2 ^ (prefixWord ++ tailWord_5717104).sum := by decide
  have hdescent : baseEnd_5717104 < baseStart_5717104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717111 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 4]
def baseStart_5717111 : Nat := 118140960795 + 5717111 * 2 ^ 59
def prefixEnd_5717111 : Nat := 4983230072969 + 3 ^ 40 * 5717111 * 2
def baseEnd_5717111 : Nat := 2935625898106886510619991

theorem tailTrace_5717111 : CollatzResearch.WordTrace tailWord_5717111 prefixEnd_5717111 2935625898106886510619991 := by
  unfold tailWord_5717111
  simp only [CollatzResearch.WordTrace]
  refine ⟨208520168790890726668351187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139013445860593817778900791 208520168790890726668351187)
  ·
    refine ⟨312780253186336090002526781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208520168790890726668351187 312780253186336090002526781)
    ·
      refine ⟨117292594944876033750947543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312780253186336090002526781 117292594944876033750947543)
      ·
        refine ⟨175938892417314050626421315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117292594944876033750947543 175938892417314050626421315)
        ·
          refine ⟨263908338625971075939631973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175938892417314050626421315 263908338625971075939631973)
          ·
            refine ⟨49482813492369576738680995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263908338625971075939631973 49482813492369576738680995)
            ·
              refine ⟨74224220238554365108021493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49482813492369576738680995 74224220238554365108021493)
              ·
                refine ⟨6958520647364471728877015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74224220238554365108021493 6958520647364471728877015)
                ·
                  refine ⟨10437780971046707593315523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6958520647364471728877015 10437780971046707593315523)
                  ·
                    refine ⟨15656671456570061389973285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10437780971046707593315523 15656671456570061389973285)
                    ·
                      refine ⟨2935625898106886510619991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15656671456570061389973285 2935625898106886510619991)
                      ·
                        rfl

theorem cell23_5717111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_5717111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717111 prefixEnd_5717111 := by exact prefixLift 5717111
  have htrace : WordTrace (prefixWord ++ tailWord_5717111) baseStart_5717111 baseEnd_5717111 := by
    simpa [prefixWord, tailWord_5717111, baseEnd_5717111] using wordTrace_append hprefix tailTrace_5717111
  have hstable : (prefixWord ++ tailWord_5717111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717111).length < 2 ^ (prefixWord ++ tailWord_5717111).sum := by decide
  have hdescent : baseEnd_5717111 < baseStart_5717111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717148 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_5717148 : Nat := 118140960795 + 5717148 * 2 ^ 59
def prefixEnd_5717148 : Nat := 4983230072969 + 3 ^ 40 * 5717148 * 2
def baseEnd_5717148 : Nat := 2935644896891102865857321

theorem tailTrace_5717148 : CollatzResearch.WordTrace tailWord_5717148 prefixEnd_5717148 2935644896891102865857321 := by
  unfold tailWord_5717148
  simp only [CollatzResearch.WordTrace]
  refine ⟨104260759145878340993724049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139014345527837787991632065 104260759145878340993724049)
  ·
    refine ⟨78195569359408755745293037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104260759145878340993724049 78195569359408755745293037)
    ·
      refine ⟨29323338509778283404484889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78195569359408755745293037 29323338509778283404484889)
      ·
        refine ⟨21992503882333712553363667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29323338509778283404484889 21992503882333712553363667)
        ·
          refine ⟨32988755823500568830045501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21992503882333712553363667 32988755823500568830045501)
          ·
            refine ⟨12370783433812713311267063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32988755823500568830045501 12370783433812713311267063)
            ·
              refine ⟨18556175150719069966900595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12370783433812713311267063 18556175150719069966900595)
              ·
                refine ⟨27834262726078604950350893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18556175150719069966900595 27834262726078604950350893)
                ·
                  refine ⟨10437848522279476856381585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27834262726078604950350893 10437848522279476856381585)
                  ·
                    refine ⟨7828386391709607642286189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10437848522279476856381585 7828386391709607642286189)
                    ·
                      refine ⟨2935644896891102865857321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7828386391709607642286189 2935644896891102865857321)
                      ·
                        rfl

theorem cell23_5717148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_5717148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717148 prefixEnd_5717148 := by exact prefixLift 5717148
  have htrace : WordTrace (prefixWord ++ tailWord_5717148) baseStart_5717148 baseEnd_5717148 := by
    simpa [prefixWord, tailWord_5717148, baseEnd_5717148] using wordTrace_append hprefix tailTrace_5717148
  have hstable : (prefixWord ++ tailWord_5717148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717148).length < 2 ^ (prefixWord ++ tailWord_5717148).sum := by decide
  have hdescent : baseEnd_5717148 < baseStart_5717148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717162 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5717162 : Nat := 118140960795 + 5717162 * 2 ^ 59
def prefixEnd_5717162 : Nat := 4983230072969 + 3 ^ 40 * 5717162 * 2
def baseEnd_5717162 : Nat := 2935652085620265811082257

theorem tailTrace_5717162 : CollatzResearch.WordTrace tailWord_5717162 prefixEnd_5717162 2935652085620265811082257 := by
  unfold tailWord_5717162
  simp only [CollatzResearch.WordTrace]
  refine ⟨52130507228426490594614435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139014685942470641585638493 52130507228426490594614435)
  ·
    refine ⟨78195760842639735891921653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52130507228426490594614435 78195760842639735891921653)
    ·
      refine ⟨7330852578997475239867655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78195760842639735891921653 7330852578997475239867655)
      ·
        refine ⟨10996278868496212859801483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7330852578997475239867655 10996278868496212859801483)
        ·
          refine ⟨16494418302744319289702225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10996278868496212859801483 16494418302744319289702225)
          ·
            refine ⟨12370813727058239467276669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16494418302744319289702225 12370813727058239467276669)
            ·
              refine ⟨4639055147646839800228751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12370813727058239467276669 4639055147646839800228751)
              ·
                refine ⟨6958582721470259700343127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639055147646839800228751 6958582721470259700343127)
                ·
                  refine ⟨10437874082205389550514691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6958582721470259700343127 10437874082205389550514691)
                  ·
                    refine ⟨15656811123308084325772037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10437874082205389550514691 15656811123308084325772037)
                    ·
                      refine ⟨2935652085620265811082257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15656811123308084325772037 2935652085620265811082257)
                      ·
                        rfl

theorem cell23_5717162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5717162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717162 prefixEnd_5717162 := by exact prefixLift 5717162
  have htrace : WordTrace (prefixWord ++ tailWord_5717162) baseStart_5717162 baseEnd_5717162 := by
    simpa [prefixWord, tailWord_5717162, baseEnd_5717162] using wordTrace_append hprefix tailTrace_5717162
  have hstable : (prefixWord ++ tailWord_5717162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717162).length < 2 ^ (prefixWord ++ tailWord_5717162).sum := by decide
  have hdescent : baseEnd_5717162 < baseStart_5717162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717165 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_5717165 : Nat := 118140960795 + 5717165 * 2 ^ 59
def prefixEnd_5717165 : Nat := 4983230072969 + 3 ^ 40 * 5717165 * 2
def baseEnd_5717165 : Nat := 2935653626062229299344743

theorem tailTrace_5717165 : CollatzResearch.WordTrace tailWord_5717165 prefixEnd_5717165 2935653626062229299344743 := by
  unfold tailWord_5717165
  simp only [CollatzResearch.WordTrace]
  refine ⟨208522138332695093890816949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139014758888463395927211299 208522138332695093890816949)
  ·
    refine ⟨19548950468690165052264089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208522138332695093890816949 19548950468690165052264089)
    ·
      refine ⟨14661712851517623789198067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19548950468690165052264089 14661712851517623789198067)
      ·
        refine ⟨21992569277276435683797101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14661712851517623789198067 21992569277276435683797101)
        ·
          refine ⟨8247213478978663381423913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21992569277276435683797101 8247213478978663381423913)
          ·
            refine ⟨6185410109233997536067935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8247213478978663381423913 6185410109233997536067935)
            ·
              refine ⟨9278115163850996304101903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6185410109233997536067935 9278115163850996304101903)
              ·
                refine ⟨13917172745776494456152855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9278115163850996304101903 13917172745776494456152855)
                ·
                  refine ⟨20875759118664741684229283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13917172745776494456152855 20875759118664741684229283)
                  ·
                    refine ⟨31313638677997112526343925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20875759118664741684229283 31313638677997112526343925)
                    ·
                      refine ⟨2935653626062229299344743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31313638677997112526343925 2935653626062229299344743)
                      ·
                        rfl

theorem cell23_5717165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_5717165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717165 prefixEnd_5717165 := by exact prefixLift 5717165
  have htrace : WordTrace (prefixWord ++ tailWord_5717165) baseStart_5717165 baseEnd_5717165 := by
    simpa [prefixWord, tailWord_5717165, baseEnd_5717165] using wordTrace_append hprefix tailTrace_5717165
  have hstable : (prefixWord ++ tailWord_5717165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717165).length < 2 ^ (prefixWord ++ tailWord_5717165).sum := by decide
  have hdescent : baseEnd_5717165 < baseStart_5717165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717205 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5717205 : Nat := 118140960795 + 5717205 * 2 ^ 59
def prefixEnd_5717205 : Nat := 4983230072969 + 3 ^ 40 * 5717205 * 2
def baseEnd_5717205 : Nat := 2935674165288409142844559

theorem tailTrace_5717205 : CollatzResearch.WordTrace tailWord_5717205 prefixEnd_5717205 2935674165288409142844559 := by
  unfold tailWord_5717205
  simp only [CollatzResearch.WordTrace]
  refine ⟨208523597252550180722273069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139015731501700120481515379 208523597252550180722273069)
  ·
    refine ⟨78196348969706317770852401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208523597252550180722273069 78196348969706317770852401)
    ·
      refine ⟨58647261727279738328139301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78196348969706317770852401 58647261727279738328139301)
      ·
        refine ⟨10996361573864950936526119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58647261727279738328139301 10996361573864950936526119)
        ·
          refine ⟨16494542360797426404789179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10996361573864950936526119 16494542360797426404789179)
          ·
            refine ⟨24741813541196139607183769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16494542360797426404789179 24741813541196139607183769)
            ·
              refine ⟨18556360155897104705387827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24741813541196139607183769 18556360155897104705387827)
              ·
                refine ⟨27834540233845657058081741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18556360155897104705387827 27834540233845657058081741)
                ·
                  refine ⟨10437952587692121396780653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27834540233845657058081741 10437952587692121396780653)
                  ·
                    refine ⟨3914232220384545523792745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10437952587692121396780653 3914232220384545523792745)
                    ·
                      refine ⟨2935674165288409142844559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914232220384545523792745 2935674165288409142844559)
                      ·
                        rfl

theorem cell23_5717205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5717205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717205 prefixEnd_5717205 := by exact prefixLift 5717205
  have htrace : WordTrace (prefixWord ++ tailWord_5717205) baseStart_5717205 baseEnd_5717205 := by
    simpa [prefixWord, tailWord_5717205, baseEnd_5717205] using wordTrace_append hprefix tailTrace_5717205
  have hstable : (prefixWord ++ tailWord_5717205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717205).length < 2 ^ (prefixWord ++ tailWord_5717205).sum := by decide
  have hdescent : baseEnd_5717205 < baseStart_5717205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717235 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 4, 2, 2]
def baseStart_5717235 : Nat := 118140960795 + 5717235 * 2 ^ 59
def prefixEnd_5717235 : Nat := 4983230072969 + 3 ^ 40 * 5717235 * 2
def baseEnd_5717235 : Nat := 2935689569708044025469421

theorem tailTrace_5717235 : CollatzResearch.WordTrace tailWord_5717235 prefixEnd_5717235 2935689569708044025469421 := by
  unfold tailWord_5717235
  simp only [CollatzResearch.WordTrace]
  refine ⟨208524691442441495845865159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139016460961627663897243439 208524691442441495845865159)
  ·
    refine ⟨312787037163662243768797739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208524691442441495845865159 312787037163662243768797739)
    ·
      refine ⟨469180555745493365653196609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312787037163662243768797739 469180555745493365653196609)
      ·
        refine ⟨351885416809120024239897457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469180555745493365653196609 351885416809120024239897457)
        ·
          refine ⟨263914062606840018179923093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351885416809120024239897457 263914062606840018179923093)
          ·
            refine ⟨12370971684695625852183895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 263914062606840018179923093 12370971684695625852183895)
            ·
              refine ⟨18556457527043438778275843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12370971684695625852183895 18556457527043438778275843)
              ·
                refine ⟨27834686290565158167413765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18556457527043438778275843 27834686290565158167413765)
                ·
                  refine ⟨5219003679480967156390081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27834686290565158167413765 5219003679480967156390081)
                  ·
                    refine ⟨3914252759610725367292561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5219003679480967156390081 3914252759610725367292561)
                    ·
                      refine ⟨2935689569708044025469421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914252759610725367292561 2935689569708044025469421)
                      ·
                        rfl

theorem cell23_5717235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 2, 2].length) (baseStart_5717235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717235 prefixEnd_5717235 := by exact prefixLift 5717235
  have htrace : WordTrace (prefixWord ++ tailWord_5717235) baseStart_5717235 baseEnd_5717235 := by
    simpa [prefixWord, tailWord_5717235, baseEnd_5717235] using wordTrace_append hprefix tailTrace_5717235
  have hstable : (prefixWord ++ tailWord_5717235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717235).length < 2 ^ (prefixWord ++ tailWord_5717235).sum := by decide
  have hdescent : baseEnd_5717235 < baseStart_5717235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717241 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 7]
def baseStart_5717241 : Nat := 118140960795 + 5717241 * 2 ^ 59
def prefixEnd_5717241 : Nat := 4983230072969 + 3 ^ 40 * 5717241 * 2
def baseEnd_5717241 : Nat := 326188072287996777999377

theorem tailTrace_5717241 : CollatzResearch.WordTrace tailWord_5717241 prefixEnd_5717241 326188072287996777999377 := by
  unfold tailWord_5717241
  simp only [CollatzResearch.WordTrace]
  refine ⟨208524910280419758870583577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139016606853613172580389051 208524910280419758870583577)
  ·
    refine ⟨156393682710314819152937683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208524910280419758870583577 156393682710314819152937683)
    ·
      refine ⟨234590524065472228729406525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156393682710314819152937683 234590524065472228729406525)
      ·
        refine ⟨87971446524552085773527447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234590524065472228729406525 87971446524552085773527447)
        ·
          refine ⟨131957169786828128660291171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87971446524552085773527447 131957169786828128660291171)
          ·
            refine ⟨197935754680242192990436757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131957169786828128660291171 197935754680242192990436757)
            ·
              refine ⟨9278238500636352796426723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197935754680242192990436757 9278238500636352796426723)
              ·
                refine ⟨13917357750954529194640085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9278238500636352796426723 13917357750954529194640085)
                ·
                  refine ⟨326188072287996777999377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13917357750954529194640085 326188072287996777999377)
                  ·
                    rfl

theorem cell23_5717241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 7].length) (baseStart_5717241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717241 prefixEnd_5717241 := by exact prefixLift 5717241
  have htrace : WordTrace (prefixWord ++ tailWord_5717241) baseStart_5717241 baseEnd_5717241 := by
    simpa [prefixWord, tailWord_5717241, baseEnd_5717241] using wordTrace_append hprefix tailTrace_5717241
  have hstable : (prefixWord ++ tailWord_5717241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717241).length < 2 ^ (prefixWord ++ tailWord_5717241).sum := by decide
  have hdescent : baseEnd_5717241 < baseStart_5717241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717252 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_5717252 : Nat := 118140960795 + 5717252 * 2 ^ 59
def prefixEnd_5717252 : Nat := 4983230072969 + 3 ^ 40 * 5717252 * 2
def baseEnd_5717252 : Nat := 2935698298879170458956843

theorem tailTrace_5717252 : CollatzResearch.WordTrace tailWord_5717252 prefixEnd_5717252 2935698298879170458956843 := by
  unfold tailWord_5717252
  simp only [CollatzResearch.WordTrace]
  refine ⟨104262655741689953874617005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139016874322253271832822673 104262655741689953874617005)
  ·
    refine ⟨39098495903133732702981377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104262655741689953874617005 39098495903133732702981377)
    ·
      refine ⟨29323871927350299527236033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39098495903133732702981377 29323871927350299527236033)
      ·
        refine ⟨21992903945512724645427025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29323871927350299527236033 21992903945512724645427025)
        ·
          refine ⟨16494677959134543484070269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21992903945512724645427025 16494677959134543484070269)
          ·
            refine ⟨6185504234675453806526351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16494677959134543484070269 6185504234675453806526351)
            ·
              refine ⟨9278256352013180709789527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6185504234675453806526351 9278256352013180709789527)
              ·
                refine ⟨13917384528019771064684291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9278256352013180709789527 13917384528019771064684291)
                ·
                  refine ⟨20876076792029656597026437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13917384528019771064684291 20876076792029656597026437)
                  ·
                    refine ⟨3914264398505560611942457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20876076792029656597026437 3914264398505560611942457)
                    ·
                      refine ⟨2935698298879170458956843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914264398505560611942457 2935698298879170458956843)
                      ·
                        rfl

theorem cell23_5717252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_5717252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717252 prefixEnd_5717252 := by exact prefixLift 5717252
  have htrace : WordTrace (prefixWord ++ tailWord_5717252) baseStart_5717252 baseEnd_5717252 := by
    simpa [prefixWord, tailWord_5717252, baseEnd_5717252] using wordTrace_append hprefix tailTrace_5717252
  have hstable : (prefixWord ++ tailWord_5717252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717252).length < 2 ^ (prefixWord ++ tailWord_5717252).sum := by decide
  have hdescent : baseEnd_5717252 < baseStart_5717252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717271 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 1, 7]
def baseStart_5717271 : Nat := 118140960795 + 5717271 * 2 ^ 59
def prefixEnd_5717271 : Nat := 4983230072969 + 3 ^ 40 * 5717271 * 2
def baseEnd_5717271 : Nat := 978569351670535294873085

theorem tailTrace_5717271 : CollatzResearch.WordTrace tailWord_5717271 prefixEnd_5717271 978569351670535294873085 := by
  unfold tailWord_5717271
  simp only [CollatzResearch.WordTrace]
  refine ⟨208526004470311073994175667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139017336313540715996117111 208526004470311073994175667)
  ·
    refine ⟨312789006705466610991263501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208526004470311073994175667 312789006705466610991263501)
    ·
      refine ⟨117295877514549979121723813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312789006705466610991263501 117295877514549979121723813)
      ·
        refine ⟨21992977033978121085323215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117295877514549979121723813 21992977033978121085323215)
        ·
          refine ⟨32989465550967181627984823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21992977033978121085323215 32989465550967181627984823)
          ·
            refine ⟨49484198326450772441977235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32989465550967181627984823 49484198326450772441977235)
            ·
              refine ⟨74226297489676158662965853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49484198326450772441977235 74226297489676158662965853)
              ·
                refine ⟨27834861558628559498612195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74226297489676158662965853 27834861558628559498612195)
                ·
                  refine ⟨41752292337942839247918293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27834861558628559498612195 41752292337942839247918293)
                  ·
                    refine ⟨978569351670535294873085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41752292337942839247918293 978569351670535294873085)
                    ·
                      rfl

theorem cell23_5717271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_5717271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717271 prefixEnd_5717271 := by exact prefixLift 5717271
  have htrace : WordTrace (prefixWord ++ tailWord_5717271) baseStart_5717271 baseEnd_5717271 := by
    simpa [prefixWord, tailWord_5717271, baseEnd_5717271] using wordTrace_append hprefix tailTrace_5717271
  have hstable : (prefixWord ++ tailWord_5717271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717271).length < 2 ^ (prefixWord ++ tailWord_5717271).sum := by decide
  have hdescent : baseEnd_5717271 < baseStart_5717271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717281 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_5717281 : Nat := 118140960795 + 5717281 * 2 ^ 59
def prefixEnd_5717281 : Nat := 4983230072969 + 3 ^ 40 * 5717281 * 2
def baseEnd_5717281 : Nat := 2935713189818150845494209

theorem tailTrace_5717281 : CollatzResearch.WordTrace tailWord_5717281 prefixEnd_5717281 2935713189818150845494209 := by
  unfold tailWord_5717281
  simp only [CollatzResearch.WordTrace]
  refine ⟨208526369200274845702039697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139017579466849897134693131 208526369200274845702039697)
  ·
    refine ⟨156394776900206134276529773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208526369200274845702039697 156394776900206134276529773)
    ·
      refine ⟨58648041337577300353698665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156394776900206134276529773 58648041337577300353698665)
      ·
        refine ⟨43986031003182975265273999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58648041337577300353698665 43986031003182975265273999)
        ·
          refine ⟨65979046504774462897910999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43986031003182975265273999 65979046504774462897910999)
          ·
            refine ⟨98968569757161694346866499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65979046504774462897910999 98968569757161694346866499)
            ·
              refine ⟨148452854635742541520299749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98968569757161694346866499 148452854635742541520299749)
              ·
                refine ⟨27834910244201726535056203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148452854635742541520299749 27834910244201726535056203)
                ·
                  refine ⟨41752365366302589802584305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27834910244201726535056203 41752365366302589802584305)
                  ·
                    refine ⟨31314274024726942351938229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41752365366302589802584305 31314274024726942351938229)
                    ·
                      refine ⟨2935713189818150845494209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31314274024726942351938229 2935713189818150845494209)
                      ·
                        rfl

theorem cell23_5717281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_5717281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717281 prefixEnd_5717281 := by exact prefixLift 5717281
  have htrace : WordTrace (prefixWord ++ tailWord_5717281) baseStart_5717281 baseEnd_5717281 := by
    simpa [prefixWord, tailWord_5717281, baseEnd_5717281] using wordTrace_append hprefix tailTrace_5717281
  have hstable : (prefixWord ++ tailWord_5717281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717281).length < 2 ^ (prefixWord ++ tailWord_5717281).sum := by decide
  have hdescent : baseEnd_5717281 < baseStart_5717281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717288 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 4, 5]
def baseStart_5717288 : Nat := 118140960795 + 5717288 * 2 ^ 59
def prefixEnd_5717288 : Nat := 4983230072969 + 3 ^ 40 * 5717288 * 2
def baseEnd_5717288 : Nat := 978572261394244106035559

theorem tailTrace_5717288 : CollatzResearch.WordTrace tailWord_5717288 prefixEnd_5717288 978572261394244106035559 := by
  unfold tailWord_5717288
  simp only [CollatzResearch.WordTrace]
  refine ⟨104263312255624742948772259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139017749674166323931696345 104263312255624742948772259)
  ·
    refine ⟨156394968383437114423158389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104263312255624742948772259 156394968383437114423158389)
    ·
      refine ⟨14662028285947229477171099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156394968383437114423158389 14662028285947229477171099)
      ·
        refine ⟨21993042428920844215756649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14662028285947229477171099 21993042428920844215756649)
        ·
          refine ⟨16494781821690633161817487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21993042428920844215756649 16494781821690633161817487)
          ·
            refine ⟨24742172732535949742726231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16494781821690633161817487 24742172732535949742726231)
            ·
              refine ⟨37113259098803924614089347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24742172732535949742726231 37113259098803924614089347)
              ·
                refine ⟨55669888648205886921134021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37113259098803924614089347 55669888648205886921134021)
                ·
                  refine ⟨10438104121538603797712629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55669888648205886921134021 10438104121538603797712629)
                  ·
                    refine ⟨978572261394244106035559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10438104121538603797712629 978572261394244106035559)
                    ·
                      rfl

theorem cell23_5717288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_5717288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717288 prefixEnd_5717288 := by exact prefixLift 5717288
  have htrace : WordTrace (prefixWord ++ tailWord_5717288) baseStart_5717288 baseEnd_5717288 := by
    simpa [prefixWord, tailWord_5717288, baseEnd_5717288] using wordTrace_append hprefix tailTrace_5717288
  have hstable : (prefixWord ++ tailWord_5717288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717288).length < 2 ^ (prefixWord ++ tailWord_5717288).sum := by decide
  have hdescent : baseEnd_5717288 < baseStart_5717288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717298 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_5717298 : Nat := 118140960795 + 5717298 * 2 ^ 59
def prefixEnd_5717298 : Nat := 4983230072969 + 3 ^ 40 * 5717298 * 2
def baseEnd_5717298 : Nat := 2935721918989277278981631

theorem tailTrace_5717298 : CollatzResearch.WordTrace tailWord_5717298 prefixEnd_5717298 2935721918989277278981631 := by
  unfold tailWord_5717298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52131747310303314401352137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139017992827475505070272365 52131747310303314401352137)
  ·
    refine ⟨39098810482727485801014103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52131747310303314401352137 39098810482727485801014103)
    ·
      refine ⟨58648215724091228701521155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39098810482727485801014103 58648215724091228701521155)
      ·
        refine ⟨87972323586136843052281733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58648215724091228701521155 87972323586136843052281733)
        ·
          refine ⟨16494810672400658072302825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87972323586136843052281733 16494810672400658072302825)
          ·
            refine ⟨12371108004300493554227119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16494810672400658072302825 12371108004300493554227119)
            ·
              refine ⟨18556662006450740331340679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12371108004300493554227119 18556662006450740331340679)
              ·
                refine ⟨27834993009676110497011019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18556662006450740331340679 27834993009676110497011019)
                ·
                  refine ⟨41752489514514165745516529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27834993009676110497011019 41752489514514165745516529)
                  ·
                    refine ⟨31314367135885624309137397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41752489514514165745516529 31314367135885624309137397)
                    ·
                      refine ⟨2935721918989277278981631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31314367135885624309137397 2935721918989277278981631)
                      ·
                        rfl

theorem cell23_5717298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_5717298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717298 prefixEnd_5717298 := by exact prefixLift 5717298
  have htrace : WordTrace (prefixWord ++ tailWord_5717298) baseStart_5717298 baseEnd_5717298 := by
    simpa [prefixWord, tailWord_5717298, baseEnd_5717298] using wordTrace_append hprefix tailTrace_5717298
  have hstable : (prefixWord ++ tailWord_5717298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717298).length < 2 ^ (prefixWord ++ tailWord_5717298).sum := by decide
  have hdescent : baseEnd_5717298 < baseStart_5717298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717321 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_5717321 : Nat := 118140960795 + 5717321 * 2 ^ 59
def prefixEnd_5717321 : Nat := 4983230072969 + 3 ^ 40 * 5717321 * 2
def baseEnd_5717321 : Nat := 2935733729044330688994025

theorem tailTrace_5717321 : CollatzResearch.WordTrace tailWord_5717321 prefixEnd_5717321 2935733729044330688994025 := by
  unfold tailWord_5717321
  simp only [CollatzResearch.WordTrace]
  refine ⟨208527828120129932533495817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139018552080086621688997211 208527828120129932533495817)
  ·
    refine ⟨156395871090097449400121863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208527828120129932533495817 156395871090097449400121863)
    ·
      refine ⟨234593806635146174100182795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156395871090097449400121863 234593806635146174100182795)
      ·
        refine ⟨351890709952719261150274193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234593806635146174100182795 351890709952719261150274193)
        ·
          refine ⟨263918032464539445862705645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351890709952719261150274193 263918032464539445862705645)
          ·
            refine ⟨98969262174202292198514617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263918032464539445862705645 98969262174202292198514617)
            ·
              refine ⟨74226946630651719148885963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98969262174202292198514617 74226946630651719148885963)
              ·
                refine ⟨111340419945977578723328945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74226946630651719148885963 111340419945977578723328945)
                ·
                  refine ⟨83505314959483184042496709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111340419945977578723328945 83505314959483184042496709)
                  ·
                    refine ⟨15657246554903097007968133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83505314959483184042496709 15657246554903097007968133)
                    ·
                      refine ⟨2935733729044330688994025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15657246554903097007968133 2935733729044330688994025)
                      ·
                        rfl

theorem cell23_5717321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_5717321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717321 prefixEnd_5717321 := by exact prefixLift 5717321
  have htrace : WordTrace (prefixWord ++ tailWord_5717321) baseStart_5717321 baseEnd_5717321 := by
    simpa [prefixWord, tailWord_5717321, baseEnd_5717321] using wordTrace_append hprefix tailTrace_5717321
  have hstable : (prefixWord ++ tailWord_5717321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717321).length < 2 ^ (prefixWord ++ tailWord_5717321).sum := by decide
  have hdescent : baseEnd_5717321 < baseStart_5717321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717348 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 6]
def baseStart_5717348 : Nat := 118140960795 + 5717348 * 2 ^ 59
def prefixEnd_5717348 : Nat := 4983230072969 + 3 ^ 40 * 5717348 * 2
def baseEnd_5717348 : Nat := 326194177002444675928489

theorem tailTrace_5717348 : CollatzResearch.WordTrace tailWord_5717348 prefixEnd_5717348 326194177002444675928489 := by
  unfold tailWord_5717348
  simp only [CollatzResearch.WordTrace]
  refine ⟨104264406445516058072364349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139019208594021410763152465 104264406445516058072364349)
  ·
    refine ⟨39099152417068521777136631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104264406445516058072364349 39099152417068521777136631)
    ·
      refine ⟨58648728625602782665704947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39099152417068521777136631 58648728625602782665704947)
      ·
        refine ⟨87973092938404173998557421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58648728625602782665704947 87973092938404173998557421)
        ·
          refine ⟨32989909851901565249459033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87973092938404173998557421 32989909851901565249459033)
          ·
            refine ⟨24742432388926173937094275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32989909851901565249459033 24742432388926173937094275)
            ·
              refine ⟨37113648583389260905641413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24742432388926173937094275 37113648583389260905641413)
              ·
                refine ⟨6958809109385486419807765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37113648583389260905641413 6958809109385486419807765)
                ·
                  refine ⟨326194177002444675928489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6958809109385486419807765 326194177002444675928489)
                  ·
                    rfl

theorem cell23_5717348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_5717348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717348 prefixEnd_5717348 := by exact prefixLift 5717348
  have htrace : WordTrace (prefixWord ++ tailWord_5717348) baseStart_5717348 baseEnd_5717348 := by
    simpa [prefixWord, tailWord_5717348, baseEnd_5717348] using wordTrace_append hprefix tailTrace_5717348
  have hstable : (prefixWord ++ tailWord_5717348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717348).length < 2 ^ (prefixWord ++ tailWord_5717348).sum := by decide
  have hdescent : baseEnd_5717348 < baseStart_5717348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717371 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 7]
def baseStart_5717371 : Nat := 118140960795 + 5717371 * 2 ^ 59
def prefixEnd_5717371 : Nat := 4983230072969 + 3 ^ 40 * 5717371 * 2
def baseEnd_5717371 : Nat := 2935759403077055493368795

theorem tailTrace_5717371 : CollatzResearch.WordTrace tailWord_5717371 prefixEnd_5717371 2935759403077055493368795 := by
  unfold tailWord_5717371
  simp only [CollatzResearch.WordTrace]
  refine ⟨208529651769948791072815967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139019767846632527381877311 208529651769948791072815967)
  ·
    refine ⟨312794477654923186609223951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208529651769948791072815967 312794477654923186609223951)
    ·
      refine ⟨469191716482384779913835927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312794477654923186609223951 469191716482384779913835927)
      ·
        refine ⟨703787574723577169870753891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469191716482384779913835927 703787574723577169870753891)
        ·
          refine ⟨1055681362085365754806130837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703787574723577169870753891 1055681362085365754806130837)
          ·
            refine ⟨49485063847751519756537383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1055681362085365754806130837 49485063847751519756537383)
            ·
              refine ⟨74227595771627279634806075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49485063847751519756537383 74227595771627279634806075)
              ·
                refine ⟨111341393657440919452209113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74227595771627279634806075 111341393657440919452209113)
                ·
                  refine ⟨83506045243080689589156835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111341393657440919452209113 83506045243080689589156835)
                  ·
                    refine ⟨125259067864621034383735253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83506045243080689589156835 125259067864621034383735253)
                    ·
                      refine ⟨2935759403077055493368795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125259067864621034383735253 2935759403077055493368795)
                      ·
                        rfl

theorem cell23_5717371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_5717371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717371 prefixEnd_5717371 := by exact prefixLift 5717371
  have htrace : WordTrace (prefixWord ++ tailWord_5717371) baseStart_5717371 baseEnd_5717371 := by
    simpa [prefixWord, tailWord_5717371, baseEnd_5717371] using wordTrace_append hprefix tailTrace_5717371
  have hstable : (prefixWord ++ tailWord_5717371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717371).length < 2 ^ (prefixWord ++ tailWord_5717371).sum := by decide
  have hdescent : baseEnd_5717371 < baseStart_5717371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717432 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 3, 2, 2]
def baseStart_5717432 : Nat := 118140960795 + 5717432 * 2 ^ 59
def prefixEnd_5717432 : Nat := 4983230072969 + 3 ^ 40 * 5717432 * 2
def baseEnd_5717432 : Nat := 2935790725396979754706015

theorem tailTrace_5717432 : CollatzResearch.WordTrace tailWord_5717432 prefixEnd_5717432 2935790725396979754706015 := by
  unfold tailWord_5717432
  simp only [CollatzResearch.WordTrace]
  refine ⟨104265938311363899245393275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139021251081818532327191033 104265938311363899245393275)
  ·
    refine ⟨156398907467045848868089913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104265938311363899245393275 156398907467045848868089913)
    ·
      refine ⟨117299180600284386651067435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156398907467045848868089913 117299180600284386651067435)
      ·
        refine ⟨175948770900426579976601153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117299180600284386651067435 175948770900426579976601153)
        ·
          refine ⟨131961578175319934982450865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175948770900426579976601153 131961578175319934982450865)
          ·
            refine ⟨98971183631489951236838149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131961578175319934982450865 98971183631489951236838149)
            ·
              refine ⟨18557096930904365856907153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98971183631489951236838149 18557096930904365856907153)
              ·
                refine ⟨13917822698178274392680365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18557096930904365856907153 13917822698178274392680365)
                ·
                  refine ⟨5219183511816852897255137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13917822698178274392680365 5219183511816852897255137)
                  ·
                    refine ⟨3914387633862639672941353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5219183511816852897255137 3914387633862639672941353)
                    ·
                      refine ⟨2935790725396979754706015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914387633862639672941353 2935790725396979754706015)
                      ·
                        rfl

theorem cell23_5717432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_5717432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717432 prefixEnd_5717432 := by exact prefixLift 5717432
  have htrace : WordTrace (prefixWord ++ tailWord_5717432) baseStart_5717432 baseEnd_5717432 := by
    simpa [prefixWord, tailWord_5717432, baseEnd_5717432] using wordTrace_append hprefix tailTrace_5717432
  have hstable : (prefixWord ++ tailWord_5717432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717432).length < 2 ^ (prefixWord ++ tailWord_5717432).sum := by decide
  have hdescent : baseEnd_5717432 < baseStart_5717432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717452 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 1, 2, 3]
def baseStart_5717452 : Nat := 118140960795 + 5717452 * 2 ^ 59
def prefixEnd_5717452 : Nat := 4983230072969 + 3 ^ 40 * 5717452 * 2
def baseEnd_5717452 : Nat := 2935800995010069676455923

theorem tailTrace_5717452 : CollatzResearch.WordTrace tailWord_5717452 prefixEnd_5717452 2935800995010069676455923 := by
  unfold tailWord_5717452
  simp only [CollatzResearch.WordTrace]
  refine ⟨104266303041327670953257305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139021737388436894604343073 104266303041327670953257305)
  ·
    refine ⟨78199727280995753214942979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104266303041327670953257305 78199727280995753214942979)
    ·
      refine ⟨117299590921493629822414469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78199727280995753214942979 117299590921493629822414469)
      ·
        refine ⟨21993673297780055591702713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117299590921493629822414469 21993673297780055591702713)
        ·
          refine ⟨16495254973335041693777035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21993673297780055591702713 16495254973335041693777035)
          ·
            refine ⟨24742882460002562540665553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16495254973335041693777035 24742882460002562540665553)
            ·
              refine ⟨18557161845001921905499165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24742882460002562540665553 18557161845001921905499165)
              ·
                refine ⟨6958935691875720714562187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18557161845001921905499165 6958935691875720714562187)
                ·
                  refine ⟨10438403537813581071843281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6958935691875720714562187 10438403537813581071843281)
                  ·
                    refine ⟨7828802653360185803882461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10438403537813581071843281 7828802653360185803882461)
                    ·
                      refine ⟨2935800995010069676455923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7828802653360185803882461 2935800995010069676455923)
                      ·
                        rfl

theorem cell23_5717452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_5717452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717452 prefixEnd_5717452 := by exact prefixLift 5717452
  have htrace : WordTrace (prefixWord ++ tailWord_5717452) baseStart_5717452 baseEnd_5717452 := by
    simpa [prefixWord, tailWord_5717452, baseEnd_5717452] using wordTrace_append hprefix tailTrace_5717452
  have hstable : (prefixWord ++ tailWord_5717452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717452).length < 2 ^ (prefixWord ++ tailWord_5717452).sum := by decide
  have hdescent : baseEnd_5717452 < baseStart_5717452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717525 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_5717525 : Nat := 118140960795 + 5717525 * 2 ^ 59
def prefixEnd_5717525 : Nat := 4983230072969 + 3 ^ 40 * 5717525 * 2
def baseEnd_5717525 : Nat := 2935838479097847890843087

theorem tailTrace_5717525 : CollatzResearch.WordTrace tailWord_5717525 prefixEnd_5717525 2935838479097847890843087 := by
  unfold tailWord_5717525
  simp only [CollatzResearch.WordTrace]
  refine ⟨208535268611390875373922029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139023512407593916915948019 208535268611390875373922029)
  ·
    refine ⟨78200725729271578265220761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208535268611390875373922029 78200725729271578265220761)
    ·
      refine ⟨58650544296953683698915571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78200725729271578265220761 58650544296953683698915571)
      ·
        refine ⟨87975816445430525548373357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58650544296953683698915571 87975816445430525548373357)
        ·
          refine ⟨32990931167036447080640009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87975816445430525548373357 32990931167036447080640009)
          ·
            refine ⟨24743198375277335310480007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32990931167036447080640009 24743198375277335310480007)
            ·
              refine ⟨37114797562916002965720011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24743198375277335310480007 37114797562916002965720011)
              ·
                refine ⟨55672196344374004448580017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37114797562916002965720011 55672196344374004448580017)
                ·
                  refine ⟨41754147258280503336435013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55672196344374004448580017 41754147258280503336435013)
                  ·
                    refine ⟨7828902610927594375581565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41754147258280503336435013 7828902610927594375581565)
                    ·
                      refine ⟨2935838479097847890843087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7828902610927594375581565 2935838479097847890843087)
                      ·
                        rfl

theorem cell23_5717525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_5717525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717525 prefixEnd_5717525 := by exact prefixLift 5717525
  have htrace : WordTrace (prefixWord ++ tailWord_5717525) baseStart_5717525 baseEnd_5717525 := by
    simpa [prefixWord, tailWord_5717525, baseEnd_5717525] using wordTrace_append hprefix tailTrace_5717525
  have hstable : (prefixWord ++ tailWord_5717525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717525).length < 2 ^ (prefixWord ++ tailWord_5717525).sum := by decide
  have hdescent : baseEnd_5717525 < baseStart_5717525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717539 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 1, 4, 2]
def baseStart_5717539 : Nat := 118140960795 + 5717539 * 2 ^ 59
def prefixEnd_5717539 : Nat := 4983230072969 + 3 ^ 40 * 5717539 * 2
def baseEnd_5717539 : Nat := 2935845667827010836068023

theorem tailTrace_5717539 : CollatzResearch.WordTrace tailWord_5717539 prefixEnd_5717539 2935845667827010836068023 := by
  unfold tailWord_5717539
  simp only [CollatzResearch.WordTrace]
  refine ⟨208535779233340155764931671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139023852822226770509954447 208535779233340155764931671)
  ·
    refine ⟨312803668850010233647397507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208535779233340155764931671 312803668850010233647397507)
    ·
      refine ⟨469205503275015350471096261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312803668850010233647397507 469205503275015350471096261)
      ·
        refine ⟨87976031864065378213330549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 469205503275015350471096261 87976031864065378213330549)
        ·
          refine ⟨8247752987256129207499739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87976031864065378213330549 8247752987256129207499739)
          ·
            refine ⟨12371629480884193811249609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8247752987256129207499739 12371629480884193811249609)
            ·
              refine ⟨9278722110663145358437207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12371629480884193811249609 9278722110663145358437207)
              ·
                refine ⟨13918083165994718037655811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9278722110663145358437207 13918083165994718037655811)
                ·
                  refine ⟨20877124748992077056483717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13918083165994718037655811 20877124748992077056483717)
                  ·
                    refine ⟨3914460890436014448090697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20877124748992077056483717 3914460890436014448090697)
                    ·
                      refine ⟨2935845667827010836068023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914460890436014448090697 2935845667827010836068023)
                      ·
                        rfl

theorem cell23_5717539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_5717539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717539 prefixEnd_5717539 := by exact prefixLift 5717539
  have htrace : WordTrace (prefixWord ++ tailWord_5717539) baseStart_5717539 baseEnd_5717539 := by
    simpa [prefixWord, tailWord_5717539, baseEnd_5717539] using wordTrace_append hprefix tailTrace_5717539
  have hstable : (prefixWord ++ tailWord_5717539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717539).length < 2 ^ (prefixWord ++ tailWord_5717539).sum := by decide
  have hdescent : baseEnd_5717539 < baseStart_5717539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717562 : List Nat := [3, 1, 1, 1, 3, 2, 4, 3, 5]
def baseStart_5717562 : Nat := 118140960795 + 5717562 * 2 ^ 59
def prefixEnd_5717562 : Nat := 4983230072969 + 3 ^ 40 * 5717562 * 2
def baseEnd_5717562 : Nat := 326206386431340471786713

theorem tailTrace_5717562 : CollatzResearch.WordTrace tailWord_5717562 prefixEnd_5717562 326206386431340471786713 := by
  unfold tailWord_5717562
  simp only [CollatzResearch.WordTrace]
  refine ⟨52134154528064207673254735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139024412074837887128679293 52134154528064207673254735)
  ·
    refine ⟨78201231792096311509882103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52134154528064207673254735 78201231792096311509882103)
    ·
      refine ⟨117301847688144467264823155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78201231792096311509882103 117301847688144467264823155)
      ·
        refine ⟨175952771532216700897234733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117301847688144467264823155 175952771532216700897234733)
        ·
          refine ⟨65982289324581262836463025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175952771532216700897234733 65982289324581262836463025)
          ·
            refine ⟨49486716993435947127347269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65982289324581262836463025 49486716993435947127347269)
            ·
              refine ⟨9278759436269240086377613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49486716993435947127347269 9278759436269240086377613)
              ·
                refine ⟨3479534788600965032391605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9278759436269240086377613 3479534788600965032391605)
                ·
                  refine ⟨326206386431340471786713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3479534788600965032391605 326206386431340471786713)
                  ·
                    rfl

theorem cell23_5717562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_5717562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717562 prefixEnd_5717562 := by exact prefixLift 5717562
  have htrace : WordTrace (prefixWord ++ tailWord_5717562) baseStart_5717562 baseEnd_5717562 := by
    simpa [prefixWord, tailWord_5717562, baseEnd_5717562] using wordTrace_append hprefix tailTrace_5717562
  have hstable : (prefixWord ++ tailWord_5717562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717562).length < 2 ^ (prefixWord ++ tailWord_5717562).sum := by decide
  have hdescent : baseEnd_5717562 < baseStart_5717562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717590 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_5717590 : Nat := 118140960795 + 5717590 * 2 ^ 59
def prefixEnd_5717590 : Nat := 4983230072969 + 3 ^ 40 * 5717590 * 2
def baseEnd_5717590 : Nat := 2935871855340390136530289

theorem tailTrace_5717590 : CollatzResearch.WordTrace tailWord_5717590 prefixEnd_5717590 2935871855340390136530289 := by
  unfold tailWord_5717590
  simp only [CollatzResearch.WordTrace]
  refine ⟨13033602459759711967189889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139025092904103594316692149 13033602459759711967189889)
  ·
    refine ⟨9775201844819783975392417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13033602459759711967189889 9775201844819783975392417)
    ·
      refine ⟨7331401383614837981544313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9775201844819783975392417 7331401383614837981544313)
      ·
        refine ⟨5498551037711128486158235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7331401383614837981544313 5498551037711128486158235)
        ·
          refine ⟨8247826556566692729237353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5498551037711128486158235 8247826556566692729237353)
          ·
            refine ⟨6185869917425019546928015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8247826556566692729237353 6185869917425019546928015)
            ·
              refine ⟨9278804876137529320392023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6185869917425019546928015 9278804876137529320392023)
              ·
                refine ⟨13918207314206293980588035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9278804876137529320392023 13918207314206293980588035)
                ·
                  refine ⟨20877310971309440970882053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13918207314206293980588035 20877310971309440970882053)
                  ·
                    refine ⟨3914495807120520182040385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20877310971309440970882053 3914495807120520182040385)
                    ·
                      refine ⟨2935871855340390136530289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914495807120520182040385 2935871855340390136530289)
                      ·
                        rfl

theorem cell23_5717590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_5717590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717590 prefixEnd_5717590 := by exact prefixLift 5717590
  have htrace : WordTrace (prefixWord ++ tailWord_5717590) baseStart_5717590 baseEnd_5717590 := by
    simpa [prefixWord, tailWord_5717590, baseEnd_5717590] using wordTrace_append hprefix tailTrace_5717590
  have hstable : (prefixWord ++ tailWord_5717590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717590).length < 2 ^ (prefixWord ++ tailWord_5717590).sum := by decide
  have hdescent : baseEnd_5717590 < baseStart_5717590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717632 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 3]
def baseStart_5717632 : Nat := 118140960795 + 5717632 * 2 ^ 59
def prefixEnd_5717632 : Nat := 4983230072969 + 3 ^ 40 * 5717632 * 2
def baseEnd_5717632 : Nat := 2935893421527878972205095

theorem tailTrace_5717632 : CollatzResearch.WordTrace tailWord_5717632 prefixEnd_5717632 2935893421527878972205095 := by
  unfold tailWord_5717632
  simp only [CollatzResearch.WordTrace]
  refine ⟨104269585611001616324033575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139026114148002155098711433 104269585611001616324033575)
  ·
    refine ⟨156404378416502424486050363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104269585611001616324033575 156404378416502424486050363)
    ·
      refine ⟨234606567624753636729075545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156404378416502424486050363 234606567624753636729075545)
      ·
        refine ⟨175954925718565227546806659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234606567624753636729075545 175954925718565227546806659)
        ·
          refine ⟨263932388577847841320209989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175954925718565227546806659 263932388577847841320209989)
          ·
            refine ⟨49487322858346470247539373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263932388577847841320209989 49487322858346470247539373)
            ·
              refine ⟨18557746071879926342827265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49487322858346470247539373 18557746071879926342827265)
              ·
                refine ⟨13918309553909944757120449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18557746071879926342827265 13918309553909944757120449)
                ·
                  refine ⟨10438732165432458567840337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13918309553909944757120449 10438732165432458567840337)
                  ·
                    refine ⟨7829049124074343925880253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10438732165432458567840337 7829049124074343925880253)
                    ·
                      refine ⟨2935893421527878972205095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7829049124074343925880253 2935893421527878972205095)
                      ·
                        rfl

theorem cell23_5717632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_5717632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717632 prefixEnd_5717632 := by exact prefixLift 5717632
  have htrace : WordTrace (prefixWord ++ tailWord_5717632) baseStart_5717632 baseEnd_5717632 := by
    simpa [prefixWord, tailWord_5717632, baseEnd_5717632] using wordTrace_append hprefix tailTrace_5717632
  have hstable : (prefixWord ++ tailWord_5717632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717632).length < 2 ^ (prefixWord ++ tailWord_5717632).sum := by decide
  have hdescent : baseEnd_5717632 < baseStart_5717632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717635 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 6]
def baseStart_5717635 : Nat := 118140960795 + 5717635 * 2 ^ 59
def prefixEnd_5717635 : Nat := 4983230072969 + 3 ^ 40 * 5717635 * 2
def baseEnd_5717635 : Nat := 326210551329982495607509

theorem tailTrace_5717635 : CollatzResearch.WordTrace tailWord_5717635 prefixEnd_5717635 326210551329982495607509 := by
  unfold tailWord_5717635
  simp only [CollatzResearch.WordTrace]
  refine ⟨208539280640992364160426359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139026187093994909440284239 208539280640992364160426359)
  ·
    refine ⟨312808920961488546240639539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208539280640992364160426359 312808920961488546240639539)
    ·
      refine ⟨469213381442232819360959309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312808920961488546240639539 469213381442232819360959309)
      ·
        refine ⟨175955018040837307260359741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 469213381442232819360959309 175955018040837307260359741)
        ·
          refine ⟨65983131765313990222634903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175955018040837307260359741 65983131765313990222634903)
          ·
            refine ⟨98974697647970985333952355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65983131765313990222634903 98974697647970985333952355)
            ·
              refine ⟨148462046471956478000928533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98974697647970985333952355 148462046471956478000928533)
              ·
                refine ⟨6959158428372959906293525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148462046471956478000928533 6959158428372959906293525)
                ·
                  refine ⟨326210551329982495607509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6959158428372959906293525 326210551329982495607509)
                  ·
                    rfl

theorem cell23_5717635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 6].length) (baseStart_5717635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717635 prefixEnd_5717635 := by exact prefixLift 5717635
  have htrace : WordTrace (prefixWord ++ tailWord_5717635) baseStart_5717635 baseEnd_5717635 := by
    simpa [prefixWord, tailWord_5717635, baseEnd_5717635] using wordTrace_append hprefix tailTrace_5717635
  have hstable : (prefixWord ++ tailWord_5717635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717635).length < 2 ^ (prefixWord ++ tailWord_5717635).sum := by decide
  have hdescent : baseEnd_5717635 < baseStart_5717635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717639 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 3, 4]
def baseStart_5717639 : Nat := 118140960795 + 5717639 * 2 ^ 59
def prefixEnd_5717639 : Nat := 4983230072969 + 3 ^ 40 * 5717639 * 2
def baseEnd_5717639 : Nat := 978632338630820148272521

theorem tailTrace_5717639 : CollatzResearch.WordTrace tailWord_5717639 prefixEnd_5717639 978632338630820148272521 := by
  unfold tailWord_5717639
  simp only [CollatzResearch.WordTrace]
  refine ⟨208539426532977872843571971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139026284355318581895714647 208539426532977872843571971)
  ·
    refine ⟨312809139799466809265357957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208539426532977872843571971 312809139799466809265357957)
    ·
      refine ⟨58651713712400026737254617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312809139799466809265357957 58651713712400026737254617)
      ·
        refine ⟨43988785284300020052940963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58651713712400026737254617 43988785284300020052940963)
        ·
          refine ⟨65983177926450030079411445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43988785284300020052940963 65983177926450030079411445)
          ·
            refine ⟨6185922930604690319944823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65983177926450030079411445 6185922930604690319944823)
            ·
              refine ⟨9278884395907035479917235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6185922930604690319944823 9278884395907035479917235)
              ·
                refine ⟨13918326593860553219875853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9278884395907035479917235 13918326593860553219875853)
                ·
                  refine ⟨5219372472697707457453445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13918326593860553219875853 5219372472697707457453445)
                  ·
                    refine ⟨978632338630820148272521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5219372472697707457453445 978632338630820148272521)
                    ·
                      rfl

theorem cell23_5717639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_5717639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717639 prefixEnd_5717639 := by exact prefixLift 5717639
  have htrace : WordTrace (prefixWord ++ tailWord_5717639) baseStart_5717639 baseEnd_5717639 := by
    simpa [prefixWord, tailWord_5717639, baseEnd_5717639] using wordTrace_append hprefix tailTrace_5717639
  have hstable : (prefixWord ++ tailWord_5717639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717639).length < 2 ^ (prefixWord ++ tailWord_5717639).sum := by decide
  have hdescent : baseEnd_5717639 < baseStart_5717639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717682 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_5717682 : Nat := 118140960795 + 5717682 * 2 ^ 59
def prefixEnd_5717682 : Nat := 4983230072969 + 3 ^ 40 * 5717682 * 2
def baseEnd_5717682 : Nat := 978639698520201258859955

theorem tailTrace_5717682 : CollatzResearch.WordTrace tailWord_5717682 prefixEnd_5717682 978639698520201258859955 := by
  unfold tailWord_5717682
  simp only [CollatzResearch.WordTrace]
  refine ⟨52135248717955522796846825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139027329914548060791591533 52135248717955522796846825)
  ·
    refine ⟨39101436538466642097635119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52135248717955522796846825 39101436538466642097635119)
    ·
      refine ⟨58652154807699963146452679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39101436538466642097635119 58652154807699963146452679)
      ·
        refine ⟨87978232211549944719679019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58652154807699963146452679 87978232211549944719679019)
        ·
          refine ⟨131967348317324917079518529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87978232211549944719679019 131967348317324917079518529)
          ·
            refine ⟨98975511237993687809638897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131967348317324917079518529 98975511237993687809638897)
            ·
              refine ⟨74231633428495265857229173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98975511237993687809638897 74231633428495265857229173)
              ·
                refine ⟨6959215633921431174115235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74231633428495265857229173 6959215633921431174115235)
                ·
                  refine ⟨10438823450882146761172853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6959215633921431174115235 10438823450882146761172853)
                  ·
                    refine ⟨978639698520201258859955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10438823450882146761172853 978639698520201258859955)
                    ·
                      rfl

theorem cell23_5717682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_5717682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717682 prefixEnd_5717682 := by exact prefixLift 5717682
  have htrace : WordTrace (prefixWord ++ tailWord_5717682) baseStart_5717682 baseEnd_5717682 := by
    simpa [prefixWord, tailWord_5717682, baseEnd_5717682] using wordTrace_append hprefix tailTrace_5717682
  have hstable : (prefixWord ++ tailWord_5717682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717682).length < 2 ^ (prefixWord ++ tailWord_5717682).sum := by decide
  have hdescent : baseEnd_5717682 < baseStart_5717682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717686 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_5717686 : Nat := 118140960795 + 5717686 * 2 ^ 59
def prefixEnd_5717686 : Nat := 4983230072969 + 3 ^ 40 * 5717686 * 2
def baseEnd_5717686 : Nat := 326213461053691306769983

theorem tailTrace_5717686 : CollatzResearch.WordTrace tailWord_5717686 prefixEnd_5717686 326213461053691306769983 := by
  unfold tailWord_5717686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13033821297737974991908307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139027427175871733247021941 13033821297737974991908307)
  ·
    refine ⟨19550731946606962487862461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13033821297737974991908307 19550731946606962487862461)
    ·
      refine ⟨7331524479977610932948423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19550731946606962487862461 7331524479977610932948423)
      ·
        refine ⟨10997286719966416399422635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7331524479977610932948423 10997286719966416399422635)
        ·
          refine ⟨16495930079949624599133953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10997286719966416399422635 16495930079949624599133953)
          ·
            refine ⟨12371947559962218449350465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16495930079949624599133953 12371947559962218449350465)
            ·
              refine ⟨9278960669971663837012849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12371947559962218449350465 9278960669971663837012849)
              ·
                refine ⟨6959220502478747877759637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9278960669971663837012849 6959220502478747877759637)
                ·
                  refine ⟨326213461053691306769983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6959220502478747877759637 326213461053691306769983)
                  ·
                    rfl

theorem cell23_5717686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_5717686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717686 prefixEnd_5717686 := by exact prefixLift 5717686
  have htrace : WordTrace (prefixWord ++ tailWord_5717686) baseStart_5717686 baseEnd_5717686 := by
    simpa [prefixWord, tailWord_5717686, baseEnd_5717686] using wordTrace_append hprefix tailTrace_5717686
  have hstable : (prefixWord ++ tailWord_5717686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717686).length < 2 ^ (prefixWord ++ tailWord_5717686).sum := by decide
  have hdescent : baseEnd_5717686 < baseStart_5717686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717689 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 2, 3, 2]
def baseStart_5717689 : Nat := 118140960795 + 5717689 * 2 ^ 59
def prefixEnd_5717689 : Nat := 4983230072969 + 3 ^ 40 * 5717689 * 2
def baseEnd_5717689 : Nat := 2935922689925185249192333

theorem tailTrace_5717689 : CollatzResearch.WordTrace tailWord_5717689 prefixEnd_5717689 2935922689925185249192333 := by
  unfold tailWord_5717689
  simp only [CollatzResearch.WordTrace]
  refine ⟨208541250182796731382892121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139027500121864487588594747 208541250182796731382892121)
  ·
    refine ⟨156405937637097548537169091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208541250182796731382892121 156405937637097548537169091)
    ·
      refine ⟨234608906455646322805753637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156405937637097548537169091 234608906455646322805753637)
      ·
        refine ⟨43989169960433685526078807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234608906455646322805753637 43989169960433685526078807)
        ·
          refine ⟨65983754940650528289118211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43989169960433685526078807 65983754940650528289118211)
          ·
            refine ⟨98975632410975792433677317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65983754940650528289118211 98975632410975792433677317)
            ·
              refine ⟨18557931077057961081314497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98975632410975792433677317 18557931077057961081314497)
              ·
                refine ⟨13918448307793470810985873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18557931077057961081314497 13918448307793470810985873)
                ·
                  refine ⟨10438836230845103108239405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13918448307793470810985873 10438836230845103108239405)
                  ·
                    refine ⟨3914563586566913665589777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10438836230845103108239405 3914563586566913665589777)
                    ·
                      refine ⟨2935922689925185249192333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914563586566913665589777 2935922689925185249192333)
                      ·
                        rfl

theorem cell23_5717689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_5717689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717689 prefixEnd_5717689 := by exact prefixLift 5717689
  have htrace : WordTrace (prefixWord ++ tailWord_5717689) baseStart_5717689 baseEnd_5717689 := by
    simpa [prefixWord, tailWord_5717689, baseEnd_5717689] using wordTrace_append hprefix tailTrace_5717689
  have hstable : (prefixWord ++ tailWord_5717689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717689).length < 2 ^ (prefixWord ++ tailWord_5717689).sum := by decide
  have hdescent : baseEnd_5717689 < baseStart_5717689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717695 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 3, 6]
def baseStart_5717695 : Nat := 118140960795 + 5717695 * 2 ^ 59
def prefixEnd_5717695 : Nat := 4983230072969 + 3 ^ 40 * 5717695 * 2
def baseEnd_5717695 : Nat := 978641923603037408572435

theorem tailTrace_5717695 : CollatzResearch.WordTrace tailWord_5717695 prefixEnd_5717695 978641923603037408572435 := by
  unfold tailWord_5717695
  simp only [CollatzResearch.WordTrace]
  refine ⟨208541469020774994407610539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139027646013849996271740359 208541469020774994407610539)
  ·
    refine ⟨312812203531162491611415809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208541469020774994407610539 312812203531162491611415809)
    ·
      refine ⟨234609152648371868708561857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312812203531162491611415809 234609152648371868708561857)
      ·
        refine ⟨175956864486278901531421393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234609152648371868708561857 175956864486278901531421393)
        ·
          refine ⟨131967648364709176148566045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175956864486278901531421393 131967648364709176148566045)
          ·
            refine ⟨49487868136765941055712267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131967648364709176148566045 49487868136765941055712267)
            ·
              refine ⟨74231802205148911583568401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49487868136765941055712267 74231802205148911583568401)
              ·
                refine ⟨55673851653861683687676301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74231802205148911583568401 55673851653861683687676301)
                ·
                  refine ⟨20877694370198131382878613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55673851653861683687676301 20877694370198131382878613)
                  ·
                    refine ⟨978641923603037408572435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20877694370198131382878613 978641923603037408572435)
                    ·
                      rfl

theorem cell23_5717695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_5717695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717695 prefixEnd_5717695 := by exact prefixLift 5717695
  have htrace : WordTrace (prefixWord ++ tailWord_5717695) baseStart_5717695 baseEnd_5717695 := by
    simpa [prefixWord, tailWord_5717695, baseEnd_5717695] using wordTrace_append hprefix tailTrace_5717695
  have hstable : (prefixWord ++ tailWord_5717695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717695).length < 2 ^ (prefixWord ++ tailWord_5717695).sum := by decide
  have hdescent : baseEnd_5717695 < baseStart_5717695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717696 : List Nat := [2, 1, 1, 2, 4, 1, 3, 4, 1, 1, 3]
def baseStart_5717696 : Nat := 118140960795 + 5717696 * 2 ^ 59
def prefixEnd_5717696 : Nat := 4983230072969 + 3 ^ 40 * 5717696 * 2
def baseEnd_5717696 : Nat := 2935926284289766721804801

theorem tailTrace_5717696 : CollatzResearch.WordTrace tailWord_5717696 prefixEnd_5717696 2935926284289766721804801 := by
  unfold tailWord_5717696
  simp only [CollatzResearch.WordTrace]
  refine ⟨104270752746885685789198471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139027670329180914385597961 104270752746885685789198471)
  ·
    refine ⟨156406129120328528683797707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104270752746885685789198471 156406129120328528683797707)
    ·
      refine ⟨234609193680492793025696561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156406129120328528683797707 234609193680492793025696561)
      ·
        refine ⟨175956895260369594769272421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234609193680492793025696561 175956895260369594769272421)
        ·
          refine ⟨32991917861319299019238579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175956895260369594769272421 32991917861319299019238579)
          ·
            refine ⟨49487876791978948528857869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32991917861319299019238579 49487876791978948528857869)
            ·
              refine ⟨18557953796992105698321701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49487876791978948528857869 18557953796992105698321701)
              ·
                refine ⟨3479616336936019818435319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18557953796992105698321701 3479616336936019818435319)
                ·
                  refine ⟨5219424505404029727652979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479616336936019818435319 5219424505404029727652979)
                  ·
                    refine ⟨7829136758106044591479469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5219424505404029727652979 7829136758106044591479469)
                    ·
                      refine ⟨2935926284289766721804801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7829136758106044591479469 2935926284289766721804801)
                      ·
                        rfl

theorem cell23_5717696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 1, 1, 3].length) (baseStart_5717696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717696 prefixEnd_5717696 := by exact prefixLift 5717696
  have htrace : WordTrace (prefixWord ++ tailWord_5717696) baseStart_5717696 baseEnd_5717696 := by
    simpa [prefixWord, tailWord_5717696, baseEnd_5717696] using wordTrace_append hprefix tailTrace_5717696
  have hstable : (prefixWord ++ tailWord_5717696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717696).length < 2 ^ (prefixWord ++ tailWord_5717696).sum := by decide
  have hdescent : baseEnd_5717696 < baseStart_5717696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717732 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_5717732 : Nat := 118140960795 + 5717732 * 2 ^ 59
def prefixEnd_5717732 : Nat := 4983230072969 + 3 ^ 40 * 5717732 * 2
def baseEnd_5717732 : Nat := 2935944769593328580954635

theorem tailTrace_5717732 : CollatzResearch.WordTrace tailWord_5717732 prefixEnd_5717732 2935944769593328580954635 := by
  unfold tailWord_5717732
  simp only [CollatzResearch.WordTrace]
  refine ⟨104271409260820474863353725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139028545681093966484471633 104271409260820474863353725)
  ·
    refine ⟨39101778472807678073757647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104271409260820474863353725 39101778472807678073757647)
    ·
      refine ⟨58652667709211517110636471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39101778472807678073757647 58652667709211517110636471)
      ·
        refine ⟨87979001563817275665954707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58652667709211517110636471 87979001563817275665954707)
        ·
          refine ⟨131968502345725913498932061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87979001563817275665954707 131968502345725913498932061)
          ·
            refine ⟨49488188379647217562099523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131968502345725913498932061 49488188379647217562099523)
            ·
              refine ⟨74232282569470826343149285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49488188379647217562099523 74232282569470826343149285)
              ·
                refine ⟨13918552981775779939340491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74232282569470826343149285 13918552981775779939340491)
                ·
                  refine ⟨20877829472663669909010737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13918552981775779939340491 20877829472663669909010737)
                  ·
                    refine ⟨15658372104497752431758053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20877829472663669909010737 15658372104497752431758053)
                    ·
                      refine ⟨2935944769593328580954635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15658372104497752431758053 2935944769593328580954635)
                      ·
                        rfl

theorem cell23_5717732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_5717732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717732 prefixEnd_5717732 := by exact prefixLift 5717732
  have htrace : WordTrace (prefixWord ++ tailWord_5717732) baseStart_5717732 baseEnd_5717732 := by
    simpa [prefixWord, tailWord_5717732, baseEnd_5717732] using wordTrace_append hprefix tailTrace_5717732
  have hstable : (prefixWord ++ tailWord_5717732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717732).length < 2 ^ (prefixWord ++ tailWord_5717732).sum := by decide
  have hdescent : baseEnd_5717732 < baseStart_5717732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717736 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_5717736 : Nat := 118140960795 + 5717736 * 2 ^ 59
def prefixEnd_5717736 : Nat := 4983230072969 + 3 ^ 40 * 5717736 * 2
def baseEnd_5717736 : Nat := 2935946823515946565304617

theorem tailTrace_5717736 : CollatzResearch.WordTrace tailWord_5717736 prefixEnd_5717736 2935946823515946565304617 := by
  unfold tailWord_5717736
  simp only [CollatzResearch.WordTrace]
  refine ⟨104271482206813229204926531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139028642942417638939902041 104271482206813229204926531)
  ·
    refine ⟨156407223310219843807389797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104271482206813229204926531 156407223310219843807389797)
    ·
      refine ⟨29326354370666220713885587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156407223310219843807389797 29326354370666220713885587)
      ·
        refine ⟨43989531555999331070828381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29326354370666220713885587 43989531555999331070828381)
        ·
          refine ⟨16496074333499749151560643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43989531555999331070828381 16496074333499749151560643)
          ·
            refine ⟨24744111500249623727340965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16496074333499749151560643 24744111500249623727340965)
            ·
              refine ⟨4639520906296804448876431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24744111500249623727340965 4639520906296804448876431)
              ·
                refine ⟨6959281359445206673314647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639520906296804448876431 6959281359445206673314647)
                ·
                  refine ⟨10438922039167810009971971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6959281359445206673314647 10438922039167810009971971)
                  ·
                    refine ⟨15658383058751715014957957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10438922039167810009971971 15658383058751715014957957)
                    ·
                      refine ⟨2935946823515946565304617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15658383058751715014957957 2935946823515946565304617)
                      ·
                        rfl

theorem cell23_5717736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_5717736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717736 prefixEnd_5717736 := by exact prefixLift 5717736
  have htrace : WordTrace (prefixWord ++ tailWord_5717736) baseStart_5717736 baseEnd_5717736 := by
    simpa [prefixWord, tailWord_5717736, baseEnd_5717736] using wordTrace_append hprefix tailTrace_5717736
  have hstable : (prefixWord ++ tailWord_5717736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717736).length < 2 ^ (prefixWord ++ tailWord_5717736).sum := by decide
  have hdescent : baseEnd_5717736 < baseStart_5717736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717755 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 2, 7]
def baseStart_5717755 : Nat := 118140960795 + 5717755 * 2 ^ 59
def prefixEnd_5717755 : Nat := 4983230072969 + 3 ^ 40 * 5717755 * 2
def baseEnd_5717755 : Nat := 978652193216127330322343

theorem tailTrace_5717755 : CollatzResearch.WordTrace tailWord_5717755 prefixEnd_5717755 978652193216127330322343 := by
  unfold tailWord_5717755
  simp only [CollatzResearch.WordTrace]
  refine ⟨208543657400557624654794719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139029104933705083103196479 208543657400557624654794719)
  ·
    refine ⟨312815486100836436982192079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208543657400557624654794719 312815486100836436982192079)
    ·
      refine ⟨469223229151254655473288119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312815486100836436982192079 469223229151254655473288119)
      ·
        refine ⟨703834843726881983209932179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469223229151254655473288119 703834843726881983209932179)
        ·
          refine ⟨1055752265590322974814898269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703834843726881983209932179 1055752265590322974814898269)
          ·
            refine ⟨395907099596371115555586851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1055752265590322974814898269 395907099596371115555586851)
            ·
              refine ⟨593860649394556673333380277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395907099596371115555586851 593860649394556673333380277)
              ·
                refine ⟨55674435880739688125004401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 593860649394556673333380277 55674435880739688125004401)
                ·
                  refine ⟨41755826910554766093753301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55674435880739688125004401 41755826910554766093753301)
                  ·
                    refine ⟨978652193216127330322343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41755826910554766093753301 978652193216127330322343)
                    ·
                      rfl

theorem cell23_5717755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 7].length) (baseStart_5717755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717755 prefixEnd_5717755 := by exact prefixLift 5717755
  have htrace : WordTrace (prefixWord ++ tailWord_5717755) baseStart_5717755 baseEnd_5717755 := by
    simpa [prefixWord, tailWord_5717755, baseEnd_5717755] using wordTrace_append hprefix tailTrace_5717755
  have hstable : (prefixWord ++ tailWord_5717755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717755).length < 2 ^ (prefixWord ++ tailWord_5717755).sum := by decide
  have hdescent : baseEnd_5717755 < baseStart_5717755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717775 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_5717775 : Nat := 118140960795 + 5717775 * 2 ^ 59
def prefixEnd_5717775 : Nat := 4983230072969 + 3 ^ 40 * 5717775 * 2
def baseEnd_5717775 : Nat := 2935966849261471912716937

theorem tailTrace_5717775 : CollatzResearch.WordTrace tailWord_5717775 prefixEnd_5717775 2935966849261471912716937 := by
  unfold tailWord_5717775
  simp only [CollatzResearch.WordTrace]
  refine ⟨208544386860485168070522779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139029591240323445380348519 208544386860485168070522779)
  ·
    refine ⟨312816580290727752105784169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208544386860485168070522779 312816580290727752105784169)
    ·
      refine ⟨234612435218045814079338127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312816580290727752105784169 234612435218045814079338127)
      ·
        refine ⟨351918652827068721119007191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234612435218045814079338127 351918652827068721119007191)
        ·
          refine ⟨527877979240603081678510787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351918652827068721119007191 527877979240603081678510787)
          ·
            refine ⟨791816968860904622517766181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527877979240603081678510787 791816968860904622517766181)
            ·
              refine ⟨148465681661419616722081159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 791816968860904622517766181 148465681661419616722081159)
              ·
                refine ⟨222698522492129425083121739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148465681661419616722081159 222698522492129425083121739)
                ·
                  refine ⟨334047783738194137624682609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222698522492129425083121739 334047783738194137624682609)
                  ·
                    refine ⟨250535837803645603218511957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334047783738194137624682609 250535837803645603218511957)
                    ·
                      refine ⟨2935966849261471912716937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 250535837803645603218511957 2935966849261471912716937)
                      ·
                        rfl

theorem cell23_5717775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_5717775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717775 prefixEnd_5717775 := by exact prefixLift 5717775
  have htrace : WordTrace (prefixWord ++ tailWord_5717775) baseStart_5717775 baseEnd_5717775 := by
    simpa [prefixWord, tailWord_5717775, baseEnd_5717775] using wordTrace_append hprefix tailTrace_5717775
  have hstable : (prefixWord ++ tailWord_5717775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717775).length < 2 ^ (prefixWord ++ tailWord_5717775).sum := by decide
  have hdescent : baseEnd_5717775 < baseStart_5717775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717830 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_5717830 : Nat := 118140960795 + 5717830 * 2 ^ 59
def prefixEnd_5717830 : Nat := 4983230072969 + 3 ^ 40 * 5717830 * 2
def baseEnd_5717830 : Nat := 2935995090697469197529185

theorem tailTrace_5717830 : CollatzResearch.WordTrace tailWord_5717830 prefixEnd_5717830 2935995090697469197529185 := by
  unfold tailWord_5717830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517074777352684764492967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139030928583523941642516629 6517074777352684764492967)
  ·
    refine ⟨9775612166029027146739451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6517074777352684764492967 9775612166029027146739451)
    ·
      refine ⟨14663418249043540720109177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9775612166029027146739451 14663418249043540720109177)
      ·
        refine ⟨10997563686782655540081883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14663418249043540720109177 10997563686782655540081883)
        ·
          refine ⟨16496345530173983310122825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10997563686782655540081883 16496345530173983310122825)
          ·
            refine ⟨12372259147630487482592119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16496345530173983310122825 12372259147630487482592119)
            ·
              refine ⟨18558388721445731223888179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12372259147630487482592119 18558388721445731223888179)
              ·
                refine ⟨27837583082168596835832269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18558388721445731223888179 27837583082168596835832269)
                ·
                  refine ⟨10439093655813223813437101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27837583082168596835832269 10439093655813223813437101)
                  ·
                    refine ⟨3914660120929958930038913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10439093655813223813437101 3914660120929958930038913)
                    ·
                      refine ⟨2935995090697469197529185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914660120929958930038913 2935995090697469197529185)
                      ·
                        rfl

theorem cell23_5717830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_5717830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717830 prefixEnd_5717830 := by exact prefixLift 5717830
  have htrace : WordTrace (prefixWord ++ tailWord_5717830) baseStart_5717830 baseEnd_5717830 := by
    simpa [prefixWord, tailWord_5717830, baseEnd_5717830] using wordTrace_append hprefix tailTrace_5717830
  have hstable : (prefixWord ++ tailWord_5717830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717830).length < 2 ^ (prefixWord ++ tailWord_5717830).sum := by decide
  have hdescent : baseEnd_5717830 < baseStart_5717830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717849 : List Nat := [1, 2, 1, 2, 2, 3, 2, 5, 5]
def baseStart_5717849 : Nat := 118140960795 + 5717849 * 2 ^ 59
def prefixEnd_5717849 : Nat := 4983230072969 + 3 ^ 40 * 5717849 * 2
def baseEnd_5717849 : Nat := 326222760758878291465733

theorem tailTrace_5717849 : CollatzResearch.WordTrace tailWord_5717849 prefixEnd_5717849 326222760758878291465733 := by
  unfold tailWord_5717849
  simp only [CollatzResearch.WordTrace]
  refine ⟨208547085862217078708716601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139031390574811385805811067 208547085862217078708716601)
  ·
    refine ⟨156410314396662809031537451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208547085862217078708716601 156410314396662809031537451)
    ·
      refine ⟨234615471594994213547306177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156410314396662809031537451 234615471594994213547306177)
      ·
        refine ⟨175961603696245660160479633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234615471594994213547306177 175961603696245660160479633)
        ·
          refine ⟨131971202772184245120359725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175961603696245660160479633 131971202772184245120359725)
          ·
            refine ⟨49489201039569091920134897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131971202772184245120359725 49489201039569091920134897)
            ·
              refine ⟨37116900779676818940101173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49489201039569091920134897 37116900779676818940101173)
              ·
                refine ⟨3479709448094701775634485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37116900779676818940101173 3479709448094701775634485)
                ·
                  refine ⟨326222760758878291465733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3479709448094701775634485 326222760758878291465733)
                  ·
                    rfl

theorem cell23_5717849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 5].length) (baseStart_5717849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717849 prefixEnd_5717849 := by exact prefixLift 5717849
  have htrace : WordTrace (prefixWord ++ tailWord_5717849) baseStart_5717849 baseEnd_5717849 := by
    simpa [prefixWord, tailWord_5717849, baseEnd_5717849] using wordTrace_append hprefix tailTrace_5717849
  have hstable : (prefixWord ++ tailWord_5717849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717849).length < 2 ^ (prefixWord ++ tailWord_5717849).sum := by decide
  have hdescent : baseEnd_5717849 < baseStart_5717849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717860 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 2, 2, 2]
def baseStart_5717860 : Nat := 118140960795 + 5717860 * 2 ^ 59
def prefixEnd_5717860 : Nat := 4983230072969 + 3 ^ 40 * 5717860 * 2
def baseEnd_5717860 : Nat := 2936010495117104080154047

theorem tailTrace_5717860 : CollatzResearch.WordTrace tailWord_5717860 prefixEnd_5717860 2936010495117104080154047 := by
  unfold tailWord_5717860
  simp only [CollatzResearch.WordTrace]
  refine ⟨104273743532588613793683517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139031658043451485058244689 104273743532588613793683517)
  ·
    refine ⟨39102653824720730172631319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104273743532588613793683517 39102653824720730172631319)
    ·
      refine ⟨58653980737081095258946979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39102653824720730172631319 58653980737081095258946979)
      ·
        refine ⟨87980971105621642888420469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58653980737081095258946979 87980971105621642888420469)
        ·
          refine ⟨8248216041152029020789419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87980971105621642888420469 8248216041152029020789419)
          ·
            refine ⟨12372324061728043531184129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8248216041152029020789419 12372324061728043531184129)
            ·
              refine ⟨9279243046296032648388097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12372324061728043531184129 9279243046296032648388097)
              ·
                refine ⟨6959432284722024486291073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9279243046296032648388097 6959432284722024486291073)
                ·
                  refine ⟨5219574213541518364718305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6959432284722024486291073 5219574213541518364718305)
                  ·
                    refine ⟨3914680660156138773538729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5219574213541518364718305 3914680660156138773538729)
                    ·
                      refine ⟨2936010495117104080154047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914680660156138773538729 2936010495117104080154047)
                      ·
                        rfl

theorem cell23_5717860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_5717860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717860 prefixEnd_5717860 := by exact prefixLift 5717860
  have htrace : WordTrace (prefixWord ++ tailWord_5717860) baseStart_5717860 baseEnd_5717860 := by
    simpa [prefixWord, tailWord_5717860, baseEnd_5717860] using wordTrace_append hprefix tailTrace_5717860
  have hstable : (prefixWord ++ tailWord_5717860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717860).length < 2 ^ (prefixWord ++ tailWord_5717860).sum := by decide
  have hdescent : baseEnd_5717860 < baseStart_5717860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717899 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 3, 6, 2]
def baseStart_5717899 : Nat := 118140960795 + 5717899 * 2 ^ 59
def prefixEnd_5717899 : Nat := 4983230072969 + 3 ^ 40 * 5717899 * 2
def baseEnd_5717899 : Nat := 2936030520862629427566367

theorem tailTrace_5717899 : CollatzResearch.WordTrace tailWord_5717899 prefixEnd_5717899 2936030520862629427566367 := by
  unfold tailWord_5717899
  simp only [CollatzResearch.WordTrace]
  refine ⟨208548909512035937248036751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139032606341357291498691167 208548909512035937248036751)
  ·
    refine ⟨312823364268053905872055127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208548909512035937248036751 312823364268053905872055127)
    ·
      refine ⟨469235046402080858808082691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312823364268053905872055127 469235046402080858808082691)
      ·
        refine ⟨703852569603121288212124037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469235046402080858808082691 703852569603121288212124037)
        ·
          refine ⟨131972356800585241539773257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 703852569603121288212124037 131972356800585241539773257)
          ·
            refine ⟨98979267600438931154829943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131972356800585241539773257 98979267600438931154829943)
            ·
              refine ⟨148468901400658396732244915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98979267600438931154829943 148468901400658396732244915)
              ·
                refine ⟨222703352100987595098367373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148468901400658396732244915 222703352100987595098367373)
                ·
                  refine ⟨83513757037870348161887765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222703352100987595098367373 83513757037870348161887765)
                  ·
                    refine ⟨3914707361150172570088489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83513757037870348161887765 3914707361150172570088489)
                    ·
                      refine ⟨2936030520862629427566367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914707361150172570088489 2936030520862629427566367)
                      ·
                        rfl

theorem cell23_5717899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 6, 2].length) (baseStart_5717899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717899 prefixEnd_5717899 := by exact prefixLift 5717899
  have htrace : WordTrace (prefixWord ++ tailWord_5717899) baseStart_5717899 baseEnd_5717899 := by
    simpa [prefixWord, tailWord_5717899, baseEnd_5717899] using wordTrace_append hprefix tailTrace_5717899
  have hstable : (prefixWord ++ tailWord_5717899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717899).length < 2 ^ (prefixWord ++ tailWord_5717899).sum := by decide
  have hdescent : baseEnd_5717899 < baseStart_5717899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717909 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_5717909 : Nat := 118140960795 + 5717909 * 2 ^ 59
def prefixEnd_5717909 : Nat := 4983230072969 + 3 ^ 40 * 5717909 * 2
def baseEnd_5717909 : Nat := 978678551889724796147107

theorem tailTrace_5717909 : CollatzResearch.WordTrace tailWord_5717909 prefixEnd_5717909 978678551889724796147107 := by
  unfold tailWord_5717909
  simp only [CollatzResearch.WordTrace]
  refine ⟨208549274241999708955900781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139032849494666472637267187 208549274241999708955900781)
  ·
    refine ⟨78205977840749890858462793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208549274241999708955900781 78205977840749890858462793)
    ·
      refine ⟨58654483380562418143847095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78205977840749890858462793 58654483380562418143847095)
      ·
        refine ⟨87981725070843627215770643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58654483380562418143847095 87981725070843627215770643)
        ·
          refine ⟨131972587606265440823655965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87981725070843627215770643 131972587606265440823655965)
          ·
            refine ⟨49489720352349540308870987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131972587606265440823655965 49489720352349540308870987)
            ·
              refine ⟨74234580528524310463306481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49489720352349540308870987 74234580528524310463306481)
              ·
                refine ⟨55675935396393232847479861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74234580528524310463306481 55675935396393232847479861)
                ·
                  refine ⟨5219618943411865579451237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55675935396393232847479861 5219618943411865579451237)
                  ·
                    refine ⟨978678551889724796147107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5219618943411865579451237 978678551889724796147107)
                    ·
                      rfl

theorem cell23_5717909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_5717909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717909 prefixEnd_5717909 := by exact prefixLift 5717909
  have htrace : WordTrace (prefixWord ++ tailWord_5717909) baseStart_5717909 baseEnd_5717909 := by
    simpa [prefixWord, tailWord_5717909, baseEnd_5717909] using wordTrace_append hprefix tailTrace_5717909
  have hstable : (prefixWord ++ tailWord_5717909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717909).length < 2 ^ (prefixWord ++ tailWord_5717909).sum := by decide
  have hdescent : baseEnd_5717909 < baseStart_5717909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717960 : List Nat := [2, 1, 3, 1, 4, 3, 1, 3, 1, 4]
def baseStart_5717960 : Nat := 118140960795 + 5717960 * 2 ^ 59
def prefixEnd_5717960 : Nat := 4983230072969 + 3 ^ 40 * 5717960 * 2
def baseEnd_5717960 : Nat := 978687281060851229634529

theorem tailTrace_5717960 : CollatzResearch.WordTrace tailWord_5717960 prefixEnd_5717960 978687281060851229634529 := by
  unfold tailWord_5717960
  simp only [CollatzResearch.WordTrace]
  refine ⟨104275567182407472333003667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139034089576543296444004889 104275567182407472333003667)
  ·
    refine ⟨156413350773611208499505501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104275567182407472333003667 156413350773611208499505501)
    ·
      refine ⟨58655006540104203187314563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156413350773611208499505501 58655006540104203187314563)
      ·
        refine ⟨87982509810156304780971845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58655006540104203187314563 87982509810156304780971845)
        ·
          refine ⟨16496720589404307146432221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87982509810156304780971845 16496720589404307146432221)
          ·
            refine ⟨6186270221026615179912083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16496720589404307146432221 6186270221026615179912083)
            ·
              refine ⟨9279405331539922769868125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6186270221026615179912083 9279405331539922769868125)
              ·
                refine ⟨3479776999327471038700547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9279405331539922769868125 3479776999327471038700547)
                ·
                  refine ⟨5219665498991206558050821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479776999327471038700547 5219665498991206558050821)
                  ·
                    refine ⟨978687281060851229634529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5219665498991206558050821 978687281060851229634529)
                    ·
                      rfl

theorem cell23_5717960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_5717960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717960 prefixEnd_5717960 := by exact prefixLift 5717960
  have htrace : WordTrace (prefixWord ++ tailWord_5717960) baseStart_5717960 baseEnd_5717960 := by
    simpa [prefixWord, tailWord_5717960, baseEnd_5717960] using wordTrace_append hprefix tailTrace_5717960
  have hstable : (prefixWord ++ tailWord_5717960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717960).length < 2 ^ (prefixWord ++ tailWord_5717960).sum := by decide
  have hdescent : baseEnd_5717960 < baseStart_5717960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717983 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 3, 1, 3]
def baseStart_5717983 : Nat := 118140960795 + 5717983 * 2 ^ 59
def prefixEnd_5717983 : Nat := 4983230072969 + 3 ^ 40 * 5717983 * 2
def baseEnd_5717983 : Nat := 2936073653237607098915981

theorem tailTrace_5717983 : CollatzResearch.WordTrace tailWord_5717983 prefixEnd_5717983 2936073653237607098915981 := by
  unfold tailWord_5717983
  simp only [CollatzResearch.WordTrace]
  refine ⟨208551973243731619594094603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139034648829154413062729735 208551973243731619594094603)
  ·
    refine ⟨312827959865597429391141905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208551973243731619594094603 312827959865597429391141905)
    ·
      refine ⟨234620969899198072043356429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312827959865597429391141905 234620969899198072043356429)
      ·
        refine ⟨87982863712199277016258661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234620969899198072043356429 87982863712199277016258661)
        ·
          refine ⟨16496786946037364440548499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87982863712199277016258661 16496786946037364440548499)
          ·
            refine ⟨24745180419056046660822749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16496786946037364440548499 24745180419056046660822749)
            ·
              refine ⟨9279442657146017497808531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24745180419056046660822749 9279442657146017497808531)
              ·
                refine ⟨13919163985719026246712797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9279442657146017497808531 13919163985719026246712797)
                ·
                  refine ⟨5219686494644634842517299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13919163985719026246712797 5219686494644634842517299)
                  ·
                    refine ⟨7829529741966952263775949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5219686494644634842517299 7829529741966952263775949)
                    ·
                      refine ⟨2936073653237607098915981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7829529741966952263775949 2936073653237607098915981)
                      ·
                        rfl

theorem cell23_5717983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_5717983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717983 prefixEnd_5717983 := by exact prefixLift 5717983
  have htrace : WordTrace (prefixWord ++ tailWord_5717983) baseStart_5717983 baseEnd_5717983 := by
    simpa [prefixWord, tailWord_5717983, baseEnd_5717983] using wordTrace_append hprefix tailTrace_5717983
  have hstable : (prefixWord ++ tailWord_5717983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717983).length < 2 ^ (prefixWord ++ tailWord_5717983).sum := by decide
  have hdescent : baseEnd_5717983 < baseStart_5717983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5717999 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 1, 6]
def baseStart_5717999 : Nat := 118140960795 + 5717999 * 2 ^ 59
def prefixEnd_5717999 : Nat := 4983230072969 + 3 ^ 40 * 5717999 * 2
def baseEnd_5717999 : Nat := 978693956309359678771969

theorem tailTrace_5717999 : CollatzResearch.WordTrace tailWord_5717999 prefixEnd_5717999 978693956309359678771969 := by
  unfold tailWord_5717999
  simp only [CollatzResearch.WordTrace]
  refine ⟨208552556811673654326677051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139035037874449102884451367 208552556811673654326677051)
  ·
    refine ⟨312828835217510481490015577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208552556811673654326677051 312828835217510481490015577)
    ·
      refine ⟨234621626413132861117511683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312828835217510481490015577 234621626413132861117511683)
      ·
        refine ⟨351932439619699291676267525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234621626413132861117511683 351932439619699291676267525)
        ·
          refine ⟨65987332428693617189300161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 351932439619699291676267525 65987332428693617189300161)
          ·
            refine ⟨49490499321520212891975121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65987332428693617189300161 49490499321520212891975121)
            ·
              refine ⟨37117874491140159668981341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49490499321520212891975121 37117874491140159668981341)
              ·
                refine ⟨13919202934177559875868003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37117874491140159668981341 13919202934177559875868003)
                ·
                  refine ⟨20878804401266339813802005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13919202934177559875868003 20878804401266339813802005)
                  ·
                    refine ⟨978693956309359678771969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20878804401266339813802005 978693956309359678771969)
                    ·
                      rfl

theorem cell23_5717999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_5717999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5717999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5717999 prefixEnd_5717999 := by exact prefixLift 5717999
  have htrace : WordTrace (prefixWord ++ tailWord_5717999) baseStart_5717999 baseEnd_5717999 := by
    simpa [prefixWord, tailWord_5717999, baseEnd_5717999] using wordTrace_append hprefix tailTrace_5717999
  have hstable : (prefixWord ++ tailWord_5717999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5717999).length < 2 ^ (prefixWord ++ tailWord_5717999).sum := by decide
  have hdescent : baseEnd_5717999 < baseStart_5717999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5717999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718089 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 4, 6]
def baseStart_5718089 : Nat := 118140960795 + 5718089 * 2 ^ 59
def prefixEnd_5718089 : Nat := 4983230072969 + 3 ^ 40 * 5718089 * 2
def baseEnd_5718089 : Nat := 978709360728994561396831

theorem tailTrace_5718089 : CollatzResearch.WordTrace tailWord_5718089 prefixEnd_5718089 978709360728994561396831 := by
  unfold tailWord_5718089
  simp only [CollatzResearch.WordTrace]
  refine ⟨208555839381347599697453321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139037226254231733131635547 208555839381347599697453321)
  ·
    refine ⟨156416879536010699773089991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208555839381347599697453321 156416879536010699773089991)
    ·
      refine ⟨234625319304016049659634987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156416879536010699773089991 234625319304016049659634987)
      ·
        refine ⟨351937978956024074489452481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234625319304016049659634987 351937978956024074489452481)
        ·
          refine ⟨263953484217018055867089361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351937978956024074489452481 263953484217018055867089361)
          ·
            refine ⟨197965113162763541900317021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263953484217018055867089361 197965113162763541900317021)
            ·
              refine ⟨74236917436036328212618883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197965113162763541900317021 74236917436036328212618883)
              ·
                refine ⟨111355376154054492318928325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74236917436036328212618883 111355376154054492318928325)
                ·
                  refine ⟨20879133028885217309799061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111355376154054492318928325 20879133028885217309799061)
                  ·
                    refine ⟨978709360728994561396831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20879133028885217309799061 978709360728994561396831)
                    ·
                      rfl

theorem cell23_5718089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_5718089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718089 prefixEnd_5718089 := by exact prefixLift 5718089
  have htrace : WordTrace (prefixWord ++ tailWord_5718089) baseStart_5718089 baseEnd_5718089 := by
    simpa [prefixWord, tailWord_5718089, baseEnd_5718089] using wordTrace_append hprefix tailTrace_5718089
  have hstable : (prefixWord ++ tailWord_5718089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718089).length < 2 ^ (prefixWord ++ tailWord_5718089).sum := by decide
  have hdescent : baseEnd_5718089 < baseStart_5718089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718096 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 2, 8, 2]
def baseStart_5718096 : Nat := 118140960795 + 5718096 * 2 ^ 59
def prefixEnd_5718096 : Nat := 4983230072969 + 3 ^ 40 * 5718096 * 2
def baseEnd_5718096 : Nat := 2936131676551565156802961

theorem tailTrace_5718096 : CollatzResearch.WordTrace tailWord_5718096 prefixEnd_5718096 2936131676551565156802961 := by
  unfold tailWord_5718096
  simp only [CollatzResearch.WordTrace]
  refine ⟨104278047346161119946479071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139037396461548159928638761 104278047346161119946479071)
  ·
    refine ⟨156417071019241679919718607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104278047346161119946479071 156417071019241679919718607)
    ·
      refine ⟨234625606528862519879577911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156417071019241679919718607 234625606528862519879577911)
      ·
        refine ⟨351938409793293779819366867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234625606528862519879577911 351938409793293779819366867)
        ·
          refine ⟨527907614689940669729050301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351938409793293779819366867 527907614689940669729050301)
          ·
            refine ⟨197965355508727751148393863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 527907614689940669729050301 197965355508727751148393863)
            ·
              refine ⟨296948033263091626722590795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197965355508727751148393863 296948033263091626722590795)
              ·
                refine ⟨445422049894637440083886193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296948033263091626722590795 445422049894637440083886193)
                ·
                  refine ⟨334066537420978080062914645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445422049894637440083886193 334066537420978080062914645)
                  ·
                    refine ⟨3914842235402086875737281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 334066537420978080062914645 3914842235402086875737281)
                    ·
                      refine ⟨2936131676551565156802961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914842235402086875737281 2936131676551565156802961)
                      ·
                        rfl

theorem cell23_5718096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 8, 2].length) (baseStart_5718096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718096 prefixEnd_5718096 := by exact prefixLift 5718096
  have htrace : WordTrace (prefixWord ++ tailWord_5718096) baseStart_5718096 baseEnd_5718096 := by
    simpa [prefixWord, tailWord_5718096, baseEnd_5718096] using wordTrace_append hprefix tailTrace_5718096
  have hstable : (prefixWord ++ tailWord_5718096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718096).length < 2 ^ (prefixWord ++ tailWord_5718096).sum := by decide
  have hdescent : baseEnd_5718096 < baseStart_5718096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718116 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_5718116 : Nat := 118140960795 + 5718116 * 2 ^ 59
def prefixEnd_5718116 : Nat := 4983230072969 + 3 ^ 40 * 5718116 * 2
def baseEnd_5718116 : Nat := 2936141946164655078552869

theorem tailTrace_5718116 : CollatzResearch.WordTrace tailWord_5718116 prefixEnd_5718116 2936141946164655078552869 := by
  unfold tailWord_5718116
  simp only [CollatzResearch.WordTrace]
  refine ⟨104278412076124891654343101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139037882768166522205790801 104278412076124891654343101)
  ·
    refine ⟨39104404528546834370378663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104278412076124891654343101 39104404528546834370378663)
    ·
      refine ⟨58656606792820251555567995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39104404528546834370378663 58656606792820251555567995)
      ·
        refine ⟨87984910189230377333351993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58656606792820251555567995 87984910189230377333351993)
        ·
          refine ⟨65988682641922783000013995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87984910189230377333351993 65988682641922783000013995)
          ·
            refine ⟨98983023962884174500020993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65988682641922783000013995 98983023962884174500020993)
            ·
              refine ⟨74237267972163130875015745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98983023962884174500020993 74237267972163130875015745)
              ·
                refine ⟨55677950979122348156261809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74237267972163130875015745 55677950979122348156261809)
                ·
                  refine ⟨41758463234341761117196357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55677950979122348156261809 41758463234341761117196357)
                  ·
                    refine ⟨7829711856439080209474317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41758463234341761117196357 7829711856439080209474317)
                    ·
                      refine ⟨2936141946164655078552869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7829711856439080209474317 2936141946164655078552869)
                      ·
                        rfl

theorem cell23_5718116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_5718116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718116 prefixEnd_5718116 := by exact prefixLift 5718116
  have htrace : WordTrace (prefixWord ++ tailWord_5718116) baseStart_5718116 baseEnd_5718116 := by
    simpa [prefixWord, tailWord_5718116, baseEnd_5718116] using wordTrace_append hprefix tailTrace_5718116
  have hstable : (prefixWord ++ tailWord_5718116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718116).length < 2 ^ (prefixWord ++ tailWord_5718116).sum := by decide
  have hdescent : baseEnd_5718116 < baseStart_5718116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718130 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 4, 2, 2]
def baseStart_5718130 : Nat := 118140960795 + 5718130 * 2 ^ 59
def prefixEnd_5718130 : Nat := 4983230072969 + 3 ^ 40 * 5718130 * 2
def baseEnd_5718130 : Nat := 2936149134893818023777805

theorem tailTrace_5718130 : CollatzResearch.WordTrace tailWord_5718130 prefixEnd_5718130 2936149134893818023777805 := by
  unfold tailWord_5718130
  simp only [CollatzResearch.WordTrace]
  refine ⟨52139333693549765924923961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139038223182799375799797229 52139333693549765924923961)
  ·
    refine ⟨39104500270162324443692971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52139333693549765924923961 39104500270162324443692971)
    ·
      refine ⟨58656750405243486665539457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39104500270162324443692971 58656750405243486665539457)
      ·
        refine ⟨43992562803932614999154593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58656750405243486665539457 43992562803932614999154593)
        ·
          refine ⟨32994422102949461249365945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43992562803932614999154593 32994422102949461249365945)
          ·
            refine ⟨24745816577212095937024459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32994422102949461249365945 24745816577212095937024459)
            ·
              refine ⟨37118724865818143905536689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24745816577212095937024459 37118724865818143905536689)
              ·
                refine ⟨27839043649363607929152517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37118724865818143905536689 27839043649363607929152517)
                ·
                  refine ⟨5219820684255676486716097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27839043649363607929152517 5219820684255676486716097)
                  ·
                    refine ⟨3914865513191757365037073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5219820684255676486716097 3914865513191757365037073)
                    ·
                      refine ⟨2936149134893818023777805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914865513191757365037073 2936149134893818023777805)
                      ·
                        rfl

theorem cell23_5718130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_5718130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718130 prefixEnd_5718130 := by exact prefixLift 5718130
  have htrace : WordTrace (prefixWord ++ tailWord_5718130) baseStart_5718130 baseEnd_5718130 := by
    simpa [prefixWord, tailWord_5718130, baseEnd_5718130] using wordTrace_append hprefix tailTrace_5718130
  have hstable : (prefixWord ++ tailWord_5718130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718130).length < 2 ^ (prefixWord ++ tailWord_5718130).sum := by decide
  have hdescent : baseEnd_5718130 < baseStart_5718130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718139 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 6]
def baseStart_5718139 : Nat := 118140960795 + 5718139 * 2 ^ 59
def prefixEnd_5718139 : Nat := 4983230072969 + 3 ^ 40 * 5718139 * 2
def baseEnd_5718139 : Nat := 2936153756219708488565263

theorem tailTrace_5718139 : CollatzResearch.WordTrace tailWord_5718139 prefixEnd_5718139 2936153756219708488565263 := by
  unfold tailWord_5718139
  simp only [CollatzResearch.WordTrace]
  refine ⟨208557663031166458236773471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139038442020777638824515647 208557663031166458236773471)
  ·
    refine ⟨312836494546749687355160207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208557663031166458236773471 312836494546749687355160207)
    ·
      refine ⟨469254741820124531032740311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312836494546749687355160207 469254741820124531032740311)
      ·
        refine ⟨703882112730186796549110467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469254741820124531032740311 703882112730186796549110467)
        ·
          refine ⟨1055823169095280194823665701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703882112730186796549110467 1055823169095280194823665701)
          ·
            refine ⟨197966844205365036529437319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1055823169095280194823665701 197966844205365036529437319)
            ·
              refine ⟨296950266308047554794155979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197966844205365036529437319 296950266308047554794155979)
              ·
                refine ⟨445425399462071332191233969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296950266308047554794155979 445425399462071332191233969)
                ·
                  refine ⟨334069049596553499143425477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445425399462071332191233969 334069049596553499143425477)
                  ·
                    refine ⟨62637946799353781089392277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 334069049596553499143425477 62637946799353781089392277)
                    ·
                      refine ⟨2936153756219708488565263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62637946799353781089392277 2936153756219708488565263)
                      ·
                        rfl

theorem cell23_5718139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_5718139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718139 prefixEnd_5718139 := by exact prefixLift 5718139
  have htrace : WordTrace (prefixWord ++ tailWord_5718139) baseStart_5718139 baseEnd_5718139 := by
    simpa [prefixWord, tailWord_5718139, baseEnd_5718139] using wordTrace_append hprefix tailTrace_5718139
  have hstable : (prefixWord ++ tailWord_5718139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718139).length < 2 ^ (prefixWord ++ tailWord_5718139).sum := by decide
  have hdescent : baseEnd_5718139 < baseStart_5718139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718203 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 2, 4, 2]
def baseStart_5718203 : Nat := 118140960795 + 5718203 * 2 ^ 59
def prefixEnd_5718203 : Nat := 4983230072969 + 3 ^ 40 * 5718203 * 2
def baseEnd_5718203 : Nat := 2936186618981596238164969

theorem tailTrace_5718203 : CollatzResearch.WordTrace tailWord_5718203 prefixEnd_5718203 2936186618981596238164969 := by
  unfold tailWord_5718203
  simp only [CollatzResearch.WordTrace]
  refine ⟨208559997302934597167103263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139039998201956398111402175 208559997302934597167103263)
  ·
    refine ⟨312839995954401895750654895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208559997302934597167103263 312839995954401895750654895)
    ·
      refine ⟨469259993931602843625982343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312839995954401895750654895 469259993931602843625982343)
      ·
        refine ⟨703889990897404265438973515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469259993931602843625982343 703889990897404265438973515)
        ·
          refine ⟨1055834986346106398158460273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703889990897404265438973515 1055834986346106398158460273)
          ·
            refine ⟨791876239759579798618845205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1055834986346106398158460273 791876239759579798618845205)
            ·
              refine ⟨37119198738730303060258369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 791876239759579798618845205 37119198738730303060258369)
              ·
                refine ⟨27839399054047727295193777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37119198738730303060258369 27839399054047727295193777)
                ·
                  refine ⟨20879549290535795471395333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27839399054047727295193777 20879549290535795471395333)
                  ·
                    refine ⟨3914915491975461650886625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20879549290535795471395333 3914915491975461650886625)
                    ·
                      refine ⟨2936186618981596238164969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914915491975461650886625 2936186618981596238164969)
                      ·
                        rfl

theorem cell23_5718203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 4, 2].length) (baseStart_5718203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718203 prefixEnd_5718203 := by exact prefixLift 5718203
  have htrace : WordTrace (prefixWord ++ tailWord_5718203) baseStart_5718203 baseEnd_5718203 := by
    simpa [prefixWord, tailWord_5718203, baseEnd_5718203] using wordTrace_append hprefix tailTrace_5718203
  have hstable : (prefixWord ++ tailWord_5718203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718203).length < 2 ^ (prefixWord ++ tailWord_5718203).sum := by decide
  have hdescent : baseEnd_5718203 < baseStart_5718203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718204 : List Nat := [2, 2, 2, 3, 4, 1, 2, 2, 5]
def baseStart_5718204 : Nat := 118140960795 + 5718204 * 2 ^ 59
def prefixEnd_5718204 : Nat := 4983230072969 + 3 ^ 40 * 5718204 * 2
def baseEnd_5718204 : Nat := 326243014718027859361385

theorem tailTrace_5718204 : CollatzResearch.WordTrace tailWord_5718204 prefixEnd_5718204 326243014718027859361385 := by
  unfold tailWord_5718204
  simp only [CollatzResearch.WordTrace]
  refine ⟨104280016887965487168944833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139040022517287316225259777 104280016887965487168944833)
  ·
    refine ⟨78210012665974115376708625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104280016887965487168944833 78210012665974115376708625)
    ·
      refine ⟨58657509499480586532531469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78210012665974115376708625 58657509499480586532531469)
      ·
        refine ⟨21996566062305219949699301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58657509499480586532531469 21996566062305219949699301)
        ·
          refine ⟨4124356136682228740568619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21996566062305219949699301 4124356136682228740568619)
          ·
            refine ⟨6186534205023343110852929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124356136682228740568619 6186534205023343110852929)
            ·
              refine ⟨4639900653767507333139697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6186534205023343110852929 4639900653767507333139697)
              ·
                refine ⟨3479925490325630499854773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4639900653767507333139697 3479925490325630499854773)
                ·
                  refine ⟨326243014718027859361385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3479925490325630499854773 326243014718027859361385)
                  ·
                    rfl

theorem cell23_5718204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_5718204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718204 prefixEnd_5718204 := by exact prefixLift 5718204
  have htrace : WordTrace (prefixWord ++ tailWord_5718204) baseStart_5718204 baseEnd_5718204 := by
    simpa [prefixWord, tailWord_5718204, baseEnd_5718204] using wordTrace_append hprefix tailTrace_5718204
  have hstable : (prefixWord ++ tailWord_5718204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718204).length < 2 ^ (prefixWord ++ tailWord_5718204).sum := by decide
  have hdescent : baseEnd_5718204 < baseStart_5718204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718216 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_5718216 : Nat := 118140960795 + 5718216 * 2 ^ 59
def prefixEnd_5718216 : Nat := 4983230072969 + 3 ^ 40 * 5718216 * 2
def baseEnd_5718216 : Nat := 2936193294230104687302409

theorem tailTrace_5718216 : CollatzResearch.WordTrace tailWord_5718216 prefixEnd_5718216 2936193294230104687302409 := by
  unfold tailWord_5718216
  simp only [CollatzResearch.WordTrace]
  refine ⟨104280235725943750193663251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139040314301258333591551001 104280235725943750193663251)
  ·
    refine ⟨156420353588915625290494877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104280235725943750193663251 156420353588915625290494877)
    ·
      refine ⟨58657632595843359483935579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156420353588915625290494877 58657632595843359483935579)
      ·
        refine ⟨87986448893765039225903369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58657632595843359483935579 87986448893765039225903369)
        ·
          refine ⟨65989836670323779419427527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87986448893765039225903369 65989836670323779419427527)
          ·
            refine ⟨98984755005485669129141291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65989836670323779419427527 98984755005485669129141291)
            ·
              refine ⟨148477132508228503693711937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98984755005485669129141291 148477132508228503693711937)
              ·
                refine ⟨111357849381171377770283953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148477132508228503693711937 111357849381171377770283953)
                ·
                  refine ⟨83518387035878533327712965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111357849381171377770283953 83518387035878533327712965)
                  ·
                    refine ⟨15659697569227224998946181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83518387035878533327712965 15659697569227224998946181)
                    ·
                      refine ⟨2936193294230104687302409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15659697569227224998946181 2936193294230104687302409)
                      ·
                        rfl

theorem cell23_5718216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_5718216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718216 prefixEnd_5718216 := by exact prefixLift 5718216
  have htrace : WordTrace (prefixWord ++ tailWord_5718216) baseStart_5718216 baseEnd_5718216 := by
    simpa [prefixWord, tailWord_5718216, baseEnd_5718216] using wordTrace_append hprefix tailTrace_5718216
  have hstable : (prefixWord ++ tailWord_5718216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718216).length < 2 ^ (prefixWord ++ tailWord_5718216).sum := by decide
  have hdescent : baseEnd_5718216 < baseStart_5718216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718237 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5718237 : Nat := 118140960795 + 5718237 * 2 ^ 59
def prefixEnd_5718237 : Nat := 4983230072969 + 3 ^ 40 * 5718237 * 2
def baseEnd_5718237 : Nat := 2936204077323849105139813

theorem tailTrace_5718237 : CollatzResearch.WordTrace tailWord_5718237 prefixEnd_5718237 2936204077323849105139813 := by
  unfold tailWord_5718237
  simp only [CollatzResearch.WordTrace]
  refine ⟨208561237384811420973840965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139040824923207613982560643 208561237384811420973840965)
  ·
    refine ⟨39105232009652141432595181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208561237384811420973840965 39105232009652141432595181)
    ·
      refine ⟨14664462003619553037223193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39105232009652141432595181 14664462003619553037223193)
      ·
        refine ⟨10998346502714664777917395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14664462003619553037223193 10998346502714664777917395)
        ·
          refine ⟨16497519754071997166876093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10998346502714664777917395 16497519754071997166876093)
          ·
            refine ⟨6186569907776998937578535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16497519754071997166876093 6186569907776998937578535)
            ·
              refine ⟨9279854861665498406367803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6186569907776998937578535 9279854861665498406367803)
              ·
                refine ⟨13919782292498247609551705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9279854861665498406367803 13919782292498247609551705)
                ·
                  refine ⟨10439836719373685707163779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13919782292498247609551705 10439836719373685707163779)
                  ·
                    refine ⟨15659755079060528560745669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10439836719373685707163779 15659755079060528560745669)
                    ·
                      refine ⟨2936204077323849105139813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15659755079060528560745669 2936204077323849105139813)
                      ·
                        rfl

theorem cell23_5718237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5718237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718237 prefixEnd_5718237 := by exact prefixLift 5718237
  have htrace : WordTrace (prefixWord ++ tailWord_5718237) baseStart_5718237 baseEnd_5718237 := by
    simpa [prefixWord, tailWord_5718237, baseEnd_5718237] using wordTrace_append hprefix tailTrace_5718237
  have hstable : (prefixWord ++ tailWord_5718237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718237).length < 2 ^ (prefixWord ++ tailWord_5718237).sum := by decide
  have hdescent : baseEnd_5718237 < baseStart_5718237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718247 : List Nat := [1, 1, 5, 3, 1, 1, 1, 5, 1, 4]
def baseStart_5718247 : Nat := 118140960795 + 5718247 * 2 ^ 59
def prefixEnd_5718247 : Nat := 4983230072969 + 3 ^ 40 * 5718247 * 2
def baseEnd_5718247 : Nat := 978736404043464688671589

theorem tailTrace_5718247 : CollatzResearch.WordTrace tailWord_5718247 prefixEnd_5718247 978736404043464688671589 := by
  unfold tailWord_5718247
  simp only [CollatzResearch.WordTrace]
  refine ⟨208561602114775192681704995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139041068076516795121136663 208561602114775192681704995)
  ·
    refine ⟨312842403172162789022557493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208561602114775192681704995 312842403172162789022557493)
    ·
      refine ⟨29328975297390261470864765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 312842403172162789022557493 29328975297390261470864765)
      ·
        refine ⟨10998365736521348051574287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29328975297390261470864765 10998365736521348051574287)
        ·
          refine ⟨16497548604782022077361431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10998365736521348051574287 16497548604782022077361431)
          ·
            refine ⟨24746322907173033116042147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16497548604782022077361431 24746322907173033116042147)
            ·
              refine ⟨37119484360759549674063221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24746322907173033116042147 37119484360759549674063221)
              ·
                refine ⟨3479951658821207781943427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37119484360759549674063221 3479951658821207781943427)
                ·
                  refine ⟨5219927488231811672915141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479951658821207781943427 5219927488231811672915141)
                  ·
                    refine ⟨978736404043464688671589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5219927488231811672915141 978736404043464688671589)
                    ·
                      rfl

theorem cell23_5718247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_5718247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718247 prefixEnd_5718247 := by exact prefixLift 5718247
  have htrace : WordTrace (prefixWord ++ tailWord_5718247) baseStart_5718247 baseEnd_5718247 := by
    simpa [prefixWord, tailWord_5718247, baseEnd_5718247] using wordTrace_append hprefix tailTrace_5718247
  have hstable : (prefixWord ++ tailWord_5718247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718247).length < 2 ^ (prefixWord ++ tailWord_5718247).sum := by decide
  have hdescent : baseEnd_5718247 < baseStart_5718247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718263 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 5, 5, 2]
def baseStart_5718263 : Nat := 118140960795 + 5718263 * 2 ^ 59
def prefixEnd_5718263 : Nat := 4983230072969 + 3 ^ 40 * 5718263 * 2
def baseEnd_5718263 : Nat := 2936217427820866003414693

theorem tailTrace_5718263 : CollatzResearch.WordTrace tailWord_5718263 prefixEnd_5718263 2936217427820866003414693 := by
  unfold tailWord_5718263
  simp only [CollatzResearch.WordTrace]
  refine ⟨208562185682717227414287443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139041457121811484942858295 208562185682717227414287443)
  ·
    refine ⟨312843278524075841121431165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208562185682717227414287443 312843278524075841121431165)
    ·
      refine ⟨117316229446528440420536687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312843278524075841121431165 117316229446528440420536687)
      ·
        refine ⟨175974344169792660630805031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117316229446528440420536687 175974344169792660630805031)
        ·
          refine ⟨263961516254688990946207547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175974344169792660630805031 263961516254688990946207547)
          ·
            refine ⟨395942274382033486419311321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263961516254688990946207547 395942274382033486419311321)
            ·
              refine ⟨296956705786525114814483491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395942274382033486419311321 296956705786525114814483491)
              ·
                refine ⟨445435058679787672221725237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296956705786525114814483491 445435058679787672221725237)
                ·
                  refine ⟨41759536751230094270786741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 445435058679787672221725237 41759536751230094270786741)
                  ·
                    refine ⟨3914956570427821337886257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41759536751230094270786741 3914956570427821337886257)
                    ·
                      refine ⟨2936217427820866003414693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914956570427821337886257 2936217427820866003414693)
                      ·
                        rfl

theorem cell23_5718263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_5718263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718263 prefixEnd_5718263 := by exact prefixLift 5718263
  have htrace : WordTrace (prefixWord ++ tailWord_5718263) baseStart_5718263 baseEnd_5718263 := by
    simpa [prefixWord, tailWord_5718263, baseEnd_5718263] using wordTrace_append hprefix tailTrace_5718263
  have hstable : (prefixWord ++ tailWord_5718263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718263).length < 2 ^ (prefixWord ++ tailWord_5718263).sum := by decide
  have hdescent : baseEnd_5718263 < baseStart_5718263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718280 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 1, 5, 2]
def baseStart_5718280 : Nat := 118140960795 + 5718280 * 2 ^ 59
def prefixEnd_5718280 : Nat := 4983230072969 + 3 ^ 40 * 5718280 * 2
def baseEnd_5718280 : Nat := 2936226156991992436902115

theorem tailTrace_5718280 : CollatzResearch.WordTrace tailWord_5718280 prefixEnd_5718280 2936226156991992436902115 := by
  unfold tailWord_5718280
  simp only [CollatzResearch.WordTrace]
  refine ⟨104281402861827819658828147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139041870482437092878437529 104281402861827819658828147)
  ·
    refine ⟨156422104292741729488242221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104281402861827819658828147 156422104292741729488242221)
    ·
      refine ⟨58658289109778148558090833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156422104292741729488242221 58658289109778148558090833)
      ·
        refine ⟨43993716832333611418568125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58658289109778148558090833 43993716832333611418568125)
        ·
          refine ⟨16497643812125104281963047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43993716832333611418568125 16497643812125104281963047)
          ·
            refine ⟨24746465718187656422944571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16497643812125104281963047 24746465718187656422944571)
            ·
              refine ⟨37119698577281484634416857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24746465718187656422944571 37119698577281484634416857)
              ·
                refine ⟨27839773932961113475812643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37119698577281484634416857 27839773932961113475812643)
                ·
                  refine ⟨41759660899441670213718965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27839773932961113475812643 41759660899441670213718965)
                  ·
                    refine ⟨3914968209322656582536153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41759660899441670213718965 3914968209322656582536153)
                    ·
                      refine ⟨2936226156991992436902115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914968209322656582536153 2936226156991992436902115)
                      ·
                        rfl

theorem cell23_5718280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_5718280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718280 prefixEnd_5718280 := by exact prefixLift 5718280
  have htrace : WordTrace (prefixWord ++ tailWord_5718280) baseStart_5718280 baseEnd_5718280 := by
    simpa [prefixWord, tailWord_5718280, baseEnd_5718280] using wordTrace_append hprefix tailTrace_5718280
  have hstable : (prefixWord ++ tailWord_5718280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718280).length < 2 ^ (prefixWord ++ tailWord_5718280).sum := by decide
  have hdescent : baseEnd_5718280 < baseStart_5718280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718293 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_5718293 : Nat := 118140960795 + 5718293 * 2 ^ 59
def prefixEnd_5718293 : Nat := 4983230072969 + 3 ^ 40 * 5718293 * 2
def baseEnd_5718293 : Nat := 2936232832240500886039555

theorem tailTrace_5718293 : CollatzResearch.WordTrace tailWord_5718293 prefixEnd_5718293 2936232832240500886039555 := by
  unfold tailWord_5718293
  simp only [CollatzResearch.WordTrace]
  refine ⟨208563279872608542537879533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139042186581739028358586355 208563279872608542537879533)
  ·
    refine ⟨78211229952228203451704825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208563279872608542537879533 78211229952228203451704825)
    ·
      refine ⟨58658422464171152588778619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78211229952228203451704825 58658422464171152588778619)
      ·
        refine ⟨87987633696256728883167929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58658422464171152588778619 87987633696256728883167929)
        ·
          refine ⟨65990725272192546662375947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87987633696256728883167929 65990725272192546662375947)
          ·
            refine ⟨98986087908288819993563921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65990725272192546662375947 98986087908288819993563921)
            ·
              refine ⟨74239565931216614995172941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98986087908288819993563921 74239565931216614995172941)
              ·
                refine ⟨27839837224206230623189853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74239565931216614995172941 27839837224206230623189853)
                ·
                  refine ⟨10439938959077336483696195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27839837224206230623189853 10439938959077336483696195)
                  ·
                    refine ⟨15659908438616004725544293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10439938959077336483696195 15659908438616004725544293)
                    ·
                      refine ⟨2936232832240500886039555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15659908438616004725544293 2936232832240500886039555)
                      ·
                        rfl

theorem cell23_5718293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_5718293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718293 prefixEnd_5718293 := by exact prefixLift 5718293
  have htrace : WordTrace (prefixWord ++ tailWord_5718293) baseStart_5718293 baseEnd_5718293 := by
    simpa [prefixWord, tailWord_5718293, baseEnd_5718293] using wordTrace_append hprefix tailTrace_5718293
  have hstable : (prefixWord ++ tailWord_5718293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718293).length < 2 ^ (prefixWord ++ tailWord_5718293).sum := by decide
  have hdescent : baseEnd_5718293 < baseStart_5718293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718304 : List Nat := [2, 1, 1, 5, 2, 1, 3, 3, 1, 1, 3]
def baseStart_5718304 : Nat := 118140960795 + 5718304 * 2 ^ 59
def prefixEnd_5718304 : Nat := 4983230072969 + 3 ^ 40 * 5718304 * 2
def baseEnd_5718304 : Nat := 2936238480527700343002005

theorem tailTrace_5718304 : CollatzResearch.WordTrace tailWord_5718304 prefixEnd_5718304 2936238480527700343002005 := by
  unfold tailWord_5718304
  simp only [CollatzResearch.WordTrace]
  refine ⟨104281840537784345708264983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139042454050379127611019977 104281840537784345708264983)
  ·
    refine ⟨156422760806676518562397475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104281840537784345708264983 156422760806676518562397475)
    ·
      refine ⟨234634141210014777843596213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156422760806676518562397475 234634141210014777843596213)
      ·
        refine ⟨21996950738438885422837145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234634141210014777843596213 21996950738438885422837145)
        ·
          refine ⟨16497713053829164067127859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21996950738438885422837145 16497713053829164067127859)
          ·
            refine ⟨24746569580743746100691789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16497713053829164067127859 24746569580743746100691789)
            ·
              refine ⟨9279963592778904787759421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24746569580743746100691789 9279963592778904787759421)
              ·
                refine ⟨3479986347292089295409783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9279963592778904787759421 3479986347292089295409783)
                ·
                  refine ⟨5219979520938133943114675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479986347292089295409783 5219979520938133943114675)
                  ·
                    refine ⟨7829969281407200914672013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5219979520938133943114675 7829969281407200914672013)
                    ·
                      refine ⟨2936238480527700343002005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7829969281407200914672013 2936238480527700343002005)
                      ·
                        rfl

theorem cell23_5718304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_5718304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718304 prefixEnd_5718304 := by exact prefixLift 5718304
  have htrace : WordTrace (prefixWord ++ tailWord_5718304) baseStart_5718304 baseEnd_5718304 := by
    simpa [prefixWord, tailWord_5718304, baseEnd_5718304] using wordTrace_append hprefix tailTrace_5718304
  have hstable : (prefixWord ++ tailWord_5718304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718304).length < 2 ^ (prefixWord ++ tailWord_5718304).sum := by decide
  have hdescent : baseEnd_5718304 < baseStart_5718304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718314 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_5718314 : Nat := 118140960795 + 5718314 * 2 ^ 59
def prefixEnd_5718314 : Nat := 4983230072969 + 3 ^ 40 * 5718314 * 2
def baseEnd_5718314 : Nat := 2936243615334245303876959

theorem tailTrace_5718314 : CollatzResearch.WordTrace tailWord_5718314 prefixEnd_5718314 2936243615334245303876959 := by
  unfold tailWord_5718314
  simp only [CollatzResearch.WordTrace]
  refine ⟨52141011451383115781098499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139042697203688308749595997 52141011451383115781098499)
  ·
    refine ⟨78211517177074673671647749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52141011451383115781098499 78211517177074673671647749)
    ·
      refine ⟨14664659470701501313433953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78211517177074673671647749 14664659470701501313433953)
      ·
        refine ⟨10998494603026125985075465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14664659470701501313433953 10998494603026125985075465)
        ·
          refine ⟨8248870952269594488806599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10998494603026125985075465 8248870952269594488806599)
          ·
            refine ⟨12373306428404391733209899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8248870952269594488806599 12373306428404391733209899)
            ·
              refine ⟨18559959642606587599814849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12373306428404391733209899 18559959642606587599814849)
              ·
                refine ⟨13919969731954940699861137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18559959642606587599814849 13919969731954940699861137)
                ·
                  refine ⟨10439977298966205524895853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13919969731954940699861137 10439977298966205524895853)
                  ·
                    refine ⟨3914991487112327071835945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10439977298966205524895853 3914991487112327071835945)
                    ·
                      refine ⟨2936243615334245303876959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3914991487112327071835945 2936243615334245303876959)
                      ·
                        rfl

theorem cell23_5718314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_5718314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718314 prefixEnd_5718314 := by exact prefixLift 5718314
  have htrace : WordTrace (prefixWord ++ tailWord_5718314) baseStart_5718314 baseEnd_5718314 := by
    simpa [prefixWord, tailWord_5718314, baseEnd_5718314] using wordTrace_append hprefix tailTrace_5718314
  have hstable : (prefixWord ++ tailWord_5718314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718314).length < 2 ^ (prefixWord ++ tailWord_5718314).sum := by decide
  have hdescent : baseEnd_5718314 < baseStart_5718314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718316 : List Nat := [2, 2, 1, 1, 1, 3, 13]
def baseStart_5718316 : Nat := 118140960795 + 5718316 * 2 ^ 59
def prefixEnd_5718316 : Nat := 4983230072969 + 3 ^ 40 * 5718316 * 2
def baseEnd_5718316 : Nat := 36249933855500670321629

theorem tailTrace_5718316 : CollatzResearch.WordTrace tailWord_5718316 prefixEnd_5718316 36249933855500670321629 := by
  unfold tailWord_5718316
  simp only [CollatzResearch.WordTrace]
  refine ⟨104282059375762608732983401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139042745834350144977311201 104282059375762608732983401)
  ·
    refine ⟨78211544531821956549737551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104282059375762608732983401 78211544531821956549737551)
    ·
      refine ⟨117317316797732934824606327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78211544531821956549737551 117317316797732934824606327)
      ·
        refine ⟨175975975196599402236909491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117317316797732934824606327 175975975196599402236909491)
        ·
          refine ⟨263963962794899103355364237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175975975196599402236909491 263963962794899103355364237)
          ·
            refine ⟨98986486048087163758261589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263963962794899103355364237 98986486048087163758261589)
            ·
              refine ⟨36249933855500670321629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 98986486048087163758261589 36249933855500670321629)
              ·
                rfl

theorem cell23_5718316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 13].length) (baseStart_5718316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718316 prefixEnd_5718316 := by exact prefixLift 5718316
  have htrace : WordTrace (prefixWord ++ tailWord_5718316) baseStart_5718316 baseEnd_5718316 := by
    simpa [prefixWord, tailWord_5718316, baseEnd_5718316] using wordTrace_append hprefix tailTrace_5718316
  have hstable : (prefixWord ++ tailWord_5718316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718316).length < 2 ^ (prefixWord ++ tailWord_5718316).sum := by decide
  have hdescent : baseEnd_5718316 < baseStart_5718316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718321 : List Nat := [1, 2, 2, 3, 4, 1, 3, 2, 1, 1, 3]
def baseStart_5718321 : Nat := 118140960795 + 5718321 * 2 ^ 59
def prefixEnd_5718321 : Nat := 4983230072969 + 3 ^ 40 * 5718321 * 2
def baseEnd_5718321 : Nat := 2936247209698826776489427

theorem tailTrace_5718321 : CollatzResearch.WordTrace tailWord_5718321 prefixEnd_5718321 2936247209698826776489427 := by
  unfold tailWord_5718321
  simp only [CollatzResearch.WordTrace]
  refine ⟨208564301116507103319898817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139042867411004735546599211 208564301116507103319898817)
  ·
    refine ⟨156423225837380327489924113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208564301116507103319898817 156423225837380327489924113)
    ·
      refine ⟨117317419378035245617443085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156423225837380327489924113 117317419378035245617443085)
      ·
        refine ⟨43994032266763217106541157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117317419378035245617443085 43994032266763217106541157)
        ·
          refine ⟨8248881050018103207476467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43994032266763217106541157 8248881050018103207476467)
          ·
            refine ⟨12373321575027154811214701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8248881050018103207476467 12373321575027154811214701)
            ·
              refine ⟨4639995590635183054205513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12373321575027154811214701 4639995590635183054205513)
              ·
                refine ⟨3479996692976387290654135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4639995590635183054205513 3479996692976387290654135)
                ·
                  refine ⟨5219995039464580935981203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479996692976387290654135 5219995039464580935981203)
                  ·
                    refine ⟨7829992559196871403971805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5219995039464580935981203 7829992559196871403971805)
                    ·
                      refine ⟨2936247209698826776489427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7829992559196871403971805 2936247209698826776489427)
                      ·
                        rfl

theorem cell23_5718321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_5718321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718321 prefixEnd_5718321 := by exact prefixLift 5718321
  have htrace : WordTrace (prefixWord ++ tailWord_5718321) baseStart_5718321 baseEnd_5718321 := by
    simpa [prefixWord, tailWord_5718321, baseEnd_5718321] using wordTrace_append hprefix tailTrace_5718321
  have hstable : (prefixWord ++ tailWord_5718321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718321).length < 2 ^ (prefixWord ++ tailWord_5718321).sum := by decide
  have hdescent : baseEnd_5718321 < baseStart_5718321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718360 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 4, 1, 3]
def baseStart_5718360 : Nat := 118140960795 + 5718360 * 2 ^ 59
def prefixEnd_5718360 : Nat := 4983230072969 + 3 ^ 40 * 5718360 * 2
def baseEnd_5718360 : Nat := 2936267235444352123901747

theorem tailTrace_5718360 : CollatzResearch.WordTrace tailWord_5718360 prefixEnd_5718360 2936267235444352123901747 := by
  unfold tailWord_5718360
  simp only [CollatzResearch.WordTrace]
  refine ⟨104282861781682906490284267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139043815708910541987045689 104282861781682906490284267)
  ·
    refine ⟨156424292672524359735426401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104282861781682906490284267 156424292672524359735426401)
    ·
      refine ⟨117318219504393269801569801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156424292672524359735426401 117318219504393269801569801)
      ·
        refine ⟨87988664628294952351177351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117318219504393269801569801 87988664628294952351177351)
        ·
          refine ⟨131982996942442428526766027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87988664628294952351177351 131982996942442428526766027)
          ·
            refine ⟨197974495413663642790149041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131982996942442428526766027 197974495413663642790149041)
            ·
              refine ⟨148480871560247732092611781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197974495413663642790149041 148480871560247732092611781)
              ·
                refine ⟨27840163417546449767364709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148480871560247732092611781 27840163417546449767364709)
                ·
                  refine ⟨5220030640789959331380883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27840163417546449767364709 5220030640789959331380883)
                  ·
                    refine ⟨7830045961184938997071325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5220030640789959331380883 7830045961184938997071325)
                    ·
                      refine ⟨2936267235444352123901747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7830045961184938997071325 2936267235444352123901747)
                      ·
                        rfl

theorem cell23_5718360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_5718360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718360 prefixEnd_5718360 := by exact prefixLift 5718360
  have htrace : WordTrace (prefixWord ++ tailWord_5718360) baseStart_5718360 baseEnd_5718360 := by
    simpa [prefixWord, tailWord_5718360, baseEnd_5718360] using wordTrace_append hprefix tailTrace_5718360
  have hstable : (prefixWord ++ tailWord_5718360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718360).length < 2 ^ (prefixWord ++ tailWord_5718360).sum := by decide
  have hdescent : baseEnd_5718360 < baseStart_5718360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718364 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5718364 : Nat := 118140960795 + 5718364 * 2 ^ 59
def prefixEnd_5718364 : Nat := 4983230072969 + 3 ^ 40 * 5718364 * 2
def baseEnd_5718364 : Nat := 2936269289366970108251729

theorem tailTrace_5718364 : CollatzResearch.WordTrace tailWord_5718364 prefixEnd_5718364 2936269289366970108251729 := by
  unfold tailWord_5718364
  simp only [CollatzResearch.WordTrace]
  refine ⟨104282934727675660831857073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139043912970234214442476097 104282934727675660831857073)
  ·
    refine ⟨78212201045756745623892805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104282934727675660831857073 78212201045756745623892805)
    ·
      refine ⟨14664787696079389804479901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78212201045756745623892805 14664787696079389804479901)
      ·
        refine ⟨5499295386029771176679963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14664787696079389804479901 5499295386029771176679963)
        ·
          refine ⟨8248943079044656765019945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5499295386029771176679963 8248943079044656765019945)
          ·
            refine ⟨6186707309283492573764959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8248943079044656765019945 6186707309283492573764959)
            ·
              refine ⟨9280060963925238860647439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6186707309283492573764959 9280060963925238860647439)
              ·
                refine ⟨13920091445887858290971159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9280060963925238860647439 13920091445887858290971159)
                ·
                  refine ⟨20880137168831787436456739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13920091445887858290971159 20880137168831787436456739)
                  ·
                    refine ⟨31320205753247681154685109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20880137168831787436456739 31320205753247681154685109)
                    ·
                      refine ⟨2936269289366970108251729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31320205753247681154685109 2936269289366970108251729)
                      ·
                        rfl

theorem cell23_5718364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5718364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718364 prefixEnd_5718364 := by exact prefixLift 5718364
  have htrace : WordTrace (prefixWord ++ tailWord_5718364) baseStart_5718364 baseEnd_5718364 := by
    simpa [prefixWord, tailWord_5718364, baseEnd_5718364] using wordTrace_append hprefix tailTrace_5718364
  have hstable : (prefixWord ++ tailWord_5718364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718364).length < 2 ^ (prefixWord ++ tailWord_5718364).sum := by decide
  have hdescent : baseEnd_5718364 < baseStart_5718364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718377 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 2, 1, 3]
def baseStart_5718377 : Nat := 118140960795 + 5718377 * 2 ^ 59
def prefixEnd_5718377 : Nat := 4983230072969 + 3 ^ 40 * 5718377 * 2
def baseEnd_5718377 : Nat := 2936275964615478557389169

theorem tailTrace_5718377 : CollatzResearch.WordTrace tailWord_5718377 prefixEnd_5718377 2936275964615478557389169 := by
  unfold tailWord_5718377
  simp only [CollatzResearch.WordTrace]
  refine ⟨208566343604304224883937385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139044229069536149922624923 208566343604304224883937385)
  ·
    refine ⟨156424757703228168662953039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208566343604304224883937385 156424757703228168662953039)
    ·
      refine ⟨234637136554842252994429559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156424757703228168662953039 234637136554842252994429559)
      ·
        refine ⟨351955704832263379491644339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234637136554842252994429559 351955704832263379491644339)
        ·
          refine ⟨527933557248395069237466509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351955704832263379491644339 527933557248395069237466509)
          ·
            refine ⟨197975083968148150964049941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 527933557248395069237466509 197975083968148150964049941)
            ·
              refine ⟨9280082061006944576439841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197975083968148150964049941 9280082061006944576439841)
              ·
                refine ⟨6960061545755208432329881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9280082061006944576439841 6960061545755208432329881)
                ·
                  refine ⟨5220046159316406324247411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6960061545755208432329881 5220046159316406324247411)
                  ·
                    refine ⟨7830069238974609486371117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5220046159316406324247411 7830069238974609486371117)
                    ·
                      refine ⟨2936275964615478557389169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7830069238974609486371117 2936275964615478557389169)
                      ·
                        rfl

theorem cell23_5718377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 1, 3].length) (baseStart_5718377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718377 prefixEnd_5718377 := by exact prefixLift 5718377
  have htrace : WordTrace (prefixWord ++ tailWord_5718377) baseStart_5718377 baseEnd_5718377 := by
    simpa [prefixWord, tailWord_5718377, baseEnd_5718377] using wordTrace_append hprefix tailTrace_5718377
  have hstable : (prefixWord ++ tailWord_5718377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718377).length < 2 ^ (prefixWord ++ tailWord_5718377).sum := by decide
  have hdescent : baseEnd_5718377 < baseStart_5718377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718378 : List Nat := [3, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_5718378 : Nat := 118140960795 + 5718378 * 2 ^ 59
def prefixEnd_5718378 : Nat := 4983230072969 + 3 ^ 40 * 5718378 * 2
def baseEnd_5718378 : Nat := 2936276478096133053476665

theorem tailTrace_5718378 : CollatzResearch.WordTrace tailWord_5718378 prefixEnd_5718378 2936276478096133053476665 := by
  unfold tailWord_5718378
  simp only [CollatzResearch.WordTrace]
  refine ⟨52141595019325150513680947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139044253384867068036482525 52141595019325150513680947)
  ·
    refine ⟨78212392528987725770521421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52141595019325150513680947 78212392528987725770521421)
    ·
      refine ⟨29329647198370397163945533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78212392528987725770521421 29329647198370397163945533)
      ·
        refine ⟨10998617699388898936479575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29329647198370397163945533 10998617699388898936479575)
        ·
          refine ⟨16497926549083348404719363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10998617699388898936479575 16497926549083348404719363)
          ·
            refine ⟨24746889823625022607079045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16497926549083348404719363 24746889823625022607079045)
            ·
              refine ⟨4640041841929691738827321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24746889823625022607079045 4640041841929691738827321)
              ·
                refine ⟨3480031381447268804120491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4640041841929691738827321 3480031381447268804120491)
                ·
                  refine ⟨5220047072170903206180737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480031381447268804120491 5220047072170903206180737)
                  ·
                    refine ⟨3915035304128177404635553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5220047072170903206180737 3915035304128177404635553)
                    ·
                      refine ⟨2936276478096133053476665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3915035304128177404635553 2936276478096133053476665)
                      ·
                        rfl

theorem cell23_5718378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_5718378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718378 prefixEnd_5718378 := by exact prefixLift 5718378
  have htrace : WordTrace (prefixWord ++ tailWord_5718378) baseStart_5718378 baseEnd_5718378 := by
    simpa [prefixWord, tailWord_5718378, baseEnd_5718378] using wordTrace_append hprefix tailTrace_5718378
  have hstable : (prefixWord ++ tailWord_5718378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718378).length < 2 ^ (prefixWord ++ tailWord_5718378).sum := by decide
  have hdescent : baseEnd_5718378 < baseStart_5718378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718434 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_5718434 : Nat := 118140960795 + 5718434 * 2 ^ 59
def prefixEnd_5718434 : Nat := 4983230072969 + 3 ^ 40 * 5718434 * 2
def baseEnd_5718434 : Nat := 2936305233012784834376407

theorem tailTrace_5718434 : CollatzResearch.WordTrace tailWord_5718434 prefixEnd_5718434 2936305233012784834376407 := by
  unfold tailWord_5718434
  simp only [CollatzResearch.WordTrace]
  refine ⟨52142105641274430904690589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139045615043398482412508237 52142105641274430904690589)
  ·
    refine ⟨19553289615477911589258971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52142105641274430904690589 19553289615477911589258971)
    ·
      refine ⟨29329934423216867383888457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19553289615477911589258971 29329934423216867383888457)
      ·
        refine ⟨21997450817412650537916343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29329934423216867383888457 21997450817412650537916343)
        ·
          refine ⟨32996176226118975806874515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21997450817412650537916343 32996176226118975806874515)
          ·
            refine ⟨49494264339178463710311773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32996176226118975806874515 49494264339178463710311773)
            ·
              refine ⟨18560349127191923891366915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49494264339178463710311773 18560349127191923891366915)
              ·
                refine ⟨27840523690787885837050373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18560349127191923891366915 27840523690787885837050373)
                ·
                  refine ⟨5220098192022728594446945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27840523690787885837050373 5220098192022728594446945)
                  ·
                    refine ⟨3915073644017046445835209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5220098192022728594446945 3915073644017046445835209)
                    ·
                      refine ⟨2936305233012784834376407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3915073644017046445835209 2936305233012784834376407)
                      ·
                        rfl

theorem cell23_5718434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_5718434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718434 prefixEnd_5718434 := by exact prefixLift 5718434
  have htrace : WordTrace (prefixWord ++ tailWord_5718434) baseStart_5718434 baseEnd_5718434 := by
    simpa [prefixWord, tailWord_5718434, baseEnd_5718434] using wordTrace_append hprefix tailTrace_5718434
  have hstable : (prefixWord ++ tailWord_5718434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718434).length < 2 ^ (prefixWord ++ tailWord_5718434).sum := by decide
  have hdescent : baseEnd_5718434 < baseStart_5718434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718450 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_5718450 : Nat := 118140960795 + 5718450 * 2 ^ 59
def prefixEnd_5718450 : Nat := 4983230072969 + 3 ^ 40 * 5718450 * 2
def baseEnd_5718450 : Nat := 2936313448703256771776333

theorem tailTrace_5718450 : CollatzResearch.WordTrace tailWord_5718450 prefixEnd_5718450 2936313448703256771776333 := by
  unfold tailWord_5718450
  simp only [CollatzResearch.WordTrace]
  refine ⟨52142251533259939587836201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139046004088693172234229869 52142251533259939587836201)
  ·
    refine ⟨39106688649944954690877151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52142251533259939587836201 39106688649944954690877151)
    ·
      refine ⟨58660032974917432036315727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39106688649944954690877151 58660032974917432036315727)
      ·
        refine ⟨87990049462376148054473591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58660032974917432036315727 87990049462376148054473591)
        ·
          refine ⟨131985074193564222081710387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87990049462376148054473591 131985074193564222081710387)
          ·
            refine ⟨197977611290346333122565581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131985074193564222081710387 197977611290346333122565581)
            ·
              refine ⟨74241604233879874920962093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197977611290346333122565581 74241604233879874920962093)
              ·
                refine ⟨27840601587704953095360785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74241604233879874920962093 27840601587704953095360785)
                ·
                  refine ⟨20880451190778714821520589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27840601587704953095360785 20880451190778714821520589)
                  ·
                    refine ⟨7830169196542018058070221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20880451190778714821520589 7830169196542018058070221)
                    ·
                      refine ⟨2936313448703256771776333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7830169196542018058070221 2936313448703256771776333)
                      ·
                        rfl

theorem cell23_5718450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_5718450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718450 prefixEnd_5718450 := by exact prefixLift 5718450
  have htrace : WordTrace (prefixWord ++ tailWord_5718450) baseStart_5718450 baseEnd_5718450 := by
    simpa [prefixWord, tailWord_5718450, baseEnd_5718450] using wordTrace_append hprefix tailTrace_5718450
  have hstable : (prefixWord ++ tailWord_5718450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718450).length < 2 ^ (prefixWord ++ tailWord_5718450).sum := by decide
  have hdescent : baseEnd_5718450 < baseStart_5718450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718463 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_5718463 : Nat := 118140960795 + 5718463 * 2 ^ 59
def prefixEnd_5718463 : Nat := 4983230072969 + 3 ^ 40 * 5718463 * 2
def baseEnd_5718463 : Nat := 2936320123951765220913773

theorem tailTrace_5718463 : CollatzResearch.WordTrace tailWord_5718463 prefixEnd_5718463 2936320123951765220913773 := by
  unfold tailWord_5718463
  simp only [CollatzResearch.WordTrace]
  refine ⟨208569480281992661571568043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139046320187995107714378695 208569480281992661571568043)
  ·
    refine ⟨312854220422988992357352065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208569480281992661571568043 312854220422988992357352065)
    ·
      refine ⟨234640665317241744268014049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312854220422988992357352065 234640665317241744268014049)
      ·
        refine ⟨175980498987931308201010537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234640665317241744268014049 175980498987931308201010537)
        ·
          refine ⟨131985374240948481150757903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175980498987931308201010537 131985374240948481150757903)
          ·
            refine ⟨197978061361422721726136855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131985374240948481150757903 197978061361422721726136855)
            ·
              refine ⟨296967092042134082589205283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197978061361422721726136855 296967092042134082589205283)
              ·
                refine ⟨445450638063201123883807925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296967092042134082589205283 445450638063201123883807925)
                ·
                  refine ⟨41760997318425105364106993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 445450638063201123883807925 41760997318425105364106993)
                  ·
                    refine ⟨31320747988818829023080245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41760997318425105364106993 31320747988818829023080245)
                    ·
                      refine ⟨2936320123951765220913773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31320747988818829023080245 2936320123951765220913773)
                      ·
                        rfl

theorem cell23_5718463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_5718463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718463 prefixEnd_5718463 := by exact prefixLift 5718463
  have htrace : WordTrace (prefixWord ++ tailWord_5718463) baseStart_5718463 baseEnd_5718463 := by
    simpa [prefixWord, tailWord_5718463, baseEnd_5718463] using wordTrace_append hprefix tailTrace_5718463
  have hstable : (prefixWord ++ tailWord_5718463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718463).length < 2 ^ (prefixWord ++ tailWord_5718463).sum := by decide
  have hdescent : baseEnd_5718463 < baseStart_5718463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718523 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 9]
def baseStart_5718523 : Nat := 118140960795 + 5718523 * 2 ^ 59
def prefixEnd_5718523 : Nat := 4983230072969 + 3 ^ 40 * 5718523 * 2
def baseEnd_5718523 : Nat := 2936350932791034986163497

theorem tailTrace_5718523 : CollatzResearch.WordTrace tailWord_5718523 prefixEnd_5718523 2936350932791034986163497 := by
  unfold tailWord_5718523
  simp only [CollatzResearch.WordTrace]
  refine ⟨208571668661775291818752223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139047779107850194545834815 208571668661775291818752223)
  ·
    refine ⟨312857502992662937728128335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208571668661775291818752223 312857502992662937728128335)
    ·
      refine ⟨469286254488994406592192503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312857502992662937728128335 469286254488994406592192503)
      ·
        refine ⟨703929381733491609888288755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469286254488994406592192503 703929381733491609888288755)
        ·
          refine ⟨1055894072600237414832433133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703929381733491609888288755 1055894072600237414832433133)
          ·
            refine ⟨395960277225089030562162425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1055894072600237414832433133 395960277225089030562162425)
            ·
              refine ⟨296970207918816772921621819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395960277225089030562162425 296970207918816772921621819)
              ·
                refine ⟨445455311878225159382432729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296970207918816772921621819 445455311878225159382432729)
                ·
                  refine ⟨334091483908668869536824547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445455311878225159382432729 334091483908668869536824547)
                  ·
                    refine ⟨501137225863003304305236821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 334091483908668869536824547 501137225863003304305236821)
                    ·
                      refine ⟨2936350932791034986163497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 501137225863003304305236821 2936350932791034986163497)
                      ·
                        rfl

theorem cell23_5718523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_5718523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718523 prefixEnd_5718523 := by exact prefixLift 5718523
  have htrace : WordTrace (prefixWord ++ tailWord_5718523) baseStart_5718523 baseEnd_5718523 := by
    simpa [prefixWord, tailWord_5718523, baseEnd_5718523] using wordTrace_append hprefix tailTrace_5718523
  have hstable : (prefixWord ++ tailWord_5718523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718523).length < 2 ^ (prefixWord ++ tailWord_5718523).sum := by decide
  have hdescent : baseEnd_5718523 < baseStart_5718523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718527 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 3]
def baseStart_5718527 : Nat := 118140960795 + 5718527 * 2 ^ 59
def prefixEnd_5718527 : Nat := 4983230072969 + 3 ^ 40 * 5718527 * 2
def baseEnd_5718527 : Nat := 2936352986713652970513479

theorem tailTrace_5718527 : CollatzResearch.WordTrace tailWord_5718527 prefixEnd_5718527 2936352986713652970513479 := by
  unfold tailWord_5718527
  simp only [CollatzResearch.WordTrace]
  refine ⟨208571814553760800501897835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139047876369173867001265223 208571814553760800501897835)
  ·
    refine ⟨312857721830641200752846753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208571814553760800501897835 312857721830641200752846753)
    ·
      refine ⟨234643291372980900564635065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312857721830641200752846753 234643291372980900564635065)
      ·
        refine ⟨175982468529735675423476299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234643291372980900564635065 175982468529735675423476299)
        ·
          refine ⟨263973702794603513135214449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175982468529735675423476299 263973702794603513135214449)
          ·
            refine ⟨197980277095952634851410837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263973702794603513135214449 197980277095952634851410837)
            ·
              refine ⟨9280325488872779758659883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197980277095952634851410837 9280325488872779758659883)
              ·
                refine ⟨13920488233309169637989825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9280325488872779758659883 13920488233309169637989825)
                ·
                  refine ⟨10440366174981877228492369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13920488233309169637989825 10440366174981877228492369)
                  ·
                    refine ⟨7830274631236407921369277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10440366174981877228492369 7830274631236407921369277)
                    ·
                      refine ⟨2936352986713652970513479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7830274631236407921369277 2936352986713652970513479)
                      ·
                        rfl

theorem cell23_5718527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_5718527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718527 prefixEnd_5718527 := by exact prefixLift 5718527
  have htrace : WordTrace (prefixWord ++ tailWord_5718527) baseStart_5718527 baseEnd_5718527 := by
    simpa [prefixWord, tailWord_5718527, baseEnd_5718527] using wordTrace_append hprefix tailTrace_5718527
  have hstable : (prefixWord ++ tailWord_5718527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718527).length < 2 ^ (prefixWord ++ tailWord_5718527).sum := by decide
  have hdescent : baseEnd_5718527 < baseStart_5718527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718541 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5718541 : Nat := 118140960795 + 5718541 * 2 ^ 59
def prefixEnd_5718541 : Nat := 4983230072969 + 3 ^ 40 * 5718541 * 2
def baseEnd_5718541 : Nat := 2936360175442815915738415

theorem tailTrace_5718541 : CollatzResearch.WordTrace tailWord_5718541 prefixEnd_5718541 2936360175442815915738415 := by
  unfold tailWord_5718541
  simp only [CollatzResearch.WordTrace]
  refine ⟨208572325175710080892907477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139048216783806720595271651 208572325175710080892907477)
  ·
    refine ⟨4888413871305705020927519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 208572325175710080892907477 4888413871305705020927519)
    ·
      refine ⟨7332620806958557531391279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4888413871305705020927519 7332620806958557531391279)
      ·
        refine ⟨10998931210437836297086919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7332620806958557531391279 10998931210437836297086919)
        ·
          refine ⟨16498396815656754445630379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10998931210437836297086919 16498396815656754445630379)
          ·
            refine ⟨24747595223485131668445569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16498396815656754445630379 24747595223485131668445569)
            ·
              refine ⟨18560696417613848751334177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24747595223485131668445569 18560696417613848751334177)
              ·
                refine ⟨13920522313210386563500633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18560696417613848751334177 13920522313210386563500633)
                ·
                  refine ⟨10440391734907789922625475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13920522313210386563500633 10440391734907789922625475)
                  ·
                    refine ⟨15660587602361684883938213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10440391734907789922625475 15660587602361684883938213)
                    ·
                      refine ⟨2936360175442815915738415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15660587602361684883938213 2936360175442815915738415)
                      ·
                        rfl

theorem cell23_5718541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5718541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718541 prefixEnd_5718541 := by exact prefixLift 5718541
  have htrace : WordTrace (prefixWord ++ tailWord_5718541) baseStart_5718541 baseEnd_5718541 := by
    simpa [prefixWord, tailWord_5718541, baseEnd_5718541] using wordTrace_append hprefix tailTrace_5718541
  have hstable : (prefixWord ++ tailWord_5718541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718541).length < 2 ^ (prefixWord ++ tailWord_5718541).sum := by decide
  have hdescent : baseEnd_5718541 < baseStart_5718541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718591 : List Nat := [1, 1, 2, 2, 3, 2, 4, 3, 1, 1, 3]
def baseStart_5718591 : Nat := 118140960795 + 5718591 * 2 ^ 59
def prefixEnd_5718591 : Nat := 4983230072969 + 3 ^ 40 * 5718591 * 2
def baseEnd_5718591 : Nat := 2936385849475540720113185

theorem tailTrace_5718591 : CollatzResearch.WordTrace tailWord_5718591 prefixEnd_5718591 2936385849475540720113185 := by
  unfold tailWord_5718591
  simp only [CollatzResearch.WordTrace]
  refine ⟨208574148825528939432227627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139049432550352626288151751 208574148825528939432227627)
  ·
    refine ⟨312861223238293409148341441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208574148825528939432227627 312861223238293409148341441)
    ·
      refine ⟨234645917428720056861256081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312861223238293409148341441 234645917428720056861256081)
      ·
        refine ⟨175984438071540042645942061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234645917428720056861256081 175984438071540042645942061)
        ·
          refine ⟨65994164276827515992228273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175984438071540042645942061 65994164276827515992228273)
          ·
            refine ⟨49495623207620636994171205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65994164276827515992228273 49495623207620636994171205)
            ·
              refine ⟨9280429351428869436407101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49495623207620636994171205 9280429351428869436407101)
              ·
                refine ⟨3480161006785826038652663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9280429351428869436407101 3480161006785826038652663)
                ·
                  refine ⟨5220241510178739057978995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480161006785826038652663 5220241510178739057978995)
                  ·
                    refine ⟨7830362265268108586968493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5220241510178739057978995 7830362265268108586968493)
                    ·
                      refine ⟨2936385849475540720113185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7830362265268108586968493 2936385849475540720113185)
                      ·
                        rfl

theorem cell23_5718591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 1, 1, 3].length) (baseStart_5718591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718591 prefixEnd_5718591 := by exact prefixLift 5718591
  have htrace : WordTrace (prefixWord ++ tailWord_5718591) baseStart_5718591 baseEnd_5718591 := by
    simpa [prefixWord, tailWord_5718591, baseEnd_5718591] using wordTrace_append hprefix tailTrace_5718591
  have hstable : (prefixWord ++ tailWord_5718591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718591).length < 2 ^ (prefixWord ++ tailWord_5718591).sum := by decide
  have hdescent : baseEnd_5718591 < baseStart_5718591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718600 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_5718600 : Nat := 118140960795 + 5718600 * 2 ^ 59
def prefixEnd_5718600 : Nat := 4983230072969 + 3 ^ 40 * 5718600 * 2
def baseEnd_5718600 : Nat := 2936390470801431184900643

theorem tailTrace_5718600 : CollatzResearch.WordTrace tailWord_5718600 prefixEnd_5718600 2936390470801431184900643 := by
  unfold tailWord_5718600
  simp only [CollatzResearch.WordTrace]
  refine ⟨104287238541248166984652627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139049651388330889312870169 104287238541248166984652627)
  ·
    refine ⟨156430857811872250476978941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104287238541248166984652627 156430857811872250476978941)
    ·
      refine ⟨58661571679452093928867103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156430857811872250476978941 58661571679452093928867103)
      ·
        refine ⟨87992357519178140893300655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58661571679452093928867103 87992357519178140893300655)
        ·
          refine ⟨131988536278767211339950983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87992357519178140893300655 131988536278767211339950983)
          ·
            refine ⟨197982804418150817009926475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131988536278767211339950983 197982804418150817009926475)
            ·
              refine ⟨296974206627226225514889713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197982804418150817009926475 296974206627226225514889713)
              ·
                refine ⟨222730654970419669136167285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296974206627226225514889713 222730654970419669136167285)
                ·
                  refine ⟨20880998903476843981515683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222730654970419669136167285 20880998903476843981515683)
                  ·
                    refine ⟨31321498355215265972273525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20880998903476843981515683 31321498355215265972273525)
                    ·
                      refine ⟨2936390470801431184900643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31321498355215265972273525 2936390470801431184900643)
                      ·
                        rfl

theorem cell23_5718600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_5718600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5718600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5718600 prefixEnd_5718600 := by exact prefixLift 5718600
  have htrace : WordTrace (prefixWord ++ tailWord_5718600) baseStart_5718600 baseEnd_5718600 := by
    simpa [prefixWord, tailWord_5718600, baseEnd_5718600] using wordTrace_append hprefix tailTrace_5718600
  have hstable : (prefixWord ++ tailWord_5718600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718600).length < 2 ^ (prefixWord ++ tailWord_5718600).sum := by decide
  have hdescent : baseEnd_5718600 < baseStart_5718600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
