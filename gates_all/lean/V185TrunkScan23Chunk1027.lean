import V185TrunkScan23Chunk1026

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6079917 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 6]
def baseStart_6079917 : Nat := 118140960795 + 6079917 * 2 ^ 59
def prefixEnd_6079917 : Nat := 4983230072969 + 3 ^ 40 * 6079917 * 2
def baseEnd_6079917 : Nat := 346879973382443781164053

theorem tailTrace_6079917 : CollatzResearch.WordTrace tailWord_6079917 prefixEnd_6079917 346879973382443781164053 := by
  unfold tailWord_6079917
  simp only [CollatzResearch.WordTrace]
  refine ⟨221752790714506551000078005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147835193809671034000052003 221752790714506551000078005)
  ·
    refine ⟨20789324129484989156257313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221752790714506551000078005 20789324129484989156257313)
    ·
      refine ⟨15591993097113741867192985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20789324129484989156257313 15591993097113741867192985)
      ·
        refine ⟨11693994822835306400394739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15591993097113741867192985 11693994822835306400394739)
        ·
          refine ⟨17540992234252959600592109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11693994822835306400394739 17540992234252959600592109)
          ·
            refine ⟨6577872087844859850222041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17540992234252959600592109 6577872087844859850222041)
            ·
              refine ⟨4933404065883644887666531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6577872087844859850222041 4933404065883644887666531)
              ·
                refine ⟨7400106098825467331499797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4933404065883644887666531 7400106098825467331499797)
                ·
                  refine ⟨346879973382443781164053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7400106098825467331499797 346879973382443781164053)
                  ·
                    rfl

theorem cell23_6079917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_6079917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079917 prefixEnd_6079917 := by exact prefixLift 6079917
  have htrace : WordTrace (prefixWord ++ tailWord_6079917) baseStart_6079917 baseEnd_6079917 := by
    simpa [prefixWord, tailWord_6079917, baseEnd_6079917] using wordTrace_append hprefix tailTrace_6079917
  have hstable : (prefixWord ++ tailWord_6079917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079917).length < 2 ^ (prefixWord ++ tailWord_6079917).sum := by decide
  have hdescent : baseEnd_6079917 < baseStart_6079917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079933 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_6079933 : Nat := 118140960795 + 6079933 * 2 ^ 59
def prefixEnd_6079933 : Nat := 4983230072969 + 3 ^ 40 * 6079933 * 2
def baseEnd_6079933 : Nat := 3121927976132465967876403

theorem tailTrace_6079933 : CollatzResearch.WordTrace tailWord_6079933 prefixEnd_6079933 3121927976132465967876403 := by
  unfold tailWord_6079933
  simp only [CollatzResearch.WordTrace]
  refine ⟨221753374282448585732660453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147835582854965723821773635 221753374282448585732660453)
  ·
    refine ⟨41578757677959109824873835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221753374282448585732660453 41578757677959109824873835)
    ·
      refine ⟨62368136516938664737310753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41578757677959109824873835 62368136516938664737310753)
      ·
        refine ⟨46776102387703998552983065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62368136516938664737310753 46776102387703998552983065)
        ·
          refine ⟨35082076790777998914737299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46776102387703998552983065 35082076790777998914737299)
          ·
            refine ⟨52623115186166998372105949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35082076790777998914737299 52623115186166998372105949)
            ·
              refine ⟨19733668194812624389539731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52623115186166998372105949 19733668194812624389539731)
              ·
                refine ⟨29600502292218936584309597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19733668194812624389539731 29600502292218936584309597)
                ·
                  refine ⟨11100188359582101219116099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29600502292218936584309597 11100188359582101219116099)
                  ·
                    refine ⟨16650282539373151828674149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11100188359582101219116099 16650282539373151828674149)
                    ·
                      refine ⟨3121927976132465967876403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16650282539373151828674149 3121927976132465967876403)
                      ·
                        rfl

theorem cell23_6079933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_6079933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079933 prefixEnd_6079933 := by exact prefixLift 6079933
  have htrace : WordTrace (prefixWord ++ tailWord_6079933) baseStart_6079933 baseEnd_6079933 := by
    simpa [prefixWord, tailWord_6079933, baseEnd_6079933] using wordTrace_append hprefix tailTrace_6079933
  have hstable : (prefixWord ++ tailWord_6079933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079933).length < 2 ^ (prefixWord ++ tailWord_6079933).sum := by decide
  have hdescent : baseEnd_6079933 < baseStart_6079933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079936 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_6079936 : Nat := 118140960795 + 6079936 * 2 ^ 59
def prefixEnd_6079936 : Nat := 4983230072969 + 3 ^ 40 * 6079936 * 2
def baseEnd_6079936 : Nat := 3121929516574429456138889

theorem tailTrace_6079936 : CollatzResearch.WordTrace tailWord_6079936 prefixEnd_6079936 3121929516574429456138889 := by
  unfold tailWord_6079936
  simp only [CollatzResearch.WordTrace]
  refine ⟨110876741850718858622509831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147835655800958478163346441 110876741850718858622509831)
  ·
    refine ⟨166315112776078287933764747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110876741850718858622509831 166315112776078287933764747)
    ·
      refine ⟨249472669164117431900647121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166315112776078287933764747 249472669164117431900647121)
      ·
        refine ⟨187104501873088073925485341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249472669164117431900647121 187104501873088073925485341)
        ·
          refine ⟨70164188202408027722057003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187104501873088073925485341 70164188202408027722057003)
          ·
            refine ⟨105246282303612041583085505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70164188202408027722057003 105246282303612041583085505)
            ·
              refine ⟨78934711727709031187314129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105246282303612041583085505 78934711727709031187314129)
              ·
                refine ⟨59201033795781773390485597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78934711727709031187314129 59201033795781773390485597)
                ·
                  refine ⟨22200387673418165021432099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59201033795781773390485597 22200387673418165021432099)
                  ·
                    refine ⟨33300581510127247532148149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22200387673418165021432099 33300581510127247532148149)
                    ·
                      refine ⟨3121929516574429456138889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33300581510127247532148149 3121929516574429456138889)
                      ·
                        rfl

theorem cell23_6079936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_6079936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079936 prefixEnd_6079936 := by exact prefixLift 6079936
  have htrace : WordTrace (prefixWord ++ tailWord_6079936) baseStart_6079936 baseEnd_6079936 := by
    simpa [prefixWord, tailWord_6079936, baseEnd_6079936] using wordTrace_append hprefix tailTrace_6079936
  have hstable : (prefixWord ++ tailWord_6079936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079936).length < 2 ^ (prefixWord ++ tailWord_6079936).sum := by decide
  have hdescent : baseEnd_6079936 < baseStart_6079936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079956 : List Nat := [2, 4, 1, 2, 14]
def baseStart_6079956 : Nat := 118140960795 + 6079956 * 2 ^ 59
def prefixEnd_6079956 : Nat := 4983230072969 + 3 ^ 40 * 6079956 * 2
def baseEnd_6079956 : Nat := 4282496277349134949093

theorem tailTrace_6079956 : CollatzResearch.WordTrace tailWord_6079956 prefixEnd_6079956 4282496277349134949093 := by
  unfold tailWord_6079956
  simp only [CollatzResearch.WordTrace]
  refine ⟨110877106580682630330373861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147836142107576840440498481 110877106580682630330373861)
  ·
    refine ⟨20789457483877993186945099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110877106580682630330373861 20789457483877993186945099)
    ·
      refine ⟨31184186225816989780417649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20789457483877993186945099 31184186225816989780417649)
      ·
        refine ⟨23388139669362742335313237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31184186225816989780417649 23388139669362742335313237)
        ·
          refine ⟨4282496277349134949093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 23388139669362742335313237 4282496277349134949093)
          ·
            rfl

theorem cell23_6079956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 14].length) (baseStart_6079956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079956 prefixEnd_6079956 := by exact prefixLift 6079956
  have htrace : WordTrace (prefixWord ++ tailWord_6079956) baseStart_6079956 baseEnd_6079956 := by
    simpa [prefixWord, tailWord_6079956, baseEnd_6079956] using wordTrace_append hprefix tailTrace_6079956
  have hstable : (prefixWord ++ tailWord_6079956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079956).length < 2 ^ (prefixWord ++ tailWord_6079956).sum := by decide
  have hdescent : baseEnd_6079956 < baseStart_6079956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079973 : List Nat := [1, 3, 1, 5, 1, 1, 3, 8]
def baseStart_6079973 : Nat := 118140960795 + 6079973 * 2 ^ 59
def prefixEnd_6079973 : Nat := 4983230072969 + 3 ^ 40 * 6079973 * 2
def baseEnd_6079973 : Nat := 115627722791060955976897

theorem tailTrace_6079973 : CollatzResearch.WordTrace tailWord_6079973 prefixEnd_6079973 115627722791060955976897 := by
  unfold tailWord_6079973
  simp only [CollatzResearch.WordTrace]
  refine ⟨221754833202303672564116573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147836555468202448376077715 221754833202303672564116573)
  ·
    refine ⟨83158062450863877211543715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221754833202303672564116573 83158062450863877211543715)
    ·
      refine ⟨124737093676295815817315573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83158062450863877211543715 124737093676295815817315573)
      ·
        refine ⟨11694102532152732732873335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124737093676295815817315573 11694102532152732732873335)
        ·
          refine ⟨17541153798229099099310003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11694102532152732732873335 17541153798229099099310003)
          ·
            refine ⟨26311730697343648648965005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17541153798229099099310003 26311730697343648648965005)
            ·
              refine ⟨9866899011503868243361877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26311730697343648648965005 9866899011503868243361877)
              ·
                refine ⟨115627722791060955976897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9866899011503868243361877 115627722791060955976897)
                ·
                  rfl

theorem cell23_6079973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 8].length) (baseStart_6079973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079973 prefixEnd_6079973 := by exact prefixLift 6079973
  have htrace : WordTrace (prefixWord ++ tailWord_6079973) baseStart_6079973 baseEnd_6079973 := by
    simpa [prefixWord, tailWord_6079973, baseEnd_6079973] using wordTrace_append hprefix tailTrace_6079973
  have hstable : (prefixWord ++ tailWord_6079973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079973).length < 2 ^ (prefixWord ++ tailWord_6079973).sum := by decide
  have hdescent : baseEnd_6079973 < baseStart_6079973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079983 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 3]
def baseStart_6079983 : Nat := 118140960795 + 6079983 * 2 ^ 59
def prefixEnd_6079983 : Nat := 4983230072969 + 3 ^ 40 * 6079983 * 2
def baseEnd_6079983 : Nat := 3121953650165190772251173

theorem tailTrace_6079983 : CollatzResearch.WordTrace tailWord_6079983 prefixEnd_6079983 3121953650165190772251173 := by
  unfold tailWord_6079983
  simp only [CollatzResearch.WordTrace]
  refine ⟨221755197932267444271980603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147836798621511629514653735 221755197932267444271980603)
  ·
    refine ⟨332632796898401166407970905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221755197932267444271980603 332632796898401166407970905)
    ·
      refine ⟨249474597673800874805978179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332632796898401166407970905 249474597673800874805978179)
      ·
        refine ⟨374211896510701312208967269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249474597673800874805978179 374211896510701312208967269)
        ·
          refine ⟨70164730595756496039181363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374211896510701312208967269 70164730595756496039181363)
          ·
            refine ⟨105247095893634744058772045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70164730595756496039181363 105247095893634744058772045)
            ·
              refine ⟨39467660960113029022039517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105247095893634744058772045 39467660960113029022039517)
              ·
                refine ⟨14800372860042385883264819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39467660960113029022039517 14800372860042385883264819)
                ·
                  refine ⟨22200559290063578824897229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14800372860042385883264819 22200559290063578824897229)
                  ·
                    refine ⟨8325209733773842059336461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22200559290063578824897229 8325209733773842059336461)
                    ·
                      refine ⟨3121953650165190772251173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8325209733773842059336461 3121953650165190772251173)
                      ·
                        rfl

theorem cell23_6079983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 3].length) (baseStart_6079983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079983 prefixEnd_6079983 := by exact prefixLift 6079983
  have htrace : WordTrace (prefixWord ++ tailWord_6079983) baseStart_6079983 baseEnd_6079983 := by
    simpa [prefixWord, tailWord_6079983, baseEnd_6079983] using wordTrace_append hprefix tailTrace_6079983
  have hstable : (prefixWord ++ tailWord_6079983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079983).length < 2 ^ (prefixWord ++ tailWord_6079983).sum := by decide
  have hdescent : baseEnd_6079983 < baseStart_6079983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6079990 : List Nat := [5, 1, 1, 1, 2, 3, 3, 7]
def baseStart_6079990 : Nat := 118140960795 + 6079990 * 2 ^ 59
def prefixEnd_6079990 : Nat := 4983230072969 + 3 ^ 40 * 6079990 * 2
def baseEnd_6079990 : Nat := 115628046093695268328283

theorem tailTrace_6079990 : CollatzResearch.WordTrace tailWord_6079990 prefixEnd_6079990 115628046093695268328283 := by
  unfold tailWord_6079990
  simp only [CollatzResearch.WordTrace]
  refine ⟨13859715827702630279217839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147836968828828056311656949 13859715827702630279217839)
  ·
    refine ⟨20789573741553945418826759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13859715827702630279217839 20789573741553945418826759)
    ·
      refine ⟨31184360612330918128240139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20789573741553945418826759 31184360612330918128240139)
      ·
        refine ⟨46776540918496377192360209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31184360612330918128240139 46776540918496377192360209)
        ·
          refine ⟨35082405688872282894270157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46776540918496377192360209 35082405688872282894270157)
          ·
            refine ⟨13155902133327106085351309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35082405688872282894270157 13155902133327106085351309)
            ·
              refine ⟨4933463299997664782006741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13155902133327106085351309 4933463299997664782006741)
              ·
                refine ⟨115628046093695268328283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4933463299997664782006741 115628046093695268328283)
                ·
                  rfl

theorem cell23_6079990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_6079990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6079990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6079990 prefixEnd_6079990 := by exact prefixLift 6079990
  have htrace : WordTrace (prefixWord ++ tailWord_6079990) baseStart_6079990 baseEnd_6079990 := by
    simpa [prefixWord, tailWord_6079990, baseEnd_6079990] using wordTrace_append hprefix tailTrace_6079990
  have hstable : (prefixWord ++ tailWord_6079990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6079990).length < 2 ^ (prefixWord ++ tailWord_6079990).sum := by decide
  have hdescent : baseEnd_6079990 < baseStart_6079990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6079990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080001 : List Nat := [1, 2, 4, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_6080001 : Nat := 118140960795 + 6080001 * 2 ^ 59
def prefixEnd_6080001 : Nat := 4983230072969 + 3 ^ 40 * 6080001 * 2
def baseEnd_6080001 : Nat := 3121962892816971701826091

theorem tailTrace_6080001 : CollatzResearch.WordTrace tailWord_6080001 prefixEnd_6080001 3121962892816971701826091 := by
  unfold tailWord_6080001
  simp only [CollatzResearch.WordTrace]
  refine ⟨221755854446202233346135857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147837236297468155564090571 221755854446202233346135857)
  ·
    refine ⟨166316890834651675009601893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221755854446202233346135857 166316890834651675009601893)
    ·
      refine ⟨31184417031497189064300355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166316890834651675009601893 31184417031497189064300355)
      ·
        refine ⟨46776625547245783596450533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31184417031497189064300355 46776625547245783596450533)
        ·
          refine ⟨8770617290108584424334475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46776625547245783596450533 8770617290108584424334475)
          ·
            refine ⟨13155925935162876636501713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8770617290108584424334475 13155925935162876636501713)
            ·
              refine ⟨9866944451372157477376285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13155925935162876636501713 9866944451372157477376285)
              ·
                refine ⟨3700104169264559054016107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9866944451372157477376285 3700104169264559054016107)
                ·
                  refine ⟨5550156253896838581024161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700104169264559054016107 5550156253896838581024161)
                  ·
                    refine ⟨4162617190422628935768121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5550156253896838581024161 4162617190422628935768121)
                    ·
                      refine ⟨3121962892816971701826091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162617190422628935768121 3121962892816971701826091)
                      ·
                        rfl

theorem cell23_6080001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_6080001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080001 prefixEnd_6080001 := by exact prefixLift 6080001
  have htrace : WordTrace (prefixWord ++ tailWord_6080001) baseStart_6080001 baseEnd_6080001 := by
    simpa [prefixWord, tailWord_6080001, baseEnd_6080001] using wordTrace_append hprefix tailTrace_6080001
  have hstable : (prefixWord ++ tailWord_6080001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080001).length < 2 ^ (prefixWord ++ tailWord_6080001).sum := by decide
  have hdescent : baseEnd_6080001 < baseStart_6080001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080033 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 2, 6]
def baseStart_6080033 : Nat := 118140960795 + 6080033 * 2 ^ 59
def prefixEnd_6080033 : Nat := 4983230072969 + 3 ^ 40 * 6080033 * 2
def baseEnd_6080033 : Nat := 1040659774732638525541981

theorem tailTrace_6080033 : CollatzResearch.WordTrace tailWord_6080033 prefixEnd_6080033 1040659774732638525541981 := by
  unfold tailWord_6080033
  simp only [CollatzResearch.WordTrace]
  refine ⟨221757021582086302811300753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147838014388057535207533835 221757021582086302811300753)
  ·
    refine ⟨166317766186564727108475565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221757021582086302811300753 166317766186564727108475565)
    ·
      refine ⟨62369162319961772665678337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166317766186564727108475565 62369162319961772665678337)
      ·
        refine ⟨46776871739971329499258753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62369162319961772665678337 46776871739971329499258753)
        ·
          refine ⟨35082653804978497124444065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46776871739971329499258753 35082653804978497124444065)
          ·
            refine ⟨26311990353733872843333049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35082653804978497124444065 26311990353733872843333049)
            ·
              refine ⟨19733992765300404632499787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26311990353733872843333049 19733992765300404632499787)
              ·
                refine ⟨29600989147950606948749681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19733992765300404632499787 29600989147950606948749681)
                ·
                  refine ⟨22200741860962955211562261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29600989147950606948749681 22200741860962955211562261)
                  ·
                    refine ⟨1040659774732638525541981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22200741860962955211562261 1040659774732638525541981)
                    ·
                      rfl

theorem cell23_6080033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_6080033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080033 prefixEnd_6080033 := by exact prefixLift 6080033
  have htrace : WordTrace (prefixWord ++ tailWord_6080033) baseStart_6080033 baseEnd_6080033 := by
    simpa [prefixWord, tailWord_6080033, baseEnd_6080033] using wordTrace_append hprefix tailTrace_6080033
  have hstable : (prefixWord ++ tailWord_6080033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080033).length < 2 ^ (prefixWord ++ tailWord_6080033).sum := by decide
  have hdescent : baseEnd_6080033 < baseStart_6080033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080057 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 4, 2, 2]
def baseStart_6080057 : Nat := 118140960795 + 6080057 * 2 ^ 59
def prefixEnd_6080057 : Nat := 4983230072969 + 3 ^ 40 * 6080057 * 2
def baseEnd_6080057 : Nat := 3121991647733623482725833

theorem tailTrace_6080057 : CollatzResearch.WordTrace tailWord_6080057 prefixEnd_6080057 3121991647733623482725833 := by
  unfold tailWord_6080057
  simp only [CollatzResearch.WordTrace]
  refine ⟨221757896933999354910174425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147838597955999569940116283 221757896933999354910174425)
  ·
    refine ⟨166318422700499516182630819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221757896933999354910174425 166318422700499516182630819)
    ·
      refine ⟨249477634050749274273946229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166318422700499516182630819 249477634050749274273946229)
      ·
        refine ⟨23388528192257744463182459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249477634050749274273946229 23388528192257744463182459)
        ·
          refine ⟨35082792288386616694773689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23388528192257744463182459 35082792288386616694773689)
          ·
            refine ⟨26312094216289962521080267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35082792288386616694773689 26312094216289962521080267)
            ·
              refine ⟨39468141324434943781620401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26312094216289962521080267 39468141324434943781620401)
              ·
                refine ⟨29601105993326207836215301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39468141324434943781620401 29601105993326207836215301)
                ·
                  refine ⟨5550207373748663969290369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29601105993326207836215301 5550207373748663969290369)
                  ·
                    refine ⟨4162655530311497976967777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5550207373748663969290369 4162655530311497976967777)
                    ·
                      refine ⟨3121991647733623482725833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162655530311497976967777 3121991647733623482725833)
                      ·
                        rfl

theorem cell23_6080057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_6080057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080057 prefixEnd_6080057 := by exact prefixLift 6080057
  have htrace : WordTrace (prefixWord ++ tailWord_6080057) baseStart_6080057 baseEnd_6080057 := by
    simpa [prefixWord, tailWord_6080057, baseEnd_6080057] using wordTrace_append hprefix tailTrace_6080057
  have hstable : (prefixWord ++ tailWord_6080057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080057).length < 2 ^ (prefixWord ++ tailWord_6080057).sum := by decide
  have hdescent : baseEnd_6080057 < baseStart_6080057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080060 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_6080060 : Nat := 118140960795 + 6080060 * 2 ^ 59
def prefixEnd_6080060 : Nat := 4983230072969 + 3 ^ 40 * 6080060 * 2
def baseEnd_6080060 : Nat := 3121993188175586970988319

theorem tailTrace_6080060 : CollatzResearch.WordTrace tailWord_6080060 prefixEnd_6080060 3121993188175586970988319 := by
  unfold tailWord_6080060
  simp only [CollatzResearch.WordTrace]
  refine ⟨110879003176494243211266817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147838670901992324281689089 110879003176494243211266817)
  ·
    refine ⟨83159252382370682408450113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110879003176494243211266817 83159252382370682408450113)
    ·
      refine ⟨62369439286778011806337585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83159252382370682408450113 62369439286778011806337585)
      ·
        refine ⟨46777079465083508854753189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62369439286778011806337585 46777079465083508854753189)
        ·
          refine ⟨8770702399703157910266223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46777079465083508854753189 8770702399703157910266223)
          ·
            refine ⟨13156053599554736865399335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8770702399703157910266223 13156053599554736865399335)
            ·
              refine ⟨19734080399332105298099003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13156053599554736865399335 19734080399332105298099003)
              ·
                refine ⟨29601120598998157947148505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19734080399332105298099003 29601120598998157947148505)
                ·
                  refine ⟨22200840449248618460361379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29601120598998157947148505 22200840449248618460361379)
                  ·
                    refine ⟨33301260673872927690542069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22200840449248618460361379 33301260673872927690542069)
                    ·
                      refine ⟨3121993188175586970988319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33301260673872927690542069 3121993188175586970988319)
                      ·
                        rfl

theorem cell23_6080060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_6080060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080060 prefixEnd_6080060 := by exact prefixLift 6080060
  have htrace : WordTrace (prefixWord ++ tailWord_6080060) baseStart_6080060 baseEnd_6080060 := by
    simpa [prefixWord, tailWord_6080060, baseEnd_6080060] using wordTrace_append hprefix tailTrace_6080060
  have hstable : (prefixWord ++ tailWord_6080060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080060).length < 2 ^ (prefixWord ++ tailWord_6080060).sum := by decide
  have hdescent : baseEnd_6080060 < baseStart_6080060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080073 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 4, 3, 3]
def baseStart_6080073 : Nat := 118140960795 + 6080073 * 2 ^ 59
def prefixEnd_6080073 : Nat := 4983230072969 + 3 ^ 40 * 6080073 * 2
def baseEnd_6080073 : Nat := 3121999863424095420125759

theorem tailTrace_6080073 : CollatzResearch.WordTrace tailWord_6080073 prefixEnd_6080073 3121999863424095420125759 := by
  unfold tailWord_6080073
  simp only [CollatzResearch.WordTrace]
  refine ⟨221758480501941389642756873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147838987001294259761837915 221758480501941389642756873)
  ·
    refine ⟨166318860376456042232067655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221758480501941389642756873 166318860376456042232067655)
    ·
      refine ⟨249478290564684063348101483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166318860376456042232067655 249478290564684063348101483)
      ·
        refine ⟨374217435847026095022152225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249478290564684063348101483 374217435847026095022152225)
        ·
          refine ⟨280663076885269571266614169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374217435847026095022152225 280663076885269571266614169)
          ·
            refine ⟨210497307663952178449960627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280663076885269571266614169 210497307663952178449960627)
            ·
              refine ⟨315745961495928267674940941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210497307663952178449960627 315745961495928267674940941)
              ·
                refine ⟨118404735560973100378102853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315745961495928267674940941 118404735560973100378102853)
                ·
                  refine ⟨22200887917682456320894285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118404735560973100378102853 22200887917682456320894285)
                  ·
                    refine ⟨8325332969130921120335357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22200887917682456320894285 8325332969130921120335357)
                    ·
                      refine ⟨3121999863424095420125759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8325332969130921120335357 3121999863424095420125759)
                      ·
                        rfl

theorem cell23_6080073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3, 3].length) (baseStart_6080073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080073 prefixEnd_6080073 := by exact prefixLift 6080073
  have htrace : WordTrace (prefixWord ++ tailWord_6080073) baseStart_6080073 baseEnd_6080073 := by
    simpa [prefixWord, tailWord_6080073, baseEnd_6080073] using wordTrace_append hprefix tailTrace_6080073
  have hstable : (prefixWord ++ tailWord_6080073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080073).length < 2 ^ (prefixWord ++ tailWord_6080073).sum := by decide
  have hdescent : baseEnd_6080073 < baseStart_6080073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080113 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_6080113 : Nat := 118140960795 + 6080113 * 2 ^ 59
def prefixEnd_6080113 : Nat := 4983230072969 + 3 ^ 40 * 6080113 * 2
def baseEnd_6080113 : Nat := 3122020402650275263625575

theorem tailTrace_6080113 : CollatzResearch.WordTrace tailWord_6080113 prefixEnd_6080113 3122020402650275263625575 := by
  unfold tailWord_6080113
  simp only [CollatzResearch.WordTrace]
  refine ⟨221759939421796476474212993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147839959614530984316141995 221759939421796476474212993)
  ·
    refine ⟨166319954566347357355659745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221759939421796476474212993 166319954566347357355659745)
    ·
      refine ⟨124739965924760518016744809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166319954566347357355659745 124739965924760518016744809)
      ·
        refine ⟨93554974443570388512558607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124739965924760518016744809 93554974443570388512558607)
        ·
          refine ⟨140332461665355582768837911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93554974443570388512558607 140332461665355582768837911)
          ·
            refine ⟨210498692498033374153256867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140332461665355582768837911 210498692498033374153256867)
            ·
              refine ⟨315748038747050061229885301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210498692498033374153256867 315748038747050061229885301)
              ·
                refine ⟨29601378632535943240301747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315748038747050061229885301 29601378632535943240301747)
                ·
                  refine ⟨44402067948803914860452621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29601378632535943240301747 44402067948803914860452621)
                  ·
                    refine ⟨16650775480801468072669733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44402067948803914860452621 16650775480801468072669733)
                    ·
                      refine ⟨3122020402650275263625575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16650775480801468072669733 3122020402650275263625575)
                      ·
                        rfl

theorem cell23_6080113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_6080113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080113 prefixEnd_6080113 := by exact prefixLift 6080113
  have htrace : WordTrace (prefixWord ++ tailWord_6080113) baseStart_6080113 baseEnd_6080113 := by
    simpa [prefixWord, tailWord_6080113, baseEnd_6080113] using wordTrace_append hprefix tailTrace_6080113
  have hstable : (prefixWord ++ tailWord_6080113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080113).length < 2 ^ (prefixWord ++ tailWord_6080113).sum := by decide
  have hdescent : baseEnd_6080113 < baseStart_6080113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080133 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_6080133 : Nat := 118140960795 + 6080133 * 2 ^ 59
def prefixEnd_6080133 : Nat := 4983230072969 + 3 ^ 40 * 6080133 * 2
def baseEnd_6080133 : Nat := 3122030672263365185375483

theorem tailTrace_6080133 : CollatzResearch.WordTrace tailWord_6080133 prefixEnd_6080133 3122030672263365185375483 := by
  unfold tailWord_6080133
  simp only [CollatzResearch.WordTrace]
  refine ⟨221760668881724019889941053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147840445921149346593294035 221760668881724019889941053)
  ·
    refine ⟨83160250830646507458727895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221760668881724019889941053 83160250830646507458727895)
    ·
      refine ⟨124740376245969761188091843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83160250830646507458727895 124740376245969761188091843)
      ·
        refine ⟨187110564368954641782137765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124740376245969761188091843 187110564368954641782137765)
        ·
          refine ⟨35083230819178995334150831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187110564368954641782137765 35083230819178995334150831)
          ·
            refine ⟨52624846228768493001226247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35083230819178995334150831 52624846228768493001226247)
            ·
              refine ⟨78937269343152739501839371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52624846228768493001226247 78937269343152739501839371)
              ·
                refine ⟨118405904014729109252759057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78937269343152739501839371 118405904014729109252759057)
                ·
                  refine ⟨88804428011046831939569293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118405904014729109252759057 88804428011046831939569293)
                  ·
                    refine ⟨33301660504142561977338485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88804428011046831939569293 33301660504142561977338485)
                    ·
                      refine ⟨3122030672263365185375483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33301660504142561977338485 3122030672263365185375483)
                      ·
                        rfl

theorem cell23_6080133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_6080133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080133 prefixEnd_6080133 := by exact prefixLift 6080133
  have htrace : WordTrace (prefixWord ++ tailWord_6080133) baseStart_6080133 baseEnd_6080133 := by
    simpa [prefixWord, tailWord_6080133, baseEnd_6080133] using wordTrace_append hprefix tailTrace_6080133
  have hstable : (prefixWord ++ tailWord_6080133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080133).length < 2 ^ (prefixWord ++ tailWord_6080133).sum := by decide
  have hdescent : baseEnd_6080133 < baseStart_6080133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080140 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_6080140 : Nat := 118140960795 + 6080140 * 2 ^ 59
def prefixEnd_6080140 : Nat := 4983230072969 + 3 ^ 40 * 6080140 * 2
def baseEnd_6080140 : Nat := 1040678088875982219329317

theorem tailTrace_6080140 : CollatzResearch.WordTrace tailWord_6080140 prefixEnd_6080140 1040678088875982219329317 := by
  unfold tailWord_6080140
  simp only [CollatzResearch.WordTrace]
  refine ⟨110880462096349330042722937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147840616128465773390297249 110880462096349330042722937)
  ·
    refine ⟨83160346572261997532042203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110880462096349330042722937 83160346572261997532042203)
    ·
      refine ⟨124740519858392996298063305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83160346572261997532042203 124740519858392996298063305)
      ·
        refine ⟨93555389893794747223547479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124740519858392996298063305 93555389893794747223547479)
        ·
          refine ⟨140333084840692120835321219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93555389893794747223547479 140333084840692120835321219)
          ·
            refine ⟨210499627261038181252981829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140333084840692120835321219 210499627261038181252981829)
            ·
              refine ⟨39468680111444658984934093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210499627261038181252981829 39468680111444658984934093)
              ·
                refine ⟨14800755041791747119350285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39468680111444658984934093 14800755041791747119350285)
                ·
                  refine ⟨5550283140671905169756357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14800755041791747119350285 5550283140671905169756357)
                  ·
                    refine ⟨1040678088875982219329317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5550283140671905169756357 1040678088875982219329317)
                    ·
                      rfl

theorem cell23_6080140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_6080140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080140 prefixEnd_6080140 := by exact prefixLift 6080140
  have htrace : WordTrace (prefixWord ++ tailWord_6080140) baseStart_6080140 baseEnd_6080140 := by
    simpa [prefixWord, tailWord_6080140, baseEnd_6080140] using wordTrace_append hprefix tailTrace_6080140
  have hstable : (prefixWord ++ tailWord_6080140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080140).length < 2 ^ (prefixWord ++ tailWord_6080140).sum := by decide
  have hdescent : baseEnd_6080140 < baseStart_6080140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080190 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_6080190 : Nat := 118140960795 + 6080190 * 2 ^ 59
def prefixEnd_6080190 : Nat := 4983230072969 + 3 ^ 40 * 6080190 * 2
def baseEnd_6080190 : Nat := 3122059940660671462362721

theorem tailTrace_6080190 : CollatzResearch.WordTrace tailWord_6080190 prefixEnd_6080190 3122059940660671462362721 := by
  unfold tailWord_6080190
  simp only [CollatzResearch.WordTrace]
  refine ⟨27720343480314689828095753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147841831895011679083177349 27720343480314689828095753)
  ·
    refine ⟨20790257610236017371071815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27720343480314689828095753 20790257610236017371071815)
    ·
      refine ⟨31185386415354026056607723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20790257610236017371071815 31185386415354026056607723)
      ·
        refine ⟨46778079623031039084911585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31185386415354026056607723 46778079623031039084911585)
        ·
          refine ⟨35083559717273279313683689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46778079623031039084911585 35083559717273279313683689)
          ·
            refine ⟨26312669787954959485262767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35083559717273279313683689 26312669787954959485262767)
            ·
              refine ⟨39469004681932439227894151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26312669787954959485262767 39469004681932439227894151)
              ·
                refine ⟨59203507022898658841841227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39469004681932439227894151 59203507022898658841841227)
                ·
                  refine ⟨88805260534347988262761841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59203507022898658841841227 88805260534347988262761841)
                  ·
                    refine ⟨66603945400760991197071381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88805260534347988262761841 66603945400760991197071381)
                    ·
                      refine ⟨3122059940660671462362721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66603945400760991197071381 3122059940660671462362721)
                      ·
                        rfl

theorem cell23_6080190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_6080190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080190 prefixEnd_6080190 := by exact prefixLift 6080190
  have htrace : WordTrace (prefixWord ++ tailWord_6080190) baseStart_6080190 baseEnd_6080190 := by
    simpa [prefixWord, tailWord_6080190, baseEnd_6080190] using wordTrace_append hprefix tailTrace_6080190
  have hstable : (prefixWord ++ tailWord_6080190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080190).length < 2 ^ (prefixWord ++ tailWord_6080190).sum := by decide
  have hdescent : baseEnd_6080190 < baseStart_6080190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080204 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 6]
def baseStart_6080204 : Nat := 118140960795 + 6080204 * 2 ^ 59
def prefixEnd_6080204 : Nat := 4983230072969 + 3 ^ 40 * 6080204 * 2
def baseEnd_6080204 : Nat := 346896347709981600843073

theorem tailTrace_6080204 : CollatzResearch.WordTrace tailWord_6080204 prefixEnd_6080204 346896347709981600843073 := by
  unfold tailWord_6080204
  simp only [CollatzResearch.WordTrace]
  refine ⟨110881629232233399507887833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147842172309644532677183777 110881629232233399507887833)
  ·
    refine ⟨83161221924175049630915875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110881629232233399507887833 83161221924175049630915875)
    ·
      refine ⟨124741832886262574446373813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83161221924175049630915875 124741832886262574446373813)
      ·
        refine ⟨11694546833087116354347545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124741832886262574446373813 11694546833087116354347545)
        ·
          refine ⟨8770910124815337265760659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11694546833087116354347545 8770910124815337265760659)
          ·
            refine ⟨13156365187223005898640989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8770910124815337265760659 13156365187223005898640989)
            ·
              refine ⟨4933636945208627211990371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13156365187223005898640989 4933636945208627211990371)
              ·
                refine ⟨7400455417812940817985557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4933636945208627211990371 7400455417812940817985557)
                ·
                  refine ⟨346896347709981600843073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7400455417812940817985557 346896347709981600843073)
                  ·
                    rfl

theorem cell23_6080204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_6080204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080204 prefixEnd_6080204 := by exact prefixLift 6080204
  have htrace : WordTrace (prefixWord ++ tailWord_6080204) baseStart_6080204 baseEnd_6080204 := by
    simpa [prefixWord, tailWord_6080204, baseEnd_6080204] using wordTrace_append hprefix tailTrace_6080204
  have hstable : (prefixWord ++ tailWord_6080204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080204).length < 2 ^ (prefixWord ++ tailWord_6080204).sum := by decide
  have hdescent : baseEnd_6080204 < baseStart_6080204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080217 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 1, 5]
def baseStart_6080217 : Nat := 118140960795 + 6080217 * 2 ^ 59
def prefixEnd_6080217 : Nat := 4983230072969 + 3 ^ 40 * 6080217 * 2
def baseEnd_6080217 : Nat := 1040691268212780952241699

theorem tailTrace_6080217 : CollatzResearch.WordTrace tailWord_6080217 prefixEnd_6080217 1040691268212780952241699 := by
  unfold tailWord_6080217
  simp only [CollatzResearch.WordTrace]
  refine ⟨221763732613419702235998905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147842488408946468157332603 221763732613419702235998905)
  ·
    refine ⟨166322799460064776676999179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221763732613419702235998905 166322799460064776676999179)
    ·
      refine ⟨249484199190097165015498769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166322799460064776676999179 249484199190097165015498769)
      ·
        refine ⟨187113149392572873761624077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249484199190097165015498769 187113149392572873761624077)
        ·
          refine ⟨70167431022214827660609029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187113149392572873761624077 70167431022214827660609029)
          ·
            refine ⟨13156393316665280186364193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70167431022214827660609029 13156393316665280186364193)
            ·
              refine ⟨9867294987498960139773145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13156393316665280186364193 9867294987498960139773145)
              ·
                refine ⟨7400471240624220104829859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9867294987498960139773145 7400471240624220104829859)
                ·
                  refine ⟨11100706860936330157244789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7400471240624220104829859 11100706860936330157244789)
                  ·
                    refine ⟨1040691268212780952241699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11100706860936330157244789 1040691268212780952241699)
                    ·
                      rfl

theorem cell23_6080217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 5].length) (baseStart_6080217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080217 prefixEnd_6080217 := by exact prefixLift 6080217
  have htrace : WordTrace (prefixWord ++ tailWord_6080217) baseStart_6080217 baseEnd_6080217 := by
    simpa [prefixWord, tailWord_6080217, baseEnd_6080217] using wordTrace_append hprefix tailTrace_6080217
  have hstable : (prefixWord ++ tailWord_6080217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080217).length < 2 ^ (prefixWord ++ tailWord_6080217).sum := by decide
  have hdescent : baseEnd_6080217 < baseStart_6080217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080243 : List Nat := [1, 1, 1, 2, 2, 3, 13]
def baseStart_6080243 : Nat := 118140960795 + 6080243 * 2 ^ 59
def prefixEnd_6080243 : Nat := 4983230072969 + 3 ^ 40 * 6080243 * 2
def baseEnd_6080243 : Nat := 38544285865868638950617

theorem tailTrace_6080243 : CollatzResearch.WordTrace tailWord_6080243 prefixEnd_6080243 38544285865868638950617 := by
  unfold tailWord_6080243
  simp only [CollatzResearch.WordTrace]
  refine ⟨221764680911325508676445383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147843120607550339117630255 221764680911325508676445383)
  ·
    refine ⟨332647021366988263014668075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221764680911325508676445383 332647021366988263014668075)
    ·
      refine ⟨498970532050482394522002113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332647021366988263014668075 498970532050482394522002113)
      ·
        refine ⟨374227899037861795891501585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498970532050482394522002113 374227899037861795891501585)
        ·
          refine ⟨280670924278396346918626189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374227899037861795891501585 280670924278396346918626189)
          ·
            refine ⟨105251596604398630094484821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280670924278396346918626189 105251596604398630094484821)
            ·
              refine ⟨38544285865868638950617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 105251596604398630094484821 38544285865868638950617)
              ·
                rfl

theorem cell23_6080243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 13].length) (baseStart_6080243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080243 prefixEnd_6080243 := by exact prefixLift 6080243
  have htrace : WordTrace (prefixWord ++ tailWord_6080243) baseStart_6080243 baseEnd_6080243 := by
    simpa [prefixWord, tailWord_6080243, baseEnd_6080243] using wordTrace_append hprefix tailTrace_6080243
  have hstable : (prefixWord ++ tailWord_6080243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080243).length < 2 ^ (prefixWord ++ tailWord_6080243).sum := by decide
  have hdescent : baseEnd_6080243 < baseStart_6080243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080260 : List Nat := [2, 3, 2, 2, 1, 2, 1, 10]
def baseStart_6080260 : Nat := 118140960795 + 6080260 * 2 ^ 59
def prefixEnd_6080260 : Nat := 4983230072969 + 3 ^ 40 * 6080260 * 2
def baseEnd_6080260 : Nat := 115633180900240229203237

theorem tailTrace_6080260 : CollatzResearch.WordTrace tailWord_6080260 prefixEnd_6080260 115633180900240229203237 := by
  unfold tailWord_6080260
  simp only [CollatzResearch.WordTrace]
  refine ⟨110882650476131960289907117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147843533968175947053209489 110882650476131960289907117)
  ·
    refine ⟨41580993928549485108715169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110882650476131960289907117 41580993928549485108715169)
    ·
      refine ⟨31185745446412113831536377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41580993928549485108715169 31185745446412113831536377)
      ·
        refine ⟨23389309084809085373652283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31185745446412113831536377 23389309084809085373652283)
        ·
          refine ⟨35083963627213628060478425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23389309084809085373652283 35083963627213628060478425)
          ·
            refine ⟨26312972720410221045358819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35083963627213628060478425 26312972720410221045358819)
            ·
              refine ⟨39469459080615331568038229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26312972720410221045358819 39469459080615331568038229)
              ·
                refine ⟨115633180900240229203237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39469459080615331568038229 115633180900240229203237)
                ·
                  rfl

theorem cell23_6080260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 10].length) (baseStart_6080260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080260 prefixEnd_6080260 := by exact prefixLift 6080260
  have htrace : WordTrace (prefixWord ++ tailWord_6080260) baseStart_6080260 baseEnd_6080260 := by
    simpa [prefixWord, tailWord_6080260, baseEnd_6080260] using wordTrace_append hprefix tailTrace_6080260
  have hstable : (prefixWord ++ tailWord_6080260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080260).length < 2 ^ (prefixWord ++ tailWord_6080260).sum := by decide
  have hdescent : baseEnd_6080260 < baseStart_6080260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080287 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 3]
def baseStart_6080287 : Nat := 118140960795 + 6080287 * 2 ^ 59
def prefixEnd_6080287 : Nat := 4983230072969 + 3 ^ 40 * 6080287 * 2
def baseEnd_6080287 : Nat := 3122109748284157582849775

theorem tailTrace_6080287 : CollatzResearch.WordTrace tailWord_6080287 prefixEnd_6080287 3122109748284157582849775 := by
  unfold tailWord_6080287
  simp only [CollatzResearch.WordTrace]
  refine ⟨221766285723166104191047115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147844190482110736127364743 221766285723166104191047115)
  ·
    refine ⟨332649428584749156286570673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221766285723166104191047115 332649428584749156286570673)
    ·
      refine ⟨249487071438561867214928005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332649428584749156286570673 249487071438561867214928005)
      ·
        refine ⟨46778825894730350102799001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249487071438561867214928005 46778825894730350102799001)
        ·
          refine ⟨35084119421047762577099251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46778825894730350102799001 35084119421047762577099251)
          ·
            refine ⟨52626179131571643865648877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35084119421047762577099251 52626179131571643865648877)
            ·
              refine ⟨19734817174339366449618329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52626179131571643865648877 19734817174339366449618329)
              ·
                refine ⟨14801112880754524837213747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19734817174339366449618329 14801112880754524837213747)
                ·
                  refine ⟨22201669321131787255820621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14801112880754524837213747 22201669321131787255820621)
                  ·
                    refine ⟨8325625995424420220932733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22201669321131787255820621 8325625995424420220932733)
                    ·
                      refine ⟨3122109748284157582849775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8325625995424420220932733 3122109748284157582849775)
                      ·
                        rfl

theorem cell23_6080287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_6080287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080287 prefixEnd_6080287 := by exact prefixLift 6080287
  have htrace : WordTrace (prefixWord ++ tailWord_6080287) baseStart_6080287 baseEnd_6080287 := by
    simpa [prefixWord, tailWord_6080287, baseEnd_6080287] using wordTrace_append hprefix tailTrace_6080287
  have hstable : (prefixWord ++ tailWord_6080287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080287).length < 2 ^ (prefixWord ++ tailWord_6080287).sum := by decide
  have hdescent : baseEnd_6080287 < baseStart_6080287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080297 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 7, 3, 2]
def baseStart_6080297 : Nat := 118140960795 + 6080297 * 2 ^ 59
def prefixEnd_6080297 : Nat := 4983230072969 + 3 ^ 40 * 6080297 * 2
def baseEnd_6080297 : Nat := 3122114883090702543724729

theorem tailTrace_6080297 : CollatzResearch.WordTrace tailWord_6080297 prefixEnd_6080297 3122114883090702543724729 := by
  unfold tailWord_6080297
  simp only [CollatzResearch.WordTrace]
  refine ⟨221766650453129875898911145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147844433635419917265940763 221766650453129875898911145)
  ·
    refine ⟨166324987839847406924183359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221766650453129875898911145 166324987839847406924183359)
    ·
      refine ⟨249487481759771110386275039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166324987839847406924183359 249487481759771110386275039)
      ·
        refine ⟨374231222639656665579412559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249487481759771110386275039 374231222639656665579412559)
        ·
          refine ⟨561346833959484998369118839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374231222639656665579412559 561346833959484998369118839)
          ·
            refine ⟨842020250939227497553678259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561346833959484998369118839 842020250939227497553678259)
            ·
              refine ⟨1263030376408841246330517389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842020250939227497553678259 1263030376408841246330517389)
              ·
                refine ⟨473636391153315467373944021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1263030376408841246330517389 473636391153315467373944021)
                ·
                  refine ⟨11100852917655831266576813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 473636391153315467373944021 11100852917655831266576813)
                  ·
                    refine ⟨4162819844120936724966305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11100852917655831266576813 4162819844120936724966305)
                    ·
                      refine ⟨3122114883090702543724729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162819844120936724966305 3122114883090702543724729)
                      ·
                        rfl

theorem cell23_6080297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 3, 2].length) (baseStart_6080297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080297 prefixEnd_6080297 := by exact prefixLift 6080297
  have htrace : WordTrace (prefixWord ++ tailWord_6080297) baseStart_6080297 baseEnd_6080297 := by
    simpa [prefixWord, tailWord_6080297, baseEnd_6080297] using wordTrace_append hprefix tailTrace_6080297
  have hstable : (prefixWord ++ tailWord_6080297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080297).length < 2 ^ (prefixWord ++ tailWord_6080297).sum := by decide
  have hdescent : baseEnd_6080297 < baseStart_6080297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080305 : List Nat := [1, 2, 2, 3, 2, 4, 2, 2, 1, 2, 2]
def baseStart_6080305 : Nat := 118140960795 + 6080305 * 2 ^ 59
def prefixEnd_6080305 : Nat := 4983230072969 + 3 ^ 40 * 6080305 * 2
def baseEnd_6080305 : Nat := 3122118990935938512424693

theorem tailTrace_6080305 : CollatzResearch.WordTrace tailWord_6080305 prefixEnd_6080305 3122118990935938512424693 := by
  unfold tailWord_6080305
  simp only [CollatzResearch.WordTrace]
  refine ⟨221766942237100893265202369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147844628158067262176801579 221766942237100893265202369)
  ·
    refine ⟨166325206677825669948901777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221766942237100893265202369 166325206677825669948901777)
    ·
      refine ⟨124743905008369252461676333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166325206677825669948901777 124743905008369252461676333)
      ·
        refine ⟨46778964378138469673128625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124743905008369252461676333 46778964378138469673128625)
        ·
          refine ⟨35084223283603852254846469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46778964378138469673128625 35084223283603852254846469)
          ·
            refine ⟨6578291865675722297783713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35084223283603852254846469 6578291865675722297783713)
            ·
              refine ⟨4933718899256791723337785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6578291865675722297783713 4933718899256791723337785)
              ·
                refine ⟨3700289174442593792503339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4933718899256791723337785 3700289174442593792503339)
                ·
                  refine ⟨5550433761663890688755009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700289174442593792503339 5550433761663890688755009)
                  ·
                    refine ⟨4162825321247918016566257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5550433761663890688755009 4162825321247918016566257)
                    ·
                      refine ⟨3122118990935938512424693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162825321247918016566257 3122118990935938512424693)
                      ·
                        rfl

theorem cell23_6080305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_6080305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080305 prefixEnd_6080305 := by exact prefixLift 6080305
  have htrace : WordTrace (prefixWord ++ tailWord_6080305) baseStart_6080305 baseEnd_6080305 := by
    simpa [prefixWord, tailWord_6080305, baseEnd_6080305] using wordTrace_append hprefix tailTrace_6080305
  have hstable : (prefixWord ++ tailWord_6080305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080305).length < 2 ^ (prefixWord ++ tailWord_6080305).sum := by decide
  have hdescent : baseEnd_6080305 < baseStart_6080305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080314 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2]
def baseStart_6080314 : Nat := 118140960795 + 6080314 * 2 ^ 59
def prefixEnd_6080314 : Nat := 4983230072969 + 3 ^ 40 * 6080314 * 2
def baseEnd_6080314 : Nat := 3122123612261828977212151

theorem tailTrace_6080314 : CollatzResearch.WordTrace tailWord_6080314 prefixEnd_6080314 3122123612261828977212151 := by
  unfold tailWord_6080314
  simp only [CollatzResearch.WordTrace]
  refine ⟨55441817623517071950569999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147844846996045525201519997 55441817623517071950569999)
  ·
    refine ⟨83162726435275607925854999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55441817623517071950569999 83162726435275607925854999)
    ·
      refine ⟨124744089652913411888782499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83162726435275607925854999 124744089652913411888782499)
      ·
        refine ⟨187116134479370117833173749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124744089652913411888782499 187116134479370117833173749)
        ·
          refine ⟨17542137607440948546860039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187116134479370117833173749 17542137607440948546860039)
          ·
            refine ⟨26313206411161422820290059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17542137607440948546860039 26313206411161422820290059)
            ·
              refine ⟨39469809616742134230435089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26313206411161422820290059 39469809616742134230435089)
              ·
                refine ⟨29602357212556600672826317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39469809616742134230435089 29602357212556600672826317)
                ·
                  refine ⟨11100883954708725252309869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29602357212556600672826317 11100883954708725252309869)
                  ·
                    refine ⟨4162831483015771969616201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11100883954708725252309869 4162831483015771969616201)
                    ·
                      refine ⟨3122123612261828977212151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162831483015771969616201 3122123612261828977212151)
                      ·
                        rfl

theorem cell23_6080314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_6080314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080314 prefixEnd_6080314 := by exact prefixLift 6080314
  have htrace : WordTrace (prefixWord ++ tailWord_6080314) baseStart_6080314 baseEnd_6080314 := by
    simpa [prefixWord, tailWord_6080314, baseEnd_6080314] using wordTrace_append hprefix tailTrace_6080314
  have hstable : (prefixWord ++ tailWord_6080314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080314).length < 2 ^ (prefixWord ++ tailWord_6080314).sum := by decide
  have hdescent : baseEnd_6080314 < baseStart_6080314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080348 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_6080348 : Nat := 118140960795 + 6080348 * 2 ^ 59
def prefixEnd_6080348 : Nat := 4983230072969 + 3 ^ 40 * 6080348 * 2
def baseEnd_6080348 : Nat := 3122141070604081844186995

theorem tailTrace_6080348 : CollatzResearch.WordTrace tailWord_6080348 prefixEnd_6080348 3122141070604081844186995 := by
  unfold tailWord_6080348
  simp only [CollatzResearch.WordTrace]
  refine ⟨110884255287972555804508849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147845673717296741072678465 110884255287972555804508849)
  ·
    refine ⟨83163191465979416853381637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110884255287972555804508849 83163191465979416853381637)
    ·
      refine ⟨15593098399871140660009057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83163191465979416853381637 15593098399871140660009057)
      ·
        refine ⟨11694823799903355495006793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15593098399871140660009057 11694823799903355495006793)
        ·
          refine ⟨8771117849927516621255095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11694823799903355495006793 8771117849927516621255095)
          ·
            refine ⟨13156676774891274931882643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8771117849927516621255095 13156676774891274931882643)
            ·
              refine ⟨19735015162336912397823965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13156676774891274931882643 19735015162336912397823965)
              ·
                refine ⟨7400630685876342149183987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19735015162336912397823965 7400630685876342149183987)
                ·
                  refine ⟨11100946028814513223775981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7400630685876342149183987 11100946028814513223775981)
                  ·
                    refine ⟨4162854760805442458915993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11100946028814513223775981 4162854760805442458915993)
                    ·
                      refine ⟨3122141070604081844186995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162854760805442458915993 3122141070604081844186995)
                      ·
                        rfl

theorem cell23_6080348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_6080348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080348 prefixEnd_6080348 := by exact prefixLift 6080348
  have htrace : WordTrace (prefixWord ++ tailWord_6080348) baseStart_6080348 baseEnd_6080348 := by
    simpa [prefixWord, tailWord_6080348, baseEnd_6080348] using wordTrace_append hprefix tailTrace_6080348
  have hstable : (prefixWord ++ tailWord_6080348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080348).length < 2 ^ (prefixWord ++ tailWord_6080348).sum := by decide
  have hdescent : baseEnd_6080348 < baseStart_6080348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080377 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 2, 3, 3]
def baseStart_6080377 : Nat := 118140960795 + 6080377 * 2 ^ 59
def prefixEnd_6080377 : Nat := 4983230072969 + 3 ^ 40 * 6080377 * 2
def baseEnd_6080377 : Nat := 3122155961543062230724361

theorem tailTrace_6080377 : CollatzResearch.WordTrace tailWord_6080377 prefixEnd_6080377 3122155961543062230724361 := by
  unfold tailWord_6080377
  simp only [CollatzResearch.WordTrace]
  refine ⟨221769568292840049561823385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147846378861893366374548923 221769568292840049561823385)
  ·
    refine ⟨166327176219630037171367539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221769568292840049561823385 166327176219630037171367539)
    ·
      refine ⟨249490764329445055757051309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166327176219630037171367539 249490764329445055757051309)
      ·
        refine ⟨93559036623541895908894241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249490764329445055757051309 93559036623541895908894241)
        ·
          refine ⟨70169277467656421931670681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93559036623541895908894241 70169277467656421931670681)
          ·
            refine ⟨52626958100742316448753011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70169277467656421931670681 52626958100742316448753011)
            ·
              refine ⟨78940437151113474673129517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52626958100742316448753011 78940437151113474673129517)
              ·
                refine ⟨29602663931667553002423569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78940437151113474673129517 29602663931667553002423569)
                ·
                  refine ⟨22201997948750664751817677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29602663931667553002423569 22201997948750664751817677)
                  ·
                    refine ⟨8325749230781499281931629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22201997948750664751817677 8325749230781499281931629)
                    ·
                      refine ⟨3122155961543062230724361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8325749230781499281931629 3122155961543062230724361)
                      ·
                        rfl

theorem cell23_6080377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_6080377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080377 prefixEnd_6080377 := by exact prefixLift 6080377
  have htrace : WordTrace (prefixWord ++ tailWord_6080377) baseStart_6080377 baseEnd_6080377 := by
    simpa [prefixWord, tailWord_6080377, baseEnd_6080377] using wordTrace_append hprefix tailTrace_6080377
  have hstable : (prefixWord ++ tailWord_6080377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080377).length < 2 ^ (prefixWord ++ tailWord_6080377).sum := by decide
  have hdescent : baseEnd_6080377 < baseStart_6080377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080418 : List Nat := [3, 3, 1, 2, 3, 1, 3, 2, 5]
def baseStart_6080418 : Nat := 118140960795 + 6080418 * 2 ^ 59
def prefixEnd_6080418 : Nat := 4983230072969 + 3 ^ 40 * 6080418 * 2
def baseEnd_6080418 : Nat := 346908557138877396701297

theorem tailTrace_6080418 : CollatzResearch.WordTrace tailWord_6080418 prefixEnd_6080418 346908557138877396701297 := by
  unfold tailWord_6080418
  simp only [CollatzResearch.WordTrace]
  refine ⟨55442765921422878391016477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147847375790461009042710605 55442765921422878391016477)
  ·
    refine ⟨20791037220533579396631179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55442765921422878391016477 20791037220533579396631179)
    ·
      refine ⟨31186555830800369094946769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20791037220533579396631179 31186555830800369094946769)
      ·
        refine ⟨23389916873100276821210077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31186555830800369094946769 23389916873100276821210077)
        ·
          refine ⟨8771218827412603807953779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23389916873100276821210077 8771218827412603807953779)
          ·
            refine ⟨13156828241118905711930669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8771218827412603807953779 13156828241118905711930669)
            ·
              refine ⟨4933810590419589641974001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13156828241118905711930669 4933810590419589641974001)
              ·
                refine ⟨3700357942814692231480501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4933810590419589641974001 3700357942814692231480501)
                ·
                  refine ⟨346908557138877396701297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3700357942814692231480501 346908557138877396701297)
                  ·
                    rfl

theorem cell23_6080418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_6080418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080418 prefixEnd_6080418 := by exact prefixLift 6080418
  have htrace : WordTrace (prefixWord ++ tailWord_6080418) baseStart_6080418 baseEnd_6080418 := by
    simpa [prefixWord, tailWord_6080418, baseEnd_6080418] using wordTrace_append hprefix tailTrace_6080418
  have hstable : (prefixWord ++ tailWord_6080418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080418).length < 2 ^ (prefixWord ++ tailWord_6080418).sum := by decide
  have hdescent : baseEnd_6080418 < baseStart_6080418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080434 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2]
def baseStart_6080434 : Nat := 118140960795 + 6080434 * 2 ^ 59
def prefixEnd_6080434 : Nat := 4983230072969 + 3 ^ 40 * 6080434 * 2
def baseEnd_6080434 : Nat := 3122185229940368507711599

theorem tailTrace_6080434 : CollatzResearch.WordTrace tailWord_6080434 prefixEnd_6080434 3122185229940368507711599 := by
  unfold tailWord_6080434
  simp only [CollatzResearch.WordTrace]
  refine ⟨55442911813408387074162089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147847764835755698864432237 55442911813408387074162089)
  ·
    refine ⟨41582183860056290305621567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55442911813408387074162089 41582183860056290305621567)
    ·
      refine ⟨62373275790084435458432351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41582183860056290305621567 62373275790084435458432351)
      ·
        refine ⟨93559913685126653187648527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62373275790084435458432351 93559913685126653187648527)
        ·
          refine ⟨140339870527689979781472791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93559913685126653187648527 140339870527689979781472791)
          ·
            refine ⟨210509805791534969672209187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140339870527689979781472791 210509805791534969672209187)
            ·
              refine ⟨315764708687302454508313781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210509805791534969672209187 315764708687302454508313781)
              ·
                refine ⟨29602941439434605110154417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315764708687302454508313781 29602941439434605110154417)
                ·
                  refine ⟨22202206079575953832615813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29602941439434605110154417 22202206079575953832615813)
                  ·
                    refine ⟨4162913639920491343615465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22202206079575953832615813 4162913639920491343615465)
                    ·
                      refine ⟨3122185229940368507711599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4162913639920491343615465 3122185229940368507711599)
                      ·
                        rfl

theorem cell23_6080434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_6080434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080434 prefixEnd_6080434 := by exact prefixLift 6080434
  have htrace : WordTrace (prefixWord ++ tailWord_6080434) baseStart_6080434 baseEnd_6080434 := by
    simpa [prefixWord, tailWord_6080434, baseEnd_6080434] using wordTrace_append hprefix tailTrace_6080434
  have hstable : (prefixWord ++ tailWord_6080434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080434).length < 2 ^ (prefixWord ++ tailWord_6080434).sum := by decide
  have hdescent : baseEnd_6080434 < baseStart_6080434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080537 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_6080537 : Nat := 118140960795 + 6080537 * 2 ^ 59
def prefixEnd_6080537 : Nat := 4983230072969 + 3 ^ 40 * 6080537 * 2
def baseEnd_6080537 : Nat := 3122238118447781604723625

theorem tailTrace_6080537 : CollatzResearch.WordTrace tailWord_6080537 prefixEnd_6080537 3122238118447781604723625 := by
  unfold tailWord_6080537
  simp only [CollatzResearch.WordTrace]
  refine ⟨221775403972260396887647865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147850269314840264591765243 221775403972260396887647865)
  ·
    refine ⟨166331552979195297665735899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221775403972260396887647865 166331552979195297665735899)
    ·
      refine ⟨249497329468792946498603849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166331552979195297665735899 249497329468792946498603849)
      ·
        refine ⟨187122997101594709873952887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249497329468792946498603849 187122997101594709873952887)
        ·
          refine ⟨280684495652392064810929331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187122997101594709873952887 280684495652392064810929331)
          ·
            refine ⟨421026743478588097216393997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280684495652392064810929331 421026743478588097216393997)
            ·
              refine ⟨157885028804470536456147749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421026743478588097216393997 157885028804470536456147749)
              ·
                refine ⟨29603442900838225585527703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157885028804470536456147749 29603442900838225585527703)
                ·
                  refine ⟨44405164351257338378291555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29603442900838225585527703 44405164351257338378291555)
                  ·
                    refine ⟨66607746526886007567437333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44405164351257338378291555 66607746526886007567437333)
                    ·
                      refine ⟨3122238118447781604723625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66607746526886007567437333 3122238118447781604723625)
                      ·
                        rfl

theorem cell23_6080537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_6080537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080537 prefixEnd_6080537 := by exact prefixLift 6080537
  have htrace : WordTrace (prefixWord ++ tailWord_6080537) baseStart_6080537 baseEnd_6080537 := by
    simpa [prefixWord, tailWord_6080537, baseEnd_6080537] using wordTrace_append hprefix tailTrace_6080537
  have hstable : (prefixWord ++ tailWord_6080537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080537).length < 2 ^ (prefixWord ++ tailWord_6080537).sum := by decide
  have hdescent : baseEnd_6080537 < baseStart_6080537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080547 : List Nat := [1, 1, 1, 4, 3, 1, 2, 10]
def baseStart_6080547 : Nat := 118140960795 + 6080547 * 2 ^ 59
def prefixEnd_6080547 : Nat := 4983230072969 + 3 ^ 40 * 6080547 * 2
def baseEnd_6080547 : Nat := 115638639009419502429577

theorem tailTrace_6080547 : CollatzResearch.WordTrace tailWord_6080547 prefixEnd_6080547 115638639009419502429577 := by
  unfold tailWord_6080547
  simp only [CollatzResearch.WordTrace]
  refine ⟨221775768702224168595511895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147850512468149445730341263 221775768702224168595511895)
  ·
    refine ⟨332663653053336252893267843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221775768702224168595511895 332663653053336252893267843)
    ·
      refine ⟨498995479580004379339901765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332663653053336252893267843 498995479580004379339901765)
      ·
        refine ⟨93561652421250821126231581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 498995479580004379339901765 93561652421250821126231581)
        ·
          refine ⟨35085619657969057922336843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93561652421250821126231581 35085619657969057922336843)
          ·
            refine ⟨52628429486953586883505265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35085619657969057922336843 52628429486953586883505265)
            ·
              refine ⟨39471322115215190162628949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52628429486953586883505265 39471322115215190162628949)
              ·
                refine ⟨115638639009419502429577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39471322115215190162628949 115638639009419502429577)
                ·
                  rfl

theorem cell23_6080547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 10].length) (baseStart_6080547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080547 prefixEnd_6080547 := by exact prefixLift 6080547
  have htrace : WordTrace (prefixWord ++ tailWord_6080547) baseStart_6080547 baseEnd_6080547 := by
    simpa [prefixWord, tailWord_6080547, baseEnd_6080547] using wordTrace_append hprefix tailTrace_6080547
  have hstable : (prefixWord ++ tailWord_6080547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080547).length < 2 ^ (prefixWord ++ tailWord_6080547).sum := by decide
  have hdescent : baseEnd_6080547 < baseStart_6080547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080558 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_6080558 : Nat := 118140960795 + 6080558 * 2 ^ 59
def prefixEnd_6080558 : Nat := 4983230072969 + 3 ^ 40 * 6080558 * 2
def baseEnd_6080558 : Nat := 3122248901541526022561029

theorem tailTrace_6080558 : CollatzResearch.WordTrace tailWord_6080558 prefixEnd_6080558 3122248901541526022561029 := by
  unfold tailWord_6080558
  simp only [CollatzResearch.WordTrace]
  refine ⟨27722021238148039684270291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147850779936789544982774885 27722021238148039684270291)
  ·
    refine ⟨41583031857222059526405437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27722021238148039684270291 41583031857222059526405437)
    ·
      refine ⟨15593636946458272322402039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41583031857222059526405437 15593636946458272322402039)
      ·
        refine ⟨23390455419687408483603059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15593636946458272322402039 23390455419687408483603059)
        ·
          refine ⟨35085683129531112725404589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23390455419687408483603059 35085683129531112725404589)
          ·
            refine ⟨13157131173574167272026721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35085683129531112725404589 13157131173574167272026721)
            ·
              refine ⟨9867848380180625454020041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13157131173574167272026721 9867848380180625454020041)
              ·
                refine ⟨7400886285135469090515031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9867848380180625454020041 7400886285135469090515031)
                ·
                  refine ⟨11101329427703203635772547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7400886285135469090515031 11101329427703203635772547)
                  ·
                    refine ⟨16651994141554805453658821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11101329427703203635772547 16651994141554805453658821)
                    ·
                      refine ⟨3122248901541526022561029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16651994141554805453658821 3122248901541526022561029)
                      ·
                        rfl

theorem cell23_6080558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_6080558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080558 prefixEnd_6080558 := by exact prefixLift 6080558
  have htrace : WordTrace (prefixWord ++ tailWord_6080558) baseStart_6080558 baseEnd_6080558 := by
    simpa [prefixWord, tailWord_6080558, baseEnd_6080558] using wordTrace_append hprefix tailTrace_6080558
  have hstable : (prefixWord ++ tailWord_6080558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080558).length < 2 ^ (prefixWord ++ tailWord_6080558).sum := by decide
  have hdescent : baseEnd_6080558 < baseStart_6080558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080561 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 1, 2, 3]
def baseStart_6080561 : Nat := 118140960795 + 6080561 * 2 ^ 59
def prefixEnd_6080561 : Nat := 4983230072969 + 3 ^ 40 * 6080561 * 2
def baseEnd_6080561 : Nat := 3122250441983489510823515

theorem tailTrace_6080561 : CollatzResearch.WordTrace tailWord_6080561 prefixEnd_6080561 3122250441983489510823515 := by
  unfold tailWord_6080561
  simp only [CollatzResearch.WordTrace]
  refine ⟨221776279324173448986521537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147850852882782299324347691 221776279324173448986521537)
  ·
    refine ⟨166332209493130086739891153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221776279324173448986521537 166332209493130086739891153)
    ·
      refine ⟨124749157119847565054918365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166332209493130086739891153 124749157119847565054918365)
      ·
        refine ⟨46780933919942836895594387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124749157119847565054918365 46780933919942836895594387)
        ·
          refine ⟨70171400879914255343391581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46780933919942836895594387 70171400879914255343391581)
          ·
            refine ⟨26314275329967845753771843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70171400879914255343391581 26314275329967845753771843)
            ·
              refine ⟨39471412994951768630657765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26314275329967845753771843 39471412994951768630657765)
              ·
                refine ⟨7400889936553456618248331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39471412994951768630657765 7400889936553456618248331)
                ·
                  refine ⟨11101334904830184927372497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7400889936553456618248331 11101334904830184927372497)
                  ·
                    refine ⟨8326001178622638695529373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11101334904830184927372497 8326001178622638695529373)
                    ·
                      refine ⟨3122250441983489510823515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8326001178622638695529373 3122250441983489510823515)
                      ·
                        rfl

theorem cell23_6080561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_6080561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080561 prefixEnd_6080561 := by exact prefixLift 6080561
  have htrace : WordTrace (prefixWord ++ tailWord_6080561) baseStart_6080561 baseEnd_6080561 := by
    simpa [prefixWord, tailWord_6080561, baseEnd_6080561] using wordTrace_append hprefix tailTrace_6080561
  have hstable : (prefixWord ++ tailWord_6080561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080561).length < 2 ^ (prefixWord ++ tailWord_6080561).sum := by decide
  have hdescent : baseEnd_6080561 < baseStart_6080561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080575 : List Nat := [1, 1, 2, 2, 3, 1, 5, 3, 1, 2, 2]
def baseStart_6080575 : Nat := 118140960795 + 6080575 * 2 ^ 59
def prefixEnd_6080575 : Nat := 4983230072969 + 3 ^ 40 * 6080575 * 2
def baseEnd_6080575 : Nat := 3122257630712652456048451

theorem tailTrace_6080575 : CollatzResearch.WordTrace tailWord_6080575 prefixEnd_6080575 3122257630712652456048451 := by
  unfold tailWord_6080575
  simp only [CollatzResearch.WordTrace]
  refine ⟨221776789946122729377531179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147851193297415152918354119 221776789946122729377531179)
  ·
    refine ⟨332665184919184094066296769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221776789946122729377531179 332665184919184094066296769)
    ·
      refine ⟨249498888689388070549722577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332665184919184094066296769 249498888689388070549722577)
      ·
        refine ⟨187124166517041052912291933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249498888689388070549722577 187124166517041052912291933)
        ·
          refine ⟨70171562443890394842109475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187124166517041052912291933 70171562443890394842109475)
          ·
            refine ⟨105257343665835592263164213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70171562443890394842109475 105257343665835592263164213)
            ·
              refine ⟨9867875968672086774671645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105257343665835592263164213 9867875968672086774671645)
              ·
                refine ⟨3700453488252032540501867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9867875968672086774671645 3700453488252032540501867)
                ·
                  refine ⟨5550680232378048810752801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700453488252032540501867 5550680232378048810752801)
                  ·
                    refine ⟨4163010174283536608064601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5550680232378048810752801 4163010174283536608064601)
                    ·
                      refine ⟨3122257630712652456048451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163010174283536608064601 3122257630712652456048451)
                      ·
                        rfl

theorem cell23_6080575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 1, 2, 2].length) (baseStart_6080575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080575 prefixEnd_6080575 := by exact prefixLift 6080575
  have htrace : WordTrace (prefixWord ++ tailWord_6080575) baseStart_6080575 baseEnd_6080575 := by
    simpa [prefixWord, tailWord_6080575, baseEnd_6080575] using wordTrace_append hprefix tailTrace_6080575
  have hstable : (prefixWord ++ tailWord_6080575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080575).length < 2 ^ (prefixWord ++ tailWord_6080575).sum := by decide
  have hdescent : baseEnd_6080575 < baseStart_6080575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080598 : List Nat := [5, 2, 2, 1, 1, 2, 2, 8]
def baseStart_6080598 : Nat := 118140960795 + 6080598 * 2 ^ 59
def prefixEnd_6080598 : Nat := 4983230072969 + 3 ^ 40 * 6080598 * 2
def baseEnd_6080598 : Nat := 115639608917322439483735

theorem tailTrace_6080598 : CollatzResearch.WordTrace tailWord_6080598 prefixEnd_6080598 115639608917322439483735 := by
  unfold tailWord_6080598
  simp only [CollatzResearch.WordTrace]
  refine ⟨13861101801564962769101153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147851752550026269537078965 13861101801564962769101153)
  ·
    refine ⟨10395826351173722076825865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13861101801564962769101153 10395826351173722076825865)
    ·
      refine ⟨7796869763380291557619399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10395826351173722076825865 7796869763380291557619399)
      ·
        refine ⟨11695304645070437336429099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7796869763380291557619399 11695304645070437336429099)
        ·
          refine ⟨17542956967605656004643649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11695304645070437336429099 17542956967605656004643649)
          ·
            refine ⟨13157217725704242003482737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17542956967605656004643649 13157217725704242003482737)
            ·
              refine ⟨9867913294278181502612053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13157217725704242003482737 9867913294278181502612053)
              ·
                refine ⟨115639608917322439483735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9867913294278181502612053 115639608917322439483735)
                ·
                  rfl

theorem cell23_6080598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_6080598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080598 prefixEnd_6080598 := by exact prefixLift 6080598
  have htrace : WordTrace (prefixWord ++ tailWord_6080598) baseStart_6080598 baseEnd_6080598 := by
    simpa [prefixWord, tailWord_6080598, baseEnd_6080598] using wordTrace_append hprefix tailTrace_6080598
  have hstable : (prefixWord ++ tailWord_6080598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080598).length < 2 ^ (prefixWord ++ tailWord_6080598).sum := by decide
  have hdescent : baseEnd_6080598 < baseStart_6080598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080601 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 3, 3, 2]
def baseStart_6080601 : Nat := 118140960795 + 6080601 * 2 ^ 59
def prefixEnd_6080601 : Nat := 4983230072969 + 3 ^ 40 * 6080601 * 2
def baseEnd_6080601 : Nat := 3122270981209669354323331

theorem tailTrace_6080601 : CollatzResearch.WordTrace tailWord_6080601 prefixEnd_6080601 3122270981209669354323331 := by
  unfold tailWord_6080601
  simp only [CollatzResearch.WordTrace]
  refine ⟨221777738244028535817977657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147851825496019023878651771 221777738244028535817977657)
  ·
    refine ⟨166333303683021401863483243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221777738244028535817977657 166333303683021401863483243)
    ·
      refine ⟨249499955524532102795224865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166333303683021401863483243 249499955524532102795224865)
      ·
        refine ⟨187124966643399077096418649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249499955524532102795224865 187124966643399077096418649)
        ·
          refine ⟨140343724982549307822313987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187124966643399077096418649 140343724982549307822313987)
          ·
            refine ⟨210515587473823961733470981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140343724982549307822313987 210515587473823961733470981)
            ·
              refine ⟨39471672651341992825025809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210515587473823961733470981 39471672651341992825025809)
              ·
                refine ⟨29603754488506494618769357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39471672651341992825025809 29603754488506494618769357)
                ·
                  refine ⟨11101407933189935482038509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29603754488506494618769357 11101407933189935482038509)
                  ·
                    refine ⟨4163027974946225805764441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11101407933189935482038509 4163027974946225805764441)
                    ·
                      refine ⟨3122270981209669354323331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163027974946225805764441 3122270981209669354323331)
                      ·
                        rfl

theorem cell23_6080601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_6080601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080601 prefixEnd_6080601 := by exact prefixLift 6080601
  have htrace : WordTrace (prefixWord ++ tailWord_6080601) baseStart_6080601 baseEnd_6080601 := by
    simpa [prefixWord, tailWord_6080601, baseEnd_6080601] using wordTrace_append hprefix tailTrace_6080601
  have hstable : (prefixWord ++ tailWord_6080601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080601).length < 2 ^ (prefixWord ++ tailWord_6080601).sum := by decide
  have hdescent : baseEnd_6080601 < baseStart_6080601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080608 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 2, 1, 3]
def baseStart_6080608 : Nat := 118140960795 + 6080608 * 2 ^ 59
def prefixEnd_6080608 : Nat := 4983230072969 + 3 ^ 40 * 6080608 * 2
def baseEnd_6080608 : Nat := 3122274575574250826935799

theorem tailTrace_6080608 : CollatzResearch.WordTrace tailWord_6080608 prefixEnd_6080608 3122274575574250826935799 := by
  unfold tailWord_6080608
  simp only [CollatzResearch.WordTrace]
  refine ⟨110888996777501588006741239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147851995703335450675654985 110888996777501588006741239)
  ·
    refine ⟨166333495166252382010111859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110888996777501588006741239 166333495166252382010111859)
    ·
      refine ⟨249500242749378573015167789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166333495166252382010111859 249500242749378573015167789)
      ·
        refine ⟨93562591031016964880687921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249500242749378573015167789 93562591031016964880687921)
        ·
          refine ⟨70171943273262723660515941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93562591031016964880687921 70171943273262723660515941)
          ·
            refine ⟨13157239363736760686346739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70171943273262723660515941 13157239363736760686346739)
            ·
              refine ⟨19735859045605141029520109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13157239363736760686346739 19735859045605141029520109)
              ·
                refine ⟨7400947142101927886070041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19735859045605141029520109 7400947142101927886070041)
                ·
                  refine ⟨5550710356576445914552531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7400947142101927886070041 5550710356576445914552531)
                  ·
                    refine ⟨8326065534864668871828797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5550710356576445914552531 8326065534864668871828797)
                    ·
                      refine ⟨3122274575574250826935799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8326065534864668871828797 3122274575574250826935799)
                      ·
                        rfl

theorem cell23_6080608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_6080608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080608 prefixEnd_6080608 := by exact prefixLift 6080608
  have htrace : WordTrace (prefixWord ++ tailWord_6080608) baseStart_6080608 baseEnd_6080608 := by
    simpa [prefixWord, tailWord_6080608, baseEnd_6080608] using wordTrace_append hprefix tailTrace_6080608
  have hstable : (prefixWord ++ tailWord_6080608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080608).length < 2 ^ (prefixWord ++ tailWord_6080608).sum := by decide
  have hdescent : baseEnd_6080608 < baseStart_6080608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080631 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 3, 4, 2]
def baseStart_6080631 : Nat := 118140960795 + 6080631 * 2 ^ 59
def prefixEnd_6080631 : Nat := 4983230072969 + 3 ^ 40 * 6080631 * 2
def baseEnd_6080631 : Nat := 3122286385629304236948193

theorem tailTrace_6080631 : CollatzResearch.WordTrace tailWord_6080631 prefixEnd_6080631 3122286385629304236948193 := by
  unfold tailWord_6080631
  simp only [CollatzResearch.WordTrace]
  refine ⟨221778832433919850941569747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147852554955946567294379831 221778832433919850941569747)
  ·
    refine ⟨332668248650879776412354621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221778832433919850941569747 332668248650879776412354621)
    ·
      refine ⟨124750593244079916154632983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332668248650879776412354621 124750593244079916154632983)
      ·
        refine ⟨187125889866119874231949475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124750593244079916154632983 187125889866119874231949475)
        ·
          refine ⟨280688834799179811347924213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187125889866119874231949475 280688834799179811347924213)
          ·
            refine ⟨26314578262423107313867895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 280688834799179811347924213 26314578262423107313867895)
            ·
              refine ⟨39471867393634660970801843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26314578262423107313867895 39471867393634660970801843)
              ·
                refine ⟨59207801090451991456202765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39471867393634660970801843 59207801090451991456202765)
                ·
                  refine ⟨22202925408919496796076037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59207801090451991456202765 22202925408919496796076037)
                  ·
                    refine ⟨4163048514172405649264257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22202925408919496796076037 4163048514172405649264257)
                    ·
                      refine ⟨3122286385629304236948193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163048514172405649264257 3122286385629304236948193)
                      ·
                        rfl

theorem cell23_6080631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_6080631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080631 prefixEnd_6080631 := by exact prefixLift 6080631
  have htrace : WordTrace (prefixWord ++ tailWord_6080631) baseStart_6080631 baseEnd_6080631 := by
    simpa [prefixWord, tailWord_6080631, baseEnd_6080631] using wordTrace_append hprefix tailTrace_6080631
  have hstable : (prefixWord ++ tailWord_6080631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080631).length < 2 ^ (prefixWord ++ tailWord_6080631).sum := by decide
  have hdescent : baseEnd_6080631 < baseStart_6080631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080634 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3]
def baseStart_6080634 : Nat := 118140960795 + 6080634 * 2 ^ 59
def prefixEnd_6080634 : Nat := 4983230072969 + 3 ^ 40 * 6080634 * 2
def baseEnd_6080634 : Nat := 3122287926071267725210679

theorem tailTrace_6080634 : CollatzResearch.WordTrace tailWord_6080634 prefixEnd_6080634 3122287926071267725210679 := by
  unfold tailWord_6080634
  simp only [CollatzResearch.WordTrace]
  refine ⟨55444735463227245613482239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147852627901939321635952637 55444735463227245613482239)
  ·
    refine ⟨83167103194840868420223359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55444735463227245613482239 83167103194840868420223359)
    ·
      refine ⟨124750654792261302630335039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83167103194840868420223359 124750654792261302630335039)
      ·
        refine ⟨187125982188391953945502559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124750654792261302630335039 187125982188391953945502559)
        ·
          refine ⟨280688973282587930918253839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187125982188391953945502559 280688973282587930918253839)
          ·
            refine ⟨421033459923881896377380759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280688973282587930918253839 421033459923881896377380759)
            ·
              refine ⟨631550189885822844566071139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421033459923881896377380759 631550189885822844566071139)
              ·
                refine ⟨947325284828734266849106709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631550189885822844566071139 947325284828734266849106709)
                ·
                  refine ⟨44405872726346918758551877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 947325284828734266849106709 44405872726346918758551877)
                  ·
                    refine ⟨8326101136190047267228477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44405872726346918758551877 8326101136190047267228477)
                    ·
                      refine ⟨3122287926071267725210679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8326101136190047267228477 3122287926071267725210679)
                      ·
                        rfl

theorem cell23_6080634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_6080634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080634 prefixEnd_6080634 := by exact prefixLift 6080634
  have htrace : WordTrace (prefixWord ++ tailWord_6080634) baseStart_6080634 baseEnd_6080634 := by
    simpa [prefixWord, tailWord_6080634, baseEnd_6080634] using wordTrace_append hprefix tailTrace_6080634
  have hstable : (prefixWord ++ tailWord_6080634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080634).length < 2 ^ (prefixWord ++ tailWord_6080634).sum := by decide
  have hdescent : baseEnd_6080634 < baseStart_6080634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080671 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 7]
def baseStart_6080671 : Nat := 118140960795 + 6080671 * 2 ^ 59
def prefixEnd_6080671 : Nat := 4983230072969 + 3 ^ 40 * 6080671 * 2
def baseEnd_6080671 : Nat := 346922991650609342272001

theorem tailTrace_6080671 : CollatzResearch.WordTrace tailWord_6080671 prefixEnd_6080671 346922991650609342272001 := by
  unfold tailWord_6080671
  simp only [CollatzResearch.WordTrace]
  refine ⟨221780291353774937773025867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147853527569183291848683911 221780291353774937773025867)
  ·
    refine ⟨332670437030662406659538801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221780291353774937773025867 332670437030662406659538801)
    ·
      refine ⟨249502827772996804994654101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332670437030662406659538801 249502827772996804994654101)
      ·
        refine ⟨11695445051859225234124411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 249502827772996804994654101 11695445051859225234124411)
        ·
          refine ⟨17543167577788837851186617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11695445051859225234124411 17543167577788837851186617)
          ·
            refine ⟨13157375683341628388389963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17543167577788837851186617 13157375683341628388389963)
            ·
              refine ⟨19736063525012442582584945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13157375683341628388389963 19736063525012442582584945)
              ·
                refine ⟨14802047643759331936938709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19736063525012442582584945 14802047643759331936938709)
                ·
                  refine ⟨346922991650609342272001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14802047643759331936938709 346922991650609342272001)
                  ·
                    rfl

theorem cell23_6080671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 7].length) (baseStart_6080671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080671 prefixEnd_6080671 := by exact prefixLift 6080671
  have htrace : WordTrace (prefixWord ++ tailWord_6080671) baseStart_6080671 baseEnd_6080671 := by
    simpa [prefixWord, tailWord_6080671, baseEnd_6080671] using wordTrace_append hprefix tailTrace_6080671
  have hstable : (prefixWord ++ tailWord_6080671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080671).length < 2 ^ (prefixWord ++ tailWord_6080671).sum := by decide
  have hdescent : baseEnd_6080671 < baseStart_6080671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080686 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6080686 : Nat := 118140960795 + 6080686 * 2 ^ 59
def prefixEnd_6080686 : Nat := 4983230072969 + 3 ^ 40 * 6080686 * 2
def baseEnd_6080686 : Nat := 3122314627065301521760441

theorem tailTrace_6080686 : CollatzResearch.WordTrace tailWord_6080686 prefixEnd_6080686 3122314627065301521760441 := by
  unfold tailWord_6080686
  simp only [CollatzResearch.WordTrace]
  refine ⟨27722604806090074416852739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147853892299147063556547941 27722604806090074416852739)
  ·
    refine ⟨41583907209135111625279109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27722604806090074416852739 41583907209135111625279109)
    ·
      refine ⟨7796982601712833429739833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41583907209135111625279109 7796982601712833429739833)
      ·
        refine ⟨5847736951284625072304875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7796982601712833429739833 5847736951284625072304875)
        ·
          refine ⟨8771605426926937608457313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5847736951284625072304875 8771605426926937608457313)
          ·
            refine ⟨6578704070195203206342985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8771605426926937608457313 6578704070195203206342985)
            ·
              refine ⟨4934028052646402404757239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6578704070195203206342985 4934028052646402404757239)
              ·
                refine ⟨7401042078969603607135859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4934028052646402404757239 7401042078969603607135859)
                ·
                  refine ⟨11101563118454405410703789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7401042078969603607135859 11101563118454405410703789)
                  ·
                    refine ⟨4163086169420402029013921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11101563118454405410703789 4163086169420402029013921)
                    ·
                      refine ⟨3122314627065301521760441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163086169420402029013921 3122314627065301521760441)
                      ·
                        rfl

theorem cell23_6080686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6080686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080686 prefixEnd_6080686 := by exact prefixLift 6080686
  have htrace : WordTrace (prefixWord ++ tailWord_6080686) baseStart_6080686 baseEnd_6080686 := by
    simpa [prefixWord, tailWord_6080686, baseEnd_6080686] using wordTrace_append hprefix tailTrace_6080686
  have hstable : (prefixWord ++ tailWord_6080686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080686).length < 2 ^ (prefixWord ++ tailWord_6080686).sum := by decide
  have hdescent : baseEnd_6080686 < baseStart_6080686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080758 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_6080758 : Nat := 118140960795 + 6080758 * 2 ^ 59
def prefixEnd_6080758 : Nat := 4983230072969 + 3 ^ 40 * 6080758 * 2
def baseEnd_6080758 : Nat := 3122351597672425240060109

theorem tailTrace_6080758 : CollatzResearch.WordTrace tailWord_6080758 prefixEnd_6080758 3122351597672425240060109 := by
  unfold tailWord_6080758
  simp only [CollatzResearch.WordTrace]
  refine ⟨13861466531528734476965183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147855643002973167754295285 13861466531528734476965183)
  ·
    refine ⟨20792199797293101715447775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13861466531528734476965183 20792199797293101715447775)
    ·
      refine ⟨31188299695939652573171663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20792199797293101715447775 31188299695939652573171663)
      ·
        refine ⟨46782449543909478859757495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31188299695939652573171663 46782449543909478859757495)
        ·
          refine ⟨70173674315864218289636243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46782449543909478859757495 70173674315864218289636243)
          ·
            refine ⟨105260511473796327434454365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70173674315864218289636243 105260511473796327434454365)
            ·
              refine ⟨39472691802673622787920387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105260511473796327434454365 39472691802673622787920387)
              ·
                refine ⟨59209037704010434181880581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39472691802673622787920387 59209037704010434181880581)
                ·
                  refine ⟨11101694569501956409102609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59209037704010434181880581 11101694569501956409102609)
                  ·
                    refine ⟨8326270927126467306826957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11101694569501956409102609 8326270927126467306826957)
                    ·
                      refine ⟨3122351597672425240060109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8326270927126467306826957 3122351597672425240060109)
                      ·
                        rfl

theorem cell23_6080758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_6080758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080758 prefixEnd_6080758 := by exact prefixLift 6080758
  have htrace : WordTrace (prefixWord ++ tailWord_6080758) baseStart_6080758 baseEnd_6080758 := by
    simpa [prefixWord, tailWord_6080758, baseEnd_6080758] using wordTrace_append hprefix tailTrace_6080758
  have hstable : (prefixWord ++ tailWord_6080758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080758).length < 2 ^ (prefixWord ++ tailWord_6080758).sum := by decide
  have hdescent : baseEnd_6080758 < baseStart_6080758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080778 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 6]
def baseStart_6080778 : Nat := 118140960795 + 6080778 * 2 ^ 59
def prefixEnd_6080778 : Nat := 4983230072969 + 3 ^ 40 * 6080778 * 2
def baseEnd_6080778 : Nat := 346929096365057240201113

theorem tailTrace_6080778 : CollatzResearch.WordTrace tailWord_6080778 prefixEnd_6080778 346929096365057240201113 := by
  unfold tailWord_6080778
  simp only [CollatzResearch.WordTrace]
  refine ⟨55446048491096823761792747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147856129309591530031447325 55446048491096823761792747)
  ·
    refine ⟨83169072736645235642689121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55446048491096823761792747 83169072736645235642689121)
    ·
      refine ⟨62376804552483926732016841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83169072736645235642689121 62376804552483926732016841)
      ·
        refine ⟨46782603414362945049012631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62376804552483926732016841 46782603414362945049012631)
        ·
          refine ⟨70173905121544417573518947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46782603414362945049012631 70173905121544417573518947)
          ·
            refine ⟨105260857682316626360278421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70173905121544417573518947 105260857682316626360278421)
            ·
              refine ⟨4934102703858591860638051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105260857682316626360278421 4934102703858591860638051)
              ·
                refine ⟨7401154055787887790957077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4934102703858591860638051 7401154055787887790957077)
                ·
                  refine ⟨346929096365057240201113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7401154055787887790957077 346929096365057240201113)
                  ·
                    rfl

theorem cell23_6080778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_6080778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080778 prefixEnd_6080778 := by exact prefixLift 6080778
  have htrace : WordTrace (prefixWord ++ tailWord_6080778) baseStart_6080778 baseEnd_6080778 := by
    simpa [prefixWord, tailWord_6080778, baseEnd_6080778] using wordTrace_append hprefix tailTrace_6080778
  have hstable : (prefixWord ++ tailWord_6080778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080778).length < 2 ^ (prefixWord ++ tailWord_6080778).sum := by decide
  have hdescent : baseEnd_6080778 < baseStart_6080778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080821 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_6080821 : Nat := 118140960795 + 6080821 * 2 ^ 59
def prefixEnd_6080821 : Nat := 4983230072969 + 3 ^ 40 * 6080821 * 2
def baseEnd_6080821 : Nat := 1040794648984552831190773

theorem tailTrace_6080821 : CollatzResearch.WordTrace tailWord_6080821 prefixEnd_6080821 1040794648984552831190773 := by
  unfold tailWord_6080821
  simp only [CollatzResearch.WordTrace]
  refine ⟨221785762303231513390986317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147857174868821008927324211 221785762303231513390986317)
  ·
    refine ⟨83169660863711817521619869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221785762303231513390986317 83169660863711817521619869)
    ·
      refine ⟨31188622823891931570607451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83169660863711817521619869 31188622823891931570607451)
      ·
        refine ⟨46782934235837897355911177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31188622823891931570607451 46782934235837897355911177)
        ·
          refine ⟨35087200676878423016933383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46782934235837897355911177 35087200676878423016933383)
          ·
            refine ⟨52630801015317634525400075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35087200676878423016933383 52630801015317634525400075)
            ·
              refine ⟨78946201522976451788100113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52630801015317634525400075 78946201522976451788100113)
              ·
                refine ⟨59209651142232338841075085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78946201522976451788100113 59209651142232338841075085)
                ·
                  refine ⟨22203619178337127065403157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59209651142232338841075085 22203619178337127065403157)
                  ·
                    refine ⟨1040794648984552831190773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22203619178337127065403157 1040794648984552831190773)
                    ·
                      rfl

theorem cell23_6080821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_6080821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080821 prefixEnd_6080821 := by exact prefixLift 6080821
  have htrace : WordTrace (prefixWord ++ tailWord_6080821) baseStart_6080821 baseEnd_6080821 := by
    simpa [prefixWord, tailWord_6080821, baseEnd_6080821] using wordTrace_append hprefix tailTrace_6080821
  have hstable : (prefixWord ++ tailWord_6080821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080821).length < 2 ^ (prefixWord ++ tailWord_6080821).sum := by decide
  have hdescent : baseEnd_6080821 < baseStart_6080821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080831 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_6080831 : Nat := 118140960795 + 6080831 * 2 ^ 59
def prefixEnd_6080831 : Nat := 4983230072969 + 3 ^ 40 * 6080831 * 2
def baseEnd_6080831 : Nat := 3122389081760203454447273

theorem tailTrace_6080831 : CollatzResearch.WordTrace tailWord_6080831 prefixEnd_6080831 3122389081760203454447273 := by
  unfold tailWord_6080831
  simp only [CollatzResearch.WordTrace]
  refine ⟨221786127033195285098850347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147857418022130190065900231 221786127033195285098850347)
  ·
    refine ⟨332679190549792927648275521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221786127033195285098850347 332679190549792927648275521)
    ·
      refine ⟨249509392912344695736206641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332679190549792927648275521 249509392912344695736206641)
      ·
        refine ⟨187132044684258521802154981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249509392912344695736206641 187132044684258521802154981)
        ·
          refine ⟨35087258378298472837904059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187132044684258521802154981 35087258378298472837904059)
          ·
            refine ⟨52630887567447709256856089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35087258378298472837904059 52630887567447709256856089)
            ·
              refine ⟨39473165675585781942642067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52630887567447709256856089 39473165675585781942642067)
              ·
                refine ⟨59209748513378672913963101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39473165675585781942642067 59209748513378672913963101)
                ·
                  refine ⟨22203655692517002342736163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59209748513378672913963101 22203655692517002342736163)
                  ·
                    refine ⟨33305483538775503514104245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22203655692517002342736163 33305483538775503514104245)
                    ·
                      refine ⟨3122389081760203454447273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33305483538775503514104245 3122389081760203454447273)
                      ·
                        rfl

theorem cell23_6080831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_6080831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080831 prefixEnd_6080831 := by exact prefixLift 6080831
  have htrace : WordTrace (prefixWord ++ tailWord_6080831) baseStart_6080831 baseEnd_6080831 := by
    simpa [prefixWord, tailWord_6080831, baseEnd_6080831] using wordTrace_append hprefix tailTrace_6080831
  have hstable : (prefixWord ++ tailWord_6080831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080831).length < 2 ^ (prefixWord ++ tailWord_6080831).sum := by decide
  have hdescent : baseEnd_6080831 < baseStart_6080831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080848 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 3]
def baseStart_6080848 : Nat := 118140960795 + 6080848 * 2 ^ 59
def prefixEnd_6080848 : Nat := 4983230072969 + 3 ^ 40 * 6080848 * 2
def baseEnd_6080848 : Nat := 3122397810931329887934695

theorem tailTrace_6080848 : CollatzResearch.WordTrace tailWord_6080848 prefixEnd_6080848 3122397810931329887934695 := by
  unfold tailWord_6080848
  simp only [CollatzResearch.WordTrace]
  refine ⟨110893373537066848501109599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147857831382755798001479465 110893373537066848501109599)
  ·
    refine ⟨166340060305600272751664399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110893373537066848501109599 166340060305600272751664399)
    ·
      refine ⟨249510090458400409127496599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166340060305600272751664399 249510090458400409127496599)
      ·
        refine ⟨374265135687600613691244899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249510090458400409127496599 374265135687600613691244899)
        ·
          refine ⟨561397703531400920536867349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374265135687600613691244899 561397703531400920536867349)
          ·
            refine ⟨26315517353034418150165657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 561397703531400920536867349 26315517353034418150165657)
            ·
              refine ⟨19736638014775813612624243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26315517353034418150165657 19736638014775813612624243)
              ·
                refine ⟨29604957022163720418936365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19736638014775813612624243 29604957022163720418936365)
                ·
                  refine ⟨11101858883311395157101137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29604957022163720418936365 11101858883311395157101137)
                  ·
                    refine ⟨8326394162483546367825853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11101858883311395157101137 8326394162483546367825853)
                    ·
                      refine ⟨3122397810931329887934695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8326394162483546367825853 3122397810931329887934695)
                      ·
                        rfl

theorem cell23_6080848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 3].length) (baseStart_6080848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080848 prefixEnd_6080848 := by exact prefixLift 6080848
  have htrace : WordTrace (prefixWord ++ tailWord_6080848) baseStart_6080848 baseEnd_6080848 := by
    simpa [prefixWord, tailWord_6080848, baseEnd_6080848] using wordTrace_append hprefix tailTrace_6080848
  have hstable : (prefixWord ++ tailWord_6080848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080848).length < 2 ^ (prefixWord ++ tailWord_6080848).sum := by decide
  have hdescent : baseEnd_6080848 < baseStart_6080848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080872 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 2, 4]
def baseStart_6080872 : Nat := 118140960795 + 6080872 * 2 ^ 59
def prefixEnd_6080872 : Nat := 4983230072969 + 3 ^ 40 * 6080872 * 2
def baseEnd_6080872 : Nat := 1040803378155679264678195

theorem tailTrace_6080872 : CollatzResearch.WordTrace tailWord_6080872 prefixEnd_6080872 1040803378155679264678195 := by
  unfold tailWord_6080872
  simp only [CollatzResearch.WordTrace]
  refine ⟨110893811213023374550546435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147858414950697832734061913 110893811213023374550546435)
  ·
    refine ⟨166340716819535061825819653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110893811213023374550546435 166340716819535061825819653)
    ·
      refine ⟨31188884403662824092341185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166340716819535061825819653 31188884403662824092341185)
      ·
        refine ⟨23391663302747118069255889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31188884403662824092341185 23391663302747118069255889)
        ·
          refine ⟨17543747477060338551941917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23391663302747118069255889 17543747477060338551941917)
          ·
            refine ⟨6578905303897626956978219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17543747477060338551941917 6578905303897626956978219)
            ·
              refine ⟨9868357955846440435467329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6578905303897626956978219 9868357955846440435467329)
              ·
                refine ⟨7401268466884830326600497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9868357955846440435467329 7401268466884830326600497)
                ·
                  refine ⟨5550951350163622744950373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7401268466884830326600497 5550951350163622744950373)
                  ·
                    refine ⟨1040803378155679264678195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5550951350163622744950373 1040803378155679264678195)
                    ·
                      rfl

theorem cell23_6080872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_6080872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080872 prefixEnd_6080872 := by exact prefixLift 6080872
  have htrace : WordTrace (prefixWord ++ tailWord_6080872) baseStart_6080872 baseEnd_6080872 := by
    simpa [prefixWord, tailWord_6080872, baseEnd_6080872] using wordTrace_append hprefix tailTrace_6080872
  have hstable : (prefixWord ++ tailWord_6080872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080872).length < 2 ^ (prefixWord ++ tailWord_6080872).sum := by decide
  have hdescent : baseEnd_6080872 < baseStart_6080872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080922 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2]
def baseStart_6080922 : Nat := 118140960795 + 6080922 * 2 ^ 59
def prefixEnd_6080922 : Nat := 4983230072969 + 3 ^ 40 * 6080922 * 2
def baseEnd_6080922 : Nat := 3122435808499762598409355

theorem tailTrace_6080922 : CollatzResearch.WordTrace tailWord_6080922 prefixEnd_6080922 3122435808499762598409355 := by
  unfold tailWord_6080922
  simp only [CollatzResearch.WordTrace]
  refine ⟨55447361518966401910103255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147859630717243738426942013 55447361518966401910103255)
  ·
    refine ⟨83171042278449602865154883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55447361518966401910103255 83171042278449602865154883)
    ·
      refine ⟨124756563417674404297732325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83171042278449602865154883 124756563417674404297732325)
      ·
        refine ⟨23391855640813950805824811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124756563417674404297732325 23391855640813950805824811)
        ·
          refine ⟨35087783461220926208737217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23391855640813950805824811 35087783461220926208737217)
          ·
            refine ⟨26315837595915694656552913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35087783461220926208737217 26315837595915694656552913)
            ·
              refine ⟨19736878196936770992414685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26315837595915694656552913 19736878196936770992414685)
              ·
                refine ⟨7401329323851289122155507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19736878196936770992414685 7401329323851289122155507)
                ·
                  refine ⟨11101993985776933683233261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7401329323851289122155507 11101993985776933683233261)
                  ·
                    refine ⟨4163247744666350131212473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11101993985776933683233261 4163247744666350131212473)
                    ·
                      refine ⟨3122435808499762598409355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163247744666350131212473 3122435808499762598409355)
                      ·
                        rfl

theorem cell23_6080922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_6080922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080922 prefixEnd_6080922 := by exact prefixLift 6080922
  have htrace : WordTrace (prefixWord ++ tailWord_6080922) baseStart_6080922 baseEnd_6080922 := by
    simpa [prefixWord, tailWord_6080922, baseEnd_6080922] using wordTrace_append hprefix tailTrace_6080922
  have hstable : (prefixWord ++ tailWord_6080922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080922).length < 2 ^ (prefixWord ++ tailWord_6080922).sum := by decide
  have hdescent : baseEnd_6080922 < baseStart_6080922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6080958 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_6080958 : Nat := 118140960795 + 6080958 * 2 ^ 59
def prefixEnd_6080958 : Nat := 4983230072969 + 3 ^ 40 * 6080958 * 2
def baseEnd_6080958 : Nat := 346939365978147161951021

theorem tailTrace_6080958 : CollatzResearch.WordTrace tailWord_6080958 prefixEnd_6080958 346939365978147161951021 := by
  unfold tailWord_6080958
  simp only [CollatzResearch.WordTrace]
  refine ⟨27723844887966898223590441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147860506069156790525815685 27723844887966898223590441)
  ·
    refine ⟨20792883665975173667692831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27723844887966898223590441 20792883665975173667692831)
    ·
      refine ⟨31189325498962760501539247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20792883665975173667692831 31189325498962760501539247)
      ·
        refine ⟨46783988248444140752308871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31189325498962760501539247 46783988248444140752308871)
        ·
          refine ⟨70175982372666211128463307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46783988248444140752308871 70175982372666211128463307)
          ·
            refine ⟨105263973558999316692694961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70175982372666211128463307 105263973558999316692694961)
            ·
              refine ⟨78947980169249487519521221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105263973558999316692694961 78947980169249487519521221)
              ·
                refine ⟨14802746281734278909910229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78947980169249487519521221 14802746281734278909910229)
                ·
                  refine ⟨346939365978147161951021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14802746281734278909910229 346939365978147161951021)
                  ·
                    rfl

theorem cell23_6080958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_6080958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6080958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6080958 prefixEnd_6080958 := by exact prefixLift 6080958
  have htrace : WordTrace (prefixWord ++ tailWord_6080958) baseStart_6080958 baseEnd_6080958 := by
    simpa [prefixWord, tailWord_6080958, baseEnd_6080958] using wordTrace_append hprefix tailTrace_6080958
  have hstable : (prefixWord ++ tailWord_6080958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6080958).length < 2 ^ (prefixWord ++ tailWord_6080958).sum := by decide
  have hdescent : baseEnd_6080958 < baseStart_6080958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6080958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081008 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_6081008 : Nat := 118140960795 + 6081008 * 2 ^ 59
def prefixEnd_6081008 : Nat := 4983230072969 + 3 ^ 40 * 6081008 * 2
def baseEnd_6081008 : Nat := 3122479967836049261933959

theorem tailTrace_6081008 : CollatzResearch.WordTrace tailWord_6081008 prefixEnd_6081008 3122479967836049261933959 := by
  unfold tailWord_6081008
  simp only [CollatzResearch.WordTrace]
  refine ⟨110896291376777022164021839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147861721835702696218695785 110896291376777022164021839)
  ·
    refine ⟨166344437065165533246032759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110896291376777022164021839 166344437065165533246032759)
    ·
      refine ⟨249516655597748299869049139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166344437065165533246032759 249516655597748299869049139)
      ·
        refine ⟨374274983396622449803573709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249516655597748299869049139 374274983396622449803573709)
        ·
          refine ⟨140353118773733418676340141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374274983396622449803573709 140353118773733418676340141)
          ·
            refine ⟨52632419540150032003627553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140353118773733418676340141 52632419540150032003627553)
            ·
              refine ⟨39474314655112524002720665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52632419540150032003627553 39474314655112524002720665)
              ·
                refine ⟨29605735991334393002040499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39474314655112524002720665 29605735991334393002040499)
                ·
                  refine ⟨44408603987001589503060749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29605735991334393002040499 44408603987001589503060749)
                  ·
                    refine ⟨16653226495125596063647781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44408603987001589503060749 16653226495125596063647781)
                    ·
                      refine ⟨3122479967836049261933959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16653226495125596063647781 3122479967836049261933959)
                      ·
                        rfl

theorem cell23_6081008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_6081008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081008 prefixEnd_6081008 := by exact prefixLift 6081008
  have htrace : WordTrace (prefixWord ++ tailWord_6081008) baseStart_6081008 baseEnd_6081008 := by
    simpa [prefixWord, tailWord_6081008, baseEnd_6081008] using wordTrace_append hprefix tailTrace_6081008
  have hstable : (prefixWord ++ tailWord_6081008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081008).length < 2 ^ (prefixWord ++ tailWord_6081008).sum := by decide
  have hdescent : baseEnd_6081008 < baseStart_6081008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081025 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_6081025 : Nat := 118140960795 + 6081025 * 2 ^ 59
def prefixEnd_6081025 : Nat := 4983230072969 + 3 ^ 40 * 6081025 * 2
def baseEnd_6081025 : Nat := 3122488697007175695421381

theorem tailTrace_6081025 : CollatzResearch.WordTrace tailWord_6081025 prefixEnd_6081025 3122488697007175695421381 := by
  unfold tailWord_6081025
  simp only [CollatzResearch.WordTrace]
  refine ⟨221793202794492456231412529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147862135196328304154275019 221793202794492456231412529)
  ·
    refine ⟨166344902095869342173559397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221793202794492456231412529 166344902095869342173559397)
    ·
      refine ⟨31189669142975501657542387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166344902095869342173559397 31189669142975501657542387)
      ·
        refine ⟨46784503714463252486313581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31189669142975501657542387 46784503714463252486313581)
        ·
          refine ⟨17544188892923719682367593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46784503714463252486313581 17544188892923719682367593)
          ·
            refine ⟨13158141669692789761775695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17544188892923719682367593 13158141669692789761775695)
            ·
              refine ⟨19737212504539184642663543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13158141669692789761775695 19737212504539184642663543)
              ·
                refine ⟨29605818756808776963995315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19737212504539184642663543 29605818756808776963995315)
                ·
                  refine ⟨44408728135213165445992973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29605818756808776963995315 44408728135213165445992973)
                  ·
                    refine ⟨16653273050704937042247365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44408728135213165445992973 16653273050704937042247365)
                    ·
                      refine ⟨3122488697007175695421381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16653273050704937042247365 3122488697007175695421381)
                      ·
                        rfl

theorem cell23_6081025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_6081025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081025 prefixEnd_6081025 := by exact prefixLift 6081025
  have htrace : WordTrace (prefixWord ++ tailWord_6081025) baseStart_6081025 baseEnd_6081025 := by
    simpa [prefixWord, tailWord_6081025, baseEnd_6081025] using wordTrace_append hprefix tailTrace_6081025
  have hstable : (prefixWord ++ tailWord_6081025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081025).length < 2 ^ (prefixWord ++ tailWord_6081025).sum := by decide
  have hdescent : baseEnd_6081025 < baseStart_6081025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081045 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_6081045 : Nat := 118140960795 + 6081045 * 2 ^ 59
def prefixEnd_6081045 : Nat := 4983230072969 + 3 ^ 40 * 6081045 * 2
def baseEnd_6081045 : Nat := 3122498966620265617171289

theorem tailTrace_6081045 : CollatzResearch.WordTrace tailWord_6081045 prefixEnd_6081045 3122498966620265617171289 := by
  unfold tailWord_6081045
  simp only [CollatzResearch.WordTrace]
  refine ⟨221793932254419999647140589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147862621502946666431427059 221793932254419999647140589)
  ·
    refine ⟨83172724595407499867677721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221793932254419999647140589 83172724595407499867677721)
    ·
      refine ⟨62379543446555624900758291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83172724595407499867677721 62379543446555624900758291)
      ·
        refine ⟨93569315169833437351137437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62379543446555624900758291 93569315169833437351137437)
        ·
          refine ⟨35088493188687539006676539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93569315169833437351137437 35088493188687539006676539)
          ·
            refine ⟨52632739783031308510014809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35088493188687539006676539 52632739783031308510014809)
            ·
              refine ⟨39474554837273481382511107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52632739783031308510014809 39474554837273481382511107)
              ·
                refine ⟨59211832255910222073766661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39474554837273481382511107 59211832255910222073766661)
                ·
                  refine ⟨11102218547983166638831249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59211832255910222073766661 11102218547983166638831249)
                  ·
                    refine ⟨8326663910987374979123437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11102218547983166638831249 8326663910987374979123437)
                    ·
                      refine ⟨3122498966620265617171289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8326663910987374979123437 3122498966620265617171289)
                      ·
                        rfl

theorem cell23_6081045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_6081045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081045 prefixEnd_6081045 := by exact prefixLift 6081045
  have htrace : WordTrace (prefixWord ++ tailWord_6081045) baseStart_6081045 baseEnd_6081045 := by
    simpa [prefixWord, tailWord_6081045, baseEnd_6081045] using wordTrace_append hprefix tailTrace_6081045
  have hstable : (prefixWord ++ tailWord_6081045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081045).length < 2 ^ (prefixWord ++ tailWord_6081045).sum := by decide
  have hdescent : baseEnd_6081045 < baseStart_6081045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081052 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_6081052 : Nat := 118140960795 + 6081052 * 2 ^ 59
def prefixEnd_6081052 : Nat := 4983230072969 + 3 ^ 40 * 6081052 * 2
def baseEnd_6081052 : Nat := 1040834186994949029927919

theorem tailTrace_6081052 : CollatzResearch.WordTrace tailWord_6081052 prefixEnd_6081052 1040834186994949029927919 := by
  unfold tailWord_6081052
  simp only [CollatzResearch.WordTrace]
  refine ⟨110897093782697319921322705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147862791710263093228430273 110897093782697319921322705)
  ·
    refine ⟨83172820337022989940992029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110897093782697319921322705 83172820337022989940992029)
    ·
      refine ⟨31189807626383621227872011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83172820337022989940992029 31189807626383621227872011)
      ·
        refine ⟨46784711439575431841808017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31189807626383621227872011 46784711439575431841808017)
        ·
          refine ⟨35088533579681573881356013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46784711439575431841808017 35088533579681573881356013)
          ·
            refine ⟨13158200092380590205508505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35088533579681573881356013 13158200092380590205508505)
            ·
              refine ⟨9868650069285442654131379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13158200092380590205508505 9868650069285442654131379)
              ·
                refine ⟨14802975103928163981197069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9868650069285442654131379 14802975103928163981197069)
                ·
                  refine ⟨5551115663973061492948901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14802975103928163981197069 5551115663973061492948901)
                  ·
                    refine ⟨1040834186994949029927919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5551115663973061492948901 1040834186994949029927919)
                    ·
                      rfl

theorem cell23_6081052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_6081052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081052 prefixEnd_6081052 := by exact prefixLift 6081052
  have htrace : WordTrace (prefixWord ++ tailWord_6081052) baseStart_6081052 baseEnd_6081052 := by
    simpa [prefixWord, tailWord_6081052, baseEnd_6081052] using wordTrace_append hprefix tailTrace_6081052
  have hstable : (prefixWord ++ tailWord_6081052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081052).length < 2 ^ (prefixWord ++ tailWord_6081052).sum := by decide
  have hdescent : baseEnd_6081052 < baseStart_6081052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081102 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2]
def baseStart_6081102 : Nat := 118140960795 + 6081102 * 2 ^ 59
def prefixEnd_6081102 : Nat := 4983230072969 + 3 ^ 40 * 6081102 * 2
def baseEnd_6081102 : Nat := 3122528235017571894158527

theorem tailTrace_6081102 : CollatzResearch.WordTrace tailWord_6081102 prefixEnd_6081102 3122528235017571894158527 := by
  unfold tailWord_6081102
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724501401901687297745695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147864007476808998921310373 27724501401901687297745695)
  ·
    refine ⟨41586752102852530946618543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27724501401901687297745695 41586752102852530946618543)
    ·
      refine ⟨62380128154278796419927815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41586752102852530946618543 62380128154278796419927815)
      ·
        refine ⟨93570192231418194629891723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62380128154278796419927815 93570192231418194629891723)
        ·
          refine ⟨140355288347127291944837585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93570192231418194629891723 140355288347127291944837585)
          ·
            refine ⟨105266466260345468958628189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140355288347127291944837585 105266466260345468958628189)
            ·
              refine ⟨39474924847629550859485571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105266466260345468958628189 39474924847629550859485571)
              ·
                refine ⟨59212387271444326289228357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39474924847629550859485571 59212387271444326289228357)
                ·
                  refine ⟨11102322613395811179230317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59212387271444326289228357 11102322613395811179230317)
                  ·
                    refine ⟨4163370980023429192211369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11102322613395811179230317 4163370980023429192211369)
                    ·
                      refine ⟨3122528235017571894158527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163370980023429192211369 3122528235017571894158527)
                      ·
                        rfl

theorem cell23_6081102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_6081102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081102 prefixEnd_6081102 := by exact prefixLift 6081102
  have htrace : WordTrace (prefixWord ++ tailWord_6081102) baseStart_6081102 baseEnd_6081102 := by
    simpa [prefixWord, tailWord_6081102, baseEnd_6081102] using wordTrace_append hprefix tailTrace_6081102
  have hstable : (prefixWord ++ tailWord_6081102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081102).length < 2 ^ (prefixWord ++ tailWord_6081102).sum := by decide
  have hdescent : baseEnd_6081102 < baseStart_6081102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081109 : List Nat := [1, 3, 2, 2, 1, 1, 2, 6, 1, 1, 3]
def baseStart_6081109 : Nat := 118140960795 + 6081109 * 2 ^ 59
def prefixEnd_6081109 : Nat := 4983230072969 + 3 ^ 40 * 6081109 * 2
def baseEnd_6081109 : Nat := 3122531829382153366770995

theorem tailTrace_6081109 : CollatzResearch.WordTrace tailWord_6081109 prefixEnd_6081109 3122531829382153366770995 := by
  unfold tailWord_6081109
  simp only [CollatzResearch.WordTrace]
  refine ⟨221796266526188138577470381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147864177684125425718313587 221796266526188138577470381)
  ·
    refine ⟨83173599947320551966551393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221796266526188138577470381 83173599947320551966551393)
    ·
      refine ⟨62380199960490413974913545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83173599947320551966551393 62380199960490413974913545)
      ·
        refine ⟨46785149970367810481185159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62380199960490413974913545 46785149970367810481185159)
        ·
          refine ⟨70177724955551715721777739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46785149970367810481185159 70177724955551715721777739)
          ·
            refine ⟨105266587433327573582666609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70177724955551715721777739 105266587433327573582666609)
            ·
              refine ⟨78949940574995680186999957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105266587433327573582666609 78949940574995680186999957)
              ·
                refine ⟨3700778464452922508765623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78949940574995680186999957 3700778464452922508765623)
                ·
                  refine ⟨5551167696679383763148435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700778464452922508765623 5551167696679383763148435)
                  ·
                    refine ⟨8326751545019075644722653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5551167696679383763148435 8326751545019075644722653)
                    ·
                      refine ⟨3122531829382153366770995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8326751545019075644722653 3122531829382153366770995)
                      ·
                        rfl

theorem cell23_6081109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_6081109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081109 prefixEnd_6081109 := by exact prefixLift 6081109
  have htrace : WordTrace (prefixWord ++ tailWord_6081109) baseStart_6081109 baseEnd_6081109 := by
    simpa [prefixWord, tailWord_6081109, baseEnd_6081109] using wordTrace_append hprefix tailTrace_6081109
  have hstable : (prefixWord ++ tailWord_6081109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081109).length < 2 ^ (prefixWord ++ tailWord_6081109).sum := by decide
  have hdescent : baseEnd_6081109 < baseStart_6081109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081116 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 6]
def baseStart_6081116 : Nat := 118140960795 + 6081116 * 2 ^ 59
def prefixEnd_6081116 : Nat := 4983230072969 + 3 ^ 40 * 6081116 * 2
def baseEnd_6081116 : Nat := 346948380416303871042607

theorem tailTrace_6081116 : CollatzResearch.WordTrace tailWord_6081116 prefixEnd_6081116 346948380416303871042607 := by
  unfold tailWord_6081116
  simp only [CollatzResearch.WordTrace]
  refine ⟨110898260918581389386487601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147864347891441852515316801 110898260918581389386487601)
  ·
    refine ⟨83173695688936042039865701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110898260918581389386487601 83173695688936042039865701)
    ·
      refine ⟨15595067941675507882474819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83173695688936042039865701 15595067941675507882474819)
      ·
        refine ⟨23392601912513261823712229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15595067941675507882474819 23392601912513261823712229)
        ·
          refine ⟨4386112858596236591946043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23392601912513261823712229 4386112858596236591946043)
          ·
            refine ⟨6579169287894354887919065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386112858596236591946043 6579169287894354887919065)
            ·
              refine ⟨4934376965920766165939299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6579169287894354887919065 4934376965920766165939299)
              ·
                refine ⟨7401565448881149248908949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4934376965920766165939299 7401565448881149248908949)
                ·
                  refine ⟨346948380416303871042607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7401565448881149248908949 346948380416303871042607)
                  ·
                    rfl

theorem cell23_6081116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_6081116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081116 prefixEnd_6081116 := by exact prefixLift 6081116
  have htrace : WordTrace (prefixWord ++ tailWord_6081116) baseStart_6081116 baseEnd_6081116 := by
    simpa [prefixWord, tailWord_6081116, baseEnd_6081116] using wordTrace_append hprefix tailTrace_6081116
  have hstable : (prefixWord ++ tailWord_6081116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081116).length < 2 ^ (prefixWord ++ tailWord_6081116).sum := by decide
  have hdescent : baseEnd_6081116 < baseStart_6081116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081132 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 4]
def baseStart_6081132 : Nat := 118140960795 + 6081132 * 2 ^ 59
def prefixEnd_6081132 : Nat := 4983230072969 + 3 ^ 40 * 6081132 * 2
def baseEnd_6081132 : Nat := 3122543639437206776783389

theorem tailTrace_6081132 : CollatzResearch.WordTrace tailWord_6081132 prefixEnd_6081132 3122543639437206776783389 := by
  unfold tailWord_6081132
  simp only [CollatzResearch.WordTrace]
  refine ⟨110898552702552406752778825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147864736936736542337038433 110898552702552406752778825)
  ·
    refine ⟨83173914526914305064584119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110898552702552406752778825 83173914526914305064584119)
    ·
      refine ⟨124760871790371457596876179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83173914526914305064584119 124760871790371457596876179)
      ·
        refine ⟨187141307685557186395314269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124760871790371457596876179 187141307685557186395314269)
        ·
          refine ⟨70177990382083944898242851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187141307685557186395314269 70177990382083944898242851)
          ·
            refine ⟨105266985573125917347364277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70177990382083944898242851 105266985573125917347364277)
            ·
              refine ⟨9868779897480554751315401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105266985573125917347364277 9868779897480554751315401)
              ·
                refine ⟨7401584923110416063486551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9868779897480554751315401 7401584923110416063486551)
                ·
                  refine ⟨11102377384665624095229827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7401584923110416063486551 11102377384665624095229827)
                  ·
                    refine ⟨16653566076998436142844741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11102377384665624095229827 16653566076998436142844741)
                    ·
                      refine ⟨3122543639437206776783389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16653566076998436142844741 3122543639437206776783389)
                      ·
                        rfl

theorem cell23_6081132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_6081132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081132 prefixEnd_6081132 := by exact prefixLift 6081132
  have htrace : WordTrace (prefixWord ++ tailWord_6081132) baseStart_6081132 baseEnd_6081132 := by
    simpa [prefixWord, tailWord_6081132, baseEnd_6081132] using wordTrace_append hprefix tailTrace_6081132
  have hstable : (prefixWord ++ tailWord_6081132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081132).length < 2 ^ (prefixWord ++ tailWord_6081132).sum := by decide
  have hdescent : baseEnd_6081132 < baseStart_6081132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081145 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_6081145 : Nat := 118140960795 + 6081145 * 2 ^ 59
def prefixEnd_6081145 : Nat := 4983230072969 + 3 ^ 40 * 6081145 * 2
def baseEnd_6081145 : Nat := 3122550314685715225920829

theorem tailTrace_6081145 : CollatzResearch.WordTrace tailWord_6081145 prefixEnd_6081145 3122550314685715225920829 := by
  unfold tailWord_6081145
  simp only [CollatzResearch.WordTrace]
  refine ⟨221797579554057716725780889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147865053036038477817187259 221797579554057716725780889)
  ·
    refine ⟨166348184665543287544335667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221797579554057716725780889 166348184665543287544335667)
    ·
      refine ⟨249522276998314931316503501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166348184665543287544335667 249522276998314931316503501)
      ·
        refine ⟨93570853874368099243688813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249522276998314931316503501 93570853874368099243688813)
        ·
          refine ⟨35089070202888037216383305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93570853874368099243688813 35089070202888037216383305)
          ·
            refine ⟨26316802652166027912287479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35089070202888037216383305 26316802652166027912287479)
            ·
              refine ⟨39475203978249041868431219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26316802652166027912287479 39475203978249041868431219)
              ·
                refine ⟨59212805967373562802646829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39475203978249041868431219 59212805967373562802646829)
                ·
                  refine ⟨22204802237765086050992561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59212805967373562802646829 22204802237765086050992561)
                  ·
                    refine ⟨16653601678323814538244421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22204802237765086050992561 16653601678323814538244421)
                    ·
                      refine ⟨3122550314685715225920829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16653601678323814538244421 3122550314685715225920829)
                      ·
                        rfl

theorem cell23_6081145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_6081145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081145 prefixEnd_6081145 := by exact prefixLift 6081145
  have htrace : WordTrace (prefixWord ++ tailWord_6081145) baseStart_6081145 baseEnd_6081145 := by
    simpa [prefixWord, tailWord_6081145, baseEnd_6081145] using wordTrace_append hprefix tailTrace_6081145
  have hstable : (prefixWord ++ tailWord_6081145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081145).length < 2 ^ (prefixWord ++ tailWord_6081145).sum := by decide
  have hdescent : baseEnd_6081145 < baseStart_6081145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081152 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 5]
def baseStart_6081152 : Nat := 118140960795 + 6081152 * 2 ^ 59
def prefixEnd_6081152 : Nat := 4983230072969 + 3 ^ 40 * 6081152 * 2
def baseEnd_6081152 : Nat := 3122553909050296698533297

theorem tailTrace_6081152 : CollatzResearch.WordTrace tailWord_6081152 prefixEnd_6081152 3122553909050296698533297 := by
  unfold tailWord_6081152
  simp only [CollatzResearch.WordTrace]
  refine ⟨110898917432516178460642855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147865223243354904614190473 110898917432516178460642855)
  ·
    refine ⟨166348376148774267690964283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110898917432516178460642855 166348376148774267690964283)
    ·
      refine ⟨249522564223161401536446425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166348376148774267690964283 249522564223161401536446425)
      ·
        refine ⟨187141923167371051152334819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249522564223161401536446425 187141923167371051152334819)
        ·
          refine ⟨280712884751056576728502229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187141923167371051152334819 280712884751056576728502229)
          ·
            refine ⟨6579208236352888517074271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 280712884751056576728502229 6579208236352888517074271)
            ·
              refine ⟨9868812354529332775611407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6579208236352888517074271 9868812354529332775611407)
              ·
                refine ⟨14803218531793999163417111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9868812354529332775611407 14803218531793999163417111)
                ·
                  refine ⟨22204827797690998745125667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14803218531793999163417111 22204827797690998745125667)
                  ·
                    refine ⟨33307241696536498117688501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22204827797690998745125667 33307241696536498117688501)
                    ·
                      refine ⟨3122553909050296698533297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33307241696536498117688501 3122553909050296698533297)
                      ·
                        rfl

theorem cell23_6081152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_6081152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081152 prefixEnd_6081152 := by exact prefixLift 6081152
  have htrace : WordTrace (prefixWord ++ tailWord_6081152) baseStart_6081152 baseEnd_6081152 := by
    simpa [prefixWord, tailWord_6081152, baseEnd_6081152] using wordTrace_append hprefix tailTrace_6081152
  have hstable : (prefixWord ++ tailWord_6081152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081152).length < 2 ^ (prefixWord ++ tailWord_6081152).sum := by decide
  have hdescent : baseEnd_6081152 < baseStart_6081152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081154 : List Nat := [3, 4, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6081154 : Nat := 118140960795 + 6081154 * 2 ^ 59
def prefixEnd_6081154 : Nat := 4983230072969 + 3 ^ 40 * 6081154 * 2
def baseEnd_6081154 : Nat := 1040851645337201896902763

theorem tailTrace_6081154 : CollatzResearch.WordTrace tailWord_6081154 prefixEnd_6081154 1040851645337201896902763 := by
  unfold tailWord_6081154
  simp only [CollatzResearch.WordTrace]
  refine ⟨55449476952756277815714629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147865271874016740841905677 55449476952756277815714629)
  ·
    refine ⟨10396776928641802090446493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55449476952756277815714629 10396776928641802090446493)
    ·
      refine ⟨3898791348240675783917435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10396776928641802090446493 3898791348240675783917435)
      ·
        refine ⟨5848187022361013675876153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3898791348240675783917435 5848187022361013675876153)
        ·
          refine ⟨4386140266770760256907115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5848187022361013675876153 4386140266770760256907115)
          ·
            refine ⟨6579210400156140385360673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386140266770760256907115 6579210400156140385360673)
            ·
              refine ⟨4934407800117105289020505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6579210400156140385360673 4934407800117105289020505)
              ·
                refine ⟨3700805850087828966765379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4934407800117105289020505 3700805850087828966765379)
                ·
                  refine ⟨5551208775131743450148069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700805850087828966765379 5551208775131743450148069)
                  ·
                    refine ⟨1040851645337201896902763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5551208775131743450148069 1040851645337201896902763)
                    ·
                      rfl

theorem cell23_6081154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6081154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081154 prefixEnd_6081154 := by exact prefixLift 6081154
  have htrace : WordTrace (prefixWord ++ tailWord_6081154) baseStart_6081154 baseEnd_6081154 := by
    simpa [prefixWord, tailWord_6081154, baseEnd_6081154] using wordTrace_append hprefix tailTrace_6081154
  have hstable : (prefixWord ++ tailWord_6081154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081154).length < 2 ^ (prefixWord ++ tailWord_6081154).sum := by decide
  have hdescent : baseEnd_6081154 < baseStart_6081154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081172 : List Nat := [2, 4, 2, 2, 1, 1, 3, 8]
def baseStart_6081172 : Nat := 118140960795 + 6081172 * 2 ^ 59
def prefixEnd_6081172 : Nat := 4983230072969 + 3 ^ 40 * 6081172 * 2
def baseEnd_6081172 : Nat := 115650525135680985936415

theorem tailTrace_6081172 : CollatzResearch.WordTrace tailWord_6081172 prefixEnd_6081172 115650525135680985936415 := by
  unfold tailWord_6081172
  simp only [CollatzResearch.WordTrace]
  refine ⟨110899282162479950168506885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147865709549973266891342513 110899282162479950168506885)
  ·
    refine ⟨20793615405464990656595041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110899282162479950168506885 20793615405464990656595041)
    ·
      refine ⟨15595211554098742992446281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20793615405464990656595041 15595211554098742992446281)
      ·
        refine ⟨11696408665574057244334711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15595211554098742992446281 11696408665574057244334711)
        ·
          refine ⟨17544612998361085866502067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11696408665574057244334711 17544612998361085866502067)
          ·
            refine ⟨26316919497541628799753101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17544612998361085866502067 26316919497541628799753101)
            ·
              refine ⟨9868844811578110799907413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26316919497541628799753101 9868844811578110799907413)
              ·
                refine ⟨115650525135680985936415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9868844811578110799907413 115650525135680985936415)
                ·
                  rfl

theorem cell23_6081172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 8].length) (baseStart_6081172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081172 prefixEnd_6081172 := by exact prefixLift 6081172
  have htrace : WordTrace (prefixWord ++ tailWord_6081172) baseStart_6081172 baseEnd_6081172 := by
    simpa [prefixWord, tailWord_6081172, baseEnd_6081172] using wordTrace_append hprefix tailTrace_6081172
  have hstable : (prefixWord ++ tailWord_6081172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081172).length < 2 ^ (prefixWord ++ tailWord_6081172).sum := by decide
  have hdescent : baseEnd_6081172 < baseStart_6081172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081215 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 2, 6]
def baseStart_6081215 : Nat := 118140960795 + 6081215 * 2 ^ 59
def prefixEnd_6081215 : Nat := 4983230072969 + 3 ^ 40 * 6081215 * 2
def baseEnd_6081215 : Nat := 1040862086110509984015169

theorem tailTrace_6081215 : CollatzResearch.WordTrace tailWord_6081215 prefixEnd_6081215 1040862086110509984015169 := by
  unfold tailWord_6081215
  simp only [CollatzResearch.WordTrace]
  refine ⟨221800132663804118680829099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147866755109202745787219399 221800132663804118680829099)
  ·
    refine ⟨332700198995706178021243649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221800132663804118680829099 332700198995706178021243649)
    ·
      refine ⟨249525149246779633515932737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332700198995706178021243649 249525149246779633515932737)
      ·
        refine ⟨187143861935084725136949553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249525149246779633515932737 187143861935084725136949553)
        ·
          refine ⟨140357896451313543852712165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187143861935084725136949553 140357896451313543852712165)
          ·
            refine ⟨26317105584621289472383531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140357896451313543852712165 26317105584621289472383531)
            ·
              refine ⟨39475658376931934208575297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26317105584621289472383531 39475658376931934208575297)
              ·
                refine ⟨29606743782698950656431473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39475658376931934208575297 29606743782698950656431473)
                ·
                  refine ⟨22205057837024212992323605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29606743782698950656431473 22205057837024212992323605)
                  ·
                    refine ⟨1040862086110509984015169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22205057837024212992323605 1040862086110509984015169)
                    ·
                      rfl

theorem cell23_6081215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_6081215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081215 prefixEnd_6081215 := by exact prefixLift 6081215
  have htrace : WordTrace (prefixWord ++ tailWord_6081215) baseStart_6081215 baseEnd_6081215 := by
    simpa [prefixWord, tailWord_6081215, baseEnd_6081215] using wordTrace_append hprefix tailTrace_6081215
  have hstable : (prefixWord ++ tailWord_6081215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081215).length < 2 ^ (prefixWord ++ tailWord_6081215).sum := by decide
  have hdescent : baseEnd_6081215 < baseStart_6081215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081216 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 2, 1, 3]
def baseStart_6081216 : Nat := 118140960795 + 6081216 * 2 ^ 59
def prefixEnd_6081216 : Nat := 4983230072969 + 3 ^ 40 * 6081216 * 2
def baseEnd_6081216 : Nat := 3122586771812184448133003

theorem tailTrace_6081216 : CollatzResearch.WordTrace tailWord_6081216 prefixEnd_6081216 3122586771812184448133003 := by
  unfold tailWord_6081216
  simp only [CollatzResearch.WordTrace]
  refine ⟨110900084568400247925807751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147866779424533663901077001 110900084568400247925807751)
  ·
    refine ⟨166350126852600371888711627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110900084568400247925807751 166350126852600371888711627)
    ·
      refine ⟨249525190278900557833067441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166350126852600371888711627 249525190278900557833067441)
      ·
        refine ⟨187143892709175418374800581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249525190278900557833067441 187143892709175418374800581)
        ·
          refine ⟨35089479882970390945275109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187143892709175418374800581 35089479882970390945275109)
          ·
            refine ⟨6579277478056948302239083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35089479882970390945275109 6579277478056948302239083)
            ·
              refine ⟨9868916217085422453358625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6579277478056948302239083 9868916217085422453358625)
              ·
                refine ⟨7401687162814066840018969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9868916217085422453358625 7401687162814066840018969)
                ·
                  refine ⟨5551265372110550130014227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7401687162814066840018969 5551265372110550130014227)
                  ·
                    refine ⟨8326898058165825195021341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5551265372110550130014227 8326898058165825195021341)
                    ·
                      refine ⟨3122586771812184448133003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8326898058165825195021341 3122586771812184448133003)
                      ·
                        rfl

theorem cell23_6081216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_6081216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081216 prefixEnd_6081216 := by exact prefixLift 6081216
  have htrace : WordTrace (prefixWord ++ tailWord_6081216) baseStart_6081216 baseEnd_6081216 := by
    simpa [prefixWord, tailWord_6081216, baseEnd_6081216] using wordTrace_append hprefix tailTrace_6081216
  have hstable : (prefixWord ++ tailWord_6081216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081216).length < 2 ^ (prefixWord ++ tailWord_6081216).sum := by decide
  have hdescent : baseEnd_6081216 < baseStart_6081216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081239 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 1, 4, 2]
def baseStart_6081239 : Nat := 118140960795 + 6081239 * 2 ^ 59
def prefixEnd_6081239 : Nat := 4983230072969 + 3 ^ 40 * 6081239 * 2
def baseEnd_6081239 : Nat := 3122598581867237858145397

theorem tailTrace_6081239 : CollatzResearch.WordTrace tailWord_6081239 prefixEnd_6081239 3122598581867237858145397 := by
  unfold tailWord_6081239
  simp only [CollatzResearch.WordTrace]
  refine ⟨221801008015717170779702771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147867338677144780519801847 221801008015717170779702771)
  ·
    refine ⟨332701512023575756169554157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221801008015717170779702771 332701512023575756169554157)
    ·
      refine ⟨124763067008840908563582809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332701512023575756169554157 124763067008840908563582809)
      ·
        refine ⟨93572300256630681422687107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124763067008840908563582809 93572300256630681422687107)
        ·
          refine ⟨140358450384946022134030661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93572300256630681422687107 140358450384946022134030661)
          ·
            refine ⟨26317209447177379150130749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140358450384946022134030661 26317209447177379150130749)
            ·
              refine ⟨9868953542691517181299031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26317209447177379150130749 9868953542691517181299031)
              ·
                refine ⟨14803430314037275771948547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9868953542691517181299031 14803430314037275771948547)
                ·
                  refine ⟨22205145471055913657922821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14803430314037275771948547 22205145471055913657922821)
                  ·
                    refine ⟨4163464775822983810860529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22205145471055913657922821 4163464775822983810860529)
                    ·
                      refine ⟨3122598581867237858145397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163464775822983810860529 3122598581867237858145397)
                      ·
                        rfl

theorem cell23_6081239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_6081239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081239 prefixEnd_6081239 := by exact prefixLift 6081239
  have htrace : WordTrace (prefixWord ++ tailWord_6081239) baseStart_6081239 baseEnd_6081239 := by
    simpa [prefixWord, tailWord_6081239, baseEnd_6081239] using wordTrace_append hprefix tailTrace_6081239
  have hstable : (prefixWord ++ tailWord_6081239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081239).length < 2 ^ (prefixWord ++ tailWord_6081239).sum := by decide
  have hdescent : baseEnd_6081239 < baseStart_6081239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081329 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 2, 4, 2]
def baseStart_6081329 : Nat := 118140960795 + 6081329 * 2 ^ 59
def prefixEnd_6081329 : Nat := 4983230072969 + 3 ^ 40 * 6081329 * 2
def baseEnd_6081329 : Nat := 3122644795126142506019983

theorem tailTrace_6081329 : CollatzResearch.WordTrace tailWord_6081329 prefixEnd_6081329 3122644795126142506019983 := by
  unfold tailWord_6081329
  simp only [CollatzResearch.WordTrace]
  refine ⟨221804290585391116150479041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147869527056927410766986027 221804290585391116150479041)
  ·
    refine ⟨166353217939043337112859281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221804290585391116150479041 166353217939043337112859281)
    ·
      refine ⟨124764913454282502834644461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166353217939043337112859281 124764913454282502834644461)
      ·
        refine ⟨46786842545355938562991673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124764913454282502834644461 46786842545355938562991673)
        ·
          refine ⟨35090131909016953922243755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46786842545355938562991673 35090131909016953922243755)
          ·
            refine ⟨52635197863525430883365633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35090131909016953922243755 52635197863525430883365633)
            ·
              refine ⟨39476398397644073162524225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52635197863525430883365633 39476398397644073162524225)
              ·
                refine ⟨29607298798233054871893169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39476398397644073162524225 29607298798233054871893169)
                ·
                  refine ⟨22205474098674791153919877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29607298798233054871893169 22205474098674791153919877)
                  ·
                    refine ⟨4163526393501523341359977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22205474098674791153919877 4163526393501523341359977)
                    ·
                      refine ⟨3122644795126142506019983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163526393501523341359977 3122644795126142506019983)
                      ·
                        rfl

theorem cell23_6081329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_6081329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081329 prefixEnd_6081329 := by exact prefixLift 6081329
  have htrace : WordTrace (prefixWord ++ tailWord_6081329) baseStart_6081329 baseEnd_6081329 := by
    simpa [prefixWord, tailWord_6081329, baseEnd_6081329] using wordTrace_append hprefix tailTrace_6081329
  have hstable : (prefixWord ++ tailWord_6081329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081329).length < 2 ^ (prefixWord ++ tailWord_6081329).sum := by decide
  have hdescent : baseEnd_6081329 < baseStart_6081329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081352 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 6]
def baseStart_6081352 : Nat := 118140960795 + 6081352 * 2 ^ 59
def prefixEnd_6081352 : Nat := 4983230072969 + 3 ^ 40 * 6081352 * 2
def baseEnd_6081352 : Nat := 346961845020132879559153

theorem tailTrace_6081352 : CollatzResearch.WordTrace tailWord_6081352 prefixEnd_6081352 346961845020132879559153 := by
  unfold tailWord_6081352
  simp only [CollatzResearch.WordTrace]
  refine ⟨110902564732153895539283155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147870086309538527385710873 110902564732153895539283155)
  ·
    refine ⟨166353847098230843308924733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110902564732153895539283155 166353847098230843308924733)
    ·
      refine ⟨62382692661836566240846775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166353847098230843308924733 62382692661836566240846775)
      ·
        refine ⟨93574038992754849361270163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62382692661836566240846775 93574038992754849361270163)
        ·
          refine ⟨140361058489132274041905245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93574038992754849361270163 140361058489132274041905245)
          ·
            refine ⟨52635396933424602765714467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140361058489132274041905245 52635396933424602765714467)
            ·
              refine ⟨78953095400136904148571701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52635396933424602765714467 78953095400136904148571701)
              ·
                refine ⟨7401852693762834763928597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78953095400136904148571701 7401852693762834763928597)
                ·
                  refine ⟨346961845020132879559153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7401852693762834763928597 346961845020132879559153)
                  ·
                    rfl

theorem cell23_6081352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 6].length) (baseStart_6081352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081352 prefixEnd_6081352 := by exact prefixLift 6081352
  have htrace : WordTrace (prefixWord ++ tailWord_6081352) baseStart_6081352 baseEnd_6081352 := by
    simpa [prefixWord, tailWord_6081352, baseEnd_6081352] using wordTrace_append hprefix tailTrace_6081352
  have hstable : (prefixWord ++ tailWord_6081352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081352).length < 2 ^ (prefixWord ++ tailWord_6081352).sum := by decide
  have hdescent : baseEnd_6081352 < baseStart_6081352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081416 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 1, 5]
def baseStart_6081416 : Nat := 118140960795 + 6081416 * 2 ^ 59
def prefixEnd_6081416 : Nat := 4983230072969 + 3 ^ 40 * 6081416 * 2
def baseEnd_6081416 : Nat := 1040896489314361221877361

theorem tailTrace_6081416 : CollatzResearch.WordTrace tailWord_6081416 prefixEnd_6081416 1040896489314361221877361 := by
  unfold tailWord_6081416
  simp only [CollatzResearch.WordTrace]
  refine ⟨110903731868037965004448051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147871642490717286672597401 110903731868037965004448051)
  ·
    refine ⟨166355597802056947506672077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110903731868037965004448051 166355597802056947506672077)
    ·
      refine ⟨62383349175771355315002029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166355597802056947506672077 62383349175771355315002029)
      ·
        refine ⟨23393755940914258243125761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62383349175771355315002029 23393755940914258243125761)
        ·
          refine ⟨17545316955685693682344321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23393755940914258243125761 17545316955685693682344321)
          ·
            refine ⟨13158987716764270261758241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17545316955685693682344321 13158987716764270261758241)
            ·
              refine ⟨9869240787573202696318681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13158987716764270261758241 9869240787573202696318681)
              ·
                refine ⟨7401930590679902022239011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9869240787573202696318681 7401930590679902022239011)
                ·
                  refine ⟨11102895886019853033358517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7401930590679902022239011 11102895886019853033358517)
                  ·
                    refine ⟨1040896489314361221877361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11102895886019853033358517 1040896489314361221877361)
                    ·
                      rfl

theorem cell23_6081416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_6081416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081416 prefixEnd_6081416 := by exact prefixLift 6081416
  have htrace : WordTrace (prefixWord ++ tailWord_6081416) baseStart_6081416 baseEnd_6081416 := by
    simpa [prefixWord, tailWord_6081416, baseEnd_6081416] using wordTrace_append hprefix tailTrace_6081416
  have hstable : (prefixWord ++ tailWord_6081416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081416).length < 2 ^ (prefixWord ++ tailWord_6081416).sum := by decide
  have hdescent : baseEnd_6081416 < baseStart_6081416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081419 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 4]
def baseStart_6081419 : Nat := 118140960795 + 6081419 * 2 ^ 59
def prefixEnd_6081419 : Nat := 4983230072969 + 3 ^ 40 * 6081419 * 2
def baseEnd_6081419 : Nat := 3122691008385047153894569

theorem tailTrace_6081419 : CollatzResearch.WordTrace tailWord_6081419 prefixEnd_6081419 3122691008385047153894569 := by
  unfold tailWord_6081419
  simp only [CollatzResearch.WordTrace]
  refine ⟨221807573155065061521255311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147871715436710041014170207 221807573155065061521255311)
  ·
    refine ⟨332711359732597592281882967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221807573155065061521255311 332711359732597592281882967)
    ·
      refine ⟨499067039598896388422824451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332711359732597592281882967 499067039598896388422824451)
      ·
        refine ⟨748600559398344582634236677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499067039598896388422824451 748600559398344582634236677)
        ·
          refine ⟨140362604887189609243919377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 748600559398344582634236677 140362604887189609243919377)
          ·
            refine ⟨105271953665392206932939533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140362604887189609243919377 105271953665392206932939533)
            ·
              refine ⟨39476982624522077599852325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105271953665392206932939533 39476982624522077599852325)
              ·
                refine ⟨7401934242097889549972311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39476982624522077599852325 7401934242097889549972311)
                ·
                  refine ⟨11102901363146834324958467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7401934242097889549972311 11102901363146834324958467)
                  ·
                    refine ⟨16654352044720251487437701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11102901363146834324958467 16654352044720251487437701)
                    ·
                      refine ⟨3122691008385047153894569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16654352044720251487437701 3122691008385047153894569)
                      ·
                        rfl

theorem cell23_6081419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 4].length) (baseStart_6081419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081419 prefixEnd_6081419 := by exact prefixLift 6081419
  have htrace : WordTrace (prefixWord ++ tailWord_6081419) baseStart_6081419 baseEnd_6081419 := by
    simpa [prefixWord, tailWord_6081419, baseEnd_6081419] using wordTrace_append hprefix tailTrace_6081419
  have hstable : (prefixWord ++ tailWord_6081419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081419).length < 2 ^ (prefixWord ++ tailWord_6081419).sum := by decide
  have hdescent : baseEnd_6081419 < baseStart_6081419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081429 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_6081429 : Nat := 118140960795 + 6081429 * 2 ^ 59
def prefixEnd_6081429 : Nat := 4983230072969 + 3 ^ 40 * 6081429 * 2
def baseEnd_6081429 : Nat := 1040898714397197371589841

theorem tailTrace_6081429 : CollatzResearch.WordTrace tailWord_6081429 prefixEnd_6081429 1040898714397197371589841 := by
  unfold tailWord_6081429
  simp only [CollatzResearch.WordTrace]
  refine ⟨221807937885028833229119341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147871958590019222152746227 221807937885028833229119341)
  ·
    refine ⟨83177976706885812460919753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221807937885028833229119341 83177976706885812460919753)
    ·
      refine ⟨62383482530164359345689815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83177976706885812460919753 62383482530164359345689815)
      ·
        refine ⟨93575223795246539018534723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62383482530164359345689815 93575223795246539018534723)
        ·
          refine ⟨140362835692869808527802085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93575223795246539018534723 140362835692869808527802085)
          ·
            refine ⟨26318031692413089098962891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140362835692869808527802085 26318031692413089098962891)
            ·
              refine ⟨39477047538619633648444337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26318031692413089098962891 39477047538619633648444337)
              ·
                refine ⟨29607785653964725236333253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39477047538619633648444337 29607785653964725236333253)
                ·
                  refine ⟨5551459810118385981812485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29607785653964725236333253 5551459810118385981812485)
                  ·
                    refine ⟨1040898714397197371589841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5551459810118385981812485 1040898714397197371589841)
                    ·
                      rfl

theorem cell23_6081429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_6081429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081429 prefixEnd_6081429 := by exact prefixLift 6081429
  have htrace : WordTrace (prefixWord ++ tailWord_6081429) baseStart_6081429 baseEnd_6081429 := by
    simpa [prefixWord, tailWord_6081429, baseEnd_6081429] using wordTrace_append hprefix tailTrace_6081429
  have hstable : (prefixWord ++ tailWord_6081429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081429).length < 2 ^ (prefixWord ++ tailWord_6081429).sum := by decide
  have hdescent : baseEnd_6081429 < baseStart_6081429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081439 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 5]
def baseStart_6081439 : Nat := 118140960795 + 6081439 * 2 ^ 59
def prefixEnd_6081439 : Nat := 4983230072969 + 3 ^ 40 * 6081439 * 2
def baseEnd_6081439 : Nat := 3122701277998137075644477

theorem tailTrace_6081439 : CollatzResearch.WordTrace tailWord_6081439 prefixEnd_6081439 3122701277998137075644477 := by
  unfold tailWord_6081439
  simp only [CollatzResearch.WordTrace]
  refine ⟨221808302614992604936983371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147872201743328403291322247 221808302614992604936983371)
  ·
    refine ⟨332712453922488907405475057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221808302614992604936983371 332712453922488907405475057)
    ·
      refine ⟨249534340441866680554106293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332712453922488907405475057 249534340441866680554106293)
      ·
        refine ⟨23393844416425001301947465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249534340441866680554106293 23393844416425001301947465)
        ·
          refine ⟨17545383312318750976460599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23393844416425001301947465 17545383312318750976460599)
          ·
            refine ⟨26318074968478126464690899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17545383312318750976460599 26318074968478126464690899)
            ·
              refine ⟨39477112452717189697036349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26318074968478126464690899 39477112452717189697036349)
              ·
                refine ⟨14803917169768946136388631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39477112452717189697036349 14803917169768946136388631)
                ·
                  refine ⟨22205875754653419204582947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14803917169768946136388631 22205875754653419204582947)
                  ·
                    refine ⟨33308813631980128806874421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22205875754653419204582947 33308813631980128806874421)
                    ·
                      refine ⟨3122701277998137075644477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33308813631980128806874421 3122701277998137075644477)
                      ·
                        rfl

theorem cell23_6081439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_6081439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081439 prefixEnd_6081439 := by exact prefixLift 6081439
  have htrace : WordTrace (prefixWord ++ tailWord_6081439) baseStart_6081439 baseEnd_6081439 := by
    simpa [prefixWord, tailWord_6081439, baseEnd_6081439] using wordTrace_append hprefix tailTrace_6081439
  have hstable : (prefixWord ++ tailWord_6081439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081439).length < 2 ^ (prefixWord ++ tailWord_6081439).sum := by decide
  have hdescent : baseEnd_6081439 < baseStart_6081439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081447 : List Nat := [1, 1, 6, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_6081447 : Nat := 118140960795 + 6081447 * 2 ^ 59
def prefixEnd_6081447 : Nat := 4983230072969 + 3 ^ 40 * 6081447 * 2
def baseEnd_6081447 : Nat := 3122705385843373044344441

theorem tailTrace_6081447 : CollatzResearch.WordTrace tailWord_6081447 prefixEnd_6081447 3122705385843373044344441 := by
  unfold tailWord_6081447
  simp only [CollatzResearch.WordTrace]
  refine ⟨221808594398963622303274595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147872396265975748202183063 221808594398963622303274595)
  ·
    refine ⟨332712891598445433454911893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221808594398963622303274595 332712891598445433454911893)
    ·
      refine ⟨15595916793677129693198995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 332712891598445433454911893 15595916793677129693198995)
      ·
        refine ⟨23393875190515694539798493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15595916793677129693198995 23393875190515694539798493)
        ·
          refine ⟨8772703196443385452424435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23393875190515694539798493 8772703196443385452424435)
          ·
            refine ⟨13159054794665078178636653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8772703196443385452424435 13159054794665078178636653)
            ·
              refine ⟨4934645547999404316988745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13159054794665078178636653 4934645547999404316988745)
              ·
                refine ⟨3700984160999553237741559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4934645547999404316988745 3700984160999553237741559)
                ·
                  refine ⟨5551476241499329856612339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3700984160999553237741559 5551476241499329856612339)
                  ·
                    refine ⟨8327214362248994784918509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5551476241499329856612339 8327214362248994784918509)
                    ·
                      refine ⟨3122705385843373044344441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8327214362248994784918509 3122705385843373044344441)
                      ·
                        rfl

theorem cell23_6081447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_6081447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081447 prefixEnd_6081447 := by exact prefixLift 6081447
  have htrace : WordTrace (prefixWord ++ tailWord_6081447) baseStart_6081447 baseEnd_6081447 := by
    simpa [prefixWord, tailWord_6081447, baseEnd_6081447] using wordTrace_append hprefix tailTrace_6081447
  have hstable : (prefixWord ++ tailWord_6081447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081447).length < 2 ^ (prefixWord ++ tailWord_6081447).sum := by decide
  have hdescent : baseEnd_6081447 < baseStart_6081447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081486 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_6081486 : Nat := 118140960795 + 6081486 * 2 ^ 59
def prefixEnd_6081486 : Nat := 4983230072969 + 3 ^ 40 * 6081486 * 2
def baseEnd_6081486 : Nat := 3122725411588898391756761

theorem tailTrace_6081486 : CollatzResearch.WordTrace tailWord_6081486 prefixEnd_6081486 3122725411588898391756761 := by
  unfold tailWord_6081486
  simp only [CollatzResearch.WordTrace]
  refine ⟨27726252105727791495493039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147873344563881554642629541 27726252105727791495493039)
  ·
    refine ⟨41589378158591687243239559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27726252105727791495493039 41589378158591687243239559)
    ·
      refine ⟨62384067237887530864859339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41589378158591687243239559 62384067237887530864859339)
      ·
        refine ⟨93576100856831296297289009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62384067237887530864859339 93576100856831296297289009)
        ·
          refine ⟨70182075642623472222966757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93576100856831296297289009 70182075642623472222966757)
          ·
            refine ⟨13159139182991901041806267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70182075642623472222966757 13159139182991901041806267)
            ·
              refine ⟨19738708774487851562709401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13159139182991901041806267 19738708774487851562709401)
              ·
                refine ⟨14804031580865888672032051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19738708774487851562709401 14804031580865888672032051)
                ·
                  refine ⟨22206047371298833008048077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14804031580865888672032051 22206047371298833008048077)
                  ·
                    refine ⟨8327267764237062378018029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22206047371298833008048077 8327267764237062378018029)
                    ·
                      refine ⟨3122725411588898391756761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8327267764237062378018029 3122725411588898391756761)
                      ·
                        rfl

theorem cell23_6081486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_6081486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081486 prefixEnd_6081486 := by exact prefixLift 6081486
  have htrace : WordTrace (prefixWord ++ tailWord_6081486) baseStart_6081486 baseEnd_6081486 := by
    simpa [prefixWord, tailWord_6081486, baseEnd_6081486] using wordTrace_append hprefix tailTrace_6081486
  have hstable : (prefixWord ++ tailWord_6081486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081486).length < 2 ^ (prefixWord ++ tailWord_6081486).sum := by decide
  have hdescent : baseEnd_6081486 < baseStart_6081486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081490 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_6081490 : Nat := 118140960795 + 6081490 * 2 ^ 59
def prefixEnd_6081490 : Nat := 4983230072969 + 3 ^ 40 * 6081490 * 2
def baseEnd_6081490 : Nat := 3122727465511516376106743

theorem tailTrace_6081490 : CollatzResearch.WordTrace tailWord_6081490 prefixEnd_6081490 3122727465511516376106743 := by
  unfold tailWord_6081490
  simp only [CollatzResearch.WordTrace]
  refine ⟨55452540684451960161772481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147873441825205227098059949 55452540684451960161772481)
  ·
    refine ⟨41589405513338970121329361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55452540684451960161772481 41589405513338970121329361)
    ·
      refine ⟨31192054135004227590997021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41589405513338970121329361 31192054135004227590997021)
      ·
        refine ⟨11697020300626585346623883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31192054135004227590997021 11697020300626585346623883)
        ·
          refine ⟨17545530450939878019935825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11697020300626585346623883 17545530450939878019935825)
          ·
            refine ⟨13159147838204908514951869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17545530450939878019935825 13159147838204908514951869)
            ·
              refine ⟨4934680439326840693106951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13159147838204908514951869 4934680439326840693106951)
              ·
                refine ⟨7402020658990261039660427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4934680439326840693106951 7402020658990261039660427)
                ·
                  refine ⟨11103030988485391559490641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7402020658990261039660427 11103030988485391559490641)
                  ·
                    refine ⟨8327273241364043669617981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11103030988485391559490641 8327273241364043669617981)
                    ·
                      refine ⟨3122727465511516376106743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8327273241364043669617981 3122727465511516376106743)
                      ·
                        rfl

theorem cell23_6081490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_6081490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081490 prefixEnd_6081490 := by exact prefixLift 6081490
  have htrace : WordTrace (prefixWord ++ tailWord_6081490) baseStart_6081490 baseEnd_6081490 := by
    simpa [prefixWord, tailWord_6081490, baseEnd_6081490] using wordTrace_append hprefix tailTrace_6081490
  have hstable : (prefixWord ++ tailWord_6081490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081490).length < 2 ^ (prefixWord ++ tailWord_6081490).sum := by decide
  have hdescent : baseEnd_6081490 < baseStart_6081490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081506 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6081506 : Nat := 118140960795 + 6081506 * 2 ^ 59
def prefixEnd_6081506 : Nat := 4983230072969 + 3 ^ 40 * 6081506 * 2
def baseEnd_6081506 : Nat := 1040911893733996104502223

theorem tailTrace_6081506 : CollatzResearch.WordTrace tailWord_6081506 prefixEnd_6081506 1040911893733996104502223 := by
  unfold tailWord_6081506
  simp only [CollatzResearch.WordTrace]
  refine ⟨55452686576437468844918093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147873830870499916919781581 55452686576437468844918093)
  ·
    refine ⟨20794757466164050816844285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55452686576437468844918093 20794757466164050816844285)
    ·
      refine ⟨7798034049811519056316607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20794757466164050816844285 7798034049811519056316607)
      ·
        refine ⟨11697051074717278584474911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7798034049811519056316607 11697051074717278584474911)
        ·
          refine ⟨17545576612075917876712367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11697051074717278584474911 17545576612075917876712367)
          ·
            refine ⟨26318364918113876815068551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17545576612075917876712367 26318364918113876815068551)
            ·
              refine ⟨39477547377170815222602827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26318364918113876815068551 39477547377170815222602827)
              ·
                refine ⟨59216321065756222833904241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39477547377170815222602827 59216321065756222833904241)
                ·
                  refine ⟨44412240799317167125428181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59216321065756222833904241 44412240799317167125428181)
                  ·
                    refine ⟨1040911893733996104502223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44412240799317167125428181 1040911893733996104502223)
                    ·
                      rfl

theorem cell23_6081506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6081506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081506 prefixEnd_6081506 := by exact prefixLift 6081506
  have htrace : WordTrace (prefixWord ++ tailWord_6081506) baseStart_6081506 baseEnd_6081506 := by
    simpa [prefixWord, tailWord_6081506, baseEnd_6081506] using wordTrace_append hprefix tailTrace_6081506
  have hstable : (prefixWord ++ tailWord_6081506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081506).length < 2 ^ (prefixWord ++ tailWord_6081506).sum := by decide
  have hdescent : baseEnd_6081506 < baseStart_6081506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081519 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 2, 6]
def baseStart_6081519 : Nat := 118140960795 + 6081519 * 2 ^ 59
def prefixEnd_6081519 : Nat := 4983230072969 + 3 ^ 40 * 6081519 * 2
def baseEnd_6081519 : Nat := 1040914118816832254214703

theorem tailTrace_6081519 : CollatzResearch.WordTrace tailWord_6081519 prefixEnd_6081519 1040914118816832254214703 := by
  unfold tailWord_6081519
  simp only [CollatzResearch.WordTrace]
  refine ⟨221811220454702778599895611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147874146969801852399930407 221811220454702778599895611)
  ·
    refine ⟨332716830682054167899843417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221811220454702778599895611 332716830682054167899843417)
    ·
      refine ⟨249537623011540625924882563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332716830682054167899843417 249537623011540625924882563)
      ·
        refine ⟨374306434517310938887323845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249537623011540625924882563 374306434517310938887323845)
        ·
          refine ⟨70182456471995801041373221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374306434517310938887323845 70182456471995801041373221)
          ·
            refine ⟨13159210588499212695257479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70182456471995801041373221 13159210588499212695257479)
            ·
              refine ⟨19738815882748819042886219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13159210588499212695257479 19738815882748819042886219)
              ·
                refine ⟨29608223824123228564329329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19738815882748819042886219 29608223824123228564329329)
                ·
                  refine ⟨22206167868092421423246997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29608223824123228564329329 22206167868092421423246997)
                  ·
                    refine ⟨1040914118816832254214703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22206167868092421423246997 1040914118816832254214703)
                    ·
                      rfl

theorem cell23_6081519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_6081519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081519 prefixEnd_6081519 := by exact prefixLift 6081519
  have htrace : WordTrace (prefixWord ++ tailWord_6081519) baseStart_6081519 baseEnd_6081519 := by
    simpa [prefixWord, tailWord_6081519, baseEnd_6081519] using wordTrace_append hprefix tailTrace_6081519
  have hstable : (prefixWord ++ tailWord_6081519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081519).length < 2 ^ (prefixWord ++ tailWord_6081519).sum := by decide
  have hdescent : baseEnd_6081519 < baseStart_6081519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081529 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 2, 4, 3]
def baseStart_6081529 : Nat := 118140960795 + 6081529 * 2 ^ 59
def prefixEnd_6081529 : Nat := 4983230072969 + 3 ^ 40 * 6081529 * 2
def baseEnd_6081529 : Nat := 3122747491257041723519063

theorem tailTrace_6081529 : CollatzResearch.WordTrace tailWord_6081529 prefixEnd_6081529 3122747491257041723519063 := by
  unfold tailWord_6081529
  simp only [CollatzResearch.WordTrace]
  refine ⟨221811585184666550307759641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147874390123111033538506427 221811585184666550307759641)
  ·
    refine ⟨166358688888499912730819731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221811585184666550307759641 166358688888499912730819731)
    ·
      refine ⟨249538033332749869096229597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166358688888499912730819731 249538033332749869096229597)
      ·
        refine ⟨93576762499781200911086099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249538033332749869096229597 93576762499781200911086099)
        ·
          refine ⟨140365143749671801366629149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93576762499781200911086099 140365143749671801366629149)
          ·
            refine ⟨52636928906126925512485931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140365143749671801366629149 52636928906126925512485931)
            ·
              refine ⟨78955393359190388268728897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52636928906126925512485931 78955393359190388268728897)
              ·
                refine ⟨59216545019392791201546673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78955393359190388268728897 59216545019392791201546673)
                ·
                  refine ⟨44412408764544593401160005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59216545019392791201546673 44412408764544593401160005)
                  ·
                    refine ⟨8327326643352111262717501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44412408764544593401160005 8327326643352111262717501)
                    ·
                      refine ⟨3122747491257041723519063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8327326643352111262717501 3122747491257041723519063)
                      ·
                        rfl

theorem cell23_6081529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_6081529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081529 prefixEnd_6081529 := by exact prefixLift 6081529
  have htrace : WordTrace (prefixWord ++ tailWord_6081529) baseStart_6081529 baseEnd_6081529 := by
    simpa [prefixWord, tailWord_6081529, baseEnd_6081529] using wordTrace_append hprefix tailTrace_6081529
  have hstable : (prefixWord ++ tailWord_6081529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081529).length < 2 ^ (prefixWord ++ tailWord_6081529).sum := by decide
  have hdescent : baseEnd_6081529 < baseStart_6081529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081543 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 4, 2, 2]
def baseStart_6081543 : Nat := 118140960795 + 6081543 * 2 ^ 59
def prefixEnd_6081543 : Nat := 4983230072969 + 3 ^ 40 * 6081543 * 2
def baseEnd_6081543 : Nat := 3122754679986204668743999

theorem tailTrace_6081543 : CollatzResearch.WordTrace tailWord_6081543 prefixEnd_6081543 3122754679986204668743999 := by
  unfold tailWord_6081543
  simp only [CollatzResearch.WordTrace]
  refine ⟨221812095806615830698769283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147874730537743887132512855 221812095806615830698769283)
  ·
    refine ⟨332718143709923746048153925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221812095806615830698769283 332718143709923746048153925)
    ·
      refine ⟨62384651945610702384028861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332718143709923746048153925 62384651945610702384028861)
      ·
        refine ⟨23394244479604013394010823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62384651945610702384028861 23394244479604013394010823)
        ·
          refine ⟨35091366719406020091016235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23394244479604013394010823 35091366719406020091016235)
          ·
            refine ⟨52637050079109030136524353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35091366719406020091016235 52637050079109030136524353)
            ·
              refine ⟨39477787559331772602393265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52637050079109030136524353 39477787559331772602393265)
              ·
                refine ⟨29608340669498829451794949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39477787559331772602393265 29608340669498829451794949)
                ·
                  refine ⟨5551563875531030522211553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29608340669498829451794949 5551563875531030522211553)
                  ·
                    refine ⟨4163672906648272891658665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5551563875531030522211553 4163672906648272891658665)
                    ·
                      refine ⟨3122754679986204668743999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163672906648272891658665 3122754679986204668743999)
                      ·
                        rfl

theorem cell23_6081543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_6081543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081543 prefixEnd_6081543 := by exact prefixLift 6081543
  have htrace : WordTrace (prefixWord ++ tailWord_6081543) baseStart_6081543 baseEnd_6081543 := by
    simpa [prefixWord, tailWord_6081543, baseEnd_6081543] using wordTrace_append hprefix tailTrace_6081543
  have hstable : (prefixWord ++ tailWord_6081543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081543).length < 2 ^ (prefixWord ++ tailWord_6081543).sum := by decide
  have hdescent : baseEnd_6081543 < baseStart_6081543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081560 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 2, 2, 2]
def baseStart_6081560 : Nat := 118140960795 + 6081560 * 2 ^ 59
def prefixEnd_6081560 : Nat := 4983230072969 + 3 ^ 40 * 6081560 * 2
def baseEnd_6081560 : Nat := 3122763409157331102231421

theorem tailTrace_6081560 : CollatzResearch.WordTrace tailWord_6081560 prefixEnd_6081560 3122763409157331102231421 := by
  unfold tailWord_6081560
  simp only [CollatzResearch.WordTrace]
  refine ⟨110906357923777121301069067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147875143898369495068092089 110906357923777121301069067)
  ·
    refine ⟨166359536885665681951603601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110906357923777121301069067 166359536885665681951603601)
    ·
      refine ⟨124769652664249261463702701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166359536885665681951603601 124769652664249261463702701)
      ·
        refine ⟨46788619749093473048888513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124769652664249261463702701 46788619749093473048888513)
        ·
          refine ⟨35091464811820104786666385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46788619749093473048888513 35091464811820104786666385)
          ·
            refine ⟨26318598608865078589999789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35091464811820104786666385 26318598608865078589999789)
            ·
              refine ⟨9869474478324404471249921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26318598608865078589999789 9869474478324404471249921)
              ·
                refine ⟨7402105858743303353437441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9869474478324404471249921 7402105858743303353437441)
                ·
                  refine ⟨5551579394057477515078081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7402105858743303353437441 5551579394057477515078081)
                  ·
                    refine ⟨4163684545543108136308561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5551579394057477515078081 4163684545543108136308561)
                    ·
                      refine ⟨3122763409157331102231421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163684545543108136308561 3122763409157331102231421)
                      ·
                        rfl

theorem cell23_6081560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_6081560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081560 prefixEnd_6081560 := by exact prefixLift 6081560
  have htrace : WordTrace (prefixWord ++ tailWord_6081560) baseStart_6081560 baseEnd_6081560 := by
    simpa [prefixWord, tailWord_6081560, baseEnd_6081560] using wordTrace_append hprefix tailTrace_6081560
  have hstable : (prefixWord ++ tailWord_6081560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081560).length < 2 ^ (prefixWord ++ tailWord_6081560).sum := by decide
  have hdescent : baseEnd_6081560 < baseStart_6081560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081589 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_6081589 : Nat := 118140960795 + 6081589 * 2 ^ 59
def prefixEnd_6081589 : Nat := 4983230072969 + 3 ^ 40 * 6081589 * 2
def baseEnd_6081589 : Nat := 3122778300096311488768787

theorem tailTrace_6081589 : CollatzResearch.WordTrace tailWord_6081589 prefixEnd_6081589 3122778300096311488768787 := by
  unfold tailWord_6081589
  simp only [CollatzResearch.WordTrace]
  refine ⟨221813773564449180554943821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147875849042966120369962547 221813773564449180554943821)
  ·
    refine ⟨83180165086668442708103933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221813773564449180554943821 83180165086668442708103933)
    ·
      refine ⟨31192561907500666015538975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83180165086668442708103933 31192561907500666015538975)
      ·
        refine ⟨46788842861250999023308463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31192561907500666015538975 46788842861250999023308463)
        ·
          refine ⟨70183264291876498534962695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46788842861250999023308463 70183264291876498534962695)
          ·
            refine ⟨105274896437814747802444043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70183264291876498534962695 105274896437814747802444043)
            ·
              refine ⟨157912344656722121703666065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105274896437814747802444043 157912344656722121703666065)
              ·
                refine ⟨118434258492541591277749549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157912344656722121703666065 118434258492541591277749549)
                ·
                  refine ⟨44412846934703096729156081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118434258492541591277749549 44412846934703096729156081)
                  ·
                    refine ⟨33309635201027322546867061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44412846934703096729156081 33309635201027322546867061)
                    ·
                      refine ⟨3122778300096311488768787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33309635201027322546867061 3122778300096311488768787)
                      ·
                        rfl

theorem cell23_6081589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_6081589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081589 prefixEnd_6081589 := by exact prefixLift 6081589
  have htrace : WordTrace (prefixWord ++ tailWord_6081589) baseStart_6081589 baseEnd_6081589 := by
    simpa [prefixWord, tailWord_6081589, baseEnd_6081589] using wordTrace_append hprefix tailTrace_6081589
  have hstable : (prefixWord ++ tailWord_6081589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081589).length < 2 ^ (prefixWord ++ tailWord_6081589).sum := by decide
  have hdescent : baseEnd_6081589 < baseStart_6081589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081613 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_6081613 : Nat := 118140960795 + 6081613 * 2 ^ 59
def prefixEnd_6081613 : Nat := 4983230072969 + 3 ^ 40 * 6081613 * 2
def baseEnd_6081613 : Nat := 1040930207877339798289559

theorem tailTrace_6081613 : CollatzResearch.WordTrace tailWord_6081613 prefixEnd_6081613 1040930207877339798289559 := by
  unfold tailWord_6081613
  simp only [CollatzResearch.WordTrace]
  refine ⟨221814648916362232653817493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147876432610908155102544995 221814648916362232653817493)
  ·
    refine ⟨10397561667954479655647695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221814648916362232653817493 10397561667954479655647695)
    ·
      refine ⟨15596342501931719483471543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10397561667954479655647695 15596342501931719483471543)
      ·
        refine ⟨23394513752897579225207315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15596342501931719483471543 23394513752897579225207315)
        ·
          refine ⟨35091770629346368837810973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23394513752897579225207315 35091770629346368837810973)
          ·
            refine ⟨13159413986004888314179115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35091770629346368837810973 13159413986004888314179115)
            ·
              refine ⟨19739120979007332471268673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13159413986004888314179115 19739120979007332471268673)
              ·
                refine ⟨14804340734255499353451505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19739120979007332471268673 14804340734255499353451505)
                ·
                  refine ⟨11103255550691624515088629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14804340734255499353451505 11103255550691624515088629)
                  ·
                    refine ⟨1040930207877339798289559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11103255550691624515088629 1040930207877339798289559)
                    ·
                      rfl

theorem cell23_6081613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_6081613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081613 prefixEnd_6081613 := by exact prefixLift 6081613
  have htrace : WordTrace (prefixWord ++ tailWord_6081613) baseStart_6081613 baseEnd_6081613 := by
    simpa [prefixWord, tailWord_6081613, baseEnd_6081613] using wordTrace_append hprefix tailTrace_6081613
  have hstable : (prefixWord ++ tailWord_6081613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081613).length < 2 ^ (prefixWord ++ tailWord_6081613).sum := by decide
  have hdescent : baseEnd_6081613 < baseStart_6081613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081616 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 4, 4, 2]
def baseStart_6081616 : Nat := 118140960795 + 6081616 * 2 ^ 59
def prefixEnd_6081616 : Nat := 4983230072969 + 3 ^ 40 * 6081616 * 2
def baseEnd_6081616 : Nat := 3122792164073982883131163

theorem tailTrace_6081616 : CollatzResearch.WordTrace tailWord_6081616 prefixEnd_6081616 3122792164073982883131163 := by
  unfold tailWord_6081616
  simp only [CollatzResearch.WordTrace]
  refine ⟨110907379167675682083088351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147876505556900909444117801 110907379167675682083088351)
  ·
    refine ⟨166361068751513523124632527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110907379167675682083088351 166361068751513523124632527)
    ·
      refine ⟨249541603127270284686948791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166361068751513523124632527 249541603127270284686948791)
      ·
        refine ⟨374312404690905427030423187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249541603127270284686948791 374312404690905427030423187)
        ·
          refine ⟨561468607036358140545634781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374312404690905427030423187 561468607036358140545634781)
          ·
            refine ⟨210550727638634302704613043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 561468607036358140545634781 210550727638634302704613043)
            ·
              refine ⟨315826091457951454056919565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210550727638634302704613043 315826091457951454056919565)
              ·
                refine ⟨118434784296731795271344837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315826091457951454056919565 118434784296731795271344837)
                ·
                  refine ⟨22206522055637211613377157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118434784296731795271344837 22206522055637211613377157)
                  ·
                    refine ⟨4163722885431977177508217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22206522055637211613377157 4163722885431977177508217)
                    ·
                      refine ⟨3122792164073982883131163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163722885431977177508217 3122792164073982883131163)
                      ·
                        rfl

theorem cell23_6081616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 4, 2].length) (baseStart_6081616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081616 prefixEnd_6081616 := by exact prefixLift 6081616
  have htrace : WordTrace (prefixWord ++ tailWord_6081616) baseStart_6081616 baseEnd_6081616 := by
    simpa [prefixWord, tailWord_6081616, baseEnd_6081616] using wordTrace_append hprefix tailTrace_6081616
  have hstable : (prefixWord ++ tailWord_6081616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081616).length < 2 ^ (prefixWord ++ tailWord_6081616).sum := by decide
  have hdescent : baseEnd_6081616 < baseStart_6081616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081626 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_6081626 : Nat := 118140960795 + 6081626 * 2 ^ 59
def prefixEnd_6081626 : Nat := 4983230072969 + 3 ^ 40 * 6081626 * 2
def baseEnd_6081626 : Nat := 1040932432960175948002039

theorem tailTrace_6081626 : CollatzResearch.WordTrace tailWord_6081626 prefixEnd_6081626 1040932432960175948002039 := by
  unfold tailWord_6081626
  simp only [CollatzResearch.WordTrace]
  refine ⟨55453780766328783968510183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147876748710210090582693821 55453780766328783968510183)
  ·
    refine ⟨83180671149493175952765275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55453780766328783968510183 83180671149493175952765275)
    ·
      refine ⟨124771006724239763929147913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83180671149493175952765275 124771006724239763929147913)
      ·
        refine ⟨93578255043179822946860935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124771006724239763929147913 93578255043179822946860935)
        ·
          refine ⟨140367382564769734420291403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93578255043179822946860935 140367382564769734420291403)
          ·
            refine ⟨210551073847154601630437105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140367382564769734420291403 210551073847154601630437105)
            ·
              refine ⟨157913305385365951222827829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210551073847154601630437105 157913305385365951222827829)
              ·
                refine ⟨14804372379878057927140109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157913305385365951222827829 14804372379878057927140109)
                ·
                  refine ⟨5551639642454271722677541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14804372379878057927140109 5551639642454271722677541)
                  ·
                    refine ⟨1040932432960175948002039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5551639642454271722677541 1040932432960175948002039)
                    ·
                      rfl

theorem cell23_6081626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_6081626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081626 prefixEnd_6081626 := by exact prefixLift 6081626
  have htrace : WordTrace (prefixWord ++ tailWord_6081626) baseStart_6081626 baseEnd_6081626 := by
    simpa [prefixWord, tailWord_6081626, baseEnd_6081626] using wordTrace_append hprefix tailTrace_6081626
  have hstable : (prefixWord ++ tailWord_6081626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081626).length < 2 ^ (prefixWord ++ tailWord_6081626).sum := by decide
  have hdescent : baseEnd_6081626 < baseStart_6081626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081636 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_6081636 : Nat := 118140960795 + 6081636 * 2 ^ 59
def prefixEnd_6081636 : Nat := 4983230072969 + 3 ^ 40 * 6081636 * 2
def baseEnd_6081636 : Nat := 3122802433687072804881071

theorem tailTrace_6081636 : CollatzResearch.WordTrace tailWord_6081636 prefixEnd_6081636 3122802433687072804881071 := by
  unfold tailWord_6081636
  simp only [CollatzResearch.WordTrace]
  refine ⟨110907743897639453790952381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147876991863519271721269841 110907743897639453790952381)
  ·
    refine ⟨41590403961614795171607143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110907743897639453790952381 41590403961614795171607143)
    ·
      refine ⟨62385605942422192757410715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41590403961614795171607143 62385605942422192757410715)
      ·
        refine ⟨93578408913633289136116073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62385605942422192757410715 93578408913633289136116073)
        ·
          refine ⟨70183806685224966852087055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93578408913633289136116073 70183806685224966852087055)
          ·
            refine ⟨105275710027837450278130583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70183806685224966852087055 105275710027837450278130583)
            ·
              refine ⟨157913565041756175417195875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105275710027837450278130583 157913565041756175417195875)
              ·
                refine ⟨236870347562634263125793813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157913565041756175417195875 236870347562634263125793813)
                ·
                  refine ⟨11103297541998481084021585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 236870347562634263125793813 11103297541998481084021585)
                  ·
                    refine ⟨8327473156498860813016189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11103297541998481084021585 8327473156498860813016189)
                    ·
                      refine ⟨3122802433687072804881071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8327473156498860813016189 3122802433687072804881071)
                      ·
                        rfl

theorem cell23_6081636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_6081636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081636 prefixEnd_6081636 := by exact prefixLift 6081636
  have htrace : WordTrace (prefixWord ++ tailWord_6081636) baseStart_6081636 baseEnd_6081636 := by
    simpa [prefixWord, tailWord_6081636, baseEnd_6081636] using wordTrace_append hprefix tailTrace_6081636
  have hstable : (prefixWord ++ tailWord_6081636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081636).length < 2 ^ (prefixWord ++ tailWord_6081636).sum := by decide
  have hdescent : baseEnd_6081636 < baseStart_6081636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081693 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_6081693 : Nat := 118140960795 + 6081693 * 2 ^ 59
def prefixEnd_6081693 : Nat := 4983230072969 + 3 ^ 40 * 6081693 * 2
def baseEnd_6081693 : Nat := 3122831702084379081868309

theorem tailTrace_6081693 : CollatzResearch.WordTrace tailWord_6081693 prefixEnd_6081693 3122831702084379081868309 := by
  unfold tailWord_6081693
  simp only [CollatzResearch.WordTrace]
  refine ⟨221817566756072406316729733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147878377837381604211153155 221817566756072406316729733)
  ·
    refine ⟨41590793766763576184386825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221817566756072406316729733 41590793766763576184386825)
    ·
      refine ⟨31193095325072682138290119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41590793766763576184386825 31193095325072682138290119)
      ·
        refine ⟨46789642987609023207435179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31193095325072682138290119 46789642987609023207435179)
        ·
          refine ⟨70184464481413534811152769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46789642987609023207435179 70184464481413534811152769)
          ·
            refine ⟨52638348361060151108364577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70184464481413534811152769 52638348361060151108364577)
            ·
              refine ⟨39478761270795113331273433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52638348361060151108364577 39478761270795113331273433)
              ·
                refine ⟨29609070953096334998455075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39478761270795113331273433 29609070953096334998455075)
                ·
                  refine ⟨44413606429644502497682613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29609070953096334998455075 44413606429644502497682613)
                  ·
                    refine ⟨4163775602779172109157745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44413606429644502497682613 4163775602779172109157745)
                    ·
                      refine ⟨3122831702084379081868309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163775602779172109157745 3122831702084379081868309)
                      ·
                        rfl

theorem cell23_6081693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_6081693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081693 prefixEnd_6081693 := by exact prefixLift 6081693
  have htrace : WordTrace (prefixWord ++ tailWord_6081693) baseStart_6081693 baseEnd_6081693 := by
    simpa [prefixWord, tailWord_6081693, baseEnd_6081693] using wordTrace_append hprefix tailTrace_6081693
  have hstable : (prefixWord ++ tailWord_6081693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081693).length < 2 ^ (prefixWord ++ tailWord_6081693).sum := by decide
  have hdescent : baseEnd_6081693 < baseStart_6081693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081700 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_6081700 : Nat := 118140960795 + 6081700 * 2 ^ 59
def prefixEnd_6081700 : Nat := 4983230072969 + 3 ^ 40 * 6081700 * 2
def baseEnd_6081700 : Nat := 3122835296448960554480777

theorem tailTrace_6081700 : CollatzResearch.WordTrace tailWord_6081700 prefixEnd_6081700 3122835296448960554480777 := by
  unfold tailWord_6081700
  simp only [CollatzResearch.WordTrace]
  refine ⟨110908911033523523256117277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147878548044698031008156369 110908911033523523256117277)
  ·
    refine ⟨41590841637571321221043979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110908911033523523256117277 41590841637571321221043979)
    ·
      refine ⟨62386262456356981831565969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41590841637571321221043979 62386262456356981831565969)
      ·
        refine ⟨46789696842267736373674477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62386262456356981831565969 46789696842267736373674477)
        ·
          refine ⟨17546136315850401140127929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46789696842267736373674477 17546136315850401140127929)
          ·
            refine ⟨13159602236887800855095947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17546136315850401140127929 13159602236887800855095947)
            ·
              refine ⟨19739403355331701282643921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13159602236887800855095947 19739403355331701282643921)
              ·
                refine ⟨14804552516498775961982941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19739403355331701282643921 14804552516498775961982941)
                ·
                  refine ⟨5551707193687040985743603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14804552516498775961982941 5551707193687040985743603)
                  ·
                    refine ⟨8327560790530561478615405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5551707193687040985743603 8327560790530561478615405)
                    ·
                      refine ⟨3122835296448960554480777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8327560790530561478615405 3122835296448960554480777)
                      ·
                        rfl

theorem cell23_6081700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_6081700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081700 prefixEnd_6081700 := by exact prefixLift 6081700
  have htrace : WordTrace (prefixWord ++ tailWord_6081700) baseStart_6081700 baseEnd_6081700 := by
    simpa [prefixWord, tailWord_6081700, baseEnd_6081700] using wordTrace_append hprefix tailTrace_6081700
  have hstable : (prefixWord ++ tailWord_6081700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081700).length < 2 ^ (prefixWord ++ tailWord_6081700).sum := by decide
  have hdescent : baseEnd_6081700 < baseStart_6081700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081703 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 3, 5]
def baseStart_6081703 : Nat := 118140960795 + 6081703 * 2 ^ 59
def prefixEnd_6081703 : Nat := 4983230072969 + 3 ^ 40 * 6081703 * 2
def baseEnd_6081703 : Nat := 1040945612296974680914421

theorem tailTrace_6081703 : CollatzResearch.WordTrace tailWord_6081703 prefixEnd_6081703 1040945612296974680914421 := by
  unfold tailWord_6081703
  simp only [CollatzResearch.WordTrace]
  refine ⟨221817931486036178024593763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147878620990690785349729175 221817931486036178024593763)
  ·
    refine ⟨332726897229054267036890645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221817931486036178024593763 332726897229054267036890645)
    ·
      refine ⟨15596573307611918767354249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 332726897229054267036890645 15596573307611918767354249)
      ·
        refine ⟨11697429980708939075515687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15596573307611918767354249 11697429980708939075515687)
        ·
          refine ⟨17546144971063408613273531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11697429980708939075515687 17546144971063408613273531)
          ·
            refine ⟨26319217456595112919910297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17546144971063408613273531 26319217456595112919910297)
            ·
              refine ⟨19739413092446334689932723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26319217456595112919910297 19739413092446334689932723)
              ·
                refine ⟨29609119638669502034899085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19739413092446334689932723 29609119638669502034899085)
                ·
                  refine ⟨11103419864501063263087157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29609119638669502034899085 11103419864501063263087157)
                  ·
                    refine ⟨1040945612296974680914421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11103419864501063263087157 1040945612296974680914421)
                    ·
                      rfl

theorem cell23_6081703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_6081703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081703 prefixEnd_6081703 := by exact prefixLift 6081703
  have htrace : WordTrace (prefixWord ++ tailWord_6081703) baseStart_6081703 baseEnd_6081703 := by
    simpa [prefixWord, tailWord_6081703, baseEnd_6081703] using wordTrace_append hprefix tailTrace_6081703
  have hstable : (prefixWord ++ tailWord_6081703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081703).length < 2 ^ (prefixWord ++ tailWord_6081703).sum := by decide
  have hdescent : baseEnd_6081703 < baseStart_6081703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081736 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_6081736 : Nat := 118140960795 + 6081736 * 2 ^ 59
def prefixEnd_6081736 : Nat := 4983230072969 + 3 ^ 40 * 6081736 * 2
def baseEnd_6081736 : Nat := 3122853781752522413630611

theorem tailTrace_6081736 : CollatzResearch.WordTrace tailWord_6081736 prefixEnd_6081736 3122853781752522413630611 := by
  unfold tailWord_6081736
  simp only [CollatzResearch.WordTrace]
  refine ⟨110909567547458312330272531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147879423396611083107030041 110909567547458312330272531)
  ·
    refine ⟨166364351321187468495408797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110909567547458312330272531 166364351321187468495408797)
    ·
      refine ⟨62386631745445300685778299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166364351321187468495408797 62386631745445300685778299)
      ·
        refine ⟨93579947618167951028667449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62386631745445300685778299 93579947618167951028667449)
        ·
          refine ⟨70184960713625963271500587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93579947618167951028667449 70184960713625963271500587)
          ·
            refine ⟨105277441070438944907250881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70184960713625963271500587 105277441070438944907250881)
            ·
              refine ⟨78958080802829208680438161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105277441070438944907250881 78958080802829208680438161)
              ·
                refine ⟨59218560602121906510328621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78958080802829208680438161 59218560602121906510328621)
                ·
                  refine ⟨22206960225795714941373233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59218560602121906510328621 22206960225795714941373233)
                  ·
                    refine ⟨16655220169346786206029925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22206960225795714941373233 16655220169346786206029925)
                    ·
                      refine ⟨3122853781752522413630611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16655220169346786206029925 3122853781752522413630611)
                      ·
                        rfl

theorem cell23_6081736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_6081736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081736 prefixEnd_6081736 := by exact prefixLift 6081736
  have htrace : WordTrace (prefixWord ++ tailWord_6081736) baseStart_6081736 baseEnd_6081736 := by
    simpa [prefixWord, tailWord_6081736, baseEnd_6081736] using wordTrace_append hprefix tailTrace_6081736
  have hstable : (prefixWord ++ tailWord_6081736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081736).length < 2 ^ (prefixWord ++ tailWord_6081736).sum := by decide
  have hdescent : baseEnd_6081736 < baseStart_6081736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081746 : List Nat := [3, 2, 2, 2, 1, 1, 2, 10]
def baseStart_6081746 : Nat := 118140960795 + 6081746 * 2 ^ 59
def prefixEnd_6081746 : Nat := 4983230072969 + 3 ^ 40 * 6081746 * 2
def baseEnd_6081746 : Nat := 115661441354039532389095

theorem tailTrace_6081746 : CollatzResearch.WordTrace tailWord_6081746 prefixEnd_6081746 115661441354039532389095 := by
  unfold tailWord_6081746
  simp only [CollatzResearch.WordTrace]
  refine ⟨55454874956220099092102273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147879666549920264245606061 55454874956220099092102273)
  ·
    refine ⟨41591156217165074319076705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55454874956220099092102273 41591156217165074319076705)
    ·
      refine ⟨31193367162873805739307529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41591156217165074319076705 31193367162873805739307529)
      ·
        refine ⟨23395025372155354304480647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31193367162873805739307529 23395025372155354304480647)
        ·
          refine ⟨35092538058233031456720971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23395025372155354304480647 35092538058233031456720971)
          ·
            refine ⟨52638807087349547185081457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35092538058233031456720971 52638807087349547185081457)
            ·
              refine ⟨39479105315512160388811093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52638807087349547185081457 39479105315512160388811093)
              ·
                refine ⟨115661441354039532389095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39479105315512160388811093 115661441354039532389095)
                ·
                  rfl

theorem cell23_6081746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 10].length) (baseStart_6081746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081746 prefixEnd_6081746 := by exact prefixLift 6081746
  have htrace : WordTrace (prefixWord ++ tailWord_6081746) baseStart_6081746 baseEnd_6081746 := by
    simpa [prefixWord, tailWord_6081746, baseEnd_6081746] using wordTrace_append hprefix tailTrace_6081746
  have hstable : (prefixWord ++ tailWord_6081746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081746).length < 2 ^ (prefixWord ++ tailWord_6081746).sum := by decide
  have hdescent : baseEnd_6081746 < baseStart_6081746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081757 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_6081757 : Nat := 118140960795 + 6081757 * 2 ^ 59
def prefixEnd_6081757 : Nat := 4983230072969 + 3 ^ 40 * 6081757 * 2
def baseEnd_6081757 : Nat := 3122864564846266831468015

theorem tailTrace_6081757 : CollatzResearch.WordTrace tailWord_6081757 prefixEnd_6081757 3122864564846266831468015 := by
  unfold tailWord_6081757
  simp only [CollatzResearch.WordTrace]
  refine ⟨221819901027840545247059525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147879934018560363498039683 221819901027840545247059525)
  ·
    refine ⟨41591231442720102233823661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221819901027840545247059525 41591231442720102233823661)
    ·
      refine ⟨15596711791020038337683873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41591231442720102233823661 15596711791020038337683873)
      ·
        refine ⟨11697533843265028753262905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15596711791020038337683873 11697533843265028753262905)
        ·
          refine ⟨8773150382448771564947179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11697533843265028753262905 8773150382448771564947179)
          ·
            refine ⟨13159725573673157347420769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8773150382448771564947179 13159725573673157347420769)
            ·
              refine ⟨9869794180254868010565577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13159725573673157347420769 9869794180254868010565577)
              ·
                refine ⟨7402345635191151007924183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9869794180254868010565577 7402345635191151007924183)
                ·
                  refine ⟨11103518452786726511886275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7402345635191151007924183 11103518452786726511886275)
                  ·
                    refine ⟨16655277679180089767829413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11103518452786726511886275 16655277679180089767829413)
                    ·
                      refine ⟨3122864564846266831468015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16655277679180089767829413 3122864564846266831468015)
                      ·
                        rfl

theorem cell23_6081757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_6081757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081757 prefixEnd_6081757 := by exact prefixLift 6081757
  have htrace : WordTrace (prefixWord ++ tailWord_6081757) baseStart_6081757 baseEnd_6081757 := by
    simpa [prefixWord, tailWord_6081757, baseEnd_6081757] using wordTrace_append hprefix tailTrace_6081757
  have hstable : (prefixWord ++ tailWord_6081757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081757).length < 2 ^ (prefixWord ++ tailWord_6081757).sum := by decide
  have hdescent : baseEnd_6081757 < baseStart_6081757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081760 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 3]
def baseStart_6081760 : Nat := 118140960795 + 6081760 * 2 ^ 59
def prefixEnd_6081760 : Nat := 4983230072969 + 3 ^ 40 * 6081760 * 2
def baseEnd_6081760 : Nat := 3122866105288230319730501

theorem tailTrace_6081760 : CollatzResearch.WordTrace tailWord_6081760 prefixEnd_6081760 3122866105288230319730501 := by
  unfold tailWord_6081760
  simp only [CollatzResearch.WordTrace]
  refine ⟨110910005223414838379709367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147880006964553117839612489 110910005223414838379709367)
  ·
    refine ⟨166365007835122257569564051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110910005223414838379709367 166365007835122257569564051)
    ·
      refine ⟨249547511752683386354346077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166365007835122257569564051 249547511752683386354346077)
      ·
        refine ⟨93580316907256269882879779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249547511752683386354346077 93580316907256269882879779)
        ·
          refine ⟨140370475360884404824319669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93580316907256269882879779 140370475360884404824319669)
          ·
            refine ⟨13159732065082912952279969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140370475360884404824319669 13159732065082912952279969)
            ·
              refine ⟨9869799048812184714209977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13159732065082912952279969 9869799048812184714209977)
              ·
                refine ⟨7402349286609138535657483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9869799048812184714209977 7402349286609138535657483)
                ·
                  refine ⟨11103523929913707803486225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7402349286609138535657483 11103523929913707803486225)
                  ·
                    refine ⟨8327642947435280852614669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11103523929913707803486225 8327642947435280852614669)
                    ·
                      refine ⟨3122866105288230319730501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8327642947435280852614669 3122866105288230319730501)
                      ·
                        rfl

theorem cell23_6081760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_6081760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081760 prefixEnd_6081760 := by exact prefixLift 6081760
  have htrace : WordTrace (prefixWord ++ tailWord_6081760) baseStart_6081760 baseEnd_6081760 := by
    simpa [prefixWord, tailWord_6081760, baseEnd_6081760] using wordTrace_append hprefix tailTrace_6081760
  have hstable : (prefixWord ++ tailWord_6081760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081760).length < 2 ^ (prefixWord ++ tailWord_6081760).sum := by decide
  have hdescent : baseEnd_6081760 < baseStart_6081760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081774 : List Nat := [4, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_6081774 : Nat := 118140960795 + 6081774 * 2 ^ 59
def prefixEnd_6081774 : Nat := 4983230072969 + 3 ^ 40 * 6081774 * 2
def baseEnd_6081774 : Nat := 3122873294017393264955437

theorem tailTrace_6081774 : CollatzResearch.WordTrace tailWord_6081774 prefixEnd_6081774 3122873294017393264955437 := by
  unfold tailWord_6081774
  simp only [CollatzResearch.WordTrace]
  refine ⟨27727565133597369643803547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147880347379185971433618917 27727565133597369643803547)
  ·
    refine ⟨41591347700396054465705321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27727565133597369643803547 41591347700396054465705321)
    ·
      refine ⟨31193510775297040849278991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41591347700396054465705321 31193510775297040849278991)
      ·
        refine ⟨46790266162945561273918487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31193510775297040849278991 46790266162945561273918487)
        ·
          refine ⟨70185399244418341910877731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46790266162945561273918487 70185399244418341910877731)
          ·
            refine ⟨105278098866627512866316597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70185399244418341910877731 105278098866627512866316597)
            ·
              refine ⟨9869821768746329331217181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105278098866627512866316597 9869821768746329331217181)
              ·
                refine ⟨3701183163279873499206443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9869821768746329331217181 3701183163279873499206443)
                ·
                  refine ⟨5551774744919810248809665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701183163279873499206443 5551774744919810248809665)
                  ·
                    refine ⟨4163831058689857686607249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5551774744919810248809665 4163831058689857686607249)
                    ·
                      refine ⟨3122873294017393264955437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163831058689857686607249 3122873294017393264955437)
                      ·
                        rfl

theorem cell23_6081774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_6081774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081774 prefixEnd_6081774 := by exact prefixLift 6081774
  have htrace : WordTrace (prefixWord ++ tailWord_6081774) baseStart_6081774 baseEnd_6081774 := by
    simpa [prefixWord, tailWord_6081774, baseEnd_6081774] using wordTrace_append hprefix tailTrace_6081774
  have hstable : (prefixWord ++ tailWord_6081774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081774).length < 2 ^ (prefixWord ++ tailWord_6081774).sum := by decide
  have hdescent : baseEnd_6081774 < baseStart_6081774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081786 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_6081786 : Nat := 118140960795 + 6081786 * 2 ^ 59
def prefixEnd_6081786 : Nat := 4983230072969 + 3 ^ 40 * 6081786 * 2
def baseEnd_6081786 : Nat := 3122879455785247218005381

theorem tailTrace_6081786 : CollatzResearch.WordTrace tailWord_6081786 prefixEnd_6081786 3122879455785247218005381 := by
  unfold tailWord_6081786
  simp only [CollatzResearch.WordTrace]
  refine ⟨55455239686183870799966303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147880639163156988799910141 55455239686183870799966303)
  ·
    refine ⟨83182859529275806199949455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55455239686183870799966303 83182859529275806199949455)
    ·
      refine ⟨124774289293913709299924183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83182859529275806199949455 124774289293913709299924183)
      ·
        refine ⟨187161433940870563949886275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124774289293913709299924183 187161433940870563949886275)
        ·
          refine ⟨280742150911305845924829413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187161433940870563949886275 280742150911305845924829413)
          ·
            refine ⟨52639153295869846110905515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280742150911305845924829413 52639153295869846110905515)
            ·
              refine ⟨78958729943804769166358273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52639153295869846110905515 78958729943804769166358273)
              ·
                refine ⟨59219047457853576874768705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78958729943804769166358273 59219047457853576874768705)
                ·
                  refine ⟨44414285593390182656076529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59219047457853576874768705 44414285593390182656076529)
                  ·
                    refine ⟨33310714195042636992057397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44414285593390182656076529 33310714195042636992057397)
                    ·
                      refine ⟨3122879455785247218005381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33310714195042636992057397 3122879455785247218005381)
                      ·
                        rfl

theorem cell23_6081786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_6081786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081786 prefixEnd_6081786 := by exact prefixLift 6081786
  have htrace : WordTrace (prefixWord ++ tailWord_6081786) baseStart_6081786 baseEnd_6081786 := by
    simpa [prefixWord, tailWord_6081786, baseEnd_6081786] using wordTrace_append hprefix tailTrace_6081786
  have hstable : (prefixWord ++ tailWord_6081786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081786).length < 2 ^ (prefixWord ++ tailWord_6081786).sum := by decide
  have hdescent : baseEnd_6081786 < baseStart_6081786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081860 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6081860 : Nat := 118140960795 + 6081860 * 2 ^ 59
def prefixEnd_6081860 : Nat := 4983230072969 + 3 ^ 40 * 6081860 * 2
def baseEnd_6081860 : Nat := 3122917453353679928480041

theorem tailTrace_6081860 : CollatzResearch.WordTrace tailWord_6081860 prefixEnd_6081860 3122917453353679928480041 := by
  unfold tailWord_6081860
  simp only [CollatzResearch.WordTrace]
  refine ⟨110911828873233696919029517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147882438497644929225372689 110911828873233696919029517)
  ·
    refine ⟨41591935827462636344636069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110911828873233696919029517 41591935827462636344636069)
    ·
      refine ⟨7798487967649244314619263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41591935827462636344636069 7798487967649244314619263)
      ·
        refine ⟨11697731951473866471928895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7798487967649244314619263 11697731951473866471928895)
        ·
          refine ⟨17546597927210799707893343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11697731951473866471928895 17546597927210799707893343)
          ·
            refine ⟨26319896890816199561840015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17546597927210799707893343 26319896890816199561840015)
            ·
              refine ⟨39479845336224299342760023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26319896890816199561840015 39479845336224299342760023)
              ·
                refine ⟨59219768004336449014140035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39479845336224299342760023 59219768004336449014140035)
                ·
                  refine ⟨88829652006504673521210053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59219768004336449014140035 88829652006504673521210053)
                  ·
                    refine ⟨16655559751219626285226885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88829652006504673521210053 16655559751219626285226885)
                    ·
                      refine ⟨3122917453353679928480041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16655559751219626285226885 3122917453353679928480041)
                      ·
                        rfl

theorem cell23_6081860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6081860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081860 prefixEnd_6081860 := by exact prefixLift 6081860
  have htrace : WordTrace (prefixWord ++ tailWord_6081860) baseStart_6081860 baseEnd_6081860 := by
    simpa [prefixWord, tailWord_6081860, baseEnd_6081860] using wordTrace_append hprefix tailTrace_6081860
  have hstable : (prefixWord ++ tailWord_6081860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081860).length < 2 ^ (prefixWord ++ tailWord_6081860).sum := by decide
  have hdescent : baseEnd_6081860 < baseStart_6081860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081863 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_6081863 : Nat := 118140960795 + 6081863 * 2 ^ 59
def prefixEnd_6081863 : Nat := 4983230072969 + 3 ^ 40 * 6081863 * 2
def baseEnd_6081863 : Nat := 3122918993795643416742527

theorem tailTrace_6081863 : CollatzResearch.WordTrace tailWord_6081863 prefixEnd_6081863 3122918993795643416742527 := by
  unfold tailWord_6081863
  simp only [CollatzResearch.WordTrace]
  refine ⟨221823767165456525350418243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147882511443637683566945495 221823767165456525350418243)
  ·
    refine ⟨332735650748184788025627365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221823767165456525350418243 332735650748184788025627365)
    ·
      refine ⟨62387934515284647754805131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332735650748184788025627365 62387934515284647754805131)
      ·
        refine ⟨93581901772926971632207697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62387934515284647754805131 93581901772926971632207697)
        ·
          refine ⟨70186426329695228724155773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93581901772926971632207697 70186426329695228724155773)
          ·
            refine ⟨26319909873635710771558415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70186426329695228724155773 26319909873635710771558415)
            ·
              refine ⟨39479864810453566157337623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26319909873635710771558415 39479864810453566157337623)
              ·
                refine ⟨59219797215680349236006435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39479864810453566157337623 59219797215680349236006435)
                ·
                  refine ⟨88829695823520523854009653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59219797215680349236006435 88829695823520523854009653)
                  ·
                    refine ⟨8327783983455049111313405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88829695823520523854009653 8327783983455049111313405)
                    ·
                      refine ⟨3122918993795643416742527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8327783983455049111313405 3122918993795643416742527)
                      ·
                        rfl

theorem cell23_6081863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_6081863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081863 prefixEnd_6081863 := by exact prefixLift 6081863
  have htrace : WordTrace (prefixWord ++ tailWord_6081863) baseStart_6081863 baseEnd_6081863 := by
    simpa [prefixWord, tailWord_6081863, baseEnd_6081863] using wordTrace_append hprefix tailTrace_6081863
  have hstable : (prefixWord ++ tailWord_6081863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081863).length < 2 ^ (prefixWord ++ tailWord_6081863).sum := by decide
  have hdescent : baseEnd_6081863 < baseStart_6081863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081885 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6081885 : Nat := 118140960795 + 6081885 * 2 ^ 59
def prefixEnd_6081885 : Nat := 4983230072969 + 3 ^ 40 * 6081885 * 2
def baseEnd_6081885 : Nat := 3122930290370042330667427

theorem tailTrace_6081885 : CollatzResearch.WordTrace tailWord_6081885 prefixEnd_6081885 3122930290370042330667427 := by
  unfold tailWord_6081885
  simp only [CollatzResearch.WordTrace]
  refine ⟨221824569571376823107719109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147883046380917882071812739 221824569571376823107719109)
  ·
    refine ⟨41592106794633154332697333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221824569571376823107719109 41592106794633154332697333)
    ·
      refine ⟨3899260011996858218690375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41592106794633154332697333 3899260011996858218690375)
      ·
        refine ⟨5848890017995287328035563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3899260011996858218690375 5848890017995287328035563)
        ·
          refine ⟨8773335026992930992053345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848890017995287328035563 8773335026992930992053345)
          ·
            refine ⟨6580001270244698244040009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8773335026992930992053345 6580001270244698244040009)
            ·
              refine ⟨4935000952683523683030007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6580001270244698244040009 4935000952683523683030007)
              ·
                refine ⟨7402501429025285524545011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935000952683523683030007 7402501429025285524545011)
                ·
                  refine ⟨11103752143537928286817517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7402501429025285524545011 11103752143537928286817517)
                  ·
                    refine ⟨4163907053826723107556569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11103752143537928286817517 4163907053826723107556569)
                    ·
                      refine ⟨3122930290370042330667427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163907053826723107556569 3122930290370042330667427)
                      ·
                        rfl

theorem cell23_6081885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6081885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081885 prefixEnd_6081885 := by exact prefixLift 6081885
  have htrace : WordTrace (prefixWord ++ tailWord_6081885) baseStart_6081885 baseEnd_6081885 := by
    simpa [prefixWord, tailWord_6081885, baseEnd_6081885] using wordTrace_append hprefix tailTrace_6081885
  have hstable : (prefixWord ++ tailWord_6081885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081885).length < 2 ^ (prefixWord ++ tailWord_6081885).sum := by decide
  have hdescent : baseEnd_6081885 < baseStart_6081885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081898 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_6081898 : Nat := 118140960795 + 6081898 * 2 ^ 59
def prefixEnd_6081898 : Nat := 4983230072969 + 3 ^ 40 * 6081898 * 2
def baseEnd_6081898 : Nat := 3122936965618550779804867

theorem tailTrace_6081898 : CollatzResearch.WordTrace tailWord_6081898 prefixEnd_6081898 3122936965618550779804867 := by
  unfold tailWord_6081898
  simp only [CollatzResearch.WordTrace]
  refine ⟨55456260930082431581985587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147883362480219817551961565 55456260930082431581985587)
  ·
    refine ⟨83184391395123647372978381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55456260930082431581985587 83184391395123647372978381)
    ·
      refine ⟨31194146773171367764866893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83184391395123647372978381 31194146773171367764866893)
      ·
        refine ⟨11697805039939262911825085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31194146773171367764866893 11697805039939262911825085)
        ·
          refine ⟨4386676889977223591934407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11697805039939262911825085 4386676889977223591934407)
          ·
            refine ⟨6580015334965835387901611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386676889977223591934407 6580015334965835387901611)
            ·
              refine ⟨9870023002448753081852417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580015334965835387901611 9870023002448753081852417)
              ·
                refine ⟨7402517251836564811389313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9870023002448753081852417 7402517251836564811389313)
                ·
                  refine ⟨5551887938877423608541985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7402517251836564811389313 5551887938877423608541985)
                  ·
                    refine ⟨4163915954158067706406489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5551887938877423608541985 4163915954158067706406489)
                    ·
                      refine ⟨3122936965618550779804867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4163915954158067706406489 3122936965618550779804867)
                      ·
                        rfl

theorem cell23_6081898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_6081898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081898 prefixEnd_6081898 := by exact prefixLift 6081898
  have htrace : WordTrace (prefixWord ++ tailWord_6081898) baseStart_6081898 baseEnd_6081898 := by
    simpa [prefixWord, tailWord_6081898, baseEnd_6081898] using wordTrace_append hprefix tailTrace_6081898
  have hstable : (prefixWord ++ tailWord_6081898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081898).length < 2 ^ (prefixWord ++ tailWord_6081898).sum := by decide
  have hdescent : baseEnd_6081898 < baseStart_6081898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6081903 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 4]
def baseStart_6081903 : Nat := 118140960795 + 6081903 * 2 ^ 59
def prefixEnd_6081903 : Nat := 4983230072969 + 3 ^ 40 * 6081903 * 2
def baseEnd_6081903 : Nat := 3122939533021823260242343

theorem tailTrace_6081903 : CollatzResearch.WordTrace tailWord_6081903 prefixEnd_6081903 3122939533021823260242343 := by
  unfold tailWord_6081903
  simp only [CollatzResearch.WordTrace]
  refine ⟨221825226085311612181874363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147883484056874408121249575 221825226085311612181874363)
  ·
    refine ⟨332737839127967418272811545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221825226085311612181874363 332737839127967418272811545)
    ·
      refine ⟨249553379345975563704608659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332737839127967418272811545 249553379345975563704608659)
      ·
        refine ⟨374330069018963345556912989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249553379345975563704608659 374330069018963345556912989)
        ·
          refine ⟨140373775882111254583842371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374330069018963345556912989 140373775882111254583842371)
          ·
            refine ⟨210560663823166881875763557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140373775882111254583842371 210560663823166881875763557)
            ·
              refine ⟨39480124466843790351705667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210560663823166881875763557 39480124466843790351705667)
              ·
                refine ⟨59220186700265685527558501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39480124466843790351705667 59220186700265685527558501)
                ·
                  refine ⟨11103785006299816036417219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59220186700265685527558501 11103785006299816036417219)
                  ·
                    refine ⟨16655677509449724054625829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11103785006299816036417219 16655677509449724054625829)
                    ·
                      refine ⟨3122939533021823260242343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16655677509449724054625829 3122939533021823260242343)
                      ·
                        rfl

theorem cell23_6081903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_6081903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6081903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6081903 prefixEnd_6081903 := by exact prefixLift 6081903
  have htrace : WordTrace (prefixWord ++ tailWord_6081903) baseStart_6081903 baseEnd_6081903 := by
    simpa [prefixWord, tailWord_6081903, baseEnd_6081903] using wordTrace_append hprefix tailTrace_6081903
  have hstable : (prefixWord ++ tailWord_6081903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6081903).length < 2 ^ (prefixWord ++ tailWord_6081903).sum := by decide
  have hdescent : baseEnd_6081903 < baseStart_6081903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6081903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082020 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_6082020 : Nat := 118140960795 + 6082020 * 2 ^ 59
def prefixEnd_6082020 : Nat := 4983230072969 + 3 ^ 40 * 6082020 * 2
def baseEnd_6082020 : Nat := 1040999870086133100826435

theorem tailTrace_6082020 : CollatzResearch.WordTrace tailWord_6082020 prefixEnd_6082020 1040999870086133100826435 := by
  unfold tailWord_6082020
  simp only [CollatzResearch.WordTrace]
  refine ⟨110914746712943870581941757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147886328950591827442589009 110914746712943870581941757)
  ·
    refine ⟨41593030017353951468228159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110914746712943870581941757 41593030017353951468228159)
    ·
      refine ⟨62389545026030927202342239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41593030017353951468228159 62389545026030927202342239)
      ·
        refine ⟨93584317539046390803513359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62389545026030927202342239 93584317539046390803513359)
        ·
          refine ⟨140376476308569586205270039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93584317539046390803513359 140376476308569586205270039)
          ·
            refine ⟨210564714462854379307905059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140376476308569586205270039 210564714462854379307905059)
            ·
              refine ⟨315847071694281568961857589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210564714462854379307905059 315847071694281568961857589)
              ·
                refine ⟨29610662971338897090174149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315847071694281568961857589 29610662971338897090174149)
                ·
                  refine ⟨5551999307126043204407653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29610662971338897090174149 5551999307126043204407653)
                  ·
                    refine ⟨1040999870086133100826435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5551999307126043204407653 1040999870086133100826435)
                    ·
                      rfl

theorem cell23_6082020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_6082020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082020 prefixEnd_6082020 := by exact prefixLift 6082020
  have htrace : WordTrace (prefixWord ++ tailWord_6082020) baseStart_6082020 baseEnd_6082020 := by
    simpa [prefixWord, tailWord_6082020, baseEnd_6082020] using wordTrace_append hprefix tailTrace_6082020
  have hstable : (prefixWord ++ tailWord_6082020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082020).length < 2 ^ (prefixWord ++ tailWord_6082020).sum := by decide
  have hdescent : baseEnd_6082020 < baseStart_6082020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082021 : List Nat := [1, 3, 1, 5, 1, 2, 1, 4, 1, 1, 3]
def baseStart_6082021 : Nat := 118140960795 + 6082021 * 2 ^ 59
def prefixEnd_6082021 : Nat := 4983230072969 + 3 ^ 40 * 6082021 * 2
def baseEnd_6082021 : Nat := 3123000123739053798566801

theorem tailTrace_6082021 : CollatzResearch.WordTrace tailWord_6082021 prefixEnd_6082021 3123000123739053798566801 := by
  unfold tailWord_6082021
  simp only [CollatzResearch.WordTrace]
  refine ⟨221829529898884118334669917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147886353265922745556446611 221829529898884118334669917)
  ·
    refine ⟨83186073712081544375501219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221829529898884118334669917 83186073712081544375501219)
    ·
      refine ⟨124779110568122316563251829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83186073712081544375501219 124779110568122316563251829)
      ·
        refine ⟨11698041615761467177804859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124779110568122316563251829 11698041615761467177804859)
        ·
          refine ⟨17547062423642200766707289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11698041615761467177804859 17547062423642200766707289)
          ·
            refine ⟨13160296817731650575030467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17547062423642200766707289 13160296817731650575030467)
            ·
              refine ⟨19740445226597475862545701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13160296817731650575030467 19740445226597475862545701)
              ·
                refine ⟨3701333479987026724227319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19740445226597475862545701 3701333479987026724227319)
                ·
                  refine ⟨5552000219980540086340979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701333479987026724227319 5552000219980540086340979)
                  ·
                    refine ⟨8328000329970810129511469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5552000219980540086340979 8328000329970810129511469)
                    ·
                      refine ⟨3123000123739053798566801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8328000329970810129511469 3123000123739053798566801)
                      ·
                        rfl

theorem cell23_6082021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_6082021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082021 prefixEnd_6082021 := by exact prefixLift 6082021
  have htrace : WordTrace (prefixWord ++ tailWord_6082021) baseStart_6082021 baseEnd_6082021 := by
    simpa [prefixWord, tailWord_6082021, baseEnd_6082021] using wordTrace_append hprefix tailTrace_6082021
  have hstable : (prefixWord ++ tailWord_6082021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082021).length < 2 ^ (prefixWord ++ tailWord_6082021).sum := by decide
  have hdescent : baseEnd_6082021 < baseStart_6082021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082030 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_6082030 : Nat := 118140960795 + 6082030 * 2 ^ 59
def prefixEnd_6082030 : Nat := 4983230072969 + 3 ^ 40 * 6082030 * 2
def baseEnd_6082030 : Nat := 3123004745064944263354259

theorem tailTrace_6082030 : CollatzResearch.WordTrace tailWord_6082030 prefixEnd_6082030 3123004745064944263354259 := by
  unfold tailWord_6082030
  simp only [CollatzResearch.WordTrace]
  refine ⟨27728732269481439108968443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147886572103901008581165029 27728732269481439108968443)
  ·
    refine ⟨41593098404222158663452665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27728732269481439108968443 41593098404222158663452665)
    ·
      refine ⟨31194823803166618997589499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41593098404222158663452665 31194823803166618997589499)
      ·
        refine ⟨46792235704749928496384249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31194823803166618997589499 46792235704749928496384249)
        ·
          refine ⟨35094176778562446372288187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46792235704749928496384249 35094176778562446372288187)
          ·
            refine ⟨52641265167843669558432281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35094176778562446372288187 52641265167843669558432281)
            ·
              refine ⟨39480948875882752168824211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52641265167843669558432281 39480948875882752168824211)
              ·
                refine ⟨59221423313824128253236317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39480948875882752168824211 59221423313824128253236317)
                ·
                  refine ⟨22208033742684048094963619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59221423313824128253236317 22208033742684048094963619)
                  ·
                    refine ⟨33312050614026072142445429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22208033742684048094963619 33312050614026072142445429)
                    ·
                      refine ⟨3123004745064944263354259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33312050614026072142445429 3123004745064944263354259)
                      ·
                        rfl

theorem cell23_6082030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_6082030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082030 prefixEnd_6082030 := by exact prefixLift 6082030
  have htrace : WordTrace (prefixWord ++ tailWord_6082030) baseStart_6082030 baseEnd_6082030 := by
    simpa [prefixWord, tailWord_6082030, baseEnd_6082030] using wordTrace_append hprefix tailTrace_6082030
  have hstable : (prefixWord ++ tailWord_6082030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082030).length < 2 ^ (prefixWord ++ tailWord_6082030).sum := by decide
  have hdescent : baseEnd_6082030 < baseStart_6082030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082037 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_6082037 : Nat := 118140960795 + 6082037 * 2 ^ 59
def prefixEnd_6082037 : Nat := 4983230072969 + 3 ^ 40 * 6082037 * 2
def baseEnd_6082037 : Nat := 1041002779809841911988909

theorem tailTrace_6082037 : CollatzResearch.WordTrace tailWord_6082037 prefixEnd_6082037 1041002779809841911988909 := by
  unfold tailWord_6082037
  simp only [CollatzResearch.WordTrace]
  refine ⟨221830113466826153067252365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147886742311217435378168243 221830113466826153067252365)
  ·
    refine ⟨83186292550059807400219637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221830113466826153067252365 83186292550059807400219637)
    ·
      refine ⟨7798714926568106943770591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83186292550059807400219637 7798714926568106943770591)
      ·
        refine ⟨11698072389852160415655887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7798714926568106943770591 11698072389852160415655887)
        ·
          refine ⟨17547108584778240623483831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11698072389852160415655887 17547108584778240623483831)
          ·
            refine ⟨26320662877167360935225747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17547108584778240623483831 26320662877167360935225747)
            ·
              refine ⟨39480994315751041402838621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26320662877167360935225747 39480994315751041402838621)
              ·
                refine ⟨14805372868406640526064483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39480994315751041402838621 14805372868406640526064483)
                ·
                  refine ⟨22208059302609960789096725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14805372868406640526064483 22208059302609960789096725)
                  ·
                    refine ⟨1041002779809841911988909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22208059302609960789096725 1041002779809841911988909)
                    ·
                      rfl

theorem cell23_6082037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_6082037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082037 prefixEnd_6082037 := by exact prefixLift 6082037
  have htrace : WordTrace (prefixWord ++ tailWord_6082037) baseStart_6082037 baseEnd_6082037 := by
    simpa [prefixWord, tailWord_6082037, baseEnd_6082037] using wordTrace_append hprefix tailTrace_6082037
  have hstable : (prefixWord ++ tailWord_6082037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082037).length < 2 ^ (prefixWord ++ tailWord_6082037).sum := by decide
  have hdescent : baseEnd_6082037 < baseStart_6082037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082040 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_6082040 : Nat := 118140960795 + 6082040 * 2 ^ 59
def prefixEnd_6082040 : Nat := 4983230072969 + 3 ^ 40 * 6082040 * 2
def baseEnd_6082040 : Nat := 3123009879871489224229213

theorem tailTrace_6082040 : CollatzResearch.WordTrace tailWord_6082040 prefixEnd_6082040 3123009879871489224229213 := by
  unfold tailWord_6082040
  simp only [CollatzResearch.WordTrace]
  refine ⟨110915111442907642289805787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147886815257210189719741049 110915111442907642289805787)
  ·
    refine ⟨166372667164361463434708681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110915111442907642289805787 166372667164361463434708681)
    ·
      refine ⟨124779500373271097576031511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166372667164361463434708681 124779500373271097576031511)
      ·
        refine ⟨187169250559906646364047267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124779500373271097576031511 187169250559906646364047267)
        ·
          refine ⟨280753875839859969546070901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187169250559906646364047267 280753875839859969546070901)
          ·
            refine ⟨26320675859986872144944147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 280753875839859969546070901 26320675859986872144944147)
            ·
              refine ⟨39481013789980308217416221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26320675859986872144944147 39481013789980308217416221)
              ·
                refine ⟨14805380171242615581531083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39481013789980308217416221 14805380171242615581531083)
                ·
                  refine ⟨22208070256863923372296625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14805380171242615581531083 22208070256863923372296625)
                  ·
                    refine ⟨16656052692647942529222469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22208070256863923372296625 16656052692647942529222469)
                    ·
                      refine ⟨3123009879871489224229213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16656052692647942529222469 3123009879871489224229213)
                      ·
                        rfl

theorem cell23_6082040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_6082040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082040 prefixEnd_6082040 := by exact prefixLift 6082040
  have htrace : WordTrace (prefixWord ++ tailWord_6082040) baseStart_6082040 baseEnd_6082040 := by
    simpa [prefixWord, tailWord_6082040, baseEnd_6082040] using wordTrace_append hprefix tailTrace_6082040
  have hstable : (prefixWord ++ tailWord_6082040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082040).length < 2 ^ (prefixWord ++ tailWord_6082040).sum := by decide
  have hdescent : baseEnd_6082040 < baseStart_6082040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082073 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_6082073 : Nat := 118140960795 + 6082073 * 2 ^ 59
def prefixEnd_6082073 : Nat := 4983230072969 + 3 ^ 40 * 6082073 * 2
def baseEnd_6082073 : Nat := 3123026824733087595116561

theorem tailTrace_6082073 : CollatzResearch.WordTrace tailWord_6082073 prefixEnd_6082073 3123026824733087595116561 := by
  unfold tailWord_6082073
  simp only [CollatzResearch.WordTrace]
  refine ⟨221831426494695731215562873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147887617663130487477041915 221831426494695731215562873)
  ·
    refine ⟨166373569871021798411672155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221831426494695731215562873 166373569871021798411672155)
    ·
      refine ⟨249560354806532697617508233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166373569871021798411672155 249560354806532697617508233)
      ·
        refine ⟨187170266104899523213131175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249560354806532697617508233 187170266104899523213131175)
        ·
          refine ⟨280755399157349284819696763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187170266104899523213131175 280755399157349284819696763)
          ·
            refine ⟨421133098736023927229545145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280755399157349284819696763 421133098736023927229545145)
            ·
              refine ⟨315849824052017945422158859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421133098736023927229545145 315849824052017945422158859)
              ·
                refine ⟨473774736078026918133238289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315849824052017945422158859 473774736078026918133238289)
                ·
                  refine ⟨355331052058520188599928717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473774736078026918133238289 355331052058520188599928717)
                  ·
                    refine ⟨133249144521945070724973269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355331052058520188599928717 133249144521945070724973269)
                    ·
                      refine ⟨3123026824733087595116561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133249144521945070724973269 3123026824733087595116561)
                      ·
                        rfl

theorem cell23_6082073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_6082073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082073 prefixEnd_6082073 := by exact prefixLift 6082073
  have htrace : WordTrace (prefixWord ++ tailWord_6082073) baseStart_6082073 baseEnd_6082073 := by
    simpa [prefixWord, tailWord_6082073, baseEnd_6082073] using wordTrace_append hprefix tailTrace_6082073
  have hstable : (prefixWord ++ tailWord_6082073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082073).length < 2 ^ (prefixWord ++ tailWord_6082073).sum := by decide
  have hdescent : baseEnd_6082073 < baseStart_6082073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082094 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_6082094 : Nat := 118140960795 + 6082094 * 2 ^ 59
def prefixEnd_6082094 : Nat := 4983230072969 + 3 ^ 40 * 6082094 * 2
def baseEnd_6082094 : Nat := 3123037607826832012953965

theorem tailTrace_6082094 : CollatzResearch.WordTrace tailWord_6082094 prefixEnd_6082094 3123037607826832012953965 := by
  unfold tailWord_6082094
  simp only [CollatzResearch.WordTrace]
  refine ⟨27729024053452456475259667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147888128285079767868051557 27729024053452456475259667)
  ·
    refine ⟨41593536080178684712889501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27729024053452456475259667 41593536080178684712889501)
    ·
      refine ⟨15597576030067006767333563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41593536080178684712889501 15597576030067006767333563)
      ·
        refine ⟨23396364045100510151000345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15597576030067006767333563 23396364045100510151000345)
        ·
          refine ⟨17547273033825382613250259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23396364045100510151000345 17547273033825382613250259)
          ·
            refine ⟨26320909550738073919875389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17547273033825382613250259 26320909550738073919875389)
            ·
              refine ⟨9870341081526777719953271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26320909550738073919875389 9870341081526777719953271)
              ·
                refine ⟨14805511622290166579929907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9870341081526777719953271 14805511622290166579929907)
                ·
                  refine ⟨22208267433435249869894861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14805511622290166579929907 22208267433435249869894861)
                  ·
                    refine ⟨8328100287538218701210573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22208267433435249869894861 8328100287538218701210573)
                    ·
                      refine ⟨3123037607826832012953965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8328100287538218701210573 3123037607826832012953965)
                      ·
                        rfl

theorem cell23_6082094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_6082094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082094 prefixEnd_6082094 := by exact prefixLift 6082094
  have htrace : WordTrace (prefixWord ++ tailWord_6082094) baseStart_6082094 baseEnd_6082094 := by
    simpa [prefixWord, tailWord_6082094, baseEnd_6082094] using wordTrace_append hprefix tailTrace_6082094
  have hstable : (prefixWord ++ tailWord_6082094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082094).length < 2 ^ (prefixWord ++ tailWord_6082094).sum := by decide
  have hdescent : baseEnd_6082094 < baseStart_6082094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082104 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 1, 3, 2]
def baseStart_6082104 : Nat := 118140960795 + 6082104 * 2 ^ 59
def prefixEnd_6082104 : Nat := 4983230072969 + 3 ^ 40 * 6082104 * 2
def baseEnd_6082104 : Nat := 3123042742633376973828919

theorem tailTrace_6082104 : CollatzResearch.WordTrace tailWord_6082104 prefixEnd_6082104 3123042742633376973828919 := by
  unfold tailWord_6082104
  simp only [CollatzResearch.WordTrace]
  refine ⟨110916278578791711754970683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147888371438388949006627577 110916278578791711754970683)
  ·
    refine ⟨166374417868187567632456025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110916278578791711754970683 166374417868187567632456025)
    ·
      refine ⟨124780813401140675724342019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166374417868187567632456025 124780813401140675724342019)
      ·
        refine ⟨187171220101711013586513029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124780813401140675724342019 187171220101711013586513029)
        ·
          refine ⟨35094603769070815047471193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187171220101711013586513029 35094603769070815047471193)
          ·
            refine ⟨26320952826803111285603395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35094603769070815047471193 26320952826803111285603395)
            ·
              refine ⟨39481429240204666928405093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26320952826803111285603395 39481429240204666928405093)
              ·
                refine ⟨7402767982538375049075955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39481429240204666928405093 7402767982538375049075955)
                ·
                  refine ⟨11104151973807562573613933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7402767982538375049075955 11104151973807562573613933)
                  ·
                    refine ⟨4164056990177835965105225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11104151973807562573613933 4164056990177835965105225)
                    ·
                      refine ⟨3123042742633376973828919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164056990177835965105225 3123042742633376973828919)
                      ·
                        rfl

theorem cell23_6082104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_6082104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082104 prefixEnd_6082104 := by exact prefixLift 6082104
  have htrace : WordTrace (prefixWord ++ tailWord_6082104) baseStart_6082104 baseEnd_6082104 := by
    simpa [prefixWord, tailWord_6082104, baseEnd_6082104] using wordTrace_append hprefix tailTrace_6082104
  have hstable : (prefixWord ++ tailWord_6082104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082104).length < 2 ^ (prefixWord ++ tailWord_6082104).sum := by decide
  have hdescent : baseEnd_6082104 < baseStart_6082104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082117 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 3, 4, 2]
def baseStart_6082117 : Nat := 118140960795 + 6082117 * 2 ^ 59
def prefixEnd_6082117 : Nat := 4983230072969 + 3 ^ 40 * 6082117 * 2
def baseEnd_6082117 : Nat := 3123049417881885422966359

theorem tailTrace_6082117 : CollatzResearch.WordTrace tailWord_6082117 prefixEnd_6082117 3123049417881885422966359 := by
  unfold tailWord_6082117
  simp only [CollatzResearch.WordTrace]
  refine ⟨221833031306536326730164605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147888687537690884486776403 221833031306536326730164605)
  ·
    refine ⟨83187386739951122523811727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221833031306536326730164605 83187386739951122523811727)
    ·
      refine ⟨124781080109926683785717591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83187386739951122523811727 124781080109926683785717591)
      ·
        refine ⟨187171620164890025678576387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124781080109926683785717591 187171620164890025678576387)
        ·
          refine ⟨280757430247335038517864581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187171620164890025678576387 280757430247335038517864581)
          ·
            refine ⟨52642018171375319722099609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280757430247335038517864581 52642018171375319722099609)
            ·
              refine ⟨39481513628531489791574707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52642018171375319722099609 39481513628531489791574707)
              ·
                refine ⟨59222270442797234687362061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39481513628531489791574707 59222270442797234687362061)
                ·
                  refine ⟨22208351416048963007760773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59222270442797234687362061 22208351416048963007760773)
                  ·
                    refine ⟨4164065890509180563955145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22208351416048963007760773 4164065890509180563955145)
                    ·
                      refine ⟨3123049417881885422966359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164065890509180563955145 3123049417881885422966359)
                      ·
                        rfl

theorem cell23_6082117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_6082117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082117 prefixEnd_6082117 := by exact prefixLift 6082117
  have htrace : WordTrace (prefixWord ++ tailWord_6082117) baseStart_6082117 baseEnd_6082117 := by
    simpa [prefixWord, tailWord_6082117, baseEnd_6082117] using wordTrace_append hprefix tailTrace_6082117
  have hstable : (prefixWord ++ tailWord_6082117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082117).length < 2 ^ (prefixWord ++ tailWord_6082117).sum := by decide
  have hdescent : baseEnd_6082117 < baseStart_6082117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082120 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_6082120 : Nat := 118140960795 + 6082120 * 2 ^ 59
def prefixEnd_6082120 : Nat := 4983230072969 + 3 ^ 40 * 6082120 * 2
def baseEnd_6082120 : Nat := 3123050958323848911228845

theorem tailTrace_6082120 : CollatzResearch.WordTrace tailWord_6082120 prefixEnd_6082120 3123050958323848911228845 := by
  unfold tailWord_6082120
  simp only [CollatzResearch.WordTrace]
  refine ⟨110916570362762729121261907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147888760483683638828349209 110916570362762729121261907)
  ·
    refine ⟨166374855544144093681892861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110916570362762729121261907 166374855544144093681892861)
    ·
      refine ⟨62390570829054035130709823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166374855544144093681892861 62390570829054035130709823)
      ·
        refine ⟨93585856243581052696064735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62390570829054035130709823 93585856243581052696064735)
        ·
          refine ⟨140378784365371579044097103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93585856243581052696064735 140378784365371579044097103)
          ·
            refine ⟨210568176548057368566145655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140378784365371579044097103 210568176548057368566145655)
            ·
              refine ⟨315852264822086052849218483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210568176548057368566145655 315852264822086052849218483)
              ·
                refine ⟨473778397233129079273827725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315852264822086052849218483 473778397233129079273827725)
                ·
                  refine ⟨177666898962423404727685397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473778397233129079273827725 177666898962423404727685397)
                  ·
                    refine ⟨8328135888863597096610253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 177666898962423404727685397 8328135888863597096610253)
                    ·
                      refine ⟨3123050958323848911228845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8328135888863597096610253 3123050958323848911228845)
                      ·
                        rfl

theorem cell23_6082120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_6082120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082120 prefixEnd_6082120 := by exact prefixLift 6082120
  have htrace : WordTrace (prefixWord ++ tailWord_6082120) baseStart_6082120 baseEnd_6082120 := by
    simpa [prefixWord, tailWord_6082120, baseEnd_6082120] using wordTrace_append hprefix tailTrace_6082120
  have hstable : (prefixWord ++ tailWord_6082120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082120).length < 2 ^ (prefixWord ++ tailWord_6082120).sum := by decide
  have hdescent : baseEnd_6082120 < baseStart_6082120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082220 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_6082220 : Nat := 118140960795 + 6082220 * 2 ^ 59
def prefixEnd_6082220 : Nat := 4983230072969 + 3 ^ 40 * 6082220 * 2
def baseEnd_6082220 : Nat := 3123102306389298519978385

theorem tailTrace_6082220 : CollatzResearch.WordTrace tailWord_6082220 prefixEnd_6082220 3123102306389298519978385 := by
  unfold tailWord_6082220
  simp only [CollatzResearch.WordTrace]
  refine ⟨110918394012581587660582057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147891192016775450214109409 110918394012581587660582057)
  ·
    refine ⟨83188795509436190745436543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110918394012581587660582057 83188795509436190745436543)
    ·
      refine ⟨124783193264154286118154815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83188795509436190745436543 124783193264154286118154815)
      ·
        refine ⟨187174789896231429177232223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124783193264154286118154815 187174789896231429177232223)
        ·
          refine ⟨280762184844347143765848335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187174789896231429177232223 280762184844347143765848335)
          ·
            refine ⟨421143277266520715648772503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280762184844347143765848335 421143277266520715648772503)
            ·
              refine ⟨631714915899781073473158755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421143277266520715648772503 631714915899781073473158755)
              ·
                refine ⟨947572373849671610209738133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631714915899781073473158755 947572373849671610209738133)
                ·
                  refine ⟨44417455024203356728581475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 947572373849671610209738133 44417455024203356728581475)
                  ·
                    refine ⟨66626182536305035092872213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44417455024203356728581475 66626182536305035092872213)
                    ·
                      refine ⟨3123102306389298519978385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66626182536305035092872213 3123102306389298519978385)
                      ·
                        rfl

theorem cell23_6082220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_6082220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082220 prefixEnd_6082220 := by exact prefixLift 6082220
  have htrace : WordTrace (prefixWord ++ tailWord_6082220) baseStart_6082220 baseEnd_6082220 := by
    simpa [prefixWord, tailWord_6082220, baseEnd_6082220] using wordTrace_append hprefix tailTrace_6082220
  have hstable : (prefixWord ++ tailWord_6082220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082220).length < 2 ^ (prefixWord ++ tailWord_6082220).sum := by decide
  have hdescent : baseEnd_6082220 < baseStart_6082220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082227 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 3]
def baseStart_6082227 : Nat := 118140960795 + 6082227 * 2 ^ 59
def prefixEnd_6082227 : Nat := 4983230072969 + 3 ^ 40 * 6082227 * 2
def baseEnd_6082227 : Nat := 3123105900753879992590853

theorem tailTrace_6082227 : CollatzResearch.WordTrace tailWord_6082227 prefixEnd_6082227 3123105900753879992590853 := by
  unfold tailWord_6082227
  simp only [CollatzResearch.WordTrace]
  refine ⟨221837043336137815516668935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147891362224091877011112623 221837043336137815516668935)
  ·
    refine ⟨332755565004206723275003403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221837043336137815516668935 332755565004206723275003403)
    ·
      refine ⟨499133347506310084912505105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332755565004206723275003403 499133347506310084912505105)
      ·
        refine ⟨374350010629732563684378829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499133347506310084912505105 374350010629732563684378829)
        ·
          refine ⟨140381253986149711381642061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374350010629732563684378829 140381253986149711381642061)
          ·
            refine ⟨52642970244806141768115773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140381253986149711381642061 52642970244806141768115773)
            ·
              refine ⟨19741113841802303163043415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52642970244806141768115773 19741113841802303163043415)
              ·
                refine ⟨29611670762703454744565123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19741113841802303163043415 29611670762703454744565123)
                ·
                  refine ⟨44417506144055182116847685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29611670762703454744565123 44417506144055182116847685)
                  ·
                    refine ⟨8328282402010346646908941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44417506144055182116847685 8328282402010346646908941)
                    ·
                      refine ⟨3123105900753879992590853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8328282402010346646908941 3123105900753879992590853)
                      ·
                        rfl

theorem cell23_6082227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 3].length) (baseStart_6082227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082227 prefixEnd_6082227 := by exact prefixLift 6082227
  have htrace : WordTrace (prefixWord ++ tailWord_6082227) baseStart_6082227 baseEnd_6082227 := by
    simpa [prefixWord, tailWord_6082227, baseEnd_6082227] using wordTrace_append hprefix tailTrace_6082227
  have hstable : (prefixWord ++ tailWord_6082227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082227).length < 2 ^ (prefixWord ++ tailWord_6082227).sum := by decide
  have hdescent : baseEnd_6082227 < baseStart_6082227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082244 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_6082244 : Nat := 118140960795 + 6082244 * 2 ^ 59
def prefixEnd_6082244 : Nat := 4983230072969 + 3 ^ 40 * 6082244 * 2
def baseEnd_6082244 : Nat := 3123114629925006426078275

theorem tailTrace_6082244 : CollatzResearch.WordTrace tailWord_6082244 prefixEnd_6082244 3123114629925006426078275 := by
  unfold tailWord_6082244
  simp only [CollatzResearch.WordTrace]
  refine ⟨110918831688538113710018893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147891775584717484946691857 110918831688538113710018893)
  ·
    refine ⟨41594561883201792641257085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110918831688538113710018893 41594561883201792641257085)
    ·
      refine ⟨15597960706200672240471407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41594561883201792641257085 15597960706200672240471407)
      ·
        refine ⟨23396941059301008360707111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15597960706200672240471407 23396941059301008360707111)
        ·
          refine ⟨35095411588951512541060667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23396941059301008360707111 35095411588951512541060667)
          ·
            refine ⟨52643117383427268811591001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35095411588951512541060667 52643117383427268811591001)
            ·
              refine ⟨39482338037570451608693251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52643117383427268811591001 39482338037570451608693251)
              ·
                refine ⟨59223507056355677413039877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39482338037570451608693251 59223507056355677413039877)
                ·
                  refine ⟨11104407573066689514944977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59223507056355677413039877 11104407573066689514944977)
                  ·
                    refine ⟨8328305679800017136208733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11104407573066689514944977 8328305679800017136208733)
                    ·
                      refine ⟨3123114629925006426078275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8328305679800017136208733 3123114629925006426078275)
                      ·
                        rfl

theorem cell23_6082244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_6082244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082244 prefixEnd_6082244 := by exact prefixLift 6082244
  have htrace : WordTrace (prefixWord ++ tailWord_6082244) baseStart_6082244 baseEnd_6082244 := by
    simpa [prefixWord, tailWord_6082244, baseEnd_6082244] using wordTrace_append hprefix tailTrace_6082244
  have hstable : (prefixWord ++ tailWord_6082244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082244).length < 2 ^ (prefixWord ++ tailWord_6082244).sum := by decide
  have hdescent : baseEnd_6082244 < baseStart_6082244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082264 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 6]
def baseStart_6082264 : Nat := 118140960795 + 6082264 * 2 ^ 59
def prefixEnd_6082264 : Nat := 4983230072969 + 3 ^ 40 * 6082264 * 2
def baseEnd_6082264 : Nat := 347013877726455149758687

theorem tailTrace_6082264 : CollatzResearch.WordTrace tailWord_6082264 prefixEnd_6082264 347013877726455149758687 := by
  unfold tailWord_6082264
  simp only [CollatzResearch.WordTrace]
  refine ⟨110919196418501885417882923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147892261891335847223843897 110919196418501885417882923)
  ·
    refine ⟨166378794627752828126824385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110919196418501885417882923 166378794627752828126824385)
    ·
      refine ⟨124784095970814621095118289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166378794627752828126824385 124784095970814621095118289)
      ·
        refine ⟨93588071978110965821338717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124784095970814621095118289 93588071978110965821338717)
        ·
          refine ⟨35095526991791612183002019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93588071978110965821338717 35095526991791612183002019)
          ·
            refine ⟨52643290487687418274503029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35095526991791612183002019 52643290487687418274503029)
            ·
              refine ⟨4935308483220695463234659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52643290487687418274503029 4935308483220695463234659)
              ·
                refine ⟨7402962724831043194851989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935308483220695463234659 7402962724831043194851989)
                ·
                  refine ⟨347013877726455149758687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7402962724831043194851989 347013877726455149758687)
                  ·
                    rfl

theorem cell23_6082264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 6].length) (baseStart_6082264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082264 prefixEnd_6082264 := by exact prefixLift 6082264
  have htrace : WordTrace (prefixWord ++ tailWord_6082264) baseStart_6082264 baseEnd_6082264 := by
    simpa [prefixWord, tailWord_6082264, baseEnd_6082264] using wordTrace_append hprefix tailTrace_6082264
  have hstable : (prefixWord ++ tailWord_6082264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082264).length < 2 ^ (prefixWord ++ tailWord_6082264).sum := by decide
  have hdescent : baseEnd_6082264 < baseStart_6082264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082284 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 1, 5, 2]
def baseStart_6082284 : Nat := 118140960795 + 6082284 * 2 ^ 59
def prefixEnd_6082284 : Nat := 4983230072969 + 3 ^ 40 * 6082284 * 2
def baseEnd_6082284 : Nat := 3123135169151186269578091

theorem tailTrace_6082284 : CollatzResearch.WordTrace tailWord_6082284 prefixEnd_6082284 3123135169151186269578091 := by
  unfold tailWord_6082284
  simp only [CollatzResearch.WordTrace]
  refine ⟨110919561148465657125746953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147892748197954209500995937 110919561148465657125746953)
  ·
    refine ⟨83189670861349242844310215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110919561148465657125746953 83189670861349242844310215)
    ·
      refine ⟨124784506292023864266465323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83189670861349242844310215 124784506292023864266465323)
      ·
        refine ⟨187176759438035796399697985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124784506292023864266465323 187176759438035796399697985)
        ·
          refine ⟨140382569578526847299773489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187176759438035796399697985 140382569578526847299773489)
          ·
            refine ⟨105286927183895135474830117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140382569578526847299773489 105286927183895135474830117)
            ·
              refine ⟨19741298846980337901530647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105286927183895135474830117 19741298846980337901530647)
              ·
                refine ⟨29611948270470506852295971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19741298846980337901530647 29611948270470506852295971)
                ·
                  refine ⟨44417922405705760278443957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29611948270470506852295971 44417922405705760278443957)
                  ·
                    refine ⟨4164180225534915026104121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44417922405705760278443957 4164180225534915026104121)
                    ·
                      refine ⟨3123135169151186269578091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164180225534915026104121 3123135169151186269578091)
                      ·
                        rfl

theorem cell23_6082284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_6082284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082284 prefixEnd_6082284 := by exact prefixLift 6082284
  have htrace : WordTrace (prefixWord ++ tailWord_6082284) baseStart_6082284 baseEnd_6082284 := by
    simpa [prefixWord, tailWord_6082284, baseEnd_6082284] using wordTrace_append hprefix tailTrace_6082284
  have hstable : (prefixWord ++ tailWord_6082284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082284).length < 2 ^ (prefixWord ++ tailWord_6082284).sum := by decide
  have hdescent : baseEnd_6082284 < baseStart_6082284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082297 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 4]
def baseStart_6082297 : Nat := 118140960795 + 6082297 * 2 ^ 59
def prefixEnd_6082297 : Nat := 4983230072969 + 3 ^ 40 * 6082297 * 2
def baseEnd_6082297 : Nat := 3123141844399694718715531

theorem tailTrace_6082297 : CollatzResearch.WordTrace tailWord_6082297 prefixEnd_6082297 3123141844399694718715531 := by
  unfold tailWord_6082297
  simp only [CollatzResearch.WordTrace]
  refine ⟨221839596445884217471717145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147893064297256144981144763 221839596445884217471717145)
  ·
    refine ⟨166379697334413163103787859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221839596445884217471717145 166379697334413163103787859)
    ·
      refine ⟨249569546001619744655681789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166379697334413163103787859 249569546001619744655681789)
      ·
        refine ⟨93588579750607404245880671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249569546001619744655681789 93588579750607404245880671)
        ·
          refine ⟨140382869625911106368821007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93588579750607404245880671 140382869625911106368821007)
          ·
            refine ⟨210574304438866659553231511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140382869625911106368821007 210574304438866659553231511)
            ·
              refine ⟨315861456658299989329847267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210574304438866659553231511 315861456658299989329847267)
              ·
                refine ⟨473792184987449983994770901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315861456658299989329847267 473792184987449983994770901)
                ·
                  refine ⟨11104504335643358999877443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 473792184987449983994770901 11104504335643358999877443)
                  ·
                    refine ⟨16656756503465038499816165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11104504335643358999877443 16656756503465038499816165)
                    ·
                      refine ⟨3123141844399694718715531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16656756503465038499816165 3123141844399694718715531)
                      ·
                        rfl

theorem cell23_6082297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_6082297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082297 prefixEnd_6082297 := by exact prefixLift 6082297
  have htrace : WordTrace (prefixWord ++ tailWord_6082297) baseStart_6082297 baseEnd_6082297 := by
    simpa [prefixWord, tailWord_6082297, baseEnd_6082297] using wordTrace_append hprefix tailTrace_6082297
  have hstable : (prefixWord ++ tailWord_6082297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082297).length < 2 ^ (prefixWord ++ tailWord_6082297).sum := by decide
  have hdescent : baseEnd_6082297 < baseStart_6082297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082308 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_6082308 : Nat := 118140960795 + 6082308 * 2 ^ 59
def prefixEnd_6082308 : Nat := 4983230072969 + 3 ^ 40 * 6082308 * 2
def baseEnd_6082308 : Nat := 3123147492686894175677981

theorem tailTrace_6082308 : CollatzResearch.WordTrace tailWord_6082308 prefixEnd_6082308 3123147492686894175677981 := by
  unfold tailWord_6082308
  simp only [CollatzResearch.WordTrace]
  refine ⟨110919998824422183175183789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147893331765896244233578385 110919998824422183175183789)
  ·
    refine ⟨41594999559158318690693921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110919998824422183175183789 41594999559158318690693921)
    ·
      refine ⟨31196249669368739018020441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41594999559158318690693921 31196249669368739018020441)
      ·
        refine ⟨23397187252026554263515331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31196249669368739018020441 23397187252026554263515331)
        ·
          refine ⟨35095780878039831395272997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23397187252026554263515331 35095780878039831395272997)
          ·
            refine ⟨6580458914632468386613687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35095780878039831395272997 6580458914632468386613687)
            ·
              refine ⟨9870688371948702579920531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580458914632468386613687 9870688371948702579920531)
              ·
                refine ⟨14806032557923053869880797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9870688371948702579920531 14806032557923053869880797)
                ·
                  refine ⟨5552262209221145201205299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14806032557923053869880797 5552262209221145201205299)
                  ·
                    refine ⟨8328393313831717801807949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5552262209221145201205299 8328393313831717801807949)
                    ·
                      refine ⟨3123147492686894175677981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8328393313831717801807949 3123147492686894175677981)
                      ·
                        rfl

theorem cell23_6082308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_6082308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082308 prefixEnd_6082308 := by exact prefixLift 6082308
  have htrace : WordTrace (prefixWord ++ tailWord_6082308) baseStart_6082308 baseEnd_6082308 := by
    simpa [prefixWord, tailWord_6082308, baseEnd_6082308] using wordTrace_append hprefix tailTrace_6082308
  have hstable : (prefixWord ++ tailWord_6082308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082308).length < 2 ^ (prefixWord ++ tailWord_6082308).sum := by decide
  have hdescent : baseEnd_6082308 < baseStart_6082308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082337 : List Nat := [1, 2, 3, 2, 1, 3, 2, 9]
def baseStart_6082337 : Nat := 118140960795 + 6082337 * 2 ^ 59
def prefixEnd_6082337 : Nat := 4983230072969 + 3 ^ 40 * 6082337 * 2
def baseEnd_6082337 : Nat := 115672680875032391193161

theorem tailTrace_6082337 : CollatzResearch.WordTrace tailWord_6082337 prefixEnd_6082337 115672680875032391193161 := by
  unfold tailWord_6082337
  simp only [CollatzResearch.WordTrace]
  refine ⟨221841055365739304303173265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147894036910492869535448843 221841055365739304303173265)
  ·
    refine ⟨166380791524304478227379949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221841055365739304303173265 166380791524304478227379949)
    ·
      refine ⟨62392796821614179335267481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166380791524304478227379949 62392796821614179335267481)
      ·
        refine ⟨46794597616210634501450611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62392796821614179335267481 46794597616210634501450611)
        ·
          refine ⟨70191896424315951752175917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46794597616210634501450611 70191896424315951752175917)
          ·
            refine ⟨26321961159118481907065969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70191896424315951752175917 26321961159118481907065969)
            ·
              refine ⟨19741470869338861430299477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26321961159118481907065969 19741470869338861430299477)
              ·
                refine ⟨115672680875032391193161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19741470869338861430299477 115672680875032391193161)
                ·
                  rfl

theorem cell23_6082337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 9].length) (baseStart_6082337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082337 prefixEnd_6082337 := by exact prefixLift 6082337
  have htrace : WordTrace (prefixWord ++ tailWord_6082337) baseStart_6082337 baseEnd_6082337 := by
    simpa [prefixWord, tailWord_6082337, baseEnd_6082337] using wordTrace_append hprefix tailTrace_6082337
  have hstable : (prefixWord ++ tailWord_6082337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082337).length < 2 ^ (prefixWord ++ tailWord_6082337).sum := by decide
  have hdescent : baseEnd_6082337 < baseStart_6082337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082344 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_6082344 : Nat := 118140960795 + 6082344 * 2 ^ 59
def prefixEnd_6082344 : Nat := 4983230072969 + 3 ^ 40 * 6082344 * 2
def baseEnd_6082344 : Nat := 3123165977990456034827815

theorem tailTrace_6082344 : CollatzResearch.WordTrace tailWord_6082344 prefixEnd_6082344 3123165977990456034827815 := by
  unfold tailWord_6082344
  simp only [CollatzResearch.WordTrace]
  refine ⟨110920655338356972249339043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147894207117809296332452057 110920655338356972249339043)
  ·
    refine ⟨166380983007535458374008565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110920655338356972249339043 166380983007535458374008565)
    ·
      refine ⟨15598217156956449222563303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166380983007535458374008565 15598217156956449222563303)
      ·
        refine ⟨23397325735434673833844955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15598217156956449222563303 23397325735434673833844955)
        ·
          refine ⟨35095988603152010750767433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23397325735434673833844955 35095988603152010750767433)
          ·
            refine ⟨26321991452364008063075575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35095988603152010750767433 26321991452364008063075575)
            ·
              refine ⟨39482987178546012094613363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26321991452364008063075575 39482987178546012094613363)
              ·
                refine ⟨59224480767819018141920045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39482987178546012094613363 59224480767819018141920045)
                ·
                  refine ⟨22209180287932131803220017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59224480767819018141920045 22209180287932131803220017)
                  ·
                    refine ⟨16656885215949098852415013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22209180287932131803220017 16656885215949098852415013)
                    ·
                      refine ⟨3123165977990456034827815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16656885215949098852415013 3123165977990456034827815)
                      ·
                        rfl

theorem cell23_6082344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_6082344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082344 prefixEnd_6082344 := by exact prefixLift 6082344
  have htrace : WordTrace (prefixWord ++ tailWord_6082344) baseStart_6082344 baseEnd_6082344 := by
    simpa [prefixWord, tailWord_6082344, baseEnd_6082344] using wordTrace_append hprefix tailTrace_6082344
  have hstable : (prefixWord ++ tailWord_6082344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082344).length < 2 ^ (prefixWord ++ tailWord_6082344).sum := by decide
  have hdescent : baseEnd_6082344 < baseStart_6082344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082347 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 3]
def baseStart_6082347 : Nat := 118140960795 + 6082347 * 2 ^ 59
def prefixEnd_6082347 : Nat := 4983230072969 + 3 ^ 40 * 6082347 * 2
def baseEnd_6082347 : Nat := 3123167518432419523090301

theorem tailTrace_6082347 : CollatzResearch.WordTrace tailWord_6082347 prefixEnd_6082347 3123167518432419523090301 := by
  unfold tailWord_6082347
  simp only [CollatzResearch.WordTrace]
  refine ⟨221841420095703076011037295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147894280063802050674024863 221841420095703076011037295)
  ·
    refine ⟨332762130143554614016555943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221841420095703076011037295 332762130143554614016555943)
    ·
      refine ⟨499143195215331921024833915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332762130143554614016555943 499143195215331921024833915)
      ·
        refine ⟨748714792822997881537250873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499143195215331921024833915 748714792822997881537250873)
        ·
          refine ⟨561536094617248411152938155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748714792822997881537250873 561536094617248411152938155)
          ·
            refine ⟨842304141925872616729407233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561536094617248411152938155 842304141925872616729407233)
            ·
              refine ⟨631728106444404462547055425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842304141925872616729407233 631728106444404462547055425)
              ·
                refine ⟨473796079833303346910291569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631728106444404462547055425 473796079833303346910291569)
                ·
                  refine ⟨355347059874977510182718677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473796079833303346910291569 355347059874977510182718677)
                  ·
                    refine ⟨8328446715819785394907469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 355347059874977510182718677 8328446715819785394907469)
                    ·
                      refine ⟨3123167518432419523090301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8328446715819785394907469 3123167518432419523090301)
                      ·
                        rfl

theorem cell23_6082347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 3].length) (baseStart_6082347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082347 prefixEnd_6082347 := by exact prefixLift 6082347
  have htrace : WordTrace (prefixWord ++ tailWord_6082347) baseStart_6082347 baseEnd_6082347 := by
    simpa [prefixWord, tailWord_6082347, baseEnd_6082347] using wordTrace_append hprefix tailTrace_6082347
  have hstable : (prefixWord ++ tailWord_6082347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082347).length < 2 ^ (prefixWord ++ tailWord_6082347).sum := by decide
  have hdescent : baseEnd_6082347 < baseStart_6082347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082358 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6082358 : Nat := 118140960795 + 6082358 * 2 ^ 59
def prefixEnd_6082358 : Nat := 4983230072969 + 3 ^ 40 * 6082358 * 2
def baseEnd_6082358 : Nat := 1041057722239872993350917

theorem tailTrace_6082358 : CollatzResearch.WordTrace tailWord_6082358 prefixEnd_6082358 1041057722239872993350917 := by
  unfold tailWord_6082358
  simp only [CollatzResearch.WordTrace]
  refine ⟨13865113831166451555605483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147894547532442149926458485 13865113831166451555605483)
  ·
    refine ⟨20797670746749677333408225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13865113831166451555605483 20797670746749677333408225)
    ·
      refine ⟨15598253060062258000056169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20797670746749677333408225 15598253060062258000056169)
      ·
        refine ⟨11698689795046693500042127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15598253060062258000056169 11698689795046693500042127)
        ·
          refine ⟨17548034692570040250063191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11698689795046693500042127 17548034692570040250063191)
          ·
            refine ⟨26322052038855060375094787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17548034692570040250063191 26322052038855060375094787)
            ·
              refine ⟨39483078058282590562642181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26322052038855060375094787 39483078058282590562642181)
              ·
                refine ⟨7403077135927985730495409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39483078058282590562642181 7403077135927985730495409)
                ·
                  refine ⟨5552307851945989297871557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7403077135927985730495409 5552307851945989297871557)
                  ·
                    refine ⟨1041057722239872993350917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5552307851945989297871557 1041057722239872993350917)
                    ·
                      rfl

theorem cell23_6082358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6082358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082358 prefixEnd_6082358 := by exact prefixLift 6082358
  have htrace : WordTrace (prefixWord ++ tailWord_6082358) baseStart_6082358 baseEnd_6082358 := by
    simpa [prefixWord, tailWord_6082358, baseEnd_6082358] using wordTrace_append hprefix tailTrace_6082358
  have hstable : (prefixWord ++ tailWord_6082358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082358).length < 2 ^ (prefixWord ++ tailWord_6082358).sum := by decide
  have hdescent : baseEnd_6082358 < baseStart_6082358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082408 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_6082408 : Nat := 118140960795 + 6082408 * 2 ^ 59
def prefixEnd_6082408 : Nat := 4983230072969 + 3 ^ 40 * 6082408 * 2
def baseEnd_6082408 : Nat := 3123198840752343784427521

theorem tailTrace_6082408 : CollatzResearch.WordTrace tailWord_6082408 prefixEnd_6082408 3123198840752343784427521 := by
  unfold tailWord_6082408
  simp only [CollatzResearch.WordTrace]
  refine ⟨110921822474241041714503939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147895763298988055619338585 110921822474241041714503939)
  ·
    refine ⟨166382733711361562571755909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110921822474241041714503939 166382733711361562571755909)
    ·
      refine ⟨31196762570880292982204233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166382733711361562571755909 31196762570880292982204233)
      ·
        refine ⟨23397571928160219736653175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31196762570880292982204233 23397571928160219736653175)
        ·
          refine ⟨35096357892240329604979763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23397571928160219736653175 35096357892240329604979763)
          ·
            refine ⟨52644536838360494407469645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35096357892240329604979763 52644536838360494407469645)
            ·
              refine ⟨19741701314385185402801117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52644536838360494407469645 19741701314385185402801117)
              ·
                refine ⟨7403137992894444526050419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19741701314385185402801117 7403137992894444526050419)
                ·
                  refine ⟨11104706989341666789075629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7403137992894444526050419 11104706989341666789075629)
                  ·
                    refine ⟨4164265121003125045903361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11104706989341666789075629 4164265121003125045903361)
                    ·
                      refine ⟨3123198840752343784427521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164265121003125045903361 3123198840752343784427521)
                      ·
                        rfl

theorem cell23_6082408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_6082408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082408 prefixEnd_6082408 := by exact prefixLift 6082408
  have htrace : WordTrace (prefixWord ++ tailWord_6082408) baseStart_6082408 baseEnd_6082408 := by
    simpa [prefixWord, tailWord_6082408, baseEnd_6082408] using wordTrace_append hprefix tailTrace_6082408
  have hstable : (prefixWord ++ tailWord_6082408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082408).length < 2 ^ (prefixWord ++ tailWord_6082408).sum := by decide
  have hdescent : baseEnd_6082408 < baseStart_6082408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082447 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_6082447 : Nat := 118140960795 + 6082447 * 2 ^ 59
def prefixEnd_6082447 : Nat := 4983230072969 + 3 ^ 40 * 6082447 * 2
def baseEnd_6082447 : Nat := 3123218866497869131839841

theorem tailTrace_6082447 : CollatzResearch.WordTrace tailWord_6082447 prefixEnd_6082447 3123218866497869131839841 := by
  unfold tailWord_6082447
  simp only [CollatzResearch.WordTrace]
  refine ⟨221845067395340793089677595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147896711596893862059785063 221845067395340793089677595)
  ·
    refine ⟨332767601093011189634516393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221845067395340793089677595 332767601093011189634516393)
    ·
      refine ⟨249575700819758392225887295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332767601093011189634516393 249575700819758392225887295)
      ·
        refine ⟨374363551229637588338830943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249575700819758392225887295 374363551229637588338830943)
        ·
          refine ⟨561545326844456382508246415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374363551229637588338830943 561545326844456382508246415)
          ·
            refine ⟨842317990266684573762369623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561545326844456382508246415 842317990266684573762369623)
            ·
              refine ⟨1263476985400026860643554435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842317990266684573762369623 1263476985400026860643554435)
              ·
                refine ⟨1895215478100040290965331653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263476985400026860643554435 1895215478100040290965331653)
                ·
                  refine ⟨355352902143757554555999685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1895215478100040290965331653 355352902143757554555999685)
                  ·
                    refine ⟨66628669151954541479249941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 355352902143757554555999685 66628669151954541479249941)
                    ·
                      refine ⟨3123218866497869131839841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66628669151954541479249941 3123218866497869131839841)
                      ·
                        rfl

theorem cell23_6082447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_6082447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082447 prefixEnd_6082447 := by exact prefixLift 6082447
  have htrace : WordTrace (prefixWord ++ tailWord_6082447) baseStart_6082447 baseEnd_6082447 := by
    simpa [prefixWord, tailWord_6082447, baseEnd_6082447] using wordTrace_append hprefix tailTrace_6082447
  have hstable : (prefixWord ++ tailWord_6082447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082447).length < 2 ^ (prefixWord ++ tailWord_6082447).sum := by decide
  have hdescent : baseEnd_6082447 < baseStart_6082447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082511 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 4]
def baseStart_6082511 : Nat := 118140960795 + 6082511 * 2 ^ 59
def prefixEnd_6082511 : Nat := 4983230072969 + 3 ^ 40 * 6082511 * 2
def baseEnd_6082511 : Nat := 3123251729259756881439547

theorem tailTrace_6082511 : CollatzResearch.WordTrace tailWord_6082511 prefixEnd_6082511 3123251729259756881439547 := by
  unfold tailWord_6082511
  simp only [CollatzResearch.WordTrace]
  refine ⟨221847401667108932020007387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147898267778072621346671591 221847401667108932020007387)
  ·
    refine ⟨332771102500663398030011081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221847401667108932020007387 332771102500663398030011081)
    ·
      refine ⟨249578326875497548522508311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332771102500663398030011081 249578326875497548522508311)
      ·
        refine ⟨374367490313246322783762467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249578326875497548522508311 374367490313246322783762467)
        ·
          refine ⟨561551235469869484175643701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374367490313246322783762467 561551235469869484175643701)
          ·
            refine ⟨52645428325300264141466597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 561551235469869484175643701 52645428325300264141466597)
            ·
              refine ⟨9871017810993799526524987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52645428325300264141466597 9871017810993799526524987)
              ·
                refine ⟨14806526716490699289787481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9871017810993799526524987 14806526716490699289787481)
                ·
                  refine ⟨11104895037368024467340611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14806526716490699289787481 11104895037368024467340611)
                  ·
                    refine ⟨16657342556052036701010917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11104895037368024467340611 16657342556052036701010917)
                    ·
                      refine ⟨3123251729259756881439547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16657342556052036701010917 3123251729259756881439547)
                      ·
                        rfl

theorem cell23_6082511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 4].length) (baseStart_6082511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082511 prefixEnd_6082511 := by exact prefixLift 6082511
  have htrace : WordTrace (prefixWord ++ tailWord_6082511) baseStart_6082511 baseEnd_6082511 := by
    simpa [prefixWord, tailWord_6082511, baseEnd_6082511] using wordTrace_append hprefix tailTrace_6082511
  have hstable : (prefixWord ++ tailWord_6082511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082511).length < 2 ^ (prefixWord ++ tailWord_6082511).sum := by decide
  have hdescent : baseEnd_6082511 < baseStart_6082511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082595 : List Nat := [1, 1, 1, 4, 3, 1, 1, 6, 1, 1, 3]
def baseStart_6082595 : Nat := 118140960795 + 6082595 * 2 ^ 59
def prefixEnd_6082595 : Nat := 4983230072969 + 3 ^ 40 * 6082595 * 2
def baseEnd_6082595 : Nat := 3123294861634734552789161

theorem tailTrace_6082595 : CollatzResearch.WordTrace tailWord_6082595 prefixEnd_6082595 3123294861634734552789161 := by
  unfold tailWord_6082595
  simp only [CollatzResearch.WordTrace]
  refine ⟨221850465398804614366065239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147900310265869742910710159 221850465398804614366065239)
  ·
    refine ⟨332775698098206921549097859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221850465398804614366065239 332775698098206921549097859)
    ·
      refine ⟨499163547147310382323646789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332775698098206921549097859 499163547147310382323646789)
      ·
        refine ⟨93593165090120696685683773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 499163547147310382323646789 93593165090120696685683773)
        ·
          refine ⟨35097436908795261257131415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93593165090120696685683773 35097436908795261257131415)
          ·
            refine ⟨52646155363192891885697123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35097436908795261257131415 52646155363192891885697123)
            ·
              refine ⟨78969233044789337828545685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52646155363192891885697123 78969233044789337828545685)
              ·
                refine ⟨3701682798974500210713079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78969233044789337828545685 3701682798974500210713079)
                ·
                  refine ⟨5552524198461750316069619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701682798974500210713079 5552524198461750316069619)
                  ·
                    refine ⟨8328786297692625474104429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5552524198461750316069619 8328786297692625474104429)
                    ·
                      refine ⟨3123294861634734552789161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8328786297692625474104429 3123294861634734552789161)
                      ·
                        rfl

theorem cell23_6082595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_6082595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082595 prefixEnd_6082595 := by exact prefixLift 6082595
  have htrace : WordTrace (prefixWord ++ tailWord_6082595) baseStart_6082595 baseEnd_6082595 := by
    simpa [prefixWord, tailWord_6082595, baseEnd_6082595] using wordTrace_append hprefix tailTrace_6082595
  have hstable : (prefixWord ++ tailWord_6082595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082595).length < 2 ^ (prefixWord ++ tailWord_6082595).sum := by decide
  have hdescent : baseEnd_6082595 < baseStart_6082595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082611 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 1, 6]
def baseStart_6082611 : Nat := 118140960795 + 6082611 * 2 ^ 59
def prefixEnd_6082611 : Nat := 4983230072969 + 3 ^ 40 * 6082611 * 2
def baseEnd_6082611 : Nat := 1041101025775068830063029

theorem tailTrace_6082611 : CollatzResearch.WordTrace tailWord_6082611 prefixEnd_6082611 1041101025775068830063029 := by
  unfold tailWord_6082611
  simp only [CollatzResearch.WordTrace]
  refine ⟨221851048966746649098647687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147900699311164432732431791 221851048966746649098647687)
  ·
    refine ⟨332776573450119973647971531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221851048966746649098647687 332776573450119973647971531)
    ·
      refine ⟨499164860175179960471957297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332776573450119973647971531 499164860175179960471957297)
      ·
        refine ⟨374373645131384970353967973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499164860175179960471957297 374373645131384970353967973)
        ·
          refine ⟨70195058462134681941368995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374373645131384970353967973 70195058462134681941368995)
          ·
            refine ⟨105292587693202022912053493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70195058462134681941368995 105292587693202022912053493)
            ·
              refine ⟨9871180096237689648005015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105292587693202022912053493 9871180096237689648005015)
              ·
                refine ⟨14806770144356534472007523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9871180096237689648005015 14806770144356534472007523)
                ·
                  refine ⟨22210155216534801708011285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14806770144356534472007523 22210155216534801708011285)
                  ·
                    refine ⟨1041101025775068830063029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22210155216534801708011285 1041101025775068830063029)
                    ·
                      rfl

theorem cell23_6082611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 6].length) (baseStart_6082611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082611 prefixEnd_6082611 := by exact prefixLift 6082611
  have htrace : WordTrace (prefixWord ++ tailWord_6082611) baseStart_6082611 baseEnd_6082611 := by
    simpa [prefixWord, tailWord_6082611, baseEnd_6082611] using wordTrace_append hprefix tailTrace_6082611
  have hstable : (prefixWord ++ tailWord_6082611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082611).length < 2 ^ (prefixWord ++ tailWord_6082611).sum := by decide
  have hdescent : baseEnd_6082611 < baseStart_6082611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082621 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_6082621 : Nat := 118140960795 + 6082621 * 2 ^ 59
def prefixEnd_6082621 : Nat := 4983230072969 + 3 ^ 40 * 6082621 * 2
def baseEnd_6082621 : Nat := 3123308212131751451064041

theorem tailTrace_6082621 : CollatzResearch.WordTrace tailWord_6082621 prefixEnd_6082621 3123308212131751451064041 := by
  unfold tailWord_6082621
  simp only [CollatzResearch.WordTrace]
  refine ⟨221851413696710420806511717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147900942464473613871007811 221851413696710420806511717)
  ·
    refine ⟨41597140068133203901220947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221851413696710420806511717 41597140068133203901220947)
    ·
      refine ⟨62395710102199805851831421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41597140068133203901220947 62395710102199805851831421)
      ·
        refine ⟨23398391288324927194436783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62395710102199805851831421 23398391288324927194436783)
        ·
          refine ⟨35097586932487390791655175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23398391288324927194436783 35097586932487390791655175)
          ·
            refine ⟨52646380398731086187482763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35097586932487390791655175 52646380398731086187482763)
            ·
              refine ⟨78969570598096629281224145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52646380398731086187482763 78969570598096629281224145)
              ·
                refine ⟨59227177948572471960918109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78969570598096629281224145 59227177948572471960918109)
                ·
                  refine ⟨22210191730714676985344291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59227177948572471960918109 22210191730714676985344291)
                  ·
                    refine ⟨33315287596072015478016437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22210191730714676985344291 33315287596072015478016437)
                    ·
                      refine ⟨3123308212131751451064041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33315287596072015478016437 3123308212131751451064041)
                      ·
                        rfl

theorem cell23_6082621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_6082621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082621 prefixEnd_6082621 := by exact prefixLift 6082621
  have htrace : WordTrace (prefixWord ++ tailWord_6082621) baseStart_6082621 baseEnd_6082621 := by
    simpa [prefixWord, tailWord_6082621, baseEnd_6082621] using wordTrace_append hprefix tailTrace_6082621
  have hstable : (prefixWord ++ tailWord_6082621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082621).length < 2 ^ (prefixWord ++ tailWord_6082621).sum := by decide
  have hdescent : baseEnd_6082621 < baseStart_6082621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082631 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_6082631 : Nat := 118140960795 + 6082631 * 2 ^ 59
def prefixEnd_6082631 : Nat := 4983230072969 + 3 ^ 40 * 6082631 * 2
def baseEnd_6082631 : Nat := 3123313346938296411938995

theorem tailTrace_6082631 : CollatzResearch.WordTrace tailWord_6082631 prefixEnd_6082631 3123313346938296411938995 := by
  unfold tailWord_6082631
  simp only [CollatzResearch.WordTrace]
  refine ⟨221851778426674192514375747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147901185617782795009583831 221851778426674192514375747)
  ·
    refine ⟨332777667640011288771563621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221851778426674192514375747 332777667640011288771563621)
    ·
      refine ⟨62395812682502116644668179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332777667640011288771563621 62395812682502116644668179)
      ·
        refine ⟨93593719023753174967002269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62395812682502116644668179 93593719023753174967002269)
        ·
          refine ⟨35097644633907440612625851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93593719023753174967002269 35097644633907440612625851)
          ·
            refine ⟨52646466950861160918938777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35097644633907440612625851 52646466950861160918938777)
            ·
              refine ⟨39484850213145870689204083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52646466950861160918938777 39484850213145870689204083)
              ·
                refine ⟨59227275319718806033806125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39484850213145870689204083 59227275319718806033806125)
                ·
                  refine ⟨22210228244894552262677297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59227275319718806033806125 22210228244894552262677297)
                  ·
                    refine ⟨16657671183670914197007973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22210228244894552262677297 16657671183670914197007973)
                    ·
                      refine ⟨3123313346938296411938995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16657671183670914197007973 3123313346938296411938995)
                      ·
                        rfl

theorem cell23_6082631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_6082631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082631 prefixEnd_6082631 := by exact prefixLift 6082631
  have htrace : WordTrace (prefixWord ++ tailWord_6082631) baseStart_6082631 baseEnd_6082631 := by
    simpa [prefixWord, tailWord_6082631, baseEnd_6082631] using wordTrace_append hprefix tailTrace_6082631
  have hstable : (prefixWord ++ tailWord_6082631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082631).length < 2 ^ (prefixWord ++ tailWord_6082631).sum := by decide
  have hdescent : baseEnd_6082631 < baseStart_6082631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082638 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_6082638 : Nat := 118140960795 + 6082638 * 2 ^ 59
def prefixEnd_6082638 : Nat := 4983230072969 + 3 ^ 40 * 6082638 * 2
def baseEnd_6082638 : Nat := 3123316941302877884551463

theorem tailTrace_6082638 : CollatzResearch.WordTrace tailWord_6082638 prefixEnd_6082638 3123316941302877884551463 := by
  unfold tailWord_6082638
  simp only [CollatzResearch.WordTrace]
  refine ⟨27731504217206104088735071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147901355825099221806587045 27731504217206104088735071)
  ·
    refine ⟨41597256325809156133102607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27731504217206104088735071 41597256325809156133102607)
    ·
      refine ⟨62395884488713734199653911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41597256325809156133102607 62395884488713734199653911)
      ·
        refine ⟨93593826733070601299480867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62395884488713734199653911 93593826733070601299480867)
        ·
          refine ⟨140390740099605901949221301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93593826733070601299480867 140390740099605901949221301)
          ·
            refine ⟨13161631884338053307739497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140390740099605901949221301 13161631884338053307739497)
            ·
              refine ⟨9871223913253539980804623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13161631884338053307739497 9871223913253539980804623)
              ·
                refine ⟨14806835869880309971206935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9871223913253539980804623 14806835869880309971206935)
                ·
                  refine ⟨22210253804820464956810403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14806835869880309971206935 22210253804820464956810403)
                  ·
                    refine ⟨33315380707230697435215605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22210253804820464956810403 33315380707230697435215605)
                    ·
                      refine ⟨3123316941302877884551463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33315380707230697435215605 3123316941302877884551463)
                      ·
                        rfl

theorem cell23_6082638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_6082638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082638 prefixEnd_6082638 := by exact prefixLift 6082638
  have htrace : WordTrace (prefixWord ++ tailWord_6082638) baseStart_6082638 baseEnd_6082638 := by
    simpa [prefixWord, tailWord_6082638, baseEnd_6082638] using wordTrace_append hprefix tailTrace_6082638
  have hstable : (prefixWord ++ tailWord_6082638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082638).length < 2 ^ (prefixWord ++ tailWord_6082638).sum := by decide
  have hdescent : baseEnd_6082638 < baseStart_6082638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082652 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_6082652 : Nat := 118140960795 + 6082652 * 2 ^ 59
def prefixEnd_6082652 : Nat := 4983230072969 + 3 ^ 40 * 6082652 * 2
def baseEnd_6082652 : Nat := 3123324130032040829776399

theorem tailTrace_6082652 : CollatzResearch.WordTrace tailWord_6082652 prefixEnd_6082652 3123324130032040829776399 := by
  unfold tailWord_6082652
  simp only [CollatzResearch.WordTrace]
  refine ⟨110926272179799056550445105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147901696239732075400593473 110926272179799056550445105)
  ·
    refine ⟨83194704134849292412833829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110926272179799056550445105 83194704134849292412833829)
    ·
      refine ⟨15599007025284242327406343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83194704134849292412833829 15599007025284242327406343)
      ·
        refine ⟨23398510537926363491109515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15599007025284242327406343 23398510537926363491109515)
        ·
          refine ⟨35097765806889545236664273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23398510537926363491109515 35097765806889545236664273)
          ·
            refine ⟨26323324355167158927498205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35097765806889545236664273 26323324355167158927498205)
            ·
              refine ⟨9871246633187684597811827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26323324355167158927498205 9871246633187684597811827)
              ·
                refine ⟨14806869949781526896717741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9871246633187684597811827 14806869949781526896717741)
                ·
                  refine ⟨5552576231168072586269153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14806869949781526896717741 5552576231168072586269153)
                  ·
                    refine ⟨4164432173376054439701865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5552576231168072586269153 4164432173376054439701865)
                    ·
                      refine ⟨3123324130032040829776399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164432173376054439701865 3123324130032040829776399)
                      ·
                        rfl

theorem cell23_6082652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_6082652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082652 prefixEnd_6082652 := by exact prefixLift 6082652
  have htrace : WordTrace (prefixWord ++ tailWord_6082652) baseStart_6082652 baseEnd_6082652 := by
    simpa [prefixWord, tailWord_6082652, baseEnd_6082652] using wordTrace_append hprefix tailTrace_6082652
  have hstable : (prefixWord ++ tailWord_6082652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082652).length < 2 ^ (prefixWord ++ tailWord_6082652).sum := by decide
  have hdescent : baseEnd_6082652 < baseStart_6082652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082695 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 1, 3, 2]
def baseStart_6082695 : Nat := 118140960795 + 6082695 * 2 ^ 59
def prefixEnd_6082695 : Nat := 4983230072969 + 3 ^ 40 * 6082695 * 2
def baseEnd_6082695 : Nat := 3123346209700184161538701

theorem tailTrace_6082695 : CollatzResearch.WordTrace tailWord_6082695 prefixEnd_6082695 3123346209700184161538701 := by
  unfold tailWord_6082695
  simp only [CollatzResearch.WordTrace]
  refine ⟨221854112698442331444705539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147902741798961554296470359 221854112698442331444705539)
  ·
    refine ⟨332781169047663497167058309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221854112698442331444705539 332781169047663497167058309)
    ·
      refine ⟨62396469196436905718823433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332781169047663497167058309 62396469196436905718823433)
      ·
        refine ⟨46797351897327679289117575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62396469196436905718823433 46797351897327679289117575)
        ·
          refine ⟨70196027845991518933676363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46797351897327679289117575 70196027845991518933676363)
          ·
            refine ⟨105294041768987278400514545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70196027845991518933676363 105294041768987278400514545)
            ·
              refine ⟨78970531326740458800385909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105294041768987278400514545 78970531326740458800385909)
              ·
                refine ⟨7403487311881918012536179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78970531326740458800385909 7403487311881918012536179)
                ·
                  refine ⟨11105230967822877018804269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7403487311881918012536179 11105230967822877018804269)
                  ·
                    refine ⟨4164461612933578882051601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11105230967822877018804269 4164461612933578882051601)
                    ·
                      refine ⟨3123346209700184161538701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164461612933578882051601 3123346209700184161538701)
                      ·
                        rfl

theorem cell23_6082695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_6082695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082695 prefixEnd_6082695 := by exact prefixLift 6082695
  have htrace : WordTrace (prefixWord ++ tailWord_6082695) baseStart_6082695 baseEnd_6082695 := by
    simpa [prefixWord, tailWord_6082695, baseEnd_6082695] using wordTrace_append hprefix tailTrace_6082695
  have hstable : (prefixWord ++ tailWord_6082695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082695).length < 2 ^ (prefixWord ++ tailWord_6082695).sum := by decide
  have hdescent : baseEnd_6082695 < baseStart_6082695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082725 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 1, 4, 2]
def baseStart_6082725 : Nat := 118140960795 + 6082725 * 2 ^ 59
def prefixEnd_6082725 : Nat := 4983230072969 + 3 ^ 40 * 6082725 * 2
def baseEnd_6082725 : Nat := 3123361614119819044163563

theorem tailTrace_6082725 : CollatzResearch.WordTrace tailWord_6082725 prefixEnd_6082725 3123361614119819044163563 := by
  unfold tailWord_6082725
  simp only [CollatzResearch.WordTrace]
  refine ⟨221855206888333646568297629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147903471258889097712198419 221855206888333646568297629)
  ·
    refine ⟨83195702583125117463111611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221855206888333646568297629 83195702583125117463111611)
    ·
      refine ⟨124793553874687676194667417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83195702583125117463111611 124793553874687676194667417)
      ·
        refine ⟨93595165406015757146000563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124793553874687676194667417 93595165406015757146000563)
        ·
          refine ⟨140392748109023635719000845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93595165406015757146000563 140392748109023635719000845)
          ·
            refine ⟨52647280540883863394625317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140392748109023635719000845 52647280540883863394625317)
            ·
              refine ⟨9871365101415724386492247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52647280540883863394625317 9871365101415724386492247)
              ·
                refine ⟨14807047652123586579738371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9871365101415724386492247 14807047652123586579738371)
                ·
                  refine ⟨22210571478185379869607557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14807047652123586579738371 22210571478185379869607557)
                  ·
                    refine ⟨4164482152159758725551417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22210571478185379869607557 4164482152159758725551417)
                    ·
                      refine ⟨3123361614119819044163563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164482152159758725551417 3123361614119819044163563)
                      ·
                        rfl

theorem cell23_6082725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_6082725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082725 prefixEnd_6082725 := by exact prefixLift 6082725
  have htrace : WordTrace (prefixWord ++ tailWord_6082725) baseStart_6082725 baseEnd_6082725 := by
    simpa [prefixWord, tailWord_6082725, baseEnd_6082725] using wordTrace_append hprefix tailTrace_6082725
  have hstable : (prefixWord ++ tailWord_6082725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082725).length < 2 ^ (prefixWord ++ tailWord_6082725).sum := by decide
  have hdescent : baseEnd_6082725 < baseStart_6082725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082740 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_6082740 : Nat := 118140960795 + 6082740 * 2 ^ 59
def prefixEnd_6082740 : Nat := 4983230072969 + 3 ^ 40 * 6082740 * 2
def baseEnd_6082740 : Nat := 3123369316329636485475995

theorem tailTrace_6082740 : CollatzResearch.WordTrace tailWord_6082740 prefixEnd_6082740 3123369316329636485475995 := by
  unfold tailWord_6082740
  simp only [CollatzResearch.WordTrace]
  refine ⟨110927876991639652065046837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147903835988852869420062449 110927876991639652065046837)
  ·
    refine ⟨10399488467966217381098141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110927876991639652065046837 10399488467966217381098141)
    ·
      refine ⟨3899808175487331517911803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10399488467966217381098141 3899808175487331517911803)
      ·
        refine ⟨5849712263230997276867705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3899808175487331517911803 5849712263230997276867705)
        ·
          refine ⟨4387284197423247957650779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5849712263230997276867705 4387284197423247957650779)
          ·
            refine ⟨6580926296134871936476169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387284197423247957650779 6580926296134871936476169)
            ·
              refine ⟨4935694722101153952357127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6580926296134871936476169 4935694722101153952357127)
              ·
                refine ⟨7403542083151730928535691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935694722101153952357127 7403542083151730928535691)
                ·
                  refine ⟨11105313124727596392803537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7403542083151730928535691 11105313124727596392803537)
                  ·
                    refine ⟨8328984843545697294602653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11105313124727596392803537 8328984843545697294602653)
                    ·
                      refine ⟨3123369316329636485475995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8328984843545697294602653 3123369316329636485475995)
                      ·
                        rfl

theorem cell23_6082740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_6082740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082740 prefixEnd_6082740 := by exact prefixLift 6082740
  have htrace : WordTrace (prefixWord ++ tailWord_6082740) baseStart_6082740 baseEnd_6082740 := by
    simpa [prefixWord, tailWord_6082740, baseEnd_6082740] using wordTrace_append hprefix tailTrace_6082740
  have hstable : (prefixWord ++ tailWord_6082740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082740).length < 2 ^ (prefixWord ++ tailWord_6082740).sum := by decide
  have hdescent : baseEnd_6082740 < baseStart_6082740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082808 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 5, 4]
def baseStart_6082808 : Nat := 118140960795 + 6082808 * 2 ^ 59
def prefixEnd_6082808 : Nat := 4983230072969 + 3 ^ 40 * 6082808 * 2
def baseEnd_6082808 : Nat := 1041134744338047406475227

theorem tailTrace_6082808 : CollatzResearch.WordTrace tailWord_6082808 prefixEnd_6082808 1041134744338047406475227 := by
  unfold tailWord_6082808
  simp only [CollatzResearch.WordTrace]
  refine ⟨110929117073516475871784539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147905489431355301162379385 110929117073516475871784539)
  ·
    refine ⟨166393675610274713807676809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110929117073516475871784539 166393675610274713807676809)
    ·
      refine ⟨124795256707706035355757607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166393675610274713807676809 124795256707706035355757607)
      ·
        refine ⟨187192885061559053033636411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124795256707706035355757607 187192885061559053033636411)
        ·
          refine ⟨280789327592338579550454617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187192885061559053033636411 280789327592338579550454617)
          ·
            refine ⟨210591995694253934662840963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280789327592338579550454617 210591995694253934662840963)
            ·
              refine ⟨315887993541380901994261445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210591995694253934662840963 315887993541380901994261445)
              ·
                refine ⟨59228998789008919123924021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315887993541380901994261445 59228998789008919123924021)
                ·
                  refine ⟨5552718636469586167867877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59228998789008919123924021 5552718636469586167867877)
                  ·
                    refine ⟨1041134744338047406475227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5552718636469586167867877 1041134744338047406475227)
                    ·
                      rfl

theorem cell23_6082808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_6082808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082808 prefixEnd_6082808 := by exact prefixLift 6082808
  have htrace : WordTrace (prefixWord ++ tailWord_6082808) baseStart_6082808 baseEnd_6082808 := by
    simpa [prefixWord, tailWord_6082808, baseEnd_6082808] using wordTrace_append hprefix tailTrace_6082808
  have hstable : (prefixWord ++ tailWord_6082808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082808).length < 2 ^ (prefixWord ++ tailWord_6082808).sum := by decide
  have hdescent : baseEnd_6082808 < baseStart_6082808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082825 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 3, 4]
def baseStart_6082825 : Nat := 118140960795 + 6082825 * 2 ^ 59
def prefixEnd_6082825 : Nat := 4983230072969 + 3 ^ 40 * 6082825 * 2
def baseEnd_6082825 : Nat := 1041137654061756217637701

theorem tailTrace_6082825 : CollatzResearch.WordTrace tailWord_6082825 prefixEnd_6082825 1041137654061756217637701 := by
  unfold tailWord_6082825
  simp only [CollatzResearch.WordTrace]
  refine ⟨221858854187971363646937929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147905902791980909097958619 221858854187971363646937929)
  ·
    refine ⟨166394140640978522735203447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221858854187971363646937929 166394140640978522735203447)
    ·
      refine ⟨249591210961467784102805171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166394140640978522735203447 249591210961467784102805171)
      ·
        refine ⟨374386816442201676154207757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249591210961467784102805171 374386816442201676154207757)
        ·
          refine ⟨140395056165825628557827909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374386816442201676154207757 140395056165825628557827909)
          ·
            refine ⟨26324073031092305354592733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140395056165825628557827909 26324073031092305354592733)
            ·
              refine ⟨9871527386659614507972275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26324073031092305354592733 9871527386659614507972275)
              ·
                refine ⟨14807291079989421761958413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9871527386659614507972275 14807291079989421761958413)
                ·
                  refine ⟨5552734154996033160734405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14807291079989421761958413 5552734154996033160734405)
                  ·
                    refine ⟨1041137654061756217637701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5552734154996033160734405 1041137654061756217637701)
                    ·
                      rfl

theorem cell23_6082825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 4].length) (baseStart_6082825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082825 prefixEnd_6082825 := by exact prefixLift 6082825
  have htrace : WordTrace (prefixWord ++ tailWord_6082825) baseStart_6082825 baseEnd_6082825 := by
    simpa [prefixWord, tailWord_6082825, baseEnd_6082825] using wordTrace_append hprefix tailTrace_6082825
  have hstable : (prefixWord ++ tailWord_6082825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082825).length < 2 ^ (prefixWord ++ tailWord_6082825).sum := by decide
  have hdescent : baseEnd_6082825 < baseStart_6082825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082852 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_6082852 : Nat := 118140960795 + 6082852 * 2 ^ 59
def prefixEnd_6082852 : Nat := 4983230072969 + 3 ^ 40 * 6082852 * 2
def baseEnd_6082852 : Nat := 3123426826162940047275479

theorem tailTrace_6082852 : CollatzResearch.WordTrace tailWord_6082852 prefixEnd_6082852 3123426826162940047275479 := by
  unfold tailWord_6082852
  simp only [CollatzResearch.WordTrace]
  refine ⟨110929919479436773629085405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147906559305915698172113873 110929919479436773629085405)
  ·
    refine ⟨41598719804788790110907027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110929919479436773629085405 41598719804788790110907027)
    ·
      refine ⟨62398079707183185166360541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41598719804788790110907027 62398079707183185166360541)
      ·
        refine ⟨23399279890193694437385203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62398079707183185166360541 23399279890193694437385203)
        ·
          refine ⟨35098919835290541656077805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23399279890193694437385203 35098919835290541656077805)
          ·
            refine ⟨13162094938233953121029177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35098919835290541656077805 13162094938233953121029177)
            ·
              refine ⟨9871571203675464840771883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13162094938233953121029177 9871571203675464840771883)
              ·
                refine ⟨14807356805513197261157825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9871571203675464840771883 14807356805513197261157825)
                ·
                  refine ⟨11105517604134897945868369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14807356805513197261157825 11105517604134897945868369)
                  ·
                    refine ⟨8329138203101173459401277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11105517604134897945868369 8329138203101173459401277)
                    ·
                      refine ⟨3123426826162940047275479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8329138203101173459401277 3123426826162940047275479)
                      ·
                        rfl

theorem cell23_6082852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_6082852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082852 prefixEnd_6082852 := by exact prefixLift 6082852
  have htrace : WordTrace (prefixWord ++ tailWord_6082852) baseStart_6082852 baseEnd_6082852 := by
    simpa [prefixWord, tailWord_6082852, baseEnd_6082852] using wordTrace_append hprefix tailTrace_6082852
  have hstable : (prefixWord ++ tailWord_6082852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082852).length < 2 ^ (prefixWord ++ tailWord_6082852).sum := by decide
  have hdescent : baseEnd_6082852 < baseStart_6082852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082905 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 4]
def baseStart_6082905 : Nat := 118140960795 + 6082905 * 2 ^ 59
def prefixEnd_6082905 : Nat := 4983230072969 + 3 ^ 40 * 6082905 * 2
def baseEnd_6082905 : Nat := 3123454040637628339912735

theorem tailTrace_6082905 : CollatzResearch.WordTrace tailWord_6082905 prefixEnd_6082905 3123454040637628339912735 := by
  unfold tailWord_6082905
  simp only [CollatzResearch.WordTrace]
  refine ⟨221861772027681537309850169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147907848018454358206566779 221861772027681537309850169)
  ·
    refine ⟨166396329020761152982387627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221861772027681537309850169 166396329020761152982387627)
    ·
      refine ⟨249594493531141729473581441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166396329020761152982387627 249594493531141729473581441)
      ·
        refine ⟨187195870148356297105186081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249594493531141729473581441 187195870148356297105186081)
        ·
          refine ⟨140396902611267222828889561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187195870148356297105186081 140396902611267222828889561)
          ·
            refine ⟨105297676958450417121667171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140396902611267222828889561 105297676958450417121667171)
            ·
              refine ⟨157946515437675625682500757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105297676958450417121667171 157946515437675625682500757)
              ·
                refine ⟨7403742911141044953867223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157946515437675625682500757 7403742911141044953867223)
                ·
                  refine ⟨11105614366711567430800835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7403742911141044953867223 11105614366711567430800835)
                  ·
                    refine ⟨16658421550067351146201253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11105614366711567430800835 16658421550067351146201253)
                    ·
                      refine ⟨3123454040637628339912735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16658421550067351146201253 3123454040637628339912735)
                      ·
                        rfl

theorem cell23_6082905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_6082905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082905 prefixEnd_6082905 := by exact prefixLift 6082905
  have htrace : WordTrace (prefixWord ++ tailWord_6082905) baseStart_6082905 baseEnd_6082905 := by
    simpa [prefixWord, tailWord_6082905, baseEnd_6082905] using wordTrace_append hprefix tailTrace_6082905
  have hstable : (prefixWord ++ tailWord_6082905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082905).length < 2 ^ (prefixWord ++ tailWord_6082905).sum := by decide
  have hdescent : baseEnd_6082905 < baseStart_6082905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082915 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 4, 4]
def baseStart_6082915 : Nat := 118140960795 + 6082915 * 2 ^ 59
def prefixEnd_6082915 : Nat := 4983230072969 + 3 ^ 40 * 6082915 * 2
def baseEnd_6082915 : Nat := 1041153058481391100262563

theorem tailTrace_6082915 : CollatzResearch.WordTrace tailWord_6082915 prefixEnd_6082915 1041153058481391100262563 := by
  unfold tailWord_6082915
  simp only [CollatzResearch.WordTrace]
  refine ⟨221862136757645309017714199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147908091171763539345142799 221862136757645309017714199)
  ·
    refine ⟨332793205136467963526571299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221862136757645309017714199 332793205136467963526571299)
    ·
      refine ⟨499189807704701945289856949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332793205136467963526571299 499189807704701945289856949)
      ·
        refine ⟨46799044472315807370924089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 499189807704701945289856949 46799044472315807370924089)
        ·
          refine ⟨35099283354236855528193067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46799044472315807370924089 35099283354236855528193067)
          ·
            refine ⟨52648925031355283292289601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35099283354236855528193067 52648925031355283292289601)
            ·
              refine ⟨39486693773516462469217201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52648925031355283292289601 39486693773516462469217201)
              ·
                refine ⟨29615020330137346851912901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39486693773516462469217201 29615020330137346851912901)
                ·
                  refine ⟨5552816311900752534733669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29615020330137346851912901 5552816311900752534733669)
                  ·
                    refine ⟨1041153058481391100262563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5552816311900752534733669 1041153058481391100262563)
                    ·
                      rfl

theorem cell23_6082915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 4].length) (baseStart_6082915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082915 prefixEnd_6082915 := by exact prefixLift 6082915
  have htrace : WordTrace (prefixWord ++ tailWord_6082915) baseStart_6082915 baseEnd_6082915 := by
    simpa [prefixWord, tailWord_6082915, baseEnd_6082915] using wordTrace_append hprefix tailTrace_6082915
  have hstable : (prefixWord ++ tailWord_6082915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082915).length < 2 ^ (prefixWord ++ tailWord_6082915).sum := by decide
  have hdescent : baseEnd_6082915 < baseStart_6082915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082919 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 1, 5]
def baseStart_6082919 : Nat := 118140960795 + 6082919 * 2 ^ 59
def prefixEnd_6082919 : Nat := 4983230072969 + 3 ^ 40 * 6082919 * 2
def baseEnd_6082919 : Nat := 1041153743122263761712557

theorem tailTrace_6082919 : CollatzResearch.WordTrace tailWord_6082919 prefixEnd_6082919 1041153743122263761712557 := by
  unfold tailWord_6082919
  simp only [CollatzResearch.WordTrace]
  refine ⟨221862282649630817700859811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147908188433087211800573207 221862282649630817700859811)
  ·
    refine ⟨332793423974446226551289717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221862282649630817700859811 332793423974446226551289717)
    ·
      refine ⟨31199383497604333739183411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 332793423974446226551289717 31199383497604333739183411)
      ·
        refine ⟨46799075246406500608775117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31199383497604333739183411 46799075246406500608775117)
        ·
          refine ⟨17549653217402437728290669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46799075246406500608775117 17549653217402437728290669)
          ·
            refine ⟨6581119956525914148109001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17549653217402437728290669 6581119956525914148109001)
            ·
              refine ⟨4935839967394435611081751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6581119956525914148109001 4935839967394435611081751)
              ·
                refine ⟨7403759951091653416622627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935839967394435611081751 7403759951091653416622627)
                ·
                  refine ⟨11105639926637480124933941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7403759951091653416622627 11105639926637480124933941)
                  ·
                    refine ⟨1041153743122263761712557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11105639926637480124933941 1041153743122263761712557)
                    ·
                      rfl

theorem cell23_6082919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_6082919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082919 prefixEnd_6082919 := by exact prefixLift 6082919
  have htrace : WordTrace (prefixWord ++ tailWord_6082919) baseStart_6082919 baseEnd_6082919 := by
    simpa [prefixWord, tailWord_6082919, baseEnd_6082919] using wordTrace_append hprefix tailTrace_6082919
  have hstable : (prefixWord ++ tailWord_6082919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082919).length < 2 ^ (prefixWord ++ tailWord_6082919).sum := by decide
  have hdescent : baseEnd_6082919 < baseStart_6082919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082925 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6082925 : Nat := 118140960795 + 6082925 * 2 ^ 59
def prefixEnd_6082925 : Nat := 4983230072969 + 3 ^ 40 * 6082925 * 2
def baseEnd_6082925 : Nat := 3123464310250718261662643

theorem tailTrace_6082925 : CollatzResearch.WordTrace tailWord_6082925 prefixEnd_6082925 3123464310250718261662643 := by
  unfold tailWord_6082925
  simp only [CollatzResearch.WordTrace]
  refine ⟨221862501487609080725578229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147908334325072720483718819 221862501487609080725578229)
  ·
    refine ⟨20799609514463351318022959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221862501487609080725578229 20799609514463351318022959)
    ·
      refine ⟨31199414271695026977034439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20799609514463351318022959 31199414271695026977034439)
      ·
        refine ⟨46799121407542540465551659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31199414271695026977034439 46799121407542540465551659)
        ·
          refine ⟨70198682111313810698327489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46799121407542540465551659 70198682111313810698327489)
          ·
            refine ⟨52649011583485358023745617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70198682111313810698327489 52649011583485358023745617)
            ·
              refine ⟨39486758687614018517809213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52649011583485358023745617 39486758687614018517809213)
              ·
                refine ⟨14807534507855256944178455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39486758687614018517809213 14807534507855256944178455)
                ·
                  refine ⟨22211301761782885416267683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14807534507855256944178455 22211301761782885416267683)
                  ·
                    refine ⟨33316952642674328124401525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22211301761782885416267683 33316952642674328124401525)
                    ·
                      refine ⟨3123464310250718261662643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33316952642674328124401525 3123464310250718261662643)
                      ·
                        rfl

theorem cell23_6082925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6082925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082925 prefixEnd_6082925 := by exact prefixLift 6082925
  have htrace : WordTrace (prefixWord ++ tailWord_6082925) baseStart_6082925 baseEnd_6082925 := by
    simpa [prefixWord, tailWord_6082925, baseEnd_6082925] using wordTrace_append hprefix tailTrace_6082925
  have hstable : (prefixWord ++ tailWord_6082925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082925).length < 2 ^ (prefixWord ++ tailWord_6082925).sum := by decide
  have hdescent : baseEnd_6082925 < baseStart_6082925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082928 : List Nat := [2, 1, 1, 1, 4, 4, 10]
def baseStart_6082928 : Nat := 118140960795 + 6082928 * 2 ^ 59
def prefixEnd_6082928 : Nat := 4983230072969 + 3 ^ 40 * 6082928 * 2
def baseEnd_6082928 : Nat := 38561306798675083332409

theorem tailTrace_6082928 : CollatzResearch.WordTrace tailWord_6082928 prefixEnd_6082928 38561306798675083332409 := by
  unfold tailWord_6082928
  simp only [CollatzResearch.WordTrace]
  refine ⟨110931305453299106118968719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147908407271065474825291625 110931305453299106118968719)
  ·
    refine ⟨166396958179948659178453079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110931305453299106118968719 166396958179948659178453079)
    ·
      refine ⟨249595437269922988767679619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166396958179948659178453079 249595437269922988767679619)
      ·
        refine ⟨374393155904884483151519429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249595437269922988767679619 374393155904884483151519429)
        ·
          refine ⟨70198716732165840590909893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374393155904884483151519429 70198716732165840590909893)
          ·
            refine ⟨13162259387281095110795605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70198716732165840590909893 13162259387281095110795605)
            ·
              refine ⟨38561306798675083332409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13162259387281095110795605 38561306798675083332409)
              ·
                rfl

theorem cell23_6082928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 10].length) (baseStart_6082928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082928 prefixEnd_6082928 := by exact prefixLift 6082928
  have htrace : WordTrace (prefixWord ++ tailWord_6082928) baseStart_6082928 baseEnd_6082928 := by
    simpa [prefixWord, tailWord_6082928, baseEnd_6082928] using wordTrace_append hprefix tailTrace_6082928
  have hstable : (prefixWord ++ tailWord_6082928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082928).length < 2 ^ (prefixWord ++ tailWord_6082928).sum := by decide
  have hdescent : baseEnd_6082928 < baseStart_6082928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6082939 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 3, 2, 2]
def baseStart_6082939 : Nat := 118140960795 + 6082939 * 2 ^ 59
def prefixEnd_6082939 : Nat := 4983230072969 + 3 ^ 40 * 6082939 * 2
def baseEnd_6082939 : Nat := 3123471498979881206887579

theorem tailTrace_6082939 : CollatzResearch.WordTrace tailWord_6082939 prefixEnd_6082939 3123471498979881206887579 := by
  unfold tailWord_6082939
  simp only [CollatzResearch.WordTrace]
  refine ⟨221863012109558361116587871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147908674739705574077725247 221863012109558361116587871)
  ·
    refine ⟨332794518164337541674881807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221863012109558361116587871 332794518164337541674881807)
    ·
      refine ⟨499191777246506312512322711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332794518164337541674881807 499191777246506312512322711)
      ·
        refine ⟨748787665869759468768484067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499191777246506312512322711 748787665869759468768484067)
        ·
          refine ⟨1123181498804639203152726101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748787665869759468768484067 1123181498804639203152726101)
          ·
            refine ⟨13162283189116865661946009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1123181498804639203152726101 13162283189116865661946009)
            ·
              refine ⟨9871712391837649246459507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13162283189116865661946009 9871712391837649246459507)
              ·
                refine ⟨14807568587756473869689261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9871712391837649246459507 14807568587756473869689261)
                ·
                  refine ⟨5552838220408677701133473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14807568587756473869689261 5552838220408677701133473)
                  ·
                    refine ⟨4164628665306508275850105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5552838220408677701133473 4164628665306508275850105)
                    ·
                      refine ⟨3123471498979881206887579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164628665306508275850105 3123471498979881206887579)
                      ·
                        rfl

theorem cell23_6082939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 2, 2].length) (baseStart_6082939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6082939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6082939 prefixEnd_6082939 := by exact prefixLift 6082939
  have htrace : WordTrace (prefixWord ++ tailWord_6082939) baseStart_6082939 baseEnd_6082939 := by
    simpa [prefixWord, tailWord_6082939, baseEnd_6082939] using wordTrace_append hprefix tailTrace_6082939
  have hstable : (prefixWord ++ tailWord_6082939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6082939).length < 2 ^ (prefixWord ++ tailWord_6082939).sum := by decide
  have hdescent : baseEnd_6082939 < baseStart_6082939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6082939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083006 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_6083006 : Nat := 118140960795 + 6083006 * 2 ^ 59
def prefixEnd_6083006 : Nat := 4983230072969 + 3 ^ 40 * 6083006 * 2
def baseEnd_6083006 : Nat := 3123505902183732444749771

theorem tailTrace_6083006 : CollatzResearch.WordTrace tailWord_6083006 prefixEnd_6083006 3123505902183732444749771 := by
  unfold tailWord_6083006
  simp only [CollatzResearch.WordTrace]
  refine ⟨27733181975039453944909609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147910303866877087706184581 27733181975039453944909609)
  ·
    refine ⟨20799886481279590458682207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27733181975039453944909609 20799886481279590458682207)
    ·
      refine ⟨31199829721919385688023311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20799886481279590458682207 31199829721919385688023311)
      ·
        refine ⟨46799744582879078532034967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31199829721919385688023311 46799744582879078532034967)
        ·
          refine ⟨70199616874318617798052451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46799744582879078532034967 70199616874318617798052451)
          ·
            refine ⟨105299425311477926697078677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70199616874318617798052451 105299425311477926697078677)
            ·
              refine ⟨4935910561475527813925563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105299425311477926697078677 4935910561475527813925563)
              ·
                refine ⟨7403865842213291720888345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935910561475527813925563 7403865842213291720888345)
                ·
                  refine ⟨5552899381659968790666259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7403865842213291720888345 5552899381659968790666259)
                  ·
                    refine ⟨8329349072489953185999389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5552899381659968790666259 8329349072489953185999389)
                    ·
                      refine ⟨3123505902183732444749771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8329349072489953185999389 3123505902183732444749771)
                      ·
                        rfl

theorem cell23_6083006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_6083006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083006 prefixEnd_6083006 := by exact prefixLift 6083006
  have htrace : WordTrace (prefixWord ++ tailWord_6083006) baseStart_6083006 baseEnd_6083006 := by
    simpa [prefixWord, tailWord_6083006, baseEnd_6083006] using wordTrace_append hprefix tailTrace_6083006
  have hstable : (prefixWord ++ tailWord_6083006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083006).length < 2 ^ (prefixWord ++ tailWord_6083006).sum := by decide
  have hdescent : baseEnd_6083006 < baseStart_6083006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083015 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_6083015 : Nat := 118140960795 + 6083015 * 2 ^ 59
def prefixEnd_6083015 : Nat := 4983230072969 + 3 ^ 40 * 6083015 * 2
def baseEnd_6083015 : Nat := 3123510523509622909537229

theorem tailTrace_6083015 : CollatzResearch.WordTrace tailWord_6083015 prefixEnd_6083015 3123510523509622909537229 := by
  unfold tailWord_6083015
  simp only [CollatzResearch.WordTrace]
  refine ⟨221865784057283026096354499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147910522704855350730902999 221865784057283026096354499)
  ·
    refine ⟨332798676085924539144531749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221865784057283026096354499 332798676085924539144531749)
    ·
      refine ⟨62399751766110851089599703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332798676085924539144531749 62399751766110851089599703)
      ·
        refine ⟨93599627649166276634399555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62399751766110851089599703 93599627649166276634399555)
        ·
          refine ⟨140399441473749414951599333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93599627649166276634399555 140399441473749414951599333)
          ·
            refine ⟨26324895276328015303424875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140399441473749414951599333 26324895276328015303424875)
            ·
              refine ⟨39487342914492022955137313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26324895276328015303424875 39487342914492022955137313)
              ·
                refine ⟨29615507185869017216352985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39487342914492022955137313 29615507185869017216352985)
                ·
                  refine ⟨22211630389401762912264739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29615507185869017216352985 22211630389401762912264739)
                  ·
                    refine ⟨33317445584102644368397109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22211630389401762912264739 33317445584102644368397109)
                    ·
                      refine ⟨3123510523509622909537229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33317445584102644368397109 3123510523509622909537229)
                      ·
                        rfl

theorem cell23_6083015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_6083015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083015 prefixEnd_6083015 := by exact prefixLift 6083015
  have htrace : WordTrace (prefixWord ++ tailWord_6083015) baseStart_6083015 baseEnd_6083015 := by
    simpa [prefixWord, tailWord_6083015, baseEnd_6083015] using wordTrace_append hprefix tailTrace_6083015
  have hstable : (prefixWord ++ tailWord_6083015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083015).length < 2 ^ (prefixWord ++ tailWord_6083015).sum := by decide
  have hdescent : baseEnd_6083015 < baseStart_6083015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083016 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 1, 3, 2]
def baseStart_6083016 : Nat := 118140960795 + 6083016 * 2 ^ 59
def prefixEnd_6083016 : Nat := 4983230072969 + 3 ^ 40 * 6083016 * 2
def baseEnd_6083016 : Nat := 3123511036990277405624725

theorem tailTrace_6083016 : CollatzResearch.WordTrace tailWord_6083016 prefixEnd_6083016 3123511036990277405624725 := by
  unfold tailWord_6083016
  simp only [CollatzResearch.WordTrace]
  refine ⟨110932910265139701633570451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147910547020186268844760601 110932910265139701633570451)
  ·
    refine ⟨166399365397709552450355677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110932910265139701633570451 166399365397709552450355677)
    ·
      refine ⟨62399762024141082168883379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166399365397709552450355677 62399762024141082168883379)
      ·
        refine ⟨93599643036211623253325069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62399762024141082168883379 93599643036211623253325069)
        ·
          refine ⟨35099866138579358719996901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93599643036211623253325069 35099866138579358719996901)
          ·
            refine ⟨6581224900983629759999419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35099866138579358719996901 6581224900983629759999419)
            ·
              refine ⟨9871837351475444639999129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6581224900983629759999419 9871837351475444639999129)
              ·
                refine ⟨7403878013606583479999347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9871837351475444639999129 7403878013606583479999347)
                ·
                  refine ⟨11105817020409875219999021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7403878013606583479999347 11105817020409875219999021)
                  ·
                    refine ⟨4164681382653703207499633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11105817020409875219999021 4164681382653703207499633)
                    ·
                      refine ⟨3123511036990277405624725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164681382653703207499633 3123511036990277405624725)
                      ·
                        rfl

theorem cell23_6083016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_6083016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083016 prefixEnd_6083016 := by exact prefixLift 6083016
  have htrace : WordTrace (prefixWord ++ tailWord_6083016) baseStart_6083016 baseEnd_6083016 := by
    simpa [prefixWord, tailWord_6083016, baseEnd_6083016] using wordTrace_append hprefix tailTrace_6083016
  have hstable : (prefixWord ++ tailWord_6083016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083016).length < 2 ^ (prefixWord ++ tailWord_6083016).sum := by decide
  have hdescent : baseEnd_6083016 < baseStart_6083016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083029 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 1, 4, 2]
def baseStart_6083029 : Nat := 118140960795 + 6083029 * 2 ^ 59
def prefixEnd_6083029 : Nat := 4983230072969 + 3 ^ 40 * 6083029 * 2
def baseEnd_6083029 : Nat := 3123517712238785854762165

theorem tailTrace_6083029 : CollatzResearch.WordTrace tailWord_6083029 prefixEnd_6083029 3123517712238785854762165 := by
  unfold tailWord_6083029
  simp only [CollatzResearch.WordTrace]
  refine ⟨221866294679232306487364141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147910863119488204324909427 221866294679232306487364141)
  ·
    refine ⟨83199860504712114932761553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221866294679232306487364141 83199860504712114932761553)
    ·
      refine ⟨62399895378534086199571165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83199860504712114932761553 62399895378534086199571165)
      ·
        refine ⟨23399960766950282324839187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62399895378534086199571165 23399960766950282324839187)
        ·
          refine ⟨35099941150425423487258781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23399960766950282324839187 35099941150425423487258781)
          ·
            refine ⟨13162477931409533807722043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35099941150425423487258781 13162477931409533807722043)
            ·
              refine ⟨19743716897114300711583065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13162477931409533807722043 19743716897114300711583065)
              ·
                refine ⟨14807787672835725533687299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19743716897114300711583065 14807787672835725533687299)
                ·
                  refine ⟨22211681509253588300530949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14807787672835725533687299 22211681509253588300530949)
                  ·
                    refine ⟨4164690282985047806349553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22211681509253588300530949 4164690282985047806349553)
                    ·
                      refine ⟨3123517712238785854762165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164690282985047806349553 3123517712238785854762165)
                      ·
                        rfl

theorem cell23_6083029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_6083029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083029 prefixEnd_6083029 := by exact prefixLift 6083029
  have htrace : WordTrace (prefixWord ++ tailWord_6083029) baseStart_6083029 baseEnd_6083029 := by
    simpa [prefixWord, tailWord_6083029, baseEnd_6083029] using wordTrace_append hprefix tailTrace_6083029
  have hstable : (prefixWord ++ tailWord_6083029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083029).length < 2 ^ (prefixWord ++ tailWord_6083029).sum := by decide
  have hdescent : baseEnd_6083029 < baseStart_6083029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083052 : List Nat := [2, 2, 1, 1, 2, 1, 5, 4, 5]
def baseStart_6083052 : Nat := 118140960795 + 6083052 * 2 ^ 59
def prefixEnd_6083052 : Nat := 4983230072969 + 3 ^ 40 * 6083052 * 2
def baseEnd_6083052 : Nat := 347058835810426584974951

theorem tailTrace_6083052 : CollatzResearch.WordTrace tailWord_6083052 prefixEnd_6083052 347058835810426584974951 := by
  unfold tailWord_6083052
  simp only [CollatzResearch.WordTrace]
  refine ⟨110933566779074490707725705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147911422372099320943634273 110933566779074490707725705)
  ·
    refine ⟨83200175084305868030794279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110933566779074490707725705 83200175084305868030794279)
    ·
      refine ⟨124800262626458802046191419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83200175084305868030794279 124800262626458802046191419)
      ·
        refine ⟨187200393939688203069287129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124800262626458802046191419 187200393939688203069287129)
        ·
          refine ⟨140400295454766152301965347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187200393939688203069287129 140400295454766152301965347)
          ·
            refine ⟨210600443182149228452948021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140400295454766152301965347 210600443182149228452948021)
            ·
              refine ⟨19743791548326490167463877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210600443182149228452948021 19743791548326490167463877)
              ·
                refine ⟨3701960915311216906399477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19743791548326490167463877 3701960915311216906399477)
                ·
                  refine ⟨347058835810426584974951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3701960915311216906399477 347058835810426584974951)
                  ·
                    rfl

theorem cell23_6083052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_6083052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083052 prefixEnd_6083052 := by exact prefixLift 6083052
  have htrace : WordTrace (prefixWord ++ tailWord_6083052) baseStart_6083052 baseEnd_6083052 := by
    simpa [prefixWord, tailWord_6083052, baseEnd_6083052] using wordTrace_append hprefix tailTrace_6083052
  have hstable : (prefixWord ++ tailWord_6083052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083052).length < 2 ^ (prefixWord ++ tailWord_6083052).sum := by decide
  have hdescent : baseEnd_6083052 < baseStart_6083052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083065 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 4, 5]
def baseStart_6083065 : Nat := 118140960795 + 6083065 * 2 ^ 59
def prefixEnd_6083065 : Nat := 4983230072969 + 3 ^ 40 * 6083065 * 2
def baseEnd_6083065 : Nat := 1041178732514115904637333

theorem tailTrace_6083065 : CollatzResearch.WordTrace tailWord_6083065 prefixEnd_6083065 1041178732514115904637333 := by
  unfold tailWord_6083065
  simp only [CollatzResearch.WordTrace]
  refine ⟨221867607707101884635674649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147911738471401256423783099 221867607707101884635674649)
  ·
    refine ⟨166400705780326413476755987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221867607707101884635674649 166400705780326413476755987)
    ·
      refine ⟨249601058670489620215133981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166400705780326413476755987 249601058670489620215133981)
      ·
        refine ⟨93600397001433607580675243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249601058670489620215133981 93600397001433607580675243)
        ·
          refine ⟨140400595502150411371012865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93600397001433607580675243 140400595502150411371012865)
          ·
            refine ⟨105300446626612808528259649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140400595502150411371012865 105300446626612808528259649)
            ·
              refine ⟨78975334969959606396194737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105300446626612808528259649 78975334969959606396194737)
              ·
                refine ⟨59231501227469704797146053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78975334969959606396194737 59231501227469704797146053)
                ·
                  refine ⟨11105906480150569649464885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59231501227469704797146053 11105906480150569649464885)
                  ·
                    refine ⟨1041178732514115904637333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11105906480150569649464885 1041178732514115904637333)
                    ·
                      rfl

theorem cell23_6083065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_6083065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083065 prefixEnd_6083065 := by exact prefixLift 6083065
  have htrace : WordTrace (prefixWord ++ tailWord_6083065) baseStart_6083065 baseEnd_6083065 := by
    simpa [prefixWord, tailWord_6083065, baseEnd_6083065] using wordTrace_append hprefix tailTrace_6083065
  have hstable : (prefixWord ++ tailWord_6083065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083065).length < 2 ^ (prefixWord ++ tailWord_6083065).sum := by decide
  have hdescent : baseEnd_6083065 < baseStart_6083065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083122 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_6083122 : Nat := 118140960795 + 6083122 * 2 ^ 59
def prefixEnd_6083122 : Nat := 4983230072969 + 3 ^ 40 * 6083122 * 2
def baseEnd_6083122 : Nat := 3123565465939653990899237

theorem tailTrace_6083122 : CollatzResearch.WordTrace tailWord_6083122 prefixEnd_6083122 3123565465939653990899237 := by
  unfold tailWord_6083122
  simp only [CollatzResearch.WordTrace]
  refine ⟨55467421666973845842624905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147913124445263588913666413 55467421666973845842624905)
  ·
    refine ⟨41600566250230384381968679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55467421666973845842624905 41600566250230384381968679)
    ·
      refine ⟨62400849375345576572953019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41600566250230384381968679 62400849375345576572953019)
      ·
        refine ⟨93601274063018364859429529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62400849375345576572953019 93601274063018364859429529)
        ·
          refine ⟨70200955547263773644572147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93601274063018364859429529 70200955547263773644572147)
          ·
            refine ⟨105301433320895660466858221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70200955547263773644572147 105301433320895660466858221)
            ·
              refine ⟨39488037495335872675071833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105301433320895660466858221 39488037495335872675071833)
              ·
                refine ⟨29616028121501904506303875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39488037495335872675071833 29616028121501904506303875)
                ·
                  refine ⟨44424042182252856759455813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29616028121501904506303875 44424042182252856759455813)
                  ·
                    refine ⟨8329507909172410642397965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44424042182252856759455813 8329507909172410642397965)
                    ·
                      refine ⟨3123565465939653990899237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8329507909172410642397965 3123565465939653990899237)
                      ·
                        rfl

theorem cell23_6083122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_6083122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083122 prefixEnd_6083122 := by exact prefixLift 6083122
  have htrace : WordTrace (prefixWord ++ tailWord_6083122) baseStart_6083122 baseEnd_6083122 := by
    simpa [prefixWord, tailWord_6083122, baseEnd_6083122] using wordTrace_append hprefix tailTrace_6083122
  have hstable : (prefixWord ++ tailWord_6083122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083122).length < 2 ^ (prefixWord ++ tailWord_6083122).sum := by decide
  have hdescent : baseEnd_6083122 < baseStart_6083122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083146 : List Nat := [3, 1, 2, 1, 1, 4, 3, 3, 1, 4]
def baseStart_6083146 : Nat := 118140960795 + 6083146 * 2 ^ 59
def prefixEnd_6083146 : Nat := 4983230072969 + 3 ^ 40 * 6083146 * 2
def baseEnd_6083146 : Nat := 1041192596491787298999709

theorem tailTrace_6083146 : CollatzResearch.WordTrace tailWord_6083146 prefixEnd_6083146 1041192596491787298999709 := by
  unfold tailWord_6083146
  simp only [CollatzResearch.WordTrace]
  refine ⟨55467640504952108867343323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147913708013205623646248861 55467640504952108867343323)
  ·
    refine ⟨83201460757428163301014985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55467640504952108867343323 83201460757428163301014985)
    ·
      refine ⟨62401095568071122475761239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83201460757428163301014985 62401095568071122475761239)
      ·
        refine ⟨93601643352106683713641859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62401095568071122475761239 93601643352106683713641859)
        ·
          refine ⟨140402465028160025570462789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93601643352106683713641859 140402465028160025570462789)
          ·
            refine ⟨26325462192780004794461773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140402465028160025570462789 26325462192780004794461773)
            ·
              refine ⟨9872048322292501797923165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26325462192780004794461773 9872048322292501797923165)
              ·
                refine ⟨3702018120859688174221187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9872048322292501797923165 3702018120859688174221187)
                ·
                  refine ⟨5553027181289532261331781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702018120859688174221187 5553027181289532261331781)
                  ·
                    refine ⟨1041192596491787298999709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5553027181289532261331781 1041192596491787298999709)
                    ·
                      rfl

theorem cell23_6083146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_6083146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083146 prefixEnd_6083146 := by exact prefixLift 6083146
  have htrace : WordTrace (prefixWord ++ tailWord_6083146) baseStart_6083146 baseEnd_6083146 := by
    simpa [prefixWord, tailWord_6083146, baseEnd_6083146] using wordTrace_append hprefix tailTrace_6083146
  have hstable : (prefixWord ++ tailWord_6083146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083146).length < 2 ^ (prefixWord ++ tailWord_6083146).sum := by decide
  have hdescent : baseEnd_6083146 < baseStart_6083146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083172 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_6083172 : Nat := 118140960795 + 6083172 * 2 ^ 59
def prefixEnd_6083172 : Nat := 4983230072969 + 3 ^ 40 * 6083172 * 2
def baseEnd_6083172 : Nat := 1041197046657459598424669

theorem tailTrace_6083172 : CollatzResearch.WordTrace tailWord_6083172 prefixEnd_6083172 1041197046657459598424669 := by
  unfold tailWord_6083172
  simp only [CollatzResearch.WordTrace]
  refine ⟨110935755158857120954909885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147914340211809494606546513 110935755158857120954909885)
  ·
    refine ⟨41600908184571420358091207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110935755158857120954909885 41600908184571420358091207)
    ·
      refine ⟨62401362276857130537136811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41600908184571420358091207 62401362276857130537136811)
      ·
        refine ⟨93602043415285695805705217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62401362276857130537136811 93602043415285695805705217)
        ·
          refine ⟨70201532561464271854278913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93602043415285695805705217 70201532561464271854278913)
          ·
            refine ⟨52651149421098203890709185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70201532561464271854278913 52651149421098203890709185)
            ·
              refine ⟨39488362065823652918031889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52651149421098203890709185 39488362065823652918031889)
              ·
                refine ⟨29616271549367739688523917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39488362065823652918031889 29616271549367739688523917)
                ·
                  refine ⟨11106101831012902383196469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29616271549367739688523917 11106101831012902383196469)
                  ·
                    refine ⟨1041197046657459598424669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11106101831012902383196469 1041197046657459598424669)
                    ·
                      rfl

theorem cell23_6083172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_6083172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083172 prefixEnd_6083172 := by exact prefixLift 6083172
  have htrace : WordTrace (prefixWord ++ tailWord_6083172) baseStart_6083172 baseEnd_6083172 := by
    simpa [prefixWord, tailWord_6083172, baseEnd_6083172] using wordTrace_append hprefix tailTrace_6083172
  have hstable : (prefixWord ++ tailWord_6083172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083172).length < 2 ^ (prefixWord ++ tailWord_6083172).sum := by decide
  have hdescent : baseEnd_6083172 < baseStart_6083172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083192 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_6083192 : Nat := 118140960795 + 6083192 * 2 ^ 59
def prefixEnd_6083192 : Nat := 4983230072969 + 3 ^ 40 * 6083192 * 2
def baseEnd_6083192 : Nat := 3123601409585468717023915

theorem tailTrace_6083192 : CollatzResearch.WordTrace tailWord_6083192 prefixEnd_6083192 3123601409585468717023915 := by
  unfold tailWord_6083192
  simp only [CollatzResearch.WordTrace]
  refine ⟨110936119888820892662773915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147914826518427856883698553 110936119888820892662773915)
  ·
    refine ⟨166404179833231338994160873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110936119888820892662773915 166404179833231338994160873)
    ·
      refine ⟨124803134874923504245620655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166404179833231338994160873 124803134874923504245620655)
      ·
        refine ⟨187204702312385256368430983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124803134874923504245620655 187204702312385256368430983)
        ·
          refine ⟨280807053468577884552646475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187204702312385256368430983 280807053468577884552646475)
          ·
            refine ⟨421210580202866826828969713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280807053468577884552646475 421210580202866826828969713)
            ·
              refine ⟨315907935152150120121727285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421210580202866826828969713 315907935152150120121727285)
              ·
                refine ⟨29616368920514073761411933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315907935152150120121727285 29616368920514073761411933)
                ·
                  refine ⟨11106138345192777660529475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29616368920514073761411933 11106138345192777660529475)
                  ·
                    refine ⟨16659207517789166490794213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11106138345192777660529475 16659207517789166490794213)
                    ·
                      refine ⟨3123601409585468717023915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16659207517789166490794213 3123601409585468717023915)
                      ·
                        rfl

theorem cell23_6083192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_6083192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083192 prefixEnd_6083192 := by exact prefixLift 6083192
  have htrace : WordTrace (prefixWord ++ tailWord_6083192) baseStart_6083192 baseEnd_6083192 := by
    simpa [prefixWord, tailWord_6083192, baseEnd_6083192] using wordTrace_append hprefix tailTrace_6083192
  have hstable : (prefixWord ++ tailWord_6083192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083192).length < 2 ^ (prefixWord ++ tailWord_6083192).sum := by decide
  have hdescent : baseEnd_6083192 < baseStart_6083192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083212 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_6083212 : Nat := 118140960795 + 6083212 * 2 ^ 59
def prefixEnd_6083212 : Nat := 4983230072969 + 3 ^ 40 * 6083212 * 2
def baseEnd_6083212 : Nat := 3123611679198558638773823

theorem tailTrace_6083212 : CollatzResearch.WordTrace tailWord_6083212 prefixEnd_6083212 3123611679198558638773823 := by
  unfold tailWord_6083212
  simp only [CollatzResearch.WordTrace]
  refine ⟨110936484618784664370637945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147915312825046219160850593 110936484618784664370637945)
  ·
    refine ⟨83202363464088498277978459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110936484618784664370637945 83202363464088498277978459)
    ·
      refine ⟨124803545196132747416967689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83202363464088498277978459 124803545196132747416967689)
      ·
        refine ⟨93602658897099560562725767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124803545196132747416967689 93602658897099560562725767)
        ·
          refine ⟨140403988345649340844088651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93602658897099560562725767 140403988345649340844088651)
          ·
            refine ⟨210605982518474011266132977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140403988345649340844088651 210605982518474011266132977)
            ·
              refine ⟨157954486888855508449599733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210605982518474011266132977 157954486888855508449599733)
              ·
                refine ⟨14808233145830203917149975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157954486888855508449599733 14808233145830203917149975)
                ·
                  refine ⟨22212349718745305875724963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14808233145830203917149975 22212349718745305875724963)
                  ·
                    refine ⟨33318524578117958813587445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22212349718745305875724963 33318524578117958813587445)
                    ·
                      refine ⟨3123611679198558638773823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33318524578117958813587445 3123611679198558638773823)
                      ·
                        rfl

theorem cell23_6083212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_6083212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083212 prefixEnd_6083212 := by exact prefixLift 6083212
  have htrace : WordTrace (prefixWord ++ tailWord_6083212) baseStart_6083212 baseEnd_6083212 := by
    simpa [prefixWord, tailWord_6083212, baseEnd_6083212] using wordTrace_append hprefix tailTrace_6083212
  have hstable : (prefixWord ++ tailWord_6083212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083212).length < 2 ^ (prefixWord ++ tailWord_6083212).sum := by decide
  have hdescent : baseEnd_6083212 < baseStart_6083212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083220 : List Nat := [2, 4, 2, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_6083220 : Nat := 118140960795 + 6083220 * 2 ^ 59
def prefixEnd_6083220 : Nat := 4983230072969 + 3 ^ 40 * 6083220 * 2
def baseEnd_6083220 : Nat := 3123615787043794607473787

theorem tailTrace_6083220 : CollatzResearch.WordTrace tailWord_6083220 prefixEnd_6083220 3123615787043794607473787 := by
  unfold tailWord_6083220
  simp only [CollatzResearch.WordTrace]
  refine ⟨110936630510770173053783557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147915507347693564071711409 110936630510770173053783557)
  ·
    refine ⟨20800618220769407447584417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110936630510770173053783557 20800618220769407447584417)
    ·
      refine ⟨15600463665577055585688313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20800618220769407447584417 15600463665577055585688313)
      ·
        refine ⟨11700347749182791689266235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15600463665577055585688313 11700347749182791689266235)
        ·
          refine ⟨17550521623774187533899353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11700347749182791689266235 17550521623774187533899353)
          ·
            refine ⟨13162891217830640650424515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17550521623774187533899353 13162891217830640650424515)
            ·
              refine ⟨19744336826745960975636773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13162891217830640650424515 19744336826745960975636773)
              ·
                refine ⟨3702063155014867682931895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19744336826745960975636773 3702063155014867682931895)
                ·
                  refine ⟨5553094732522301524397843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702063155014867682931895 5553094732522301524397843)
                  ·
                    refine ⟨8329642098783452286596765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5553094732522301524397843 8329642098783452286596765)
                    ·
                      refine ⟨3123615787043794607473787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8329642098783452286596765 3123615787043794607473787)
                      ·
                        rfl

theorem cell23_6083220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_6083220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083220 prefixEnd_6083220 := by exact prefixLift 6083220
  have htrace : WordTrace (prefixWord ++ tailWord_6083220) baseStart_6083220 baseEnd_6083220 := by
    simpa [prefixWord, tailWord_6083220, baseEnd_6083220] using wordTrace_append hprefix tailTrace_6083220
  have hstable : (prefixWord ++ tailWord_6083220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083220).length < 2 ^ (prefixWord ++ tailWord_6083220).sum := by decide
  have hdescent : baseEnd_6083220 < baseStart_6083220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083229 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_6083229 : Nat := 118140960795 + 6083229 * 2 ^ 59
def prefixEnd_6083229 : Nat := 4983230072969 + 3 ^ 40 * 6083229 * 2
def baseEnd_6083229 : Nat := 3123620408369685072261245

theorem tailTrace_6083229 : CollatzResearch.WordTrace tailWord_6083229 prefixEnd_6083229 3123620408369685072261245 := by
  unfold tailWord_6083229
  simp only [CollatzResearch.WordTrace]
  refine ⟨221873589278507740644644741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147915726185671827096429827 221873589278507740644644741)
  ·
    refine ⟨41601297989720201370870889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221873589278507740644644741 41601297989720201370870889)
    ·
      refine ⟨31200973492290151028153167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41601297989720201370870889 31200973492290151028153167)
      ·
        refine ⟨46801460238435226542229751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31200973492290151028153167 46801460238435226542229751)
        ·
          refine ⟨70202190357652839813344627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46801460238435226542229751 70202190357652839813344627)
          ·
            refine ⟨105303285536479259720016941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70202190357652839813344627 105303285536479259720016941)
            ·
              refine ⟨39488732076179722395006353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105303285536479259720016941 39488732076179722395006353)
              ·
                refine ⟨29616549057134791796254765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39488732076179722395006353 29616549057134791796254765)
                ·
                  refine ⟨11106205896425546923595537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29616549057134791796254765 11106205896425546923595537)
                  ·
                    refine ⟨8329654422319160192696653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11106205896425546923595537 8329654422319160192696653)
                    ·
                      refine ⟨3123620408369685072261245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8329654422319160192696653 3123620408369685072261245)
                      ·
                        rfl

theorem cell23_6083229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_6083229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083229 prefixEnd_6083229 := by exact prefixLift 6083229
  have htrace : WordTrace (prefixWord ++ tailWord_6083229) baseStart_6083229 baseEnd_6083229 := by
    simpa [prefixWord, tailWord_6083229, baseEnd_6083229] using wordTrace_append hprefix tailTrace_6083229
  have hstable : (prefixWord ++ tailWord_6083229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083229).length < 2 ^ (prefixWord ++ tailWord_6083229).sum := by decide
  have hdescent : baseEnd_6083229 < baseStart_6083229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083260 : List Nat := [2, 2, 2, 3, 1, 1, 4, 3, 1, 2, 2]
def baseStart_6083260 : Nat := 118140960795 + 6083260 * 2 ^ 59
def prefixEnd_6083260 : Nat := 4983230072969 + 3 ^ 40 * 6083260 * 2
def baseEnd_6083260 : Nat := 3123636326269974450973603

theorem tailTrace_6083260 : CollatzResearch.WordTrace tailWord_6083260 prefixEnd_6083260 3123636326269974450973603 := by
  unfold tailWord_6083260
  simp only [CollatzResearch.WordTrace]
  refine ⟨110937359970697716469511617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147916479960930288626015489 110937359970697716469511617)
  ·
    refine ⟨83203019978023287352133713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110937359970697716469511617 83203019978023287352133713)
    ·
      refine ⟨62402264983517465514100285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83203019978023287352133713 62402264983517465514100285)
      ·
        refine ⟨23400849368819049567787607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62402264983517465514100285 23400849368819049567787607)
        ·
          refine ⟨35101274053228574351681411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23400849368819049567787607 35101274053228574351681411)
          ·
            refine ⟨52651911079842861527522117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35101274053228574351681411 52651911079842861527522117)
            ·
              refine ⟨9872233327470536536410397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52651911079842861527522117 9872233327470536536410397)
              ·
                refine ⟨3702087497801451201153899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9872233327470536536410397 3702087497801451201153899)
                ·
                  refine ⟨5553131246702176801730849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702087497801451201153899 5553131246702176801730849)
                  ·
                    refine ⟨4164848435026632601298137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5553131246702176801730849 4164848435026632601298137)
                    ·
                      refine ⟨3123636326269974450973603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164848435026632601298137 3123636326269974450973603)
                      ·
                        rfl

theorem cell23_6083260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_6083260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083260 prefixEnd_6083260 := by exact prefixLift 6083260
  have htrace : WordTrace (prefixWord ++ tailWord_6083260) baseStart_6083260 baseEnd_6083260 := by
    simpa [prefixWord, tailWord_6083260, baseEnd_6083260] using wordTrace_append hprefix tailTrace_6083260
  have hstable : (prefixWord ++ tailWord_6083260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083260).length < 2 ^ (prefixWord ++ tailWord_6083260).sum := by decide
  have hdescent : baseEnd_6083260 < baseStart_6083260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083263 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 1, 2, 3]
def baseStart_6083263 : Nat := 118140960795 + 6083263 * 2 ^ 59
def prefixEnd_6083263 : Nat := 4983230072969 + 3 ^ 40 * 6083263 * 2
def baseEnd_6083263 : Nat := 3123637866711937939236089

theorem tailTrace_6083263 : CollatzResearch.WordTrace tailWord_6083263 prefixEnd_6083263 3123637866711937939236089 := by
  unfold tailWord_6083263
  simp only [CollatzResearch.WordTrace]
  refine ⟨221874829360384564451382443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147916552906923042967588295 221874829360384564451382443)
  ·
    refine ⟨332812244040576846677073665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221874829360384564451382443 332812244040576846677073665)
    ·
      refine ⟨249609183030432635007805249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332812244040576846677073665 249609183030432635007805249)
      ·
        refine ⟨187206887272824476255853937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249609183030432635007805249 187206887272824476255853937)
        ·
          refine ⟨140405165454618357191890453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187206887272824476255853937 140405165454618357191890453)
          ·
            refine ⟨6581492130685235493369865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140405165454618357191890453 6581492130685235493369865)
            ·
              refine ⟨4936119098013926620027399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6581492130685235493369865 4936119098013926620027399)
              ·
                refine ⟨7404178647020889930041099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936119098013926620027399 7404178647020889930041099)
                ·
                  refine ⟨11106267970531334895061649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7404178647020889930041099 11106267970531334895061649)
                  ·
                    refine ⟨8329700977898501171296237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11106267970531334895061649 8329700977898501171296237)
                    ·
                      refine ⟨3123637866711937939236089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8329700977898501171296237 3123637866711937939236089)
                      ·
                        rfl

theorem cell23_6083263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_6083263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083263 prefixEnd_6083263 := by exact prefixLift 6083263
  have htrace : WordTrace (prefixWord ++ tailWord_6083263) baseStart_6083263 baseEnd_6083263 := by
    simpa [prefixWord, tailWord_6083263, baseEnd_6083263] using wordTrace_append hprefix tailTrace_6083263
  have hstable : (prefixWord ++ tailWord_6083263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083263).length < 2 ^ (prefixWord ++ tailWord_6083263).sum := by decide
  have hdescent : baseEnd_6083263 < baseStart_6083263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083270 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_6083270 : Nat := 118140960795 + 6083270 * 2 ^ 59
def prefixEnd_6083270 : Nat := 4983230072969 + 3 ^ 40 * 6083270 * 2
def baseEnd_6083270 : Nat := 1041213820358839803949519

theorem tailTrace_6083270 : CollatzResearch.WordTrace tailWord_6083270 prefixEnd_6083270 1041213820358839803949519 := by
  unfold tailWord_6083270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6933596395979975145215227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147916723114239469764591509 6933596395979975145215227)
  ·
    refine ⟨10400394593969962717822841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6933596395979975145215227 10400394593969962717822841)
    ·
      refine ⟨7800295945477472038367131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10400394593969962717822841 7800295945477472038367131)
      ·
        refine ⟨11700443918216208057550697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7800295945477472038367131 11700443918216208057550697)
        ·
          refine ⟨8775332938662156043163023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11700443918216208057550697 8775332938662156043163023)
          ·
            refine ⟨13162999407993234064744535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8775332938662156043163023 13162999407993234064744535)
            ·
              refine ⟨19744499111989851097116803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13162999407993234064744535 19744499111989851097116803)
              ·
                refine ⟨29616748667984776645675205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19744499111989851097116803 29616748667984776645675205)
                ·
                  refine ⟨5553140375247145621064101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29616748667984776645675205 5553140375247145621064101)
                  ·
                    refine ⟨1041213820358839803949519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5553140375247145621064101 1041213820358839803949519)
                    ·
                      rfl

theorem cell23_6083270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_6083270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083270 prefixEnd_6083270 := by exact prefixLift 6083270
  have htrace : WordTrace (prefixWord ++ tailWord_6083270) baseStart_6083270 baseEnd_6083270 := by
    simpa [prefixWord, tailWord_6083270, baseEnd_6083270] using wordTrace_append hprefix tailTrace_6083270
  have hstable : (prefixWord ++ tailWord_6083270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083270).length < 2 ^ (prefixWord ++ tailWord_6083270).sum := by decide
  have hdescent : baseEnd_6083270 < baseStart_6083270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083277 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_6083277 : Nat := 118140960795 + 6083277 * 2 ^ 59
def prefixEnd_6083277 : Nat := 4983230072969 + 3 ^ 40 * 6083277 * 2
def baseEnd_6083277 : Nat := 3123645055441100884461025

theorem tailTrace_6083277 : CollatzResearch.WordTrace tailWord_6083277 prefixEnd_6083277 3123645055441100884461025 := by
  unfold tailWord_6083277
  simp only [CollatzResearch.WordTrace]
  refine ⟨221875339982333844842392085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147916893321555896561594723 221875339982333844842392085)
  ·
    refine ⟨10400406561671898976987129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221875339982333844842392085 10400406561671898976987129)
    ·
      refine ⟨7800304921253924232740347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10400406561671898976987129 7800304921253924232740347)
      ·
        refine ⟨11700457381880886349110521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7800304921253924232740347 11700457381880886349110521)
        ·
          refine ⟨8775343036410664761832891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11700457381880886349110521 8775343036410664761832891)
          ·
            refine ⟨13163014554615997142749337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8775343036410664761832891 13163014554615997142749337)
            ·
              refine ⟨9872260915961997857062003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13163014554615997142749337 9872260915961997857062003)
              ·
                refine ⟨14808391373942996785593005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9872260915961997857062003 14808391373942996785593005)
                ·
                  refine ⟨5553146765228623794597377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14808391373942996785593005 5553146765228623794597377)
                  ·
                    refine ⟨4164860073921467845948033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5553146765228623794597377 4164860073921467845948033)
                    ·
                      refine ⟨3123645055441100884461025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4164860073921467845948033 3123645055441100884461025)
                      ·
                        rfl

theorem cell23_6083277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_6083277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083277 prefixEnd_6083277 := by exact prefixLift 6083277
  have htrace : WordTrace (prefixWord ++ tailWord_6083277) baseStart_6083277 baseEnd_6083277 := by
    simpa [prefixWord, tailWord_6083277, baseEnd_6083277] using wordTrace_append hprefix tailTrace_6083277
  have hstable : (prefixWord ++ tailWord_6083277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083277).length < 2 ^ (prefixWord ++ tailWord_6083277).sum := by decide
  have hdescent : baseEnd_6083277 < baseStart_6083277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083322 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 9]
def baseStart_6083322 : Nat := 118140960795 + 6083322 * 2 ^ 59
def prefixEnd_6083322 : Nat := 4983230072969 + 3 ^ 40 * 6083322 * 2
def baseEnd_6083322 : Nat := 347074240230061467599813

theorem tailTrace_6083322 : CollatzResearch.WordTrace tailWord_6083322 prefixEnd_6083322 347074240230061467599813 := by
  unfold tailWord_6083322
  simp only [CollatzResearch.WordTrace]
  refine ⟨55469245316792704381945055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147917987511447211685186813 55469245316792704381945055)
  ·
    refine ⟨83203867975189056572917583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55469245316792704381945055 83203867975189056572917583)
    ·
      refine ⟨124805801962783584859376375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83203867975189056572917583 124805801962783584859376375)
      ·
        refine ⟨187208702944175377289064563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124805801962783584859376375 187208702944175377289064563)
        ·
          refine ⟨280813054416263065933596845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187208702944175377289064563 280813054416263065933596845)
          ·
            refine ⟨105304895406098649725098817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280813054416263065933596845 105304895406098649725098817)
            ·
              refine ⟨78978671554573987293824113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105304895406098649725098817 78978671554573987293824113)
              ·
                refine ⟨59234003665930490470368085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78978671554573987293824113 59234003665930490470368085)
                ·
                  refine ⟨347074240230061467599813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59234003665930490470368085 347074240230061467599813)
                  ·
                    rfl

theorem cell23_6083322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_6083322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083322 prefixEnd_6083322 := by exact prefixLift 6083322
  have htrace : WordTrace (prefixWord ++ tailWord_6083322) baseStart_6083322 baseEnd_6083322 := by
    simpa [prefixWord, tailWord_6083322, baseEnd_6083322] using wordTrace_append hprefix tailTrace_6083322
  have hstable : (prefixWord ++ tailWord_6083322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083322).length < 2 ^ (prefixWord ++ tailWord_6083322).sum := by decide
  have hdescent : baseEnd_6083322 < baseStart_6083322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083349 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_6083349 : Nat := 118140960795 + 6083349 * 2 ^ 59
def prefixEnd_6083349 : Nat := 4983230072969 + 3 ^ 40 * 6083349 * 2
def baseEnd_6083349 : Nat := 3123682026048224602760693

theorem tailTrace_6083349 : CollatzResearch.WordTrace tailWord_6083349 prefixEnd_6083349 3123682026048224602760693 := by
  unfold tailWord_6083349
  simp only [CollatzResearch.WordTrace]
  refine ⟨221877966038073001139013101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147918644025382000759342067 221877966038073001139013101)
  ·
    refine ⟨83204237264277375427129913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221877966038073001139013101 83204237264277375427129913)
    ·
      refine ⟨62403177948208031570347435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83204237264277375427129913 62403177948208031570347435)
      ·
        refine ⟨93604766922312047355521153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62403177948208031570347435 93604766922312047355521153)
        ·
          refine ⟨70203575191734035516640865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93604766922312047355521153 70203575191734035516640865)
          ·
            refine ⟨52652681393800526637480649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70203575191734035516640865 52652681393800526637480649)
            ·
              refine ⟨39489511045350394978110487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52652681393800526637480649 39489511045350394978110487)
              ·
                refine ⟨59234266568025592467165731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39489511045350394978110487 59234266568025592467165731)
                ·
                  refine ⟨88851399852038388700748597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59234266568025592467165731 88851399852038388700748597)
                  ·
                    refine ⟨8329818736128598940695181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88851399852038388700748597 8329818736128598940695181)
                    ·
                      refine ⟨3123682026048224602760693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8329818736128598940695181 3123682026048224602760693)
                      ·
                        rfl

theorem cell23_6083349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_6083349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083349 prefixEnd_6083349 := by exact prefixLift 6083349
  have htrace : WordTrace (prefixWord ++ tailWord_6083349) baseStart_6083349 baseEnd_6083349 := by
    simpa [prefixWord, tailWord_6083349, baseEnd_6083349] using wordTrace_append hprefix tailTrace_6083349
  have hstable : (prefixWord ++ tailWord_6083349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083349).length < 2 ^ (prefixWord ++ tailWord_6083349).sum := by decide
  have hdescent : baseEnd_6083349 < baseStart_6083349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083379 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 5]
def baseStart_6083379 : Nat := 118140960795 + 6083379 * 2 ^ 59
def prefixEnd_6083379 : Nat := 4983230072969 + 3 ^ 40 * 6083379 * 2
def baseEnd_6083379 : Nat := 3123697430467859485385555

theorem tailTrace_6083379 : CollatzResearch.WordTrace tailWord_6083379 prefixEnd_6083379 3123697430467859485385555 := by
  unfold tailWord_6083379
  simp only [CollatzResearch.WordTrace]
  refine ⟨221879060227964316262605191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147919373485309544175070127 221879060227964316262605191)
  ·
    refine ⟨332818590341946474393907787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221879060227964316262605191 332818590341946474393907787)
    ·
      refine ⟨499227885512919711590861681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332818590341946474393907787 499227885512919711590861681)
      ·
        refine ⟨374420914134689783693146261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499227885512919711590861681 374420914134689783693146261)
        ·
          refine ⟨17550980350063583610616231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 374420914134689783693146261 17550980350063583610616231)
          ·
            refine ⟨26326470525095375415924347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17550980350063583610616231 26326470525095375415924347)
            ·
              refine ⟨39489705787643063123886521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26326470525095375415924347 39489705787643063123886521)
              ·
                refine ⟨29617279340732297342914891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39489705787643063123886521 29617279340732297342914891)
                ·
                  refine ⟨44425919011098446014372337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29617279340732297342914891 44425919011098446014372337)
                  ·
                    refine ⟨33319439258323834510779253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44425919011098446014372337 33319439258323834510779253)
                    ·
                      refine ⟨3123697430467859485385555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33319439258323834510779253 3123697430467859485385555)
                      ·
                        rfl

theorem cell23_6083379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_6083379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083379 prefixEnd_6083379 := by exact prefixLift 6083379
  have htrace : WordTrace (prefixWord ++ tailWord_6083379) baseStart_6083379 baseEnd_6083379 := by
    simpa [prefixWord, tailWord_6083379, baseEnd_6083379] using wordTrace_append hprefix tailTrace_6083379
  have hstable : (prefixWord ++ tailWord_6083379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083379).length < 2 ^ (prefixWord ++ tailWord_6083379).sum := by decide
  have hdescent : baseEnd_6083379 < baseStart_6083379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083439 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 3]
def baseStart_6083439 : Nat := 118140960795 + 6083439 * 2 ^ 59
def prefixEnd_6083439 : Nat := 4983230072969 + 3 ^ 40 * 6083439 * 2
def baseEnd_6083439 : Nat := 3123728239307129250635279

theorem tailTrace_6083439 : CollatzResearch.WordTrace tailWord_6083439 prefixEnd_6083439 3123728239307129250635279 := by
  unfold tailWord_6083439
  simp only [CollatzResearch.WordTrace]
  refine ⟨221881248607746946509789371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147920832405164631006526247 221881248607746946509789371)
  ·
    refine ⟨332821872911620419764684057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221881248607746946509789371 332821872911620419764684057)
    ·
      refine ⟨249616404683715314823513043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332821872911620419764684057 249616404683715314823513043)
      ·
        refine ⟨374424607025572972235269565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249616404683715314823513043 374424607025572972235269565)
        ·
          refine ⟨140409227634589864588226087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374424607025572972235269565 140409227634589864588226087)
          ·
            refine ⟨210613841451884796882339131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140409227634589864588226087 210613841451884796882339131)
            ·
              refine ⟨315920762177827195323508697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210613841451884796882339131 315920762177827195323508697)
              ·
                refine ⟨236940571633370396492631523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315920762177827195323508697 236940571633370396492631523)
                ·
                  refine ⟨355410857450055594738947285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236940571633370396492631523 355410857450055594738947285)
                  ·
                    refine ⟨8329941971485678001694077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 355410857450055594738947285 8329941971485678001694077)
                    ·
                      refine ⟨3123728239307129250635279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8329941971485678001694077 3123728239307129250635279)
                      ·
                        rfl

theorem cell23_6083439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 3].length) (baseStart_6083439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083439 prefixEnd_6083439 := by exact prefixLift 6083439
  have htrace : WordTrace (prefixWord ++ tailWord_6083439) baseStart_6083439 baseEnd_6083439 := by
    simpa [prefixWord, tailWord_6083439, baseEnd_6083439] using wordTrace_append hprefix tailTrace_6083439
  have hstable : (prefixWord ++ tailWord_6083439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083439).length < 2 ^ (prefixWord ++ tailWord_6083439).sum := by decide
  have hdescent : baseEnd_6083439 < baseStart_6083439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083449 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_6083449 : Nat := 118140960795 + 6083449 * 2 ^ 59
def prefixEnd_6083449 : Nat := 4983230072969 + 3 ^ 40 * 6083449 * 2
def baseEnd_6083449 : Nat := 3123733374113674211510233

theorem tailTrace_6083449 : CollatzResearch.WordTrace tailWord_6083449 prefixEnd_6083449 3123733374113674211510233 := by
  unfold tailWord_6083449
  simp only [CollatzResearch.WordTrace]
  refine ⟨221881613337710718217653401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147921075558473812145102267 221881613337710718217653401)
  ·
    refine ⟨166411210003283038663240051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221881613337710718217653401 166411210003283038663240051)
    ·
      refine ⟨249616815004924557994860077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166411210003283038663240051 249616815004924557994860077)
      ·
        refine ⟨93606305626846709248072529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249616815004924557994860077 93606305626846709248072529)
        ·
          refine ⟨70204729220135031936054397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93606305626846709248072529 70204729220135031936054397)
          ·
            refine ⟨26326773457550636976020399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70204729220135031936054397 26326773457550636976020399)
            ·
              refine ⟨39490160186325955464030599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26326773457550636976020399 39490160186325955464030599)
              ·
                refine ⟨59235240279488933196045899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39490160186325955464030599 59235240279488933196045899)
                ·
                  refine ⟨88852860419233399794068849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59235240279488933196045899 88852860419233399794068849)
                  ·
                    refine ⟨66639645314425049845551637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88852860419233399794068849 66639645314425049845551637)
                    ·
                      refine ⟨3123733374113674211510233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66639645314425049845551637 3123733374113674211510233)
                      ·
                        rfl

theorem cell23_6083449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_6083449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083449 prefixEnd_6083449 := by exact prefixLift 6083449
  have htrace : WordTrace (prefixWord ++ tailWord_6083449) baseStart_6083449 baseEnd_6083449 := by
    simpa [prefixWord, tailWord_6083449, baseEnd_6083449] using wordTrace_append hprefix tailTrace_6083449
  have hstable : (prefixWord ++ tailWord_6083449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083449).length < 2 ^ (prefixWord ++ tailWord_6083449).sum := by decide
  have hdescent : baseEnd_6083449 < baseStart_6083449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083463 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 6]
def baseStart_6083463 : Nat := 118140960795 + 6083463 * 2 ^ 59
def prefixEnd_6083463 : Nat := 4983230072969 + 3 ^ 40 * 6083463 * 2
def baseEnd_6083463 : Nat := 347082284760315239637241

theorem tailTrace_6083463 : CollatzResearch.WordTrace tailWord_6083463 prefixEnd_6083463 347082284760315239637241 := by
  unfold tailWord_6083463
  simp only [CollatzResearch.WordTrace]
  refine ⟨221882123959659998608663043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147921415973106665739108695 221882123959659998608663043)
  ·
    refine ⟨332823185939489997912994565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221882123959659998608663043 332823185939489997912994565)
    ·
      refine ⟨62404347363654374608686481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332823185939489997912994565 62404347363654374608686481)
      ·
        refine ⟨46803260522740780956514861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62404347363654374608686481 46803260522740780956514861)
        ·
          refine ⟨17551222696027792858693073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46803260522740780956514861 17551222696027792858693073)
          ·
            refine ⟨13163417022020844644019805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17551222696027792858693073 13163417022020844644019805)
            ·
              refine ⟨4936281383257816741507427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13163417022020844644019805 4936281383257816741507427)
              ·
                refine ⟨7404422074886725112261141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936281383257816741507427 7404422074886725112261141)
                ·
                  refine ⟨347082284760315239637241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7404422074886725112261141 347082284760315239637241)
                  ·
                    rfl

theorem cell23_6083463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 6].length) (baseStart_6083463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083463 prefixEnd_6083463 := by exact prefixLift 6083463
  have htrace : WordTrace (prefixWord ++ tailWord_6083463) baseStart_6083463 baseEnd_6083463 := by
    simpa [prefixWord, tailWord_6083463, baseEnd_6083463] using wordTrace_append hprefix tailTrace_6083463
  have hstable : (prefixWord ++ tailWord_6083463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083463).length < 2 ^ (prefixWord ++ tailWord_6083463).sum := by decide
  have hdescent : baseEnd_6083463 < baseStart_6083463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083484 : List Nat := [2, 2, 3, 3, 3, 1, 1, 3, 1, 4]
def baseStart_6083484 : Nat := 118140960795 + 6083484 * 2 ^ 59
def prefixEnd_6083484 : Nat := 4983230072969 + 3 ^ 40 * 6083484 * 2
def baseEnd_6083484 : Nat := 1041250448645527191524191

theorem tailTrace_6083484 : CollatzResearch.WordTrace tailWord_6083484 prefixEnd_6083484 1041250448645527191524191 := by
  unfold tailWord_6083484
  simp only [CollatzResearch.WordTrace]
  refine ⟨110941444946291959597588753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147921926595055946130118337 110941444946291959597588753)
  ·
    refine ⟨83206083709718969698191565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110941444946291959597588753 83206083709718969698191565)
    ·
      refine ⟨31202281391144613636821837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83206083709718969698191565 31202281391144613636821837)
      ·
        refine ⟨11700855521679230113808189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31202281391144613636821837 11700855521679230113808189)
        ·
          refine ⟨4387820820629711292678071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11700855521679230113808189 4387820820629711292678071)
          ·
            refine ⟨6581731230944566939017107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387820820629711292678071 6581731230944566939017107)
            ·
              refine ⟨9872596846416850408525661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6581731230944566939017107 9872596846416850408525661)
              ·
                refine ⟨3702223817406318903197123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9872596846416850408525661 3702223817406318903197123)
                ·
                  refine ⟨5553335726109478354795685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702223817406318903197123 5553335726109478354795685)
                  ·
                    refine ⟨1041250448645527191524191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5553335726109478354795685 1041250448645527191524191)
                    ·
                      rfl

theorem cell23_6083484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_6083484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083484 prefixEnd_6083484 := by exact prefixLift 6083484
  have htrace : WordTrace (prefixWord ++ tailWord_6083484) baseStart_6083484 baseEnd_6083484 := by
    simpa [prefixWord, tailWord_6083484, baseEnd_6083484] using wordTrace_append hprefix tailTrace_6083484
  have hstable : (prefixWord ++ tailWord_6083484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083484).length < 2 ^ (prefixWord ++ tailWord_6083484).sum := by decide
  have hdescent : baseEnd_6083484 < baseStart_6083484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083499 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 5]
def baseStart_6083499 : Nat := 118140960795 + 6083499 * 2 ^ 59
def prefixEnd_6083499 : Nat := 4983230072969 + 3 ^ 40 * 6083499 * 2
def baseEnd_6083499 : Nat := 3123759048146399015885003

theorem tailTrace_6083499 : CollatzResearch.WordTrace tailWord_6083499 prefixEnd_6083499 3123759048146399015885003 := by
  unfold tailWord_6083499
  simp only [CollatzResearch.WordTrace]
  refine ⟨221883436987529576756973551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147922291325019717837982367 221883436987529576756973551)
  ·
    refine ⟨332825155481294365135460327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221883436987529576756973551 332825155481294365135460327)
    ·
      refine ⟨499237733221941547703190491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332825155481294365135460327 499237733221941547703190491)
      ·
        refine ⟨748856599832912321554785737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499237733221941547703190491 748856599832912321554785737)
        ·
          refine ⟨561642449874684241166089303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748856599832912321554785737 561642449874684241166089303)
          ·
            refine ⟨842463674812026361749133955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561642449874684241166089303 842463674812026361749133955)
            ·
              refine ⟨1263695512218039542623700933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842463674812026361749133955 1263695512218039542623700933)
              ·
                refine ⟨236942908540882414241943925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1263695512218039542623700933 236942908540882414241943925)
                ·
                  refine ⟨22213397675707726335182243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 236942908540882414241943925 22213397675707726335182243)
                  ·
                    refine ⟨33320096513561589502773365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22213397675707726335182243 33320096513561589502773365)
                    ·
                      refine ⟨3123759048146399015885003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33320096513561589502773365 3123759048146399015885003)
                      ·
                        rfl

theorem cell23_6083499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 5].length) (baseStart_6083499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083499 prefixEnd_6083499 := by exact prefixLift 6083499
  have htrace : WordTrace (prefixWord ++ tailWord_6083499) baseStart_6083499 baseEnd_6083499 := by
    simpa [prefixWord, tailWord_6083499, baseEnd_6083499] using wordTrace_append hprefix tailTrace_6083499
  have hstable : (prefixWord ++ tailWord_6083499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083499).length < 2 ^ (prefixWord ++ tailWord_6083499).sum := by decide
  have hdescent : baseEnd_6083499 < baseStart_6083499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083557 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_6083557 : Nat := 118140960795 + 6083557 * 2 ^ 59
def prefixEnd_6083557 : Nat := 4983230072969 + 3 ^ 40 * 6083557 * 2
def baseEnd_6083557 : Nat := 1041262943341453262986579

theorem tailTrace_6083557 : CollatzResearch.WordTrace tailWord_6083557 prefixEnd_6083557 1041262943341453262986579 := by
  unfold tailWord_6083557
  simp only [CollatzResearch.WordTrace]
  refine ⟨221885552421319452662584925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147923701614212968441723283 221885552421319452662584925)
  ·
    refine ⟨83207082157994794748469347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221885552421319452662584925 83207082157994794748469347)
    ·
      refine ⟨124810623236992192122704021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83207082157994794748469347 124810623236992192122704021)
      ·
        refine ⟨5850497964234009005751751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124810623236992192122704021 5850497964234009005751751)
        ·
          refine ⟨8775746946351013508627627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850497964234009005751751 8775746946351013508627627)
          ·
            refine ⟨13163620419526520262941441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8775746946351013508627627 13163620419526520262941441)
            ·
              refine ⟨9872715314644890197206081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13163620419526520262941441 9872715314644890197206081)
              ·
                refine ⟨7404536485983667647904561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9872715314644890197206081 7404536485983667647904561)
                ·
                  refine ⟨5553402364487750735928421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7404536485983667647904561 5553402364487750735928421)
                  ·
                    refine ⟨1041262943341453262986579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5553402364487750735928421 1041262943341453262986579)
                    ·
                      rfl

theorem cell23_6083557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_6083557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083557 prefixEnd_6083557 := by exact prefixLift 6083557
  have htrace : WordTrace (prefixWord ++ tailWord_6083557) baseStart_6083557 baseEnd_6083557 := by
    simpa [prefixWord, tailWord_6083557, baseEnd_6083557] using wordTrace_append hprefix tailTrace_6083557
  have hstable : (prefixWord ++ tailWord_6083557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083557).length < 2 ^ (prefixWord ++ tailWord_6083557).sum := by decide
  have hdescent : baseEnd_6083557 < baseStart_6083557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083570 : List Nat := [3, 2, 1, 5, 1, 2, 1, 8]
def baseStart_6083570 : Nat := 118140960795 + 6083570 * 2 ^ 59
def prefixEnd_6083570 : Nat := 4983230072969 + 3 ^ 40 * 6083570 * 2
def baseEnd_6083570 : Nat := 115696129824921045855451

theorem tailTrace_6083570 : CollatzResearch.WordTrace tailWord_6083570 prefixEnd_6083570 115696129824921045855451 := by
  unfold tailWord_6083570
  simp only [CollatzResearch.WordTrace]
  refine ⟨55471506642568088970702041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147924017713514903921872109 55471506642568088970702041)
  ·
    refine ⟨41603629981926066728026531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55471506642568088970702041 41603629981926066728026531)
    ·
      refine ⟨62405444972889100092039797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41603629981926066728026531 62405444972889100092039797)
      ·
        refine ⟨5850510466208353133628731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62405444972889100092039797 5850510466208353133628731)
        ·
          refine ⟨8775765699312529700443097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850510466208353133628731 8775765699312529700443097)
          ·
            refine ⟨6581824274484397275332323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8775765699312529700443097 6581824274484397275332323)
            ·
              refine ⟨9872736411726595912998485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6581824274484397275332323 9872736411726595912998485)
              ·
                refine ⟨115696129824921045855451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9872736411726595912998485 115696129824921045855451)
                ·
                  rfl

theorem cell23_6083570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 8].length) (baseStart_6083570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083570 prefixEnd_6083570 := by exact prefixLift 6083570
  have htrace : WordTrace (prefixWord ++ tailWord_6083570) baseStart_6083570 baseEnd_6083570 := by
    simpa [prefixWord, tailWord_6083570, baseEnd_6083570] using wordTrace_append hprefix tailTrace_6083570
  have hstable : (prefixWord ++ tailWord_6083570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083570).length < 2 ^ (prefixWord ++ tailWord_6083570).sum := by decide
  have hdescent : baseEnd_6083570 < baseStart_6083570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083580 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_6083580 : Nat := 118140960795 + 6083580 * 2 ^ 59
def prefixEnd_6083580 : Nat := 4983230072969 + 3 ^ 40 * 6083580 * 2
def baseEnd_6083580 : Nat := 3123800640079413198972131

theorem tailTrace_6083580 : CollatzResearch.WordTrace tailWord_6083580 prefixEnd_6083580 3123800640079413198972131 := by
  unfold tailWord_6083580
  simp only [CollatzResearch.WordTrace]
  refine ⟨110943195650118063795336097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147924260866824085060448129 110943195650118063795336097)
  ·
    refine ⟨83207396737588547846502073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110943195650118063795336097 83207396737588547846502073)
    ·
      refine ⟨62405547553191410884876555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83207396737588547846502073 62405547553191410884876555)
      ·
        refine ⟨93608321329787116327314833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62405547553191410884876555 93608321329787116327314833)
        ·
          refine ⟨70206240997340337245486125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93608321329787116327314833 70206240997340337245486125)
          ·
            refine ⟨26327340374002626467057297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70206240997340337245486125 26327340374002626467057297)
            ·
              refine ⟨19745505280501969850292973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26327340374002626467057297 19745505280501969850292973)
              ·
                refine ⟨7404564480188238693859865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19745505280501969850292973 7404564480188238693859865)
                ·
                  refine ⟨5553423360141179020394899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7404564480188238693859865 5553423360141179020394899)
                  ·
                    refine ⟨8330135040211768530592349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5553423360141179020394899 8330135040211768530592349)
                    ·
                      refine ⟨3123800640079413198972131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8330135040211768530592349 3123800640079413198972131)
                      ·
                        rfl

theorem cell23_6083580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_6083580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083580 prefixEnd_6083580 := by exact prefixLift 6083580
  have htrace : WordTrace (prefixWord ++ tailWord_6083580) baseStart_6083580 baseEnd_6083580 := by
    simpa [prefixWord, tailWord_6083580, baseEnd_6083580] using wordTrace_append hprefix tailTrace_6083580
  have hstable : (prefixWord ++ tailWord_6083580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083580).length < 2 ^ (prefixWord ++ tailWord_6083580).sum := by decide
  have hdescent : baseEnd_6083580 < baseStart_6083580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083607 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6083607 : Nat := 118140960795 + 6083607 * 2 ^ 59
def prefixEnd_6083607 : Nat := 4983230072969 + 3 ^ 40 * 6083607 * 2
def baseEnd_6083607 : Nat := 3123814504057084593334507

theorem tailTrace_6083607 : CollatzResearch.WordTrace tailWord_6083607 prefixEnd_6083607 3123814504057084593334507 := by
  unfold tailWord_6083607
  simp only [CollatzResearch.WordTrace]
  refine ⟨221887376071138311201905075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147924917380758874134603383 221887376071138311201905075)
  ·
    refine ⟨332831064106707466802857613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221887376071138311201905075 332831064106707466802857613)
    ·
      refine ⟨124811649040015300051071605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332831064106707466802857613 124811649040015300051071605)
      ·
        refine ⟨11701092097501434379787963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124811649040015300051071605 11701092097501434379787963)
        ·
          refine ⟨17551638146252151569681945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11701092097501434379787963 17551638146252151569681945)
          ·
            refine ⟨13163728609689113677261459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17551638146252151569681945 13163728609689113677261459)
            ·
              refine ⟨19745592914533670515892189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13163728609689113677261459 19745592914533670515892189)
              ·
                refine ⟨7404597342950126443459571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19745592914533670515892189 7404597342950126443459571)
                ·
                  refine ⟨11106896014425189665189357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7404597342950126443459571 11106896014425189665189357)
                  ·
                    refine ⟨4165086005409446124446009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11106896014425189665189357 4165086005409446124446009)
                    ·
                      refine ⟨3123814504057084593334507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165086005409446124446009 3123814504057084593334507)
                      ·
                        rfl

theorem cell23_6083607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6083607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083607 prefixEnd_6083607 := by exact prefixLift 6083607
  have htrace : WordTrace (prefixWord ++ tailWord_6083607) baseStart_6083607 baseEnd_6083607 := by
    simpa [prefixWord, tailWord_6083607, baseEnd_6083607] using wordTrace_append hprefix tailTrace_6083607
  have hstable : (prefixWord ++ tailWord_6083607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083607).length < 2 ^ (prefixWord ++ tailWord_6083607).sum := by decide
  have hdescent : baseEnd_6083607 < baseStart_6083607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083654 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_6083654 : Nat := 118140960795 + 6083654 * 2 ^ 59
def prefixEnd_6083654 : Nat := 4983230072969 + 3 ^ 40 * 6083654 * 2
def baseEnd_6083654 : Nat := 3123838637647845909446791

theorem tailTrace_6083654 : CollatzResearch.WordTrace tailWord_6083654 prefixEnd_6083654 3123838637647845909446791 := by
  unfold tailWord_6083654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6934034071936501194652063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147926060201312025485910677 6934034071936501194652063)
  ·
    refine ⟨10401051107904751791978095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6934034071936501194652063 10401051107904751791978095)
    ·
      refine ⟨15601576661857127687967143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10401051107904751791978095 15601576661857127687967143)
      ·
        refine ⟨23402364992785691531950715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15601576661857127687967143 23402364992785691531950715)
        ·
          refine ⟨35103547489178537297926073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23402364992785691531950715 35103547489178537297926073)
          ·
            refine ⟨26327660616883902973444555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35103547489178537297926073 26327660616883902973444555)
            ·
              refine ⟨39491490925325854460166833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26327660616883902973444555 39491490925325854460166833)
              ·
                refine ⟨29618618193994390845125125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39491490925325854460166833 29618618193994390845125125)
                ·
                  refine ⟨5553490911373948283460961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29618618193994390845125125 5553490911373948283460961)
                  ·
                    refine ⟨4165118183530461212595721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5553490911373948283460961 4165118183530461212595721)
                    ·
                      refine ⟨3123838637647845909446791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165118183530461212595721 3123838637647845909446791)
                      ·
                        rfl

theorem cell23_6083654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_6083654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083654 prefixEnd_6083654 := by exact prefixLift 6083654
  have htrace : WordTrace (prefixWord ++ tailWord_6083654) baseStart_6083654 baseEnd_6083654 := by
    simpa [prefixWord, tailWord_6083654, baseEnd_6083654] using wordTrace_append hprefix tailTrace_6083654
  have hstable : (prefixWord ++ tailWord_6083654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083654).length < 2 ^ (prefixWord ++ tailWord_6083654).sum := by decide
  have hdescent : baseEnd_6083654 < baseStart_6083654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083656 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 1, 7]
def baseStart_6083656 : Nat := 118140960795 + 6083656 * 2 ^ 59
def prefixEnd_6083656 : Nat := 4983230072969 + 3 ^ 40 * 6083656 * 2
def baseEnd_6083656 : Nat := 1041279888203051633873927

theorem tailTrace_6083656 : CollatzResearch.WordTrace tailWord_6083656 prefixEnd_6083656 1041279888203051633873927 := by
  unfold tailWord_6083656
  simp only [CollatzResearch.WordTrace]
  refine ⟨110944581623980396285219411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147926108831973861713625881 110944581623980396285219411)
  ·
    refine ⟨166416872435970594427829117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110944581623980396285219411 166416872435970594427829117)
    ·
      refine ⟨62406327163488972910435919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166416872435970594427829117 62406327163488972910435919)
      ·
        refine ⟨93609490745233459365653879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62406327163488972910435919 93609490745233459365653879)
        ·
          refine ⟨140414236117850189048480819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93609490745233459365653879 140414236117850189048480819)
          ·
            refine ⟨210621354176775283572721229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140414236117850189048480819 210621354176775283572721229)
            ·
              refine ⟨78983007816290731339770461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210621354176775283572721229 78983007816290731339770461)
              ·
                refine ⟨29618627931109024252413923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78983007816290731339770461 29618627931109024252413923)
                ·
                  refine ⟨44427941896663536378620885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29618627931109024252413923 44427941896663536378620885)
                  ·
                    refine ⟨1041279888203051633873927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44427941896663536378620885 1041279888203051633873927)
                    ·
                      rfl

theorem cell23_6083656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_6083656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083656 prefixEnd_6083656 := by exact prefixLift 6083656
  have htrace : WordTrace (prefixWord ++ tailWord_6083656) baseStart_6083656 baseEnd_6083656 := by
    simpa [prefixWord, tailWord_6083656, baseEnd_6083656] using wordTrace_append hprefix tailTrace_6083656
  have hstable : (prefixWord ++ tailWord_6083656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083656).length < 2 ^ (prefixWord ++ tailWord_6083656).sum := by decide
  have hdescent : baseEnd_6083656 < baseStart_6083656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083677 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 7]
def baseStart_6083677 : Nat := 118140960795 + 6083677 * 2 ^ 59
def prefixEnd_6083677 : Nat := 4983230072969 + 3 ^ 40 * 6083677 * 2
def baseEnd_6083677 : Nat := 347094494189211035495465

theorem tailTrace_6083677 : CollatzResearch.WordTrace tailWord_6083677 prefixEnd_6083677 347094494189211035495465 := by
  unfold tailWord_6083677
  simp only [CollatzResearch.WordTrace]
  refine ⟨221889929180884713156953285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147926619453923142104635523 221889929180884713156953285)
  ·
    refine ⟨41604361721415883716928741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221889929180884713156953285 41604361721415883716928741)
    ·
      refine ⟨7800817822765478196924139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41604361721415883716928741 7800817822765478196924139)
      ·
        refine ⟨11701226734148217295386209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7800817822765478196924139 11701226734148217295386209)
        ·
          refine ⟨8775920050611162971539657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11701226734148217295386209 8775920050611162971539657)
          ·
            refine ⟨6581940037958372228654743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8775920050611162971539657 6581940037958372228654743)
            ·
              refine ⟨9872910056937558342982115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6581940037958372228654743 9872910056937558342982115)
              ·
                refine ⟨14809365085406337514473173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9872910056937558342982115 14809365085406337514473173)
                ·
                  refine ⟨347094494189211035495465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14809365085406337514473173 347094494189211035495465)
                  ·
                    rfl

theorem cell23_6083677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_6083677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083677 prefixEnd_6083677 := by exact prefixLift 6083677
  have htrace : WordTrace (prefixWord ++ tailWord_6083677) baseStart_6083677 baseEnd_6083677 := by
    simpa [prefixWord, tailWord_6083677, baseEnd_6083677] using wordTrace_append hprefix tailTrace_6083677
  have hstable : (prefixWord ++ tailWord_6083677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083677).length < 2 ^ (prefixWord ++ tailWord_6083677).sum := by decide
  have hdescent : baseEnd_6083677 < baseStart_6083677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083688 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6083688 : Nat := 118140960795 + 6083688 * 2 ^ 59
def prefixEnd_6083688 : Nat := 4983230072969 + 3 ^ 40 * 6083688 * 2
def baseEnd_6083688 : Nat := 3123856095990098776421635

theorem tailTrace_6083688 : CollatzResearch.WordTrace tailWord_6083688 prefixEnd_6083688 3123856095990098776421635 := by
  unfold tailWord_6083688
  simp only [CollatzResearch.WordTrace]
  refine ⟨110945165191922431017801859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147926886922563241357069145 110945165191922431017801859)
  ·
    refine ⟨166417747787883646526702789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110945165191922431017801859 166417747787883646526702789)
    ·
      refine ⟨31203327710228183723756773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166417747787883646526702789 31203327710228183723756773)
      ·
        refine ⟨5850623945667784448204395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31203327710228183723756773 5850623945667784448204395)
        ·
          refine ⟨8775935918501676672306593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850623945667784448204395 8775935918501676672306593)
          ·
            refine ⟨6581951938876257504229945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8775935918501676672306593 6581951938876257504229945)
            ·
              refine ⟨4936463954157193128172459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6581951938876257504229945 4936463954157193128172459)
              ·
                refine ⟨7404695931235789692258689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936463954157193128172459 7404695931235789692258689)
                ·
                  refine ⟨5553521948426842269194017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7404695931235789692258689 5553521948426842269194017)
                  ·
                    refine ⟨4165141461320131701895513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5553521948426842269194017 4165141461320131701895513)
                    ·
                      refine ⟨3123856095990098776421635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165141461320131701895513 3123856095990098776421635)
                      ·
                        rfl

theorem cell23_6083688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6083688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083688 prefixEnd_6083688 := by exact prefixLift 6083688
  have htrace : WordTrace (prefixWord ++ tailWord_6083688) baseStart_6083688 baseEnd_6083688 := by
    simpa [prefixWord, tailWord_6083688, baseEnd_6083688] using wordTrace_append hprefix tailTrace_6083688
  have hstable : (prefixWord ++ tailWord_6083688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083688).length < 2 ^ (prefixWord ++ tailWord_6083688).sum := by decide
  have hdescent : baseEnd_6083688 < baseStart_6083688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083703 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 5, 4]
def baseStart_6083703 : Nat := 118140960795 + 6083703 * 2 ^ 59
def prefixEnd_6083703 : Nat := 4983230072969 + 3 ^ 40 * 6083703 * 2
def baseEnd_6083703 : Nat := 1041287932733305405911355

theorem tailTrace_6083703 : CollatzResearch.WordTrace tailWord_6083703 prefixEnd_6083703 1041287932733305405911355 := by
  unfold tailWord_6083703
  simp only [CollatzResearch.WordTrace]
  refine ⟨221890877478790519597399763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147927251652527013064933175 221890877478790519597399763)
  ·
    refine ⟨332836316218185779396099645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221890877478790519597399763 332836316218185779396099645)
    ·
      refine ⟨124813618581819667273537367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332836316218185779396099645 124813618581819667273537367)
      ·
        refine ⟨187220427872729500910306051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124813618581819667273537367 187220427872729500910306051)
        ·
          refine ⟨280830641809094251365459077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187220427872729500910306051 280830641809094251365459077)
          ·
            refine ⟨52655745339205172131023577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280830641809094251365459077 52655745339205172131023577)
            ·
              refine ⟨39491809004403879098267683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52655745339205172131023577 39491809004403879098267683)
              ·
                refine ⟨59237713506605818647401525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39491809004403879098267683 59237713506605818647401525)
                ·
                  refine ⟨5553535641244295498193893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59237713506605818647401525 5553535641244295498193893)
                  ·
                    refine ⟨1041287932733305405911355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5553535641244295498193893 1041287932733305405911355)
                    ·
                      rfl

theorem cell23_6083703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_6083703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083703 prefixEnd_6083703 := by exact prefixLift 6083703
  have htrace : WordTrace (prefixWord ++ tailWord_6083703) baseStart_6083703 baseEnd_6083703 := by
    simpa [prefixWord, tailWord_6083703, baseEnd_6083703] using wordTrace_append hprefix tailTrace_6083703
  have hstable : (prefixWord ++ tailWord_6083703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083703).length < 2 ^ (prefixWord ++ tailWord_6083703).sum := by decide
  have hdescent : baseEnd_6083703 < baseStart_6083703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083760 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 3, 1, 3]
def baseStart_6083760 : Nat := 118140960795 + 6083760 * 2 ^ 59
def prefixEnd_6083760 : Nat := 4983230072969 + 3 ^ 40 * 6083760 * 2
def baseEnd_6083760 : Nat := 3123893066597222494721303

theorem tailTrace_6083760 : CollatzResearch.WordTrace tailWord_6083760 prefixEnd_6083760 3123893066597222494721303 := by
  unfold tailWord_6083760
  simp only [CollatzResearch.WordTrace]
  refine ⟨110946478219792009166112367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147928637626389345554816489 110946478219792009166112367)
  ·
    refine ⟨166419717329688013749168551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110946478219792009166112367 166419717329688013749168551)
    ·
      refine ⟨249629575994532020623752827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166419717329688013749168551 249629575994532020623752827)
      ·
        refine ⟨374444363991798030935629241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249629575994532020623752827 374444363991798030935629241)
        ·
          refine ⟨280833272993848523201721931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374444363991798030935629241 280833272993848523201721931)
          ·
            refine ⟨421249909490772784802582897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280833272993848523201721931 421249909490772784802582897)
            ·
              refine ⟨315937432118079588601937173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421249909490772784802582897 315937432118079588601937173)
              ·
                refine ⟨14809567130534980715715805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 315937432118079588601937173 14809567130534980715715805)
                ·
                  refine ⟨5553587673950617768393427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14809567130534980715715805 5553587673950617768393427)
                  ·
                    refine ⟨8330381510925926652590141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5553587673950617768393427 8330381510925926652590141)
                    ·
                      refine ⟨3123893066597222494721303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8330381510925926652590141 3123893066597222494721303)
                      ·
                        rfl

theorem cell23_6083760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3, 1, 3].length) (baseStart_6083760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083760 prefixEnd_6083760 := by exact prefixLift 6083760
  have htrace : WordTrace (prefixWord ++ tailWord_6083760) baseStart_6083760 baseEnd_6083760 := by
    simpa [prefixWord, tailWord_6083760, baseEnd_6083760] using wordTrace_append hprefix tailTrace_6083760
  have hstable : (prefixWord ++ tailWord_6083760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083760).length < 2 ^ (prefixWord ++ tailWord_6083760).sum := by decide
  have hdescent : baseEnd_6083760 < baseStart_6083760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083763 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 3, 5]
def baseStart_6083763 : Nat := 118140960795 + 6083763 * 2 ^ 59
def prefixEnd_6083763 : Nat := 4983230072969 + 3 ^ 40 * 6083763 * 2
def baseEnd_6083763 : Nat := 1041298202346395327661263

theorem tailTrace_6083763 : CollatzResearch.WordTrace tailWord_6083763 prefixEnd_6083763 1041298202346395327661263 := by
  unfold tailWord_6083763
  simp only [CollatzResearch.WordTrace]
  refine ⟨221893065858573149844583943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147928710572382099896389295 221893065858573149844583943)
  ·
    refine ⟨332839598787859724766875915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221893065858573149844583943 332839598787859724766875915)
    ·
      refine ⟨499259398181789587150313873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332839598787859724766875915 499259398181789587150313873)
      ·
        refine ⟨374444548636342190362735405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499259398181789587150313873 374444548636342190362735405)
        ·
          refine ⟨140416705738628321386025777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374444548636342190362735405 140416705738628321386025777)
          ·
            refine ⟨105312529303971241039519333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140416705738628321386025777 105312529303971241039519333)
            ·
              refine ⟨19746099244494607694909875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105312529303971241039519333 19746099244494607694909875)
              ·
                refine ⟨29619148866741911542364813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19746099244494607694909875 29619148866741911542364813)
                ·
                  refine ⟨11107180825028216828386805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29619148866741911542364813 11107180825028216828386805)
                  ·
                    refine ⟨1041298202346395327661263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11107180825028216828386805 1041298202346395327661263)
                    ·
                      rfl

theorem cell23_6083763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 5].length) (baseStart_6083763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083763 prefixEnd_6083763 := by exact prefixLift 6083763
  have htrace : WordTrace (prefixWord ++ tailWord_6083763) baseStart_6083763 baseEnd_6083763 := by
    simpa [prefixWord, tailWord_6083763, baseEnd_6083763] using wordTrace_append hprefix tailTrace_6083763
  have hstable : (prefixWord ++ tailWord_6083763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083763).length < 2 ^ (prefixWord ++ tailWord_6083763).sum := by decide
  have hdescent : baseEnd_6083763 < baseStart_6083763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083794 : List Nat := [3, 2, 2, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_6083794 : Nat := 118140960795 + 6083794 * 2 ^ 59
def prefixEnd_6083794 : Nat := 4983230072969 + 3 ^ 40 * 6083794 * 2
def baseEnd_6083794 : Nat := 3123910524939475361696147

theorem tailTrace_6083794 : CollatzResearch.WordTrace tailWord_6083794 prefixEnd_6083794 3123910524939475361696147 := by
  unfold tailWord_6083794
  simp only [CollatzResearch.WordTrace]
  refine ⟨55473549130365210534740609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147929464347640561425974957 55473549130365210534740609)
  ·
    refine ⟨41605161847773907901055457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55473549130365210534740609 41605161847773907901055457)
    ·
      refine ⟨31203871385830430925791593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41605161847773907901055457 31203871385830430925791593)
      ·
        refine ⟨23402903539372823194343695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31203871385830430925791593 23402903539372823194343695)
        ·
          refine ⟨35104355309059234791515543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23402903539372823194343695 35104355309059234791515543)
          ·
            refine ⟨52656532963588852187273315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35104355309059234791515543 52656532963588852187273315)
            ·
              refine ⟨78984799445383278280909973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52656532963588852187273315 78984799445383278280909973)
              ·
                refine ⟨3702412474002341169417655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78984799445383278280909973 3702412474002341169417655)
                ·
                  refine ⟨5553618711003511754126483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702412474002341169417655 5553618711003511754126483)
                  ·
                    refine ⟨8330428066505267631189725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5553618711003511754126483 8330428066505267631189725)
                    ·
                      refine ⟨3123910524939475361696147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8330428066505267631189725 3123910524939475361696147)
                      ·
                        rfl

theorem cell23_6083794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_6083794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083794 prefixEnd_6083794 := by exact prefixLift 6083794
  have htrace : WordTrace (prefixWord ++ tailWord_6083794) baseStart_6083794 baseEnd_6083794 := by
    simpa [prefixWord, tailWord_6083794, baseEnd_6083794] using wordTrace_append hprefix tailTrace_6083794
  have hstable : (prefixWord ++ tailWord_6083794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083794).length < 2 ^ (prefixWord ++ tailWord_6083794).sum := by decide
  have hdescent : baseEnd_6083794 < baseStart_6083794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083830 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_6083830 : Nat := 118140960795 + 6083830 * 2 ^ 59
def prefixEnd_6083830 : Nat := 4983230072969 + 3 ^ 40 * 6083830 * 2
def baseEnd_6083830 : Nat := 3123929010243037220845981

theorem tailTrace_6083830 : CollatzResearch.WordTrace tailWord_6083830 prefixEnd_6083830 3123929010243037220845981 := by
  unfold tailWord_6083830
  simp only [CollatzResearch.WordTrace]
  refine ⟨13868469346833151267954559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147930339699553613524848629 13868469346833151267954559)
  ·
    refine ⟨20802704020249726901931839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13868469346833151267954559 20802704020249726901931839)
    ·
      refine ⟨31204056030374590352897759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20802704020249726901931839 31204056030374590352897759)
      ·
        refine ⟨46806084045561885529346639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31204056030374590352897759 46806084045561885529346639)
        ·
          refine ⟨70209126068342828294019959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46806084045561885529346639 70209126068342828294019959)
          ·
            refine ⟨105313689102514242441029939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70209126068342828294019959 105313689102514242441029939)
            ·
              refine ⟨157970533653771363661544909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105313689102514242441029939 157970533653771363661544909)
              ·
                refine ⟨59238950120164261373079341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157970533653771363661544909 59238950120164261373079341)
                ·
                  refine ⟨22214606295061598014904753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59238950120164261373079341 22214606295061598014904753)
                  ·
                    refine ⟨16660954721296198511178565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22214606295061598014904753 16660954721296198511178565)
                    ·
                      refine ⟨3123929010243037220845981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16660954721296198511178565 3123929010243037220845981)
                      ·
                        rfl

theorem cell23_6083830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_6083830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083830 prefixEnd_6083830 := by exact prefixLift 6083830
  have htrace : WordTrace (prefixWord ++ tailWord_6083830) baseStart_6083830 baseEnd_6083830 := by
    simpa [prefixWord, tailWord_6083830, baseEnd_6083830] using wordTrace_append hprefix tailTrace_6083830
  have hstable : (prefixWord ++ tailWord_6083830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083830).length < 2 ^ (prefixWord ++ tailWord_6083830).sum := by decide
  have hdescent : baseEnd_6083830 < baseStart_6083830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083871 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 1, 2, 3]
def baseStart_6083871 : Nat := 118140960795 + 6083871 * 2 ^ 59
def prefixEnd_6083871 : Nat := 4983230072969 + 3 ^ 40 * 6083871 * 2
def baseEnd_6083871 : Nat := 3123950062949871560433293

theorem tailTrace_6083871 : CollatzResearch.WordTrace tailWord_6083871 prefixEnd_6083871 3123950062949871560433293 := by
  unfold tailWord_6083871
  simp only [CollatzResearch.WordTrace]
  refine ⟨221897004942181884289515467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147931336628121256193010311 221897004942181884289515467)
  ·
    refine ⟨332845507413272826434273201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221897004942181884289515467 332845507413272826434273201)
    ·
      refine ⟨249634130559954619825704901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332845507413272826434273201 249634130559954619825704901)
      ·
        refine ⟨46806399479991491217319669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249634130559954619825704901 46806399479991491217319669)
        ·
          refine ⟨4388099951249202301623719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46806399479991491217319669 4388099951249202301623719)
          ·
            refine ⟨6582149926873803452435579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388099951249202301623719 6582149926873803452435579)
            ·
              refine ⟨9873224890310705178653369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582149926873803452435579 9873224890310705178653369)
              ·
                refine ⟨7404918667733028883990027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9873224890310705178653369 7404918667733028883990027)
                ·
                  refine ⟨11107378001599543325985041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7404918667733028883990027 11107378001599543325985041)
                  ·
                    refine ⟨8330533501199657494488781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11107378001599543325985041 8330533501199657494488781)
                    ·
                      refine ⟨3123950062949871560433293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8330533501199657494488781 3123950062949871560433293)
                      ·
                        rfl

theorem cell23_6083871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_6083871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083871 prefixEnd_6083871 := by exact prefixLift 6083871
  have htrace : WordTrace (prefixWord ++ tailWord_6083871) baseStart_6083871 baseEnd_6083871 := by
    simpa [prefixWord, tailWord_6083871, baseEnd_6083871] using wordTrace_append hprefix tailTrace_6083871
  have hstable : (prefixWord ++ tailWord_6083871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083871).length < 2 ^ (prefixWord ++ tailWord_6083871).sum := by decide
  have hdescent : baseEnd_6083871 < baseStart_6083871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083873 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_6083873 : Nat := 118140960795 + 6083873 * 2 ^ 59
def prefixEnd_6083873 : Nat := 4983230072969 + 3 ^ 40 * 6083873 * 2
def baseEnd_6083873 : Nat := 3123951089911180552608283

theorem tailTrace_6083873 : CollatzResearch.WordTrace tailWord_6083873 prefixEnd_6083873 3123951089911180552608283 := by
  unfold tailWord_6083873
  simp only [CollatzResearch.WordTrace]
  refine ⟨221897077888174638631088273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147931385258783092420725515 221897077888174638631088273)
  ·
    refine ⟨166422808416130978973316205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221897077888174638631088273 166422808416130978973316205)
    ·
      refine ⟨62408553156049117114993577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166422808416130978973316205 62408553156049117114993577)
      ·
        refine ⟨46806414867036837836245183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62408553156049117114993577 46806414867036837836245183)
        ·
          refine ⟨70209622300555256754367775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46806414867036837836245183 70209622300555256754367775)
          ·
            refine ⟨105314433450832885131551663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70209622300555256754367775 105314433450832885131551663)
            ·
              refine ⟨157971650176249327697327495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105314433450832885131551663 157971650176249327697327495)
              ·
                refine ⟨236957475264373991545991243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157971650176249327697327495 236957475264373991545991243)
                ·
                  refine ⟨355436212896560987318986865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236957475264373991545991243 355436212896560987318986865)
                  ·
                    refine ⟨266577159672420740489240149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355436212896560987318986865 266577159672420740489240149)
                    ·
                      refine ⟨3123951089911180552608283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 266577159672420740489240149 3123951089911180552608283)
                      ·
                        rfl

theorem cell23_6083873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_6083873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083873 prefixEnd_6083873 := by exact prefixLift 6083873
  have htrace : WordTrace (prefixWord ++ tailWord_6083873) baseStart_6083873 baseEnd_6083873 := by
    simpa [prefixWord, tailWord_6083873, baseEnd_6083873] using wordTrace_append hprefix tailTrace_6083873
  have hstable : (prefixWord ++ tailWord_6083873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083873).length < 2 ^ (prefixWord ++ tailWord_6083873).sum := by decide
  have hdescent : baseEnd_6083873 < baseStart_6083873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083920 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_6083920 : Nat := 118140960795 + 6083920 * 2 ^ 59
def prefixEnd_6083920 : Nat := 4983230072969 + 3 ^ 40 * 6083920 * 2
def baseEnd_6083920 : Nat := 3123975223501941868720567

theorem tailTrace_6083920 : CollatzResearch.WordTrace tailWord_6083920 prefixEnd_6083920 3123975223501941868720567 := by
  unfold tailWord_6083920
  simp only [CollatzResearch.WordTrace]
  refine ⟨110949396059502182829024607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147932528079336243772032809 110949396059502182829024607)
  ·
    refine ⟨166424094089253274243536911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110949396059502182829024607 166424094089253274243536911)
    ·
      refine ⟨249636141133879911365305367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166424094089253274243536911 249636141133879911365305367)
      ·
        refine ⟨374454211700819867047958051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249636141133879911365305367 374454211700819867047958051)
        ·
          refine ⟨561681317551229800571937077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374454211700819867047958051 561681317551229800571937077)
          ·
            refine ⟨52657623520427793803619101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 561681317551229800571937077 52657623520427793803619101)
            ·
              refine ⟨19746608820160422676357163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52657623520427793803619101 19746608820160422676357163)
              ·
                refine ⟨29619913230240634014535745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19746608820160422676357163 29619913230240634014535745)
                ·
                  refine ⟨22214934922680475510901809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29619913230240634014535745 22214934922680475510901809)
                  ·
                    refine ⟨16661201192010356633176357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22214934922680475510901809 16661201192010356633176357)
                    ·
                      refine ⟨3123975223501941868720567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16661201192010356633176357 3123975223501941868720567)
                      ·
                        rfl

theorem cell23_6083920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_6083920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083920 prefixEnd_6083920 := by exact prefixLift 6083920
  have htrace : WordTrace (prefixWord ++ tailWord_6083920) baseStart_6083920 baseEnd_6083920 := by
    simpa [prefixWord, tailWord_6083920, baseEnd_6083920] using wordTrace_append hprefix tailTrace_6083920
  have hstable : (prefixWord ++ tailWord_6083920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083920).length < 2 ^ (prefixWord ++ tailWord_6083920).sum := by decide
  have hdescent : baseEnd_6083920 < baseStart_6083920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083924 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_6083924 : Nat := 118140960795 + 6083924 * 2 ^ 59
def prefixEnd_6083924 : Nat := 4983230072969 + 3 ^ 40 * 6083924 * 2
def baseEnd_6083924 : Nat := 3123977277424559853070549

theorem tailTrace_6083924 : CollatzResearch.WordTrace tailWord_6083924 prefixEnd_6083924 3123977277424559853070549 := by
  unfold tailWord_6083924
  simp only [CollatzResearch.WordTrace]
  refine ⟨110949469005494937170597413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147932625340659916227463217 110949469005494937170597413)
  ·
    refine ⟨20803025438530300719487015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110949469005494937170597413 20803025438530300719487015)
    ·
      refine ⟨31204538157795451079230523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20803025438530300719487015 31204538157795451079230523)
      ·
        refine ⟨46806807236693176618845785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31204538157795451079230523 46806807236693176618845785)
        ·
          refine ⟨35105105427519882464134339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46806807236693176618845785 35105105427519882464134339)
          ·
            refine ⟨52657658141279823696201509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35105105427519882464134339 52657658141279823696201509)
            ·
              refine ⟨9873310901489966943037783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52657658141279823696201509 9873310901489966943037783)
              ·
                refine ⟨14809966352234950414556675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9873310901489966943037783 14809966352234950414556675)
                ·
                  refine ⟨22214949528352425621835013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14809966352234950414556675 22214949528352425621835013)
                  ·
                    refine ⟨4165303036566079804094065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22214949528352425621835013 4165303036566079804094065)
                    ·
                      refine ⟨3123977277424559853070549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165303036566079804094065 3123977277424559853070549)
                      ·
                        rfl

theorem cell23_6083924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_6083924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083924 prefixEnd_6083924 := by exact prefixLift 6083924
  have htrace : WordTrace (prefixWord ++ tailWord_6083924) baseStart_6083924 baseEnd_6083924 := by
    simpa [prefixWord, tailWord_6083924, baseEnd_6083924] using wordTrace_append hprefix tailTrace_6083924
  have hstable : (prefixWord ++ tailWord_6083924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083924).length < 2 ^ (prefixWord ++ tailWord_6083924).sum := by decide
  have hdescent : baseEnd_6083924 < baseStart_6083924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083980 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_6083980 : Nat := 118140960795 + 6083980 * 2 ^ 59
def prefixEnd_6083980 : Nat := 4983230072969 + 3 ^ 40 * 6083980 * 2
def baseEnd_6083980 : Nat := 3124006032341211633970291

theorem tailTrace_6083980 : CollatzResearch.WordTrace tailWord_6083980 prefixEnd_6083980 3124006032341211633970291 := by
  unfold tailWord_6083980
  simp only [CollatzResearch.WordTrace]
  refine ⟨110950490249393497952616697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147933986999191330603488929 110950490249393497952616697)
  ·
    refine ⟨83212867687045123464462523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110950490249393497952616697 83212867687045123464462523)
    ·
      refine ⟨124819301530567685196693785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83212867687045123464462523 124819301530567685196693785)
      ·
        refine ⟨93614476147925763897520339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124819301530567685196693785 93614476147925763897520339)
        ·
          refine ⟨140421714221888645846280509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93614476147925763897520339 140421714221888645846280509)
          ·
            refine ⟨52658142833208242192355191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140421714221888645846280509 52658142833208242192355191)
            ·
              refine ⟨78987214249812363288532787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52658142833208242192355191 78987214249812363288532787)
              ·
                refine ⟨118480821374718544932799181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78987214249812363288532787 118480821374718544932799181)
                ·
                  refine ⟨44430308015519454349799693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118480821374718544932799181 44430308015519454349799693)
                  ·
                    refine ⟨16661365505819795381174885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44430308015519454349799693 16661365505819795381174885)
                    ·
                      refine ⟨3124006032341211633970291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16661365505819795381174885 3124006032341211633970291)
                      ·
                        rfl

theorem cell23_6083980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_6083980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083980 prefixEnd_6083980 := by exact prefixLift 6083980
  have htrace : WordTrace (prefixWord ++ tailWord_6083980) baseStart_6083980 baseEnd_6083980 := by
    simpa [prefixWord, tailWord_6083980, baseEnd_6083980] using wordTrace_append hprefix tailTrace_6083980
  have hstable : (prefixWord ++ tailWord_6083980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083980).length < 2 ^ (prefixWord ++ tailWord_6083980).sum := by decide
  have hdescent : baseEnd_6083980 < baseStart_6083980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083997 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_6083997 : Nat := 118140960795 + 6083997 * 2 ^ 59
def prefixEnd_6083997 : Nat := 4983230072969 + 3 ^ 40 * 6083997 * 2
def baseEnd_6083997 : Nat := 3124014761512338067457713

theorem tailTrace_6083997 : CollatzResearch.WordTrace tailWord_6083997 prefixEnd_6083997 3124014761512338067457713 := by
  unfold tailWord_6083997
  simp only [CollatzResearch.WordTrace]
  refine ⟨221901600539725407808602245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147934400359816938539068163 221901600539725407808602245)
  ·
    refine ⟨41606550101198513964112921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221901600539725407808602245 41606550101198513964112921)
    ·
      refine ⟨31204912575898885473084691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41606550101198513964112921 31204912575898885473084691)
      ·
        refine ⟨46807368863848328209627037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31204912575898885473084691 46807368863848328209627037)
        ·
          refine ⟨17552763323943123078610139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46807368863848328209627037 17552763323943123078610139)
          ·
            refine ⟨26329144985914684617915209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17552763323943123078610139 26329144985914684617915209)
            ·
              refine ⟨19746858739436013463436407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26329144985914684617915209 19746858739436013463436407)
              ·
                refine ⟨29620288109154020195154611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19746858739436013463436407 29620288109154020195154611)
                ·
                  refine ⟨44430432163731030292731917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29620288109154020195154611 44430432163731030292731917)
                  ·
                    refine ⟨16661412061399136359774469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44430432163731030292731917 16661412061399136359774469)
                    ·
                      refine ⟨3124014761512338067457713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16661412061399136359774469 3124014761512338067457713)
                      ·
                        rfl

theorem cell23_6083997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_6083997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083997 prefixEnd_6083997 := by exact prefixLift 6083997
  have htrace : WordTrace (prefixWord ++ tailWord_6083997) baseStart_6083997 baseEnd_6083997 := by
    simpa [prefixWord, tailWord_6083997, baseEnd_6083997] using wordTrace_append hprefix tailTrace_6083997
  have hstable : (prefixWord ++ tailWord_6083997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083997).length < 2 ^ (prefixWord ++ tailWord_6083997).sum := by decide
  have hdescent : baseEnd_6083997 < baseStart_6083997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6083998 : List Nat := [4, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_6083998 : Nat := 118140960795 + 6083998 * 2 ^ 59
def prefixEnd_6083998 : Nat := 4983230072969 + 3 ^ 40 * 6083998 * 2
def baseEnd_6083998 : Nat := 347112808332554729282801

theorem tailTrace_6083998 : CollatzResearch.WordTrace tailWord_6083998 prefixEnd_6083998 347112808332554729282801 := by
  unfold tailWord_6083998
  simp only [CollatzResearch.WordTrace]
  refine ⟨27737704626590223122423581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147934424675147856652925765 27737704626590223122423581)
  ·
    refine ⟨10401639234971333670908843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27737704626590223122423581 10401639234971333670908843)
    ·
      refine ⟨15602458852457000506363265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10401639234971333670908843 15602458852457000506363265)
      ·
        refine ⟨11701844139342750379772449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15602458852457000506363265 11701844139342750379772449)
        ·
          refine ⟨8776383104507062784829337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11701844139342750379772449 8776383104507062784829337)
          ·
            refine ⟨6582287328380297088622003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8776383104507062784829337 6582287328380297088622003)
            ·
              refine ⟨9873430992570445632933005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582287328380297088622003 9873430992570445632933005)
              ·
                refine ⟨3702536622213917112349877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9873430992570445632933005 3702536622213917112349877)
                ·
                  refine ⟨347112808332554729282801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3702536622213917112349877 347112808332554729282801)
                  ·
                    rfl

theorem cell23_6083998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_6083998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6083998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6083998 prefixEnd_6083998 := by exact prefixLift 6083998
  have htrace : WordTrace (prefixWord ++ tailWord_6083998) baseStart_6083998 baseEnd_6083998 := by
    simpa [prefixWord, tailWord_6083998, baseEnd_6083998] using wordTrace_append hprefix tailTrace_6083998
  have hstable : (prefixWord ++ tailWord_6083998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6083998).length < 2 ^ (prefixWord ++ tailWord_6083998).sum := by decide
  have hdescent : baseEnd_6083998 < baseStart_6083998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6083998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084024 : List Nat := [2, 1, 2, 1, 2, 2, 2, 6, 1, 4]
def baseStart_6084024 : Nat := 118140960795 + 6084024 * 2 ^ 59
def prefixEnd_6084024 : Nat := 4983230072969 + 3 ^ 40 * 6084024 * 2
def baseEnd_6084024 : Nat := 1041342875163336487273363

theorem tailTrace_6084024 : CollatzResearch.WordTrace tailWord_6084024 prefixEnd_6084024 1041342875163336487273363 := by
  unfold tailWord_6084024
  simp only [CollatzResearch.WordTrace]
  refine ⟨110951292655313795709917563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147935056873751727613223417 110951292655313795709917563)
  ·
    refine ⟨166426938982970693564876345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110951292655313795709917563 166426938982970693564876345)
    ·
      refine ⟨124820204237228020173657259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166426938982970693564876345 124820204237228020173657259)
      ·
        refine ⟨187230306355842030260485889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124820204237228020173657259 187230306355842030260485889)
        ·
          refine ⟨140422729766881522695364417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187230306355842030260485889 140422729766881522695364417)
          ·
            refine ⟨105317047325161142021523313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140422729766881522695364417 105317047325161142021523313)
            ·
              refine ⟨78987785493870856516142485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105317047325161142021523313 78987785493870856516142485)
              ·
                refine ⟨3702552445025196399194179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78987785493870856516142485 3702552445025196399194179)
                ·
                  refine ⟨5553828667537794598791269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702552445025196399194179 5553828667537794598791269)
                  ·
                    refine ⟨1041342875163336487273363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5553828667537794598791269 1041342875163336487273363)
                    ·
                      rfl

theorem cell23_6084024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_6084024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084024 prefixEnd_6084024 := by exact prefixLift 6084024
  have htrace : WordTrace (prefixWord ++ tailWord_6084024) baseStart_6084024 baseEnd_6084024 := by
    simpa [prefixWord, tailWord_6084024, baseEnd_6084024] using wordTrace_append hprefix tailTrace_6084024
  have hstable : (prefixWord ++ tailWord_6084024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084024).length < 2 ^ (prefixWord ++ tailWord_6084024).sum := by decide
  have hdescent : baseEnd_6084024 < baseStart_6084024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084098 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6084098 : Nat := 118140960795 + 6084098 * 2 ^ 59
def prefixEnd_6084098 : Nat := 4983230072969 + 3 ^ 40 * 6084098 * 2
def baseEnd_6084098 : Nat := 3124066623058442172294749

theorem tailTrace_6084098 : CollatzResearch.WordTrace tailWord_6084098 prefixEnd_6084098 3124066623058442172294749 := by
  unfold tailWord_6084098
  simp only [CollatzResearch.WordTrace]
  refine ⟨55476321078089875514507237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147936856208239668038685965 55476321078089875514507237)
  ·
    refine ⟨10401810202141851658970107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55476321078089875514507237 10401810202141851658970107)
    ·
      refine ⟨15602715303212777488455161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10401810202141851658970107 15602715303212777488455161)
      ·
        refine ⟨11702036477409583116341371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15602715303212777488455161 11702036477409583116341371)
        ·
          refine ⟨17553054716114374674512057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11702036477409583116341371 17553054716114374674512057)
          ·
            refine ⟨13164791037085781005884043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17553054716114374674512057 13164791037085781005884043)
            ·
              refine ⟨19747186555628671508826065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13164791037085781005884043 19747186555628671508826065)
              ·
                refine ⟨14810389916721503631619549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19747186555628671508826065 14810389916721503631619549)
                ·
                  refine ⟨5553896218770563861857331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14810389916721503631619549 5553896218770563861857331)
                  ·
                    refine ⟨8330844328155845792785997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5553896218770563861857331 8330844328155845792785997)
                    ·
                      refine ⟨3124066623058442172294749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8330844328155845792785997 3124066623058442172294749)
                      ·
                        rfl

theorem cell23_6084098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6084098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084098 prefixEnd_6084098 := by exact prefixLift 6084098
  have htrace : WordTrace (prefixWord ++ tailWord_6084098) baseStart_6084098 baseEnd_6084098 := by
    simpa [prefixWord, tailWord_6084098, baseEnd_6084098] using wordTrace_append hprefix tailTrace_6084098
  have hstable : (prefixWord ++ tailWord_6084098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084098).length < 2 ^ (prefixWord ++ tailWord_6084098).sum := by decide
  have hdescent : baseEnd_6084098 < baseStart_6084098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084102 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_6084102 : Nat := 118140960795 + 6084102 * 2 ^ 59
def prefixEnd_6084102 : Nat := 4983230072969 + 3 ^ 40 * 6084102 * 2
def baseEnd_6084102 : Nat := 3124068676981060156644731

theorem tailTrace_6084102 : CollatzResearch.WordTrace tailWord_6084102 prefixEnd_6084102 3124068676981060156644731 := by
  unfold tailWord_6084102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6934544693885781585661705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147936953469563340494116373 6934544693885781585661705)
  ·
    refine ⟨5200908520414336189246279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6934544693885781585661705 5200908520414336189246279)
    ·
      refine ⟨7801362780621504283869419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5200908520414336189246279 7801362780621504283869419)
      ·
        refine ⟨11702044170932256425804129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7801362780621504283869419 11702044170932256425804129)
        ·
          refine ⟨8776533128199192319353097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11702044170932256425804129 8776533128199192319353097)
          ·
            refine ⟨6582399846149394239514823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8776533128199192319353097 6582399846149394239514823)
            ·
              refine ⟨9873599769224091359272235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582399846149394239514823 9873599769224091359272235)
              ·
                refine ⟨14810399653836137038908353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9873599769224091359272235 14810399653836137038908353)
                ·
                  refine ⟨11107799740377102779181265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14810399653836137038908353 11107799740377102779181265)
                  ·
                    refine ⟨8330849805282827084385949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11107799740377102779181265 8330849805282827084385949)
                    ·
                      refine ⟨3124068676981060156644731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8330849805282827084385949 3124068676981060156644731)
                      ·
                        rfl

theorem cell23_6084102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_6084102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084102 prefixEnd_6084102 := by exact prefixLift 6084102
  have htrace : WordTrace (prefixWord ++ tailWord_6084102) baseStart_6084102 baseEnd_6084102 := by
    simpa [prefixWord, tailWord_6084102, baseEnd_6084102] using wordTrace_append hprefix tailTrace_6084102
  have hstable : (prefixWord ++ tailWord_6084102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084102).length < 2 ^ (prefixWord ++ tailWord_6084102).sum := by decide
  have hdescent : baseEnd_6084102 < baseStart_6084102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084108 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 2, 3, 2]
def baseStart_6084108 : Nat := 118140960795 + 6084108 * 2 ^ 59
def prefixEnd_6084108 : Nat := 4983230072969 + 3 ^ 40 * 6084108 * 2
def baseEnd_6084108 : Nat := 3124071757864987133169703

theorem tailTrace_6084108 : CollatzResearch.WordTrace tailWord_6084108 prefixEnd_6084108 3124071757864987133169703 := by
  unfold tailWord_6084108
  simp only [CollatzResearch.WordTrace]
  refine ⟨110952824521161636882946489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147937099361548849177261985 110952824521161636882946489)
  ·
    refine ⟨83214618390871227662209867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110952824521161636882946489 83214618390871227662209867)
    ·
      refine ⟨124821927586306841493314801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83214618390871227662209867 124821927586306841493314801)
      ·
        refine ⟨93616445689730131119986101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124821927586306841493314801 93616445689730131119986101)
        ·
          refine ⟨8776541783412199792498697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93616445689730131119986101 8776541783412199792498697)
          ·
            refine ⟨6582406337559149844374023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8776541783412199792498697 6582406337559149844374023)
            ·
              refine ⟨9873609506338724766561035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582406337559149844374023 9873609506338724766561035)
              ·
                refine ⟨14810414259508087149841553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9873609506338724766561035 14810414259508087149841553)
                ·
                  refine ⟨11107810694631065362381165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14810414259508087149841553 11107810694631065362381165)
                  ·
                    refine ⟨4165429010486649510892937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11107810694631065362381165 4165429010486649510892937)
                    ·
                      refine ⟨3124071757864987133169703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165429010486649510892937 3124071757864987133169703)
                      ·
                        rfl

theorem cell23_6084108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_6084108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084108 prefixEnd_6084108 := by exact prefixLift 6084108
  have htrace : WordTrace (prefixWord ++ tailWord_6084108) baseStart_6084108 baseEnd_6084108 := by
    simpa [prefixWord, tailWord_6084108, baseEnd_6084108] using wordTrace_append hprefix tailTrace_6084108
  have hstable : (prefixWord ++ tailWord_6084108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084108).length < 2 ^ (prefixWord ++ tailWord_6084108).sum := by decide
  have hdescent : baseEnd_6084108 < baseStart_6084108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084138 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_6084138 : Nat := 118140960795 + 6084138 * 2 ^ 59
def prefixEnd_6084138 : Nat := 4983230072969 + 3 ^ 40 * 6084138 * 2
def baseEnd_6084138 : Nat := 3124087162284622015794565

theorem tailTrace_6084138 : CollatzResearch.WordTrace tailWord_6084138 prefixEnd_6084138 3124087162284622015794565 := by
  unfold tailWord_6084138
  simp only [CollatzResearch.WordTrace]
  refine ⟨55476685808053647222371267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147937828821476392592990045 55476685808053647222371267)
  ·
    refine ⟨83215028712080470833556901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55476685808053647222371267 83215028712080470833556901)
    ·
      refine ⟨15602817883515088281291919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83215028712080470833556901 15602817883515088281291919)
      ·
        refine ⟨23404226825272632421937879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15602817883515088281291919 23404226825272632421937879)
        ·
          refine ⟨35106340237908948632906819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23404226825272632421937879 35106340237908948632906819)
          ·
            refine ⟨52659510356863422949360229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35106340237908948632906819 52659510356863422949360229)
            ·
              refine ⟨9873658191911891803005043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52659510356863422949360229 9873658191911891803005043)
              ·
                refine ⟨14810487287867837704507565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9873658191911891803005043 14810487287867837704507565)
                ·
                  refine ⟨5553932732950439139190337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14810487287867837704507565 5553932732950439139190337)
                  ·
                    refine ⟨4165449549712829354392753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5553932732950439139190337 4165449549712829354392753)
                    ·
                      refine ⟨3124087162284622015794565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165449549712829354392753 3124087162284622015794565)
                      ·
                        rfl

theorem cell23_6084138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_6084138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084138 prefixEnd_6084138 := by exact prefixLift 6084138
  have htrace : WordTrace (prefixWord ++ tailWord_6084138) baseStart_6084138 baseEnd_6084138 := by
    simpa [prefixWord, tailWord_6084138, baseEnd_6084138] using wordTrace_append hprefix tailTrace_6084138
  have hstable : (prefixWord ++ tailWord_6084138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084138).length < 2 ^ (prefixWord ++ tailWord_6084138).sum := by decide
  have hdescent : baseEnd_6084138 < baseStart_6084138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084189 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6084189 : Nat := 118140960795 + 6084189 * 2 ^ 59
def prefixEnd_6084189 : Nat := 4983230072969 + 3 ^ 40 * 6084189 * 2
def baseEnd_6084189 : Nat := 3124113349798001316256831

theorem tailTrace_6084189 : CollatzResearch.WordTrace tailWord_6084189 prefixEnd_6084189 3124113349798001316256831 := by
  unfold tailWord_6084189
  simp only [CollatzResearch.WordTrace]
  refine ⟨221908603355029824599591621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147939068903353216399727747 221908603355029824599591621)
  ·
    refine ⟨41607863129068092112423429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221908603355029824599591621 41607863129068092112423429)
    ·
      refine ⟨7801474336700267271079393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41607863129068092112423429 7801474336700267271079393)
      ·
        refine ⟨5851105752525200453309545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7801474336700267271079393 5851105752525200453309545)
        ·
          refine ⟨4388329314393900339982159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5851105752525200453309545 4388329314393900339982159)
          ·
            refine ⟨6582493971590850509973239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388329314393900339982159 6582493971590850509973239)
            ·
              refine ⟨9873740957386275764959859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582493971590850509973239 9873740957386275764959859)
              ·
                refine ⟨14810611436079413647439789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9873740957386275764959859 14810611436079413647439789)
                ·
                  refine ⟨5553979288529780117789921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14810611436079413647439789 5553979288529780117789921)
                  ·
                    refine ⟨4165484466397335088342441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5553979288529780117789921 4165484466397335088342441)
                    ·
                      refine ⟨3124113349798001316256831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165484466397335088342441 3124113349798001316256831)
                      ·
                        rfl

theorem cell23_6084189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6084189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084189 prefixEnd_6084189 := by exact prefixLift 6084189
  have htrace : WordTrace (prefixWord ++ tailWord_6084189) baseStart_6084189 baseEnd_6084189 := by
    simpa [prefixWord, tailWord_6084189, baseEnd_6084189] using wordTrace_append hprefix tailTrace_6084189
  have hstable : (prefixWord ++ tailWord_6084189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084189).length < 2 ^ (prefixWord ++ tailWord_6084189).sum := by decide
  have hdescent : baseEnd_6084189 < baseStart_6084189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084207 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_6084207 : Nat := 118140960795 + 6084207 * 2 ^ 59
def prefixEnd_6084207 : Nat := 4983230072969 + 3 ^ 40 * 6084207 * 2
def baseEnd_6084207 : Nat := 3124122592449782245831747

theorem tailTrace_6084207 : CollatzResearch.WordTrace tailWord_6084207 prefixEnd_6084207 3124122592449782245831747 := by
  unfold tailWord_6084207
  simp only [CollatzResearch.WordTrace]
  refine ⟨221909259868964613673746875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147939506579309742449164583 221909259868964613673746875)
  ·
    refine ⟨332863889803446920510620313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221909259868964613673746875 332863889803446920510620313)
    ·
      refine ⟨249647917352585190382965235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332863889803446920510620313 249647917352585190382965235)
      ·
        refine ⟨374471876028877785574447853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249647917352585190382965235 374471876028877785574447853)
        ·
          refine ⟨140426953510829169590417945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374471876028877785574447853 140426953510829169590417945)
          ·
            refine ⟨105320215133121877192813459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140426953510829169590417945 105320215133121877192813459)
            ·
              refine ⟨157980322699682815789220189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105320215133121877192813459 157980322699682815789220189)
              ·
                refine ⟨59242621012381055920957571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157980322699682815789220189 59242621012381055920957571)
                ·
                  refine ⟨88863931518571583881436357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59242621012381055920957571 88863931518571583881436357)
                  ·
                    refine ⟨16661987159732171977769317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88863931518571583881436357 16661987159732171977769317)
                    ·
                      refine ⟨3124122592449782245831747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16661987159732171977769317 3124122592449782245831747)
                      ·
                        rfl

theorem cell23_6084207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_6084207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084207 prefixEnd_6084207 := by exact prefixLift 6084207
  have htrace : WordTrace (prefixWord ++ tailWord_6084207) baseStart_6084207 baseEnd_6084207 := by
    simpa [prefixWord, tailWord_6084207, baseEnd_6084207] using wordTrace_append hprefix tailTrace_6084207
  have hstable : (prefixWord ++ tailWord_6084207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084207).length < 2 ^ (prefixWord ++ tailWord_6084207).sum := by decide
  have hdescent : baseEnd_6084207 < baseStart_6084207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084217 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 9]
def baseStart_6084217 : Nat := 118140960795 + 6084217 * 2 ^ 59
def prefixEnd_6084217 : Nat := 4983230072969 + 3 ^ 40 * 6084217 * 2
def baseEnd_6084217 : Nat := 347125303028480800745189

theorem tailTrace_6084217 : CollatzResearch.WordTrace tailWord_6084217 prefixEnd_6084217 347125303028480800745189 := by
  unfold tailWord_6084217
  simp only [CollatzResearch.WordTrace]
  refine ⟨221909624598928385381610905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147939749732618923587740603 221909624598928385381610905)
  ·
    refine ⟨166432218449196289036208179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221909624598928385381610905 166432218449196289036208179)
    ·
      refine ⟨249648327673794433554312269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166432218449196289036208179 249648327673794433554312269)
      ·
        refine ⟨93618122877672912582867101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249648327673794433554312269 93618122877672912582867101)
        ·
          refine ⟨35106796079127342218575163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93618122877672912582867101 35106796079127342218575163)
          ·
            refine ⟨52660194118691013327862745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35106796079127342218575163 52660194118691013327862745)
            ·
              refine ⟨39495145589018259995897059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52660194118691013327862745 39495145589018259995897059)
              ·
                refine ⟨59242718383527389993845589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39495145589018259995897059 59242718383527389993845589)
                ·
                  refine ⟨347125303028480800745189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59242718383527389993845589 347125303028480800745189)
                  ·
                    rfl

theorem cell23_6084217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 9].length) (baseStart_6084217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084217 prefixEnd_6084217 := by exact prefixLift 6084217
  have htrace : WordTrace (prefixWord ++ tailWord_6084217) baseStart_6084217 baseEnd_6084217 := by
    simpa [prefixWord, tailWord_6084217, baseEnd_6084217] using wordTrace_append hprefix tailTrace_6084217
  have hstable : (prefixWord ++ tailWord_6084217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084217).length < 2 ^ (prefixWord ++ tailWord_6084217).sum := by decide
  have hdescent : baseEnd_6084217 < baseStart_6084217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084228 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_6084228 : Nat := 118140960795 + 6084228 * 2 ^ 59
def prefixEnd_6084228 : Nat := 4983230072969 + 3 ^ 40 * 6084228 * 2
def baseEnd_6084228 : Nat := 3124133375543526663669151

theorem tailTrace_6084228 : CollatzResearch.WordTrace tailWord_6084228 prefixEnd_6084228 3124133375543526663669151 := by
  unfold tailWord_6084228
  simp only [CollatzResearch.WordTrace]
  refine ⟨110955012900944267130130669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147940017201259022840174225 110955012900944267130130669)
  ·
    refine ⟨41608129837854100173799001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110955012900944267130130669 41608129837854100173799001)
    ·
      refine ⟨31206097378390575130349251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41608129837854100173799001 31206097378390575130349251)
      ·
        refine ⟨46809146067585862695523877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31206097378390575130349251 46809146067585862695523877)
        ·
          refine ⟨8776714887672349255410727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46809146067585862695523877 8776714887672349255410727)
          ·
            refine ⟨13165072331508523883116091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8776714887672349255410727 13165072331508523883116091)
            ·
              refine ⟨19747608497262785824674137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13165072331508523883116091 19747608497262785824674137)
              ·
                refine ⟨14810706372947089368505603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19747608497262785824674137 14810706372947089368505603)
                ·
                  refine ⟨22216059559420634052758405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14810706372947089368505603 22216059559420634052758405)
                  ·
                    refine ⟨4165511167391368884892201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22216059559420634052758405 4165511167391368884892201)
                    ·
                      refine ⟨3124133375543526663669151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165511167391368884892201 3124133375543526663669151)
                      ·
                        rfl

theorem cell23_6084228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_6084228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084228 prefixEnd_6084228 := by exact prefixLift 6084228
  have htrace : WordTrace (prefixWord ++ tailWord_6084228) baseStart_6084228 baseEnd_6084228 := by
    simpa [prefixWord, tailWord_6084228, baseEnd_6084228] using wordTrace_append hprefix tailTrace_6084228
  have hstable : (prefixWord ++ tailWord_6084228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084228).length < 2 ^ (prefixWord ++ tailWord_6084228).sum := by decide
  have hdescent : baseEnd_6084228 < baseStart_6084228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084232 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6084232 : Nat := 118140960795 + 6084232 * 2 ^ 59
def prefixEnd_6084232 : Nat := 4983230072969 + 3 ^ 40 * 6084232 * 2
def baseEnd_6084232 : Nat := 3124135429466144648019133

theorem tailTrace_6084232 : CollatzResearch.WordTrace tailWord_6084232 prefixEnd_6084232 3124135429466144648019133 := by
  unfold tailWord_6084232
  simp only [CollatzResearch.WordTrace]
  refine ⟨110955085846937021471703475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147940114462582695295604633 110955085846937021471703475)
  ·
    refine ⟨166432628770405532207555213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110955085846937021471703475 166432628770405532207555213)
    ·
      refine ⟨62412235788902074577833205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166432628770405532207555213 62412235788902074577833205)
      ·
        refine ⟨5851147105209569491671863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62412235788902074577833205 5851147105209569491671863)
        ·
          refine ⟨8776720657814354237507795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851147105209569491671863 8776720657814354237507795)
          ·
            refine ⟨13165080986721531356261693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8776720657814354237507795 13165080986721531356261693)
            ·
              refine ⟨4936905370020574258598135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13165080986721531356261693 4936905370020574258598135)
              ·
                refine ⟨7405358055030861387897203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936905370020574258598135 7405358055030861387897203)
                ·
                  refine ⟨11108037082546292081845805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405358055030861387897203 11108037082546292081845805)
                  ·
                    refine ⟨4165513905954859530692177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11108037082546292081845805 4165513905954859530692177)
                    ·
                      refine ⟨3124135429466144648019133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165513905954859530692177 3124135429466144648019133)
                      ·
                        rfl

theorem cell23_6084232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6084232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084232 prefixEnd_6084232 := by exact prefixLift 6084232
  have htrace : WordTrace (prefixWord ++ tailWord_6084232) baseStart_6084232 baseEnd_6084232 := by
    simpa [prefixWord, tailWord_6084232, baseEnd_6084232] using wordTrace_append hprefix tailTrace_6084232
  have hstable : (prefixWord ++ tailWord_6084232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084232).length < 2 ^ (prefixWord ++ tailWord_6084232).sum := by decide
  have hdescent : baseEnd_6084232 < baseStart_6084232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084258 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_6084258 : Nat := 118140960795 + 6084258 * 2 ^ 59
def prefixEnd_6084258 : Nat := 4983230072969 + 3 ^ 40 * 6084258 * 2
def baseEnd_6084258 : Nat := 3124148779963161546294013

theorem tailTrace_6084258 : CollatzResearch.WordTrace tailWord_6084258 prefixEnd_6084258 3124148779963161546294013 := by
  unfold tailWord_6084258
  simp only [CollatzResearch.WordTrace]
  refine ⟨55477779997944962345963357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147940746661186566255902285 55477779997944962345963357)
  ·
    refine ⟨20804167499229360879736259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55477779997944962345963357 20804167499229360879736259)
    ·
      refine ⟨31206251248844041319604389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20804167499229360879736259 31206251248844041319604389)
      ·
        refine ⟨5851172109158257747425823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31206251248844041319604389 5851172109158257747425823)
        ·
          refine ⟨8776758163737386621138735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851172109158257747425823 8776758163737386621138735)
          ·
            refine ⟨13165137245606079931708103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8776758163737386621138735 13165137245606079931708103)
            ·
              refine ⟨19747705868409119897562155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13165137245606079931708103 19747705868409119897562155)
              ·
                refine ⟨29621558802613679846343233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19747705868409119897562155 29621558802613679846343233)
                ·
                  refine ⟨22216169101960259884757425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29621558802613679846343233 22216169101960259884757425)
                  ·
                    refine ⟨16662126826470194913568069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22216169101960259884757425 16662126826470194913568069)
                    ·
                      refine ⟨3124148779963161546294013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16662126826470194913568069 3124148779963161546294013)
                      ·
                        rfl

theorem cell23_6084258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_6084258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084258 prefixEnd_6084258 := by exact prefixLift 6084258
  have htrace : WordTrace (prefixWord ++ tailWord_6084258) baseStart_6084258 baseEnd_6084258 := by
    simpa [prefixWord, tailWord_6084258, baseEnd_6084258] using wordTrace_append hprefix tailTrace_6084258
  have hstable : (prefixWord ++ tailWord_6084258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084258).length < 2 ^ (prefixWord ++ tailWord_6084258).sum := by decide
  have hdescent : baseEnd_6084258 < baseStart_6084258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084311 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 3, 4]
def baseStart_6084311 : Nat := 118140960795 + 6084311 * 2 ^ 59
def prefixEnd_6084311 : Nat := 4983230072969 + 3 ^ 40 * 6084311 * 2
def baseEnd_6084311 : Nat := 1041391998145949946310423

theorem tailTrace_6084311 : CollatzResearch.WordTrace tailWord_6084311 prefixEnd_6084311 1041391998145949946310423 := by
  unfold tailWord_6084311
  simp only [CollatzResearch.WordTrace]
  refine ⟨221913053060587839435532787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147942035373725226290355191 221913053060587839435532787)
  ·
    refine ⟨332869579590881759153299181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221913053060587839435532787 332869579590881759153299181)
    ·
      refine ⟨124826092346580659682487193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332869579590881759153299181 124826092346580659682487193)
      ·
        refine ⟨93619569259935494761865395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124826092346580659682487193 93619569259935494761865395)
        ·
          refine ⟨140429353889903242142798093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93619569259935494761865395 140429353889903242142798093)
          ·
            refine ⟨52661007708713715803549285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140429353889903242142798093 52661007708713715803549285)
            ·
              refine ⟨9873938945383821713165491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52661007708713715803549285 9873938945383821713165491)
              ·
                refine ⟨14810908418075732569748237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9873938945383821713165491 14810908418075732569748237)
                ·
                  refine ⟨5554090656778399713655589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14810908418075732569748237 5554090656778399713655589)
                  ·
                    refine ⟨1041391998145949946310423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554090656778399713655589 1041391998145949946310423)
                    ·
                      rfl

theorem cell23_6084311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_6084311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084311 prefixEnd_6084311 := by exact prefixLift 6084311
  have htrace : WordTrace (prefixWord ++ tailWord_6084311) baseStart_6084311 baseEnd_6084311 := by
    simpa [prefixWord, tailWord_6084311, baseEnd_6084311] using wordTrace_append hprefix tailTrace_6084311
  have hstable : (prefixWord ++ tailWord_6084311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084311).length < 2 ^ (prefixWord ++ tailWord_6084311).sum := by decide
  have hdescent : baseEnd_6084311 < baseStart_6084311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084351 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 5, 1, 3]
def baseStart_6084351 : Nat := 118140960795 + 6084351 * 2 ^ 59
def prefixEnd_6084351 : Nat := 4983230072969 + 3 ^ 40 * 6084351 * 2
def baseEnd_6084351 : Nat := 3124196533664029682431085

theorem tailTrace_6084351 : CollatzResearch.WordTrace tailWord_6084351 prefixEnd_6084351 3124196533664029682431085 := by
  unfold tailWord_6084351
  simp only [CollatzResearch.WordTrace]
  refine ⟨221914511980442926266988907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147943007986961950844659271 221914511980442926266988907)
  ·
    refine ⟨332871767970664389400483361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221914511980442926266988907 332871767970664389400483361)
    ·
      refine ⟨249653825977998292050362521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332871767970664389400483361 249653825977998292050362521)
      ·
        refine ⟨187240369483498719037771891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249653825977998292050362521 187240369483498719037771891)
        ·
          refine ⟨280860554225248078556657837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187240369483498719037771891 280860554225248078556657837)
          ·
            refine ⟨105322707834468029458746689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280860554225248078556657837 105322707834468029458746689)
            ·
              refine ⟨78992030875851022094060017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105322707834468029458746689 78992030875851022094060017)
              ·
                refine ⟨59244023156888266570545013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78992030875851022094060017 59244023156888266570545013)
                ·
                  refine ⟨5554127170958274990988595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59244023156888266570545013 5554127170958274990988595)
                  ·
                    refine ⟨8331190756437412486482893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5554127170958274990988595 8331190756437412486482893)
                    ·
                      refine ⟨3124196533664029682431085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8331190756437412486482893 3124196533664029682431085)
                      ·
                        rfl

theorem cell23_6084351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_6084351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084351 prefixEnd_6084351 := by exact prefixLift 6084351
  have htrace : WordTrace (prefixWord ++ tailWord_6084351) baseStart_6084351 baseEnd_6084351 := by
    simpa [prefixWord, tailWord_6084351, baseEnd_6084351] using wordTrace_append hprefix tailTrace_6084351
  have hstable : (prefixWord ++ tailWord_6084351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084351).length < 2 ^ (prefixWord ++ tailWord_6084351).sum := by decide
  have hdescent : baseEnd_6084351 < baseStart_6084351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084388 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_6084388 : Nat := 118140960795 + 6084388 * 2 ^ 59
def prefixEnd_6084388 : Nat := 4983230072969 + 3 ^ 40 * 6084388 * 2
def baseEnd_6084388 : Nat := 1041405177482748679222805

theorem tailTrace_6084388 : CollatzResearch.WordTrace tailWord_6084388 prefixEnd_6084388 1041405177482748679222805 := by
  unfold tailWord_6084388
  simp only [CollatzResearch.WordTrace]
  refine ⟨110957930740654440793042909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147943907654205921057390545 110957930740654440793042909)
  ·
    refine ⟨41609224027745415297391091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110957930740654440793042909 41609224027745415297391091)
    ·
      refine ⟨62413836041618122946086637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41609224027745415297391091 62413836041618122946086637)
      ·
        refine ⟨23405188515606796104782489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62413836041618122946086637 23405188515606796104782489)
        ·
          refine ⟨17553891386705097078586867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23405188515606796104782489 17553891386705097078586867)
          ·
            refine ⟨26330837080057645617880301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17553891386705097078586867 26330837080057645617880301)
            ·
              refine ⟨9874063905021617106705113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26330837080057645617880301 9874063905021617106705113)
              ·
                refine ⟨7405547928766212830028835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9874063905021617106705113 7405547928766212830028835)
                ·
                  refine ⟨11108321893149319245043253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405547928766212830028835 11108321893149319245043253)
                  ·
                    refine ⟨1041405177482748679222805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11108321893149319245043253 1041405177482748679222805)
                    ·
                      rfl

theorem cell23_6084388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_6084388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084388 prefixEnd_6084388 := by exact prefixLift 6084388
  have htrace : WordTrace (prefixWord ++ tailWord_6084388) baseStart_6084388 baseEnd_6084388 := by
    simpa [prefixWord, tailWord_6084388, baseEnd_6084388] using wordTrace_append hprefix tailTrace_6084388
  have hstable : (prefixWord ++ tailWord_6084388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084388).length < 2 ^ (prefixWord ++ tailWord_6084388).sum := by decide
  have hdescent : baseEnd_6084388 < baseStart_6084388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084401 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 1, 6]
def baseStart_6084401 : Nat := 118140960795 + 6084401 * 2 ^ 59
def prefixEnd_6084401 : Nat := 4983230072969 + 3 ^ 40 * 6084401 * 2
def baseEnd_6084401 : Nat := 1041407402565584828935285

theorem tailTrace_6084401 : CollatzResearch.WordTrace tailWord_6084401 prefixEnd_6084401 1041407402565584828935285 := by
  unfold tailWord_6084401
  simp only [CollatzResearch.WordTrace]
  refine ⟨221916335630261784806309057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147944223753507856537539371 221916335630261784806309057)
  ·
    refine ⟨166437251722696338604731793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221916335630261784806309057 166437251722696338604731793)
    ·
      refine ⟨124827938792022253953548845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166437251722696338604731793 124827938792022253953548845)
      ·
        refine ⟨46810477047008345232580817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124827938792022253953548845 46810477047008345232580817)
        ·
          refine ⟨35107857785256258924435613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46810477047008345232580817 35107857785256258924435613)
          ·
            refine ⟨13165446669471097096663355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35107857785256258924435613 13165446669471097096663355)
            ·
              refine ⟨19748170004206645644995033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13165446669471097096663355 19748170004206645644995033)
              ·
                refine ⟨14811127503154984233746275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19748170004206645644995033 14811127503154984233746275)
                ·
                  refine ⟨22216691254732476350619413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14811127503154984233746275 22216691254732476350619413)
                  ·
                    refine ⟨1041407402565584828935285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22216691254732476350619413 1041407402565584828935285)
                    ·
                      rfl

theorem cell23_6084401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_6084401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084401 prefixEnd_6084401 := by exact prefixLift 6084401
  have htrace : WordTrace (prefixWord ++ tailWord_6084401) baseStart_6084401 baseEnd_6084401 := by
    simpa [prefixWord, tailWord_6084401, baseEnd_6084401] using wordTrace_append hprefix tailTrace_6084401
  have hstable : (prefixWord ++ tailWord_6084401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084401).length < 2 ^ (prefixWord ++ tailWord_6084401).sum := by decide
  have hdescent : baseEnd_6084401 < baseStart_6084401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084405 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 1, 5]
def baseStart_6084405 : Nat := 118140960795 + 6084405 * 2 ^ 59
def prefixEnd_6084405 : Nat := 4983230072969 + 3 ^ 40 * 6084405 * 2
def baseEnd_6084405 : Nat := 1041408087206457490385279

theorem tailTrace_6084405 : CollatzResearch.WordTrace tailWord_6084405 prefixEnd_6084405 1041408087206457490385279 := by
  unfold tailWord_6084405
  simp only [CollatzResearch.WordTrace]
  refine ⟨221916481522247293489454669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147944321014831528992969779 221916481522247293489454669)
  ·
    refine ⟨83218680570842735058545501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221916481522247293489454669 83218680570842735058545501)
    ·
      refine ⟨31207005214066025646954563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83218680570842735058545501 31207005214066025646954563)
      ·
        refine ⟨46810507821099038470431845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31207005214066025646954563 46810507821099038470431845)
        ·
          refine ⟨8776970216456069713205971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46810507821099038470431845 8776970216456069713205971)
          ·
            refine ⟨13165455324684104569808957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8776970216456069713205971 13165455324684104569808957)
            ·
              refine ⟨4937045746756539213678359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13165455324684104569808957 4937045746756539213678359)
              ·
                refine ⟨7405568620134808820517539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937045746756539213678359 7405568620134808820517539)
                ·
                  refine ⟨11108352930202213230776309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405568620134808820517539 11108352930202213230776309)
                  ·
                    refine ⟨1041408087206457490385279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11108352930202213230776309 1041408087206457490385279)
                    ·
                      rfl

theorem cell23_6084405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_6084405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084405 prefixEnd_6084405 := by exact prefixLift 6084405
  have htrace : WordTrace (prefixWord ++ tailWord_6084405) baseStart_6084405 baseEnd_6084405 := by
    simpa [prefixWord, tailWord_6084405, baseEnd_6084405] using wordTrace_append hprefix tailTrace_6084405
  have hstable : (prefixWord ++ tailWord_6084405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084405).length < 2 ^ (prefixWord ++ tailWord_6084405).sum := by decide
  have hdescent : baseEnd_6084405 < baseStart_6084405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084462 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_6084462 : Nat := 118140960795 + 6084462 * 2 ^ 59
def prefixEnd_6084462 : Nat := 4983230072969 + 3 ^ 40 * 6084462 * 2
def baseEnd_6084462 : Nat := 3124253530016678748143075

theorem tailTrace_6084462 : CollatzResearch.WordTrace tailWord_6084462 prefixEnd_6084462 3124253530016678748143075 := by
  unfold tailWord_6084462
  simp only [CollatzResearch.WordTrace]
  refine ⟨27739820060380099028034955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147945706988693861482853093 27739820060380099028034955)
  ·
    refine ⟨41609730090570148542052433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27739820060380099028034955 41609730090570148542052433)
    ·
      refine ⟨31207297567927611406539325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41609730090570148542052433 31207297567927611406539325)
      ·
        refine ⟨11702736587972854277452247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31207297567927611406539325 11702736587972854277452247)
        ·
          refine ⟨17554104881959281416178371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11702736587972854277452247 17554104881959281416178371)
          ·
            refine ⟨26331157322938922124267557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17554104881959281416178371 26331157322938922124267557)
            ·
              refine ⟨4937091998051047898300167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26331157322938922124267557 4937091998051047898300167)
              ·
                refine ⟨7405637997076571847450251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937091998051047898300167 7405637997076571847450251)
                ·
                  refine ⟨11108456995614857771175377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405637997076571847450251 11108456995614857771175377)
                  ·
                    refine ⟨8331342746711143328381533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11108456995614857771175377 8331342746711143328381533)
                    ·
                      refine ⟨3124253530016678748143075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8331342746711143328381533 3124253530016678748143075)
                      ·
                        rfl

theorem cell23_6084462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_6084462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084462 prefixEnd_6084462 := by exact prefixLift 6084462
  have htrace : WordTrace (prefixWord ++ tailWord_6084462) baseStart_6084462 baseEnd_6084462 := by
    simpa [prefixWord, tailWord_6084462, baseEnd_6084462] using wordTrace_append hprefix tailTrace_6084462
  have hstable : (prefixWord ++ tailWord_6084462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084462).length < 2 ^ (prefixWord ++ tailWord_6084462).sum := by decide
  have hdescent : baseEnd_6084462 < baseStart_6084462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084501 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_6084501 : Nat := 118140960795 + 6084501 * 2 ^ 59
def prefixEnd_6084501 : Nat := 4983230072969 + 3 ^ 40 * 6084501 * 2
def baseEnd_6084501 : Nat := 3124273555762204095555395

theorem tailTrace_6084501 : CollatzResearch.WordTrace tailWord_6084501 prefixEnd_6084501 3124273555762204095555395 := by
  unfold tailWord_6084501
  simp only [CollatzResearch.WordTrace]
  refine ⟨221919982929899501884949357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147946655286599667923299571 221919982929899501884949357)
  ·
    refine ⟨83219993598712313206856009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221919982929899501884949357 83219993598712313206856009)
    ·
      refine ⟨62414995199034234905142007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83219993598712313206856009 62414995199034234905142007)
      ·
        refine ⟨93622492798551352357713011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62414995199034234905142007 93622492798551352357713011)
        ·
          refine ⟨140433739197827028536569517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93622492798551352357713011 140433739197827028536569517)
          ·
            refine ⟨52662652199185135701213569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140433739197827028536569517 52662652199185135701213569)
            ·
              refine ⟨39496989149388851775910177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52662652199185135701213569 39496989149388851775910177)
              ·
                refine ⟨29622741862041638831932633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39496989149388851775910177 29622741862041638831932633)
                ·
                  refine ⟨22217056396531229123949475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29622741862041638831932633 22217056396531229123949475)
                  ·
                    refine ⟨33325584594796843685924213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22217056396531229123949475 33325584594796843685924213)
                    ·
                      refine ⟨3124273555762204095555395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33325584594796843685924213 3124273555762204095555395)
                      ·
                        rfl

theorem cell23_6084501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_6084501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084501 prefixEnd_6084501 := by exact prefixLift 6084501
  have htrace : WordTrace (prefixWord ++ tailWord_6084501) baseStart_6084501 baseEnd_6084501 := by
    simpa [prefixWord, tailWord_6084501, baseEnd_6084501] using wordTrace_append hprefix tailTrace_6084501
  have hstable : (prefixWord ++ tailWord_6084501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084501).length < 2 ^ (prefixWord ++ tailWord_6084501).sum := by decide
  have hdescent : baseEnd_6084501 < baseStart_6084501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084510 : List Nat := [4, 3, 1, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_6084510 : Nat := 118140960795 + 6084510 * 2 ^ 59
def prefixEnd_6084510 : Nat := 4983230072969 + 3 ^ 40 * 6084510 * 2
def baseEnd_6084510 : Nat := 3124278177088094560342855

theorem tailTrace_6084510 : CollatzResearch.WordTrace tailWord_6084510 prefixEnd_6084510 3124278177088094560342855 := by
  unfold tailWord_6084510
  simp only [CollatzResearch.WordTrace]
  refine ⟨27740038898358362052753373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147946874124577930948017989 27740038898358362052753373)
  ·
    refine ⟨10402514586884385769782515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27740038898358362052753373 10402514586884385769782515)
    ·
      refine ⟨15603771880326578654673773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10402514586884385769782515 15603771880326578654673773)
      ·
        refine ⟨5851414455122466995502665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15603771880326578654673773 5851414455122466995502665)
        ·
          refine ⟨4388560841341850246626999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5851414455122466995502665 4388560841341850246626999)
          ·
            refine ⟨6582841262012775369940499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388560841341850246626999 6582841262012775369940499)
            ·
              refine ⟨9874261893019163054910749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582841262012775369940499 9874261893019163054910749)
              ·
                refine ⟨3702848209882186145591531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9874261893019163054910749 3702848209882186145591531)
                ·
                  refine ⟨5554272314823279218387297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702848209882186145591531 5554272314823279218387297)
                  ·
                    refine ⟨4165704236117459413790473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5554272314823279218387297 4165704236117459413790473)
                    ·
                      refine ⟨3124278177088094560342855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165704236117459413790473 3124278177088094560342855)
                      ·
                        rfl

theorem cell23_6084510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_6084510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084510 prefixEnd_6084510 := by exact prefixLift 6084510
  have htrace : WordTrace (prefixWord ++ tailWord_6084510) baseStart_6084510 baseEnd_6084510 := by
    simpa [prefixWord, tailWord_6084510, baseEnd_6084510] using wordTrace_append hprefix tailTrace_6084510
  have hstable : (prefixWord ++ tailWord_6084510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084510).length < 2 ^ (prefixWord ++ tailWord_6084510).sum := by decide
  have hdescent : baseEnd_6084510 < baseStart_6084510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084551 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 6, 5]
def baseStart_6084551 : Nat := 118140960795 + 6084551 * 2 ^ 59
def prefixEnd_6084551 : Nat := 4983230072969 + 3 ^ 40 * 6084551 * 2
def baseEnd_6084551 : Nat := 1041433076598309633310055

theorem tailTrace_6084551 : CollatzResearch.WordTrace tailWord_6084551 prefixEnd_6084551 1041433076598309633310055 := by
  unfold tailWord_6084551
  simp only [CollatzResearch.WordTrace]
  refine ⟨221921806579718360424269507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147947871053145573616179671 221921806579718360424269507)
  ·
    refine ⟨332882709869577540636404261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221921806579718360424269507 332882709869577540636404261)
    ·
      refine ⟨62415508100545788869325799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332882709869577540636404261 62415508100545788869325799)
      ·
        refine ⟨93623262150818683303988699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62415508100545788869325799 93623262150818683303988699)
        ·
          refine ⟨140434893226228024955983049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93623262150818683303988699 140434893226228024955983049)
          ·
            refine ⟨105326169919671018716987287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140434893226228024955983049 105326169919671018716987287)
            ·
              refine ⟨157989254879506528075480931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105326169919671018716987287 157989254879506528075480931)
              ·
                refine ⟨236983882319259792113221397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157989254879506528075480931 236983882319259792113221397)
                ·
                  refine ⟨11108619483715302755307253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 236983882319259792113221397 11108619483715302755307253)
                  ·
                    refine ⟨1041433076598309633310055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11108619483715302755307253 1041433076598309633310055)
                    ·
                      rfl

theorem cell23_6084551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_6084551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084551 prefixEnd_6084551 := by exact prefixLift 6084551
  have htrace : WordTrace (prefixWord ++ tailWord_6084551) baseStart_6084551 baseEnd_6084551 := by
    simpa [prefixWord, tailWord_6084551, baseEnd_6084551] using wordTrace_append hprefix tailTrace_6084551
  have hstable : (prefixWord ++ tailWord_6084551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084551).length < 2 ^ (prefixWord ++ tailWord_6084551).sum := by decide
  have hdescent : baseEnd_6084551 < baseStart_6084551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084568 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 2, 5]
def baseStart_6084568 : Nat := 118140960795 + 6084568 * 2 ^ 59
def prefixEnd_6084568 : Nat := 4983230072969 + 3 ^ 40 * 6084568 * 2
def baseEnd_6084568 : Nat := 1041435986322018444472529

theorem tailTrace_6084568 : CollatzResearch.WordTrace tailWord_6084568 prefixEnd_6084568 1041435986322018444472529 := by
  unfold tailWord_6084568
  simp only [CollatzResearch.WordTrace]
  refine ⟨110961213310328386163819179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147948284413771181551758905 110961213310328386163819179)
  ·
    refine ⟨166441819965492579245728769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110961213310328386163819179 166441819965492579245728769)
    ·
      refine ⟨124831364974119434434296577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166441819965492579245728769 124831364974119434434296577)
      ·
        refine ⟨93623523730589575825722433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124831364974119434434296577 93623523730589575825722433)
        ·
          refine ⟨70217642797942181869291825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93623523730589575825722433 70217642797942181869291825)
          ·
            refine ⟨52663232098456636401968869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70217642797942181869291825 52663232098456636401968869)
            ·
              refine ⟨9874356018460619325369163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52663232098456636401968869 9874356018460619325369163)
              ·
                refine ⟨14811534027690928988053745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9874356018460619325369163 14811534027690928988053745)
                ·
                  refine ⟨11108650520768196741040309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14811534027690928988053745 11108650520768196741040309)
                  ·
                    refine ⟨1041435986322018444472529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11108650520768196741040309 1041435986322018444472529)
                    ·
                      rfl

theorem cell23_6084568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_6084568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084568 prefixEnd_6084568 := by exact prefixLift 6084568
  have htrace : WordTrace (prefixWord ++ tailWord_6084568) baseStart_6084568 baseEnd_6084568 := by
    simpa [prefixWord, tailWord_6084568, baseEnd_6084568] using wordTrace_append hprefix tailTrace_6084568
  have hstable : (prefixWord ++ tailWord_6084568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084568).length < 2 ^ (prefixWord ++ tailWord_6084568).sum := by decide
  have hdescent : baseEnd_6084568 < baseStart_6084568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084588 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 3, 6, 2]
def baseStart_6084588 : Nat := 118140960795 + 6084588 * 2 ^ 59
def prefixEnd_6084588 : Nat := 4983230072969 + 3 ^ 40 * 6084588 * 2
def baseEnd_6084588 : Nat := 3124318228579145255167495

theorem tailTrace_6084588 : CollatzResearch.WordTrace tailWord_6084588 prefixEnd_6084588 3124318228579145255167495 := by
  unfold tailWord_6084588
  simp only [CollatzResearch.WordTrace]
  refine ⟨110961578040292157871683209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147948770720389543828910945 110961578040292157871683209)
  ·
    refine ⟨83221183530219118403762407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110961578040292157871683209 83221183530219118403762407)
    ·
      refine ⟨124831775295328677605643611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83221183530219118403762407 124831775295328677605643611)
      ·
        refine ⟨187247662942993016408465417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124831775295328677605643611 187247662942993016408465417)
        ·
          refine ⟨140435747207244762306349063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187247662942993016408465417 140435747207244762306349063)
          ·
            refine ⟨210653620810867143459523595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140435747207244762306349063 210653620810867143459523595)
            ·
              refine ⟨315980431216300715189285393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210653620810867143459523595 315980431216300715189285393)
              ·
                refine ⟨236985323412225536391964045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315980431216300715189285393 236985323412225536391964045)
                ·
                  refine ⟨88869496279584576146986517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236985323412225536391964045 88869496279584576146986517)
                  ·
                    refine ⟨4165757638105527006889993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88869496279584576146986517 4165757638105527006889993)
                    ·
                      refine ⟨3124318228579145255167495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165757638105527006889993 3124318228579145255167495)
                      ·
                        rfl

theorem cell23_6084588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_6084588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084588 prefixEnd_6084588 := by exact prefixLift 6084588
  have htrace : WordTrace (prefixWord ++ tailWord_6084588) baseStart_6084588 baseEnd_6084588 := by
    simpa [prefixWord, tailWord_6084588, baseEnd_6084588] using wordTrace_append hprefix tailTrace_6084588
  have hstable : (prefixWord ++ tailWord_6084588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084588).length < 2 ^ (prefixWord ++ tailWord_6084588).sum := by decide
  have hdescent : baseEnd_6084588 < baseStart_6084588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084591 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_6084591 : Nat := 118140960795 + 6084591 * 2 ^ 59
def prefixEnd_6084591 : Nat := 4983230072969 + 3 ^ 40 * 6084591 * 2
def baseEnd_6084591 : Nat := 3124319769021108743429981

theorem tailTrace_6084591 : CollatzResearch.WordTrace tailWord_6084591 prefixEnd_6084591 3124319769021108743429981 := by
  unfold tailWord_6084591
  simp only [CollatzResearch.WordTrace]
  refine ⟨221923265499573447255725627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147948843666382298170483751 221923265499573447255725627)
  ·
    refine ⟨332884898249360170883588441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221923265499573447255725627 332884898249360170883588441)
    ·
      refine ⟨249663673687020128162691331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332884898249360170883588441 249663673687020128162691331)
      ·
        refine ⟨374495510530530192244036997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249663673687020128162691331 374495510530530192244036997)
        ·
          refine ⟨70217908224474411045756937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374495510530530192244036997 70217908224474411045756937)
          ·
            refine ⟨52663431168355808284317703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70217908224474411045756937 52663431168355808284317703)
            ·
              refine ⟨78995146752533712426476555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52663431168355808284317703 78995146752533712426476555)
              ·
                refine ⟨118492720128800568639714833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78995146752533712426476555 118492720128800568639714833)
                ·
                  refine ⟨88869540096600426479786125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118492720128800568639714833 88869540096600426479786125)
                  ·
                    refine ⟨33326077536225159929919797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88869540096600426479786125 33326077536225159929919797)
                    ·
                      refine ⟨3124319769021108743429981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33326077536225159929919797 3124319769021108743429981)
                      ·
                        rfl

theorem cell23_6084591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_6084591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084591 prefixEnd_6084591 := by exact prefixLift 6084591
  have htrace : WordTrace (prefixWord ++ tailWord_6084591) baseStart_6084591 baseEnd_6084591 := by
    simpa [prefixWord, tailWord_6084591, baseEnd_6084591] using wordTrace_append hprefix tailTrace_6084591
  have hstable : (prefixWord ++ tailWord_6084591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084591).length < 2 ^ (prefixWord ++ tailWord_6084591).sum := by decide
  have hdescent : baseEnd_6084591 < baseStart_6084591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084615 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 3, 4]
def baseStart_6084615 : Nat := 118140960795 + 6084615 * 2 ^ 59
def prefixEnd_6084615 : Nat := 4983230072969 + 3 ^ 40 * 6084615 * 2
def baseEnd_6084615 : Nat := 1041444030852272216509957

theorem tailTrace_6084615 : CollatzResearch.WordTrace tailWord_6084615 prefixEnd_6084615 1041444030852272216509957 := by
  unfold tailWord_6084615
  simp only [CollatzResearch.WordTrace]
  refine ⟨221924140851486499354599299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147949427234324332903066199 221924140851486499354599299)
  ·
    refine ⟨332886211277229749031898949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221924140851486499354599299 332886211277229749031898949)
    ·
      refine ⟨62416164614480577943481053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332886211277229749031898949 62416164614480577943481053)
      ·
        refine ⟨23406061730430216728805395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62416164614480577943481053 23406061730430216728805395)
        ·
          refine ⟨35109092595645325093208093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23406061730430216728805395 35109092595645325093208093)
          ·
            refine ⟨13165909723366996909953035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35109092595645325093208093 13165909723366996909953035)
            ·
              refine ⟨19748864585050495364929553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13165909723366996909953035 19748864585050495364929553)
              ·
                refine ⟨14811648438787871523697165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19748864585050495364929553 14811648438787871523697165)
                ·
                  refine ⟨5554368164545451821386437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14811648438787871523697165 5554368164545451821386437)
                  ·
                    refine ⟨1041444030852272216509957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554368164545451821386437 1041444030852272216509957)
                    ·
                      rfl

theorem cell23_6084615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_6084615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084615 prefixEnd_6084615 := by exact prefixLift 6084615
  have htrace : WordTrace (prefixWord ++ tailWord_6084615) baseStart_6084615 baseEnd_6084615 := by
    simpa [prefixWord, tailWord_6084615, baseEnd_6084615] using wordTrace_append hprefix tailTrace_6084615
  have hstable : (prefixWord ++ tailWord_6084615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084615).length < 2 ^ (prefixWord ++ tailWord_6084615).sum := by decide
  have hdescent : baseEnd_6084615 < baseStart_6084615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084632 : List Nat := [2, 1, 2, 3, 2, 1, 4, 3, 1, 4]
def baseStart_6084632 : Nat := 118140960795 + 6084632 * 2 ^ 59
def prefixEnd_6084632 : Nat := 4983230072969 + 3 ^ 40 * 6084632 * 2
def baseEnd_6084632 : Nat := 1041446940575981027672431

theorem tailTrace_6084632 : CollatzResearch.WordTrace tailWord_6084632 prefixEnd_6084632 1041446940575981027672431 := by
  unfold tailWord_6084632
  simp only [CollatzResearch.WordTrace]
  refine ⟨110962380446212455628984075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147949840594949940838645433 110962380446212455628984075)
  ·
    refine ⟨166443570669318683443476113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110962380446212455628984075 166443570669318683443476113)
    ·
      refine ⟨124832678001989012582607085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166443570669318683443476113 124832678001989012582607085)
      ·
        refine ⟨46812254250745879718477657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124832678001989012582607085 46812254250745879718477657)
        ·
          refine ⟨35109190688059409788858243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46812254250745879718477657 35109190688059409788858243)
          ·
            refine ⟨52663786032089114683287365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35109190688059409788858243 52663786032089114683287365)
            ·
              refine ⟨9874459881016709003116381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52663786032089114683287365 9874459881016709003116381)
              ·
                refine ⟨3702922455381265876168643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9874459881016709003116381 3702922455381265876168643)
                ·
                  refine ⟨5554383683071898814252965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702922455381265876168643 5554383683071898814252965)
                  ·
                    refine ⟨1041446940575981027672431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554383683071898814252965 1041446940575981027672431)
                    ·
                      rfl

theorem cell23_6084632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_6084632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084632 prefixEnd_6084632 := by exact prefixLift 6084632
  have htrace : WordTrace (prefixWord ++ tailWord_6084632) baseStart_6084632 baseEnd_6084632 := by
    simpa [prefixWord, tailWord_6084632, baseEnd_6084632] using wordTrace_append hprefix tailTrace_6084632
  have hstable : (prefixWord ++ tailWord_6084632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084632).length < 2 ^ (prefixWord ++ tailWord_6084632).sum := by decide
  have hdescent : baseEnd_6084632 < baseStart_6084632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084645 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 6]
def baseStart_6084645 : Nat := 118140960795 + 6084645 * 2 ^ 59
def prefixEnd_6084645 : Nat := 4983230072969 + 3 ^ 40 * 6084645 * 2
def baseEnd_6084645 : Nat := 347149721886272392461637

theorem tailTrace_6084645 : CollatzResearch.WordTrace tailWord_6084645 prefixEnd_6084645 347149721886272392461637 := by
  unfold tailWord_6084645
  simp only [CollatzResearch.WordTrace]
  refine ⟨221925235041377814478191389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147950156694251876318794259 221925235041377814478191389)
  ·
    refine ⟨83221963140516680429321771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221925235041377814478191389 83221963140516680429321771)
    ·
      refine ⟨124832944710775020643982657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83221963140516680429321771 124832944710775020643982657)
      ·
        refine ⟨93624708533081265482986993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124832944710775020643982657 93624708533081265482986993)
        ·
          refine ⟨70218531399810949112240245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93624708533081265482986993 70218531399810949112240245)
          ·
            refine ⟨6582987318732276479272523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70218531399810949112240245 6582987318732276479272523)
            ·
              refine ⟨9874480978098414718908785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582987318732276479272523 9874480978098414718908785)
              ·
                refine ⟨7405860733573811039181589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9874480978098414718908785 7405860733573811039181589)
                ·
                  refine ⟨347149721886272392461637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7405860733573811039181589 347149721886272392461637)
                  ·
                    rfl

theorem cell23_6084645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_6084645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084645 prefixEnd_6084645 := by exact prefixLift 6084645
  have htrace : WordTrace (prefixWord ++ tailWord_6084645) baseStart_6084645 baseEnd_6084645 := by
    simpa [prefixWord, tailWord_6084645, baseEnd_6084645] using wordTrace_append hprefix tailTrace_6084645
  have hstable : (prefixWord ++ tailWord_6084645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084645).length < 2 ^ (prefixWord ++ tailWord_6084645).sum := by decide
  have hdescent : baseEnd_6084645 < baseStart_6084645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084651 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 7]
def baseStart_6084651 : Nat := 118140960795 + 6084651 * 2 ^ 59
def prefixEnd_6084651 : Nat := 4983230072969 + 3 ^ 40 * 6084651 * 2
def baseEnd_6084651 : Nat := 3124350577860378508679705

theorem tailTrace_6084651 : CollatzResearch.WordTrace tailWord_6084651 prefixEnd_6084651 3124350577860378508679705 := by
  unfold tailWord_6084651
  simp only [CollatzResearch.WordTrace]
  refine ⟨221925453879356077502909807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147950302586237385001939871 221925453879356077502909807)
  ·
    refine ⟨332888180819034116254364711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221925453879356077502909807 332888180819034116254364711)
    ·
      refine ⟨499332271228551174381547067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332888180819034116254364711 499332271228551174381547067)
      ·
        refine ⟨748998406842826761572320601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499332271228551174381547067 748998406842826761572320601)
        ·
          refine ⟨561748805132120071179240451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748998406842826761572320601 561748805132120071179240451)
          ·
            refine ⟨842623207698180106768860677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561748805132120071179240451 842623207698180106768860677)
            ·
              refine ⟨157991851443408770019161377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 842623207698180106768860677 157991851443408770019161377)
              ·
                refine ⟨118493888582556577514371033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157991851443408770019161377 118493888582556577514371033)
                ·
                  refine ⟨88870416436917433135778275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118493888582556577514371033 88870416436917433135778275)
                  ·
                    refine ⟨133305624655376149703667413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88870416436917433135778275 133305624655376149703667413)
                    ·
                      refine ⟨3124350577860378508679705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133305624655376149703667413 3124350577860378508679705)
                      ·
                        rfl

theorem cell23_6084651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_6084651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084651 prefixEnd_6084651 := by exact prefixLift 6084651
  have htrace : WordTrace (prefixWord ++ tailWord_6084651) baseStart_6084651 baseEnd_6084651 := by
    simpa [prefixWord, tailWord_6084651, baseEnd_6084651] using wordTrace_append hprefix tailTrace_6084651
  have hstable : (prefixWord ++ tailWord_6084651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084651).length < 2 ^ (prefixWord ++ tailWord_6084651).sum := by decide
  have hdescent : baseEnd_6084651 < baseStart_6084651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084662 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_6084662 : Nat := 118140960795 + 6084662 * 2 ^ 59
def prefixEnd_6084662 : Nat := 4983230072969 + 3 ^ 40 * 6084662 * 2
def baseEnd_6084662 : Nat := 347150691794175329515795

theorem tailTrace_6084662 : CollatzResearch.WordTrace tailWord_6084662 prefixEnd_6084662 347150691794175329515795 := by
  unfold tailWord_6084662
  simp only [CollatzResearch.WordTrace]
  refine ⟨13870365942644764148847515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147950570054877484254373493 13870365942644764148847515)
  ·
    refine ⟨20805548913967146223271273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13870365942644764148847515 20805548913967146223271273)
    ·
      refine ⟨15604161685475359667453455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20805548913967146223271273 15604161685475359667453455)
      ·
        refine ⟨23406242528213039501180183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15604161685475359667453455 23406242528213039501180183)
        ·
          refine ⟨35109363792319559251770275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23406242528213039501180183 35109363792319559251770275)
          ·
            refine ⟨52664045688479338877655413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35109363792319559251770275 52664045688479338877655413)
            ·
              refine ⟨4937254283294938019780195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52664045688479338877655413 4937254283294938019780195)
              ·
                refine ⟨7405881424942407029670293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937254283294938019780195 7405881424942407029670293)
                ·
                  refine ⟨347150691794175329515795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7405881424942407029670293 347150691794175329515795)
                  ·
                    rfl

theorem cell23_6084662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_6084662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084662 prefixEnd_6084662 := by exact prefixLift 6084662
  have htrace : WordTrace (prefixWord ++ tailWord_6084662) baseStart_6084662 baseEnd_6084662 := by
    simpa [prefixWord, tailWord_6084662, baseEnd_6084662] using wordTrace_append hprefix tailTrace_6084662
  have hstable : (prefixWord ++ tailWord_6084662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084662).length < 2 ^ (prefixWord ++ tailWord_6084662).sum := by decide
  have hdescent : baseEnd_6084662 < baseStart_6084662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084695 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 4]
def baseStart_6084695 : Nat := 118140960795 + 6084695 * 2 ^ 59
def prefixEnd_6084695 : Nat := 4983230072969 + 3 ^ 40 * 6084695 * 2
def baseEnd_6084695 : Nat := 3124373171009176336529503

theorem tailTrace_6084695 : CollatzResearch.WordTrace tailWord_6084695 prefixEnd_6084695 3124373171009176336529503 := by
  unfold tailWord_6084695
  simp only [CollatzResearch.WordTrace]
  refine ⟨221927058691196673017511539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147951372460797782011674359 221927058691196673017511539)
  ·
    refine ⟨332890588036795009526267309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221927058691196673017511539 332890588036795009526267309)
    ·
      refine ⟨124833970513798128572350241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332890588036795009526267309 124833970513798128572350241)
      ·
        refine ⟨93625477885348596429262681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124833970513798128572350241 93625477885348596429262681)
        ·
          refine ⟨70219108414011447321947011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93625477885348596429262681 70219108414011447321947011)
          ·
            refine ⟨105328662621017170982920517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70219108414011447321947011 105328662621017170982920517)
            ·
              refine ⟨19749124241440719559297597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105328662621017170982920517 19749124241440719559297597)
              ·
                refine ⟨7405921590540269834736599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19749124241440719559297597 7405921590540269834736599)
                ·
                  refine ⟨11108882385810404752104899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405921590540269834736599 11108882385810404752104899)
                  ·
                    refine ⟨16663323578715607128157349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11108882385810404752104899 16663323578715607128157349)
                    ·
                      refine ⟨3124373171009176336529503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16663323578715607128157349 3124373171009176336529503)
                      ·
                        rfl

theorem cell23_6084695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_6084695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084695 prefixEnd_6084695 := by exact prefixLift 6084695
  have htrace : WordTrace (prefixWord ++ tailWord_6084695) baseStart_6084695 baseEnd_6084695 := by
    simpa [prefixWord, tailWord_6084695, baseEnd_6084695] using wordTrace_append hprefix tailTrace_6084695
  have hstable : (prefixWord ++ tailWord_6084695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084695).length < 2 ^ (prefixWord ++ tailWord_6084695).sum := by decide
  have hdescent : baseEnd_6084695 < baseStart_6084695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084705 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 2, 4]
def baseStart_6084705 : Nat := 118140960795 + 6084705 * 2 ^ 59
def prefixEnd_6084705 : Nat := 4983230072969 + 3 ^ 40 * 6084705 * 2
def baseEnd_6084705 : Nat := 1041459435271907099134819

theorem tailTrace_6084705 : CollatzResearch.WordTrace tailWord_6084705 prefixEnd_6084705 1041459435271907099134819 := by
  unfold tailWord_6084705
  simp only [CollatzResearch.WordTrace]
  refine ⟨221927423421160444725375569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147951615614106963150250379 221927423421160444725375569)
  ·
    refine ⟨166445567565870333544031677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221927423421160444725375569 166445567565870333544031677)
    ·
      refine ⟨62417087837201375079011879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166445567565870333544031677 62417087837201375079011879)
      ·
        refine ⟨93625631755802062618517819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62417087837201375079011879 93625631755802062618517819)
        ·
          refine ⟨140438447633703093927776729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93625631755802062618517819 140438447633703093927776729)
          ·
            refine ⟨105328835725277320445832547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140438447633703093927776729 105328835725277320445832547)
            ·
              refine ⟨157993253587915980668748821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105328835725277320445832547 157993253587915980668748821)
              ·
                refine ⟨7405933761933561593847601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157993253587915980668748821 7405933761933561593847601)
                ·
                  refine ⟨5554450321450171195385701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7405933761933561593847601 5554450321450171195385701)
                  ·
                    refine ⟨1041459435271907099134819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554450321450171195385701 1041459435271907099134819)
                    ·
                      rfl

theorem cell23_6084705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_6084705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084705 prefixEnd_6084705 := by exact prefixLift 6084705
  have htrace : WordTrace (prefixWord ++ tailWord_6084705) baseStart_6084705 baseEnd_6084705 := by
    simpa [prefixWord, tailWord_6084705, baseEnd_6084705] using wordTrace_append hprefix tailTrace_6084705
  have hstable : (prefixWord ++ tailWord_6084705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084705).length < 2 ^ (prefixWord ++ tailWord_6084705).sum := by decide
  have hdescent : baseEnd_6084705 < baseStart_6084705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084706 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6084706 : Nat := 118140960795 + 6084706 * 2 ^ 59
def prefixEnd_6084706 : Nat := 4983230072969 + 3 ^ 40 * 6084706 * 2
def baseEnd_6084706 : Nat := 3124378819296375793491953

theorem tailTrace_6084706 : CollatzResearch.WordTrace tailWord_6084706 prefixEnd_6084706 3124378819296375793491953 := by
  unfold tailWord_6084706
  simp only [CollatzResearch.WordTrace]
  refine ⟨55481864973539205474040493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147951639929437881264107981 55481864973539205474040493)
  ·
    refine ⟨20805699365077202052765185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55481864973539205474040493 20805699365077202052765185)
    ·
      refine ⟨15604274523807901539573889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20805699365077202052765185 15604274523807901539573889)
      ·
        refine ⟨11703205892855926154680417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15604274523807901539573889 11703205892855926154680417)
        ·
          refine ⟨8777404419641944616010313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11703205892855926154680417 8777404419641944616010313)
          ·
            refine ⟨6583053314731458462007735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8777404419641944616010313 6583053314731458462007735)
            ·
              refine ⟨9874579972097187693011603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6583053314731458462007735 9874579972097187693011603)
              ·
                refine ⟨14811869958145781539517405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9874579972097187693011603 14811869958145781539517405)
                ·
                  refine ⟨5554451234304668077319027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14811869958145781539517405 5554451234304668077319027)
                  ·
                    refine ⟨8331676851457002115978541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5554451234304668077319027 8331676851457002115978541)
                    ·
                      refine ⟨3124378819296375793491953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8331676851457002115978541 3124378819296375793491953)
                      ·
                        rfl

theorem cell23_6084706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6084706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084706 prefixEnd_6084706 := by exact prefixLift 6084706
  have htrace : WordTrace (prefixWord ++ tailWord_6084706) baseStart_6084706 baseEnd_6084706 := by
    simpa [prefixWord, tailWord_6084706, baseEnd_6084706] using wordTrace_append hprefix tailTrace_6084706
  have hstable : (prefixWord ++ tailWord_6084706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084706).length < 2 ^ (prefixWord ++ tailWord_6084706).sum := by decide
  have hdescent : baseEnd_6084706 < baseStart_6084706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084708 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_6084708 : Nat := 118140960795 + 6084708 * 2 ^ 59
def prefixEnd_6084708 : Nat := 4983230072969 + 3 ^ 40 * 6084708 * 2
def baseEnd_6084708 : Nat := 3124379846257684785666943

theorem tailTrace_6084708 : CollatzResearch.WordTrace tailWord_6084708 prefixEnd_6084708 3124379846257684785666943 := by
  unfold tailWord_6084708
  simp only [CollatzResearch.WordTrace]
  refine ⟨110963766420074788118867389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147951688560099717491823185 110963766420074788118867389)
  ·
    refine ⟨41611412407528045544575271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110963766420074788118867389 41611412407528045544575271)
    ·
      refine ⟨62417118611292068316862907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41611412407528045544575271 62417118611292068316862907)
      ·
        refine ⟨93625677916938102475294361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62417118611292068316862907 93625677916938102475294361)
        ·
          refine ⟨70219258437703576856470771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93625677916938102475294361 70219258437703576856470771)
          ·
            refine ⟨105328887656555365284706157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70219258437703576856470771 105328887656555365284706157)
            ·
              refine ⟨39498332871208261981764809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105328887656555365284706157 39498332871208261981764809)
              ·
                refine ⟨29623749653406196486323607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39498332871208261981764809 29623749653406196486323607)
                ·
                  refine ⟨44435624480109294729485411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29623749653406196486323607 44435624480109294729485411)
                  ·
                    refine ⟨66653436720163942094228117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44435624480109294729485411 66653436720163942094228117)
                    ·
                      refine ⟨3124379846257684785666943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66653436720163942094228117 3124379846257684785666943)
                      ·
                        rfl

theorem cell23_6084708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_6084708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084708 prefixEnd_6084708 := by exact prefixLift 6084708
  have htrace : WordTrace (prefixWord ++ tailWord_6084708) baseStart_6084708 baseEnd_6084708 := by
    simpa [prefixWord, tailWord_6084708, baseEnd_6084708] using wordTrace_append hprefix tailTrace_6084708
  have hstable : (prefixWord ++ tailWord_6084708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084708).length < 2 ^ (prefixWord ++ tailWord_6084708).sum := by decide
  have hdescent : baseEnd_6084708 < baseStart_6084708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084722 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_6084722 : Nat := 118140960795 + 6084722 * 2 ^ 59
def prefixEnd_6084722 : Nat := 4983230072969 + 3 ^ 40 * 6084722 * 2
def baseEnd_6084722 : Nat := 1041462344995615910297293

theorem tailTrace_6084722 : CollatzResearch.WordTrace tailWord_6084722 prefixEnd_6084722 1041462344995615910297293 := by
  unfold tailWord_6084722
  simp only [CollatzResearch.WordTrace]
  refine ⟨55482010865524714157186105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147952028974732571085829613 55482010865524714157186105)
  ·
    refine ⟨41611508149143535617889579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55482010865524714157186105 41611508149143535617889579)
    ·
      refine ⟨62417262223715303426834369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41611508149143535617889579 62417262223715303426834369)
      ·
        refine ⟨46812946667786477570125777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62417262223715303426834369 46812946667786477570125777)
        ·
          refine ⟨35109710000839858177594333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46812946667786477570125777 35109710000839858177594333)
          ·
            refine ⟨13166141250314946816597875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35109710000839858177594333 13166141250314946816597875)
            ·
              refine ⟨19749211875472420224896813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13166141250314946816597875 19749211875472420224896813)
              ·
                refine ⟨7405954453302157584336305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19749211875472420224896813 7405954453302157584336305)
                ·
                  refine ⟨5554465839976618188252229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7405954453302157584336305 5554465839976618188252229)
                  ·
                    refine ⟨1041462344995615910297293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554465839976618188252229 1041462344995615910297293)
                    ·
                      rfl

theorem cell23_6084722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_6084722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084722 prefixEnd_6084722 := by exact prefixLift 6084722
  have htrace : WordTrace (prefixWord ++ tailWord_6084722) baseStart_6084722 baseEnd_6084722 := by
    simpa [prefixWord, tailWord_6084722, baseEnd_6084722] using wordTrace_append hprefix tailTrace_6084722
  have hstable : (prefixWord ++ tailWord_6084722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084722).length < 2 ^ (prefixWord ++ tailWord_6084722).sum := by decide
  have hdescent : baseEnd_6084722 < baseStart_6084722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084732 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_6084732 : Nat := 118140960795 + 6084732 * 2 ^ 59
def prefixEnd_6084732 : Nat := 4983230072969 + 3 ^ 40 * 6084732 * 2
def baseEnd_6084732 : Nat := 3124392169793392691766833

theorem tailTrace_6084732 : CollatzResearch.WordTrace tailWord_6084732 prefixEnd_6084732 3124392169793392691766833 := by
  unfold tailWord_6084732
  simp only [CollatzResearch.WordTrace]
  refine ⟨110964204096031314168304225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147952272128041752224405633 110964204096031314168304225)
  ·
    refine ⟨83223153072023485626228169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110964204096031314168304225 83223153072023485626228169)
    ·
      refine ⟨62417364804017614219671127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83223153072023485626228169 62417364804017614219671127)
      ·
        refine ⟨93626047206026421329506691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62417364804017614219671127 93626047206026421329506691)
        ·
          refine ⟨140439070809039631994260037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93626047206026421329506691 140439070809039631994260037)
          ·
            refine ⟨26332325776694930998923757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140439070809039631994260037 26332325776694930998923757)
            ·
              refine ⟨9874622166260599124596409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26332325776694930998923757 9874622166260599124596409)
              ·
                refine ⟨7405966624695449343447307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9874622166260599124596409 7405966624695449343447307)
                ·
                  refine ⟨11108949937043174015170961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405966624695449343447307 11108949937043174015170961)
                  ·
                    refine ⟨8331712452782380511378221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11108949937043174015170961 8331712452782380511378221)
                    ·
                      refine ⟨3124392169793392691766833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8331712452782380511378221 3124392169793392691766833)
                      ·
                        rfl

theorem cell23_6084732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_6084732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084732 prefixEnd_6084732 := by exact prefixLift 6084732
  have htrace : WordTrace (prefixWord ++ tailWord_6084732) baseStart_6084732 baseEnd_6084732 := by
    simpa [prefixWord, tailWord_6084732, baseEnd_6084732] using wordTrace_append hprefix tailTrace_6084732
  have hstable : (prefixWord ++ tailWord_6084732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084732).length < 2 ^ (prefixWord ++ tailWord_6084732).sum := by decide
  have hdescent : baseEnd_6084732 < baseStart_6084732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084745 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 1, 3, 3]
def baseStart_6084745 : Nat := 118140960795 + 6084745 * 2 ^ 59
def prefixEnd_6084745 : Nat := 4983230072969 + 3 ^ 40 * 6084745 * 2
def baseEnd_6084745 : Nat := 3124398845041901140904273

theorem tailTrace_6084745 : CollatzResearch.WordTrace tailWord_6084745 prefixEnd_6084745 3124398845041901140904273 := by
  unfold tailWord_6084745
  simp only [CollatzResearch.WordTrace]
  refine ⟨221928882341015531556831689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147952588227343687704554459 221928882341015531556831689)
  ·
    refine ⟨166446661755761648667623767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221928882341015531556831689 166446661755761648667623767)
    ·
      refine ⟨249669992633642473001435651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166446661755761648667623767 249669992633642473001435651)
      ·
        refine ⟨374504988950463709502153477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249669992633642473001435651 374504988950463709502153477)
        ·
          refine ⟨70219685428211945531653777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374504988950463709502153477 70219685428211945531653777)
          ·
            refine ⟨52664764071158959148740333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70219685428211945531653777 52664764071158959148740333)
            ·
              refine ⟨19749286526684609680777625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52664764071158959148740333 19749286526684609680777625)
              ·
                refine ⟨14811964895013457260583219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19749286526684609680777625 14811964895013457260583219)
                ·
                  refine ⟨22217947342520185890874829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14811964895013457260583219 22217947342520185890874829)
                  ·
                    refine ⟨8331730253445069709078061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22217947342520185890874829 8331730253445069709078061)
                    ·
                      refine ⟨3124398845041901140904273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8331730253445069709078061 3124398845041901140904273)
                      ·
                        rfl

theorem cell23_6084745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3, 3].length) (baseStart_6084745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084745 prefixEnd_6084745 := by exact prefixLift 6084745
  have htrace : WordTrace (prefixWord ++ tailWord_6084745) baseStart_6084745 baseEnd_6084745 := by
    simpa [prefixWord, tailWord_6084745, baseEnd_6084745] using wordTrace_append hprefix tailTrace_6084745
  have hstable : (prefixWord ++ tailWord_6084745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084745).length < 2 ^ (prefixWord ++ tailWord_6084745).sum := by decide
  have hdescent : baseEnd_6084745 < baseStart_6084745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084756 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_6084756 : Nat := 118140960795 + 6084756 * 2 ^ 59
def prefixEnd_6084756 : Nat := 4983230072969 + 3 ^ 40 * 6084756 * 2
def baseEnd_6084756 : Nat := 1041468164443033532622241

theorem tailTrace_6084756 : CollatzResearch.WordTrace tailWord_6084756 prefixEnd_6084756 1041468164443033532622241 := by
  unfold tailWord_6084756
  simp only [CollatzResearch.WordTrace]
  refine ⟨110964641771987840217741061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147952855695983786956988081 110964641771987840217741061)
  ·
    refine ⟨20805870332247720040826449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110964641771987840217741061 20805870332247720040826449)
    ·
      refine ⟨15604402749185790030619837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20805870332247720040826449 15604402749185790030619837)
      ·
        refine ⟨5851651030944671261482439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15604402749185790030619837 5851651030944671261482439)
        ·
          refine ⟨8777476546417006892223659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851651030944671261482439 8777476546417006892223659)
          ·
            refine ⟨13166214819625510338335489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8777476546417006892223659 13166214819625510338335489)
            ·
              refine ⟨9874661114719132753751617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13166214819625510338335489 9874661114719132753751617)
              ·
                refine ⟨7405995836039349565313713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9874661114719132753751617 7405995836039349565313713)
                ·
                  refine ⟨5554496877029512173985285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7405995836039349565313713 5554496877029512173985285)
                  ·
                    refine ⟨1041468164443033532622241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554496877029512173985285 1041468164443033532622241)
                    ·
                      rfl

theorem cell23_6084756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_6084756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084756 prefixEnd_6084756 := by exact prefixLift 6084756
  have htrace : WordTrace (prefixWord ++ tailWord_6084756) baseStart_6084756 baseEnd_6084756 := by
    simpa [prefixWord, tailWord_6084756, baseEnd_6084756] using wordTrace_append hprefix tailTrace_6084756
  have hstable : (prefixWord ++ tailWord_6084756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084756).length < 2 ^ (prefixWord ++ tailWord_6084756).sum := by decide
  have hdescent : baseEnd_6084756 < baseStart_6084756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084808 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 11]
def baseStart_6084808 : Nat := 118140960795 + 6084808 * 2 ^ 59
def prefixEnd_6084808 : Nat := 4983230072969 + 3 ^ 40 * 6084808 * 2
def baseEnd_6084808 : Nat := 347159021591459377157387

theorem tailTrace_6084808 : CollatzResearch.WordTrace tailWord_6084808 prefixEnd_6084808 347159021591459377157387 := by
  unfold tailWord_6084808
  simp only [CollatzResearch.WordTrace]
  refine ⟨110965590069893646658187539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147954120093191528877583385 110965590069893646658187539)
  ·
    refine ⟨166448385104840469987281309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110965590069893646658187539 166448385104840469987281309)
    ·
      refine ⟨62418144414315176245230491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166448385104840469987281309 62418144414315176245230491)
      ·
        refine ⟨93627216621472764367845737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62418144414315176245230491 93627216621472764367845737)
        ·
          refine ⟨70220412466104573275884303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93627216621472764367845737 70220412466104573275884303)
          ·
            refine ⟨105330618699156859913826455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70220412466104573275884303 105330618699156859913826455)
            ·
              refine ⟨157995928048735289870739683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105330618699156859913826455 157995928048735289870739683)
              ·
                refine ⟨236993892073102934806109525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157995928048735289870739683 236993892073102934806109525)
                ·
                  refine ⟨347159021591459377157387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 236993892073102934806109525 347159021591459377157387)
                  ·
                    rfl

theorem cell23_6084808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 11].length) (baseStart_6084808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084808 prefixEnd_6084808 := by exact prefixLift 6084808
  have htrace : WordTrace (prefixWord ++ tailWord_6084808) baseStart_6084808 baseEnd_6084808 := by
    simpa [prefixWord, tailWord_6084808, baseEnd_6084808] using wordTrace_append hprefix tailTrace_6084808
  have hstable : (prefixWord ++ tailWord_6084808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084808).length < 2 ^ (prefixWord ++ tailWord_6084808).sum := by decide
  have hdescent : baseEnd_6084808 < baseStart_6084808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084865 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_6084865 : Nat := 118140960795 + 6084865 * 2 ^ 59
def prefixEnd_6084865 : Nat := 4983230072969 + 3 ^ 40 * 6084865 * 2
def baseEnd_6084865 : Nat := 3124460462720440671403721

theorem tailTrace_6084865 : CollatzResearch.WordTrace tailWord_6084865 prefixEnd_6084865 3124460462720440671403721 := by
  unfold tailWord_6084865
  simp only [CollatzResearch.WordTrace]
  refine ⟨221933259100580792051200049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147955506067053861367466699 221933259100580792051200049)
  ·
    refine ⟨166449944325435594038400037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221933259100580792051200049 166449944325435594038400037)
    ·
      refine ⟨31209364561019173882200007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166449944325435594038400037 31209364561019173882200007)
      ·
        refine ⟨46814046841528760823300011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31209364561019173882200007 46814046841528760823300011)
        ·
          refine ⟨70221070262293141234950017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46814046841528760823300011 70221070262293141234950017)
          ·
            refine ⟨52665802696719855926212513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70221070262293141234950017 52665802696719855926212513)
            ·
              refine ⟨39499352022539891944659385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52665802696719855926212513 39499352022539891944659385)
              ·
                refine ⟨29624514016904918958494539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39499352022539891944659385 29624514016904918958494539)
                ·
                  refine ⟨44436771025357378437741809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29624514016904918958494539 44436771025357378437741809)
                  ·
                    refine ⟨33327578269018033828306357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44436771025357378437741809 33327578269018033828306357)
                    ·
                      refine ⟨3124460462720440671403721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33327578269018033828306357 3124460462720440671403721)
                      ·
                        rfl

theorem cell23_6084865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_6084865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084865 prefixEnd_6084865 := by exact prefixLift 6084865
  have htrace : WordTrace (prefixWord ++ tailWord_6084865) baseStart_6084865 baseEnd_6084865 := by
    simpa [prefixWord, tailWord_6084865, baseEnd_6084865] using wordTrace_append hprefix tailTrace_6084865
  have hstable : (prefixWord ++ tailWord_6084865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084865).length < 2 ^ (prefixWord ++ tailWord_6084865).sum := by decide
  have hdescent : baseEnd_6084865 < baseStart_6084865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084872 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 2, 5]
def baseStart_6084872 : Nat := 118140960795 + 6084872 * 2 ^ 59
def prefixEnd_6084872 : Nat := 4983230072969 + 3 ^ 40 * 6084872 * 2
def baseEnd_6084872 : Nat := 1041488019028340714672063

theorem tailTrace_6084872 : CollatzResearch.WordTrace tailWord_6084872 prefixEnd_6084872 1041488019028340714672063 := by
  unfold tailWord_6084872
  simp only [CollatzResearch.WordTrace]
  refine ⟨110966757205777716123352435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147955676274370288164469913 110966757205777716123352435)
  ·
    refine ⟨166450135808666574185028653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110966757205777716123352435 166450135808666574185028653)
    ·
      refine ⟨62418800928249965319385745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166450135808666574185028653 62418800928249965319385745)
      ·
        refine ⟨46814100696187473989539309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62418800928249965319385745 46814100696187473989539309)
        ·
          refine ⟨17555287761070302746077241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46814100696187473989539309 17555287761070302746077241)
          ·
            refine ⟨13166465820802727059557931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17555287761070302746077241 13166465820802727059557931)
            ·
              refine ⟨19749698731204090589336897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13166465820802727059557931 19749698731204090589336897)
              ·
                refine ⟨14812274048403067942002673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19749698731204090589336897 14812274048403067942002673)
                ·
                  refine ⟨11109205536302300956502005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14812274048403067942002673 11109205536302300956502005)
                  ·
                    refine ⟨1041488019028340714672063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11109205536302300956502005 1041488019028340714672063)
                    ·
                      rfl

theorem cell23_6084872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_6084872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084872 prefixEnd_6084872 := by exact prefixLift 6084872
  have htrace : WordTrace (prefixWord ++ tailWord_6084872) baseStart_6084872 baseEnd_6084872 := by
    simpa [prefixWord, tailWord_6084872, baseEnd_6084872] using wordTrace_append hprefix tailTrace_6084872
  have hstable : (prefixWord ++ tailWord_6084872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084872).length < 2 ^ (prefixWord ++ tailWord_6084872).sum := by decide
  have hdescent : baseEnd_6084872 < baseStart_6084872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084892 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_6084892 : Nat := 118140960795 + 6084892 * 2 ^ 59
def prefixEnd_6084892 : Nat := 4983230072969 + 3 ^ 40 * 6084892 * 2
def baseEnd_6084892 : Nat := 3124474326698112065766097

theorem tailTrace_6084892 : CollatzResearch.WordTrace tailWord_6084892 prefixEnd_6084892 3124474326698112065766097 := by
  unfold tailWord_6084892
  simp only [CollatzResearch.WordTrace]
  refine ⟨110967121935741487831216465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147956162580988650441621953 110967121935741487831216465)
  ·
    refine ⟨83225341451806115873412349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110967121935741487831216465 83225341451806115873412349)
    ·
      refine ⟨31209503044427293452529631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83225341451806115873412349 31209503044427293452529631)
      ·
        refine ⟨46814254566640940178794447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31209503044427293452529631 46814254566640940178794447)
        ·
          refine ⟨70221381849961410268191671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46814254566640940178794447 70221381849961410268191671)
          ·
            refine ⟨105332072774942115402287507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70221381849961410268191671 105332072774942115402287507)
            ·
              refine ⟨157998109162413173103431261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105332072774942115402287507 157998109162413173103431261)
              ·
                refine ⟨59249290935904939913786723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157998109162413173103431261 59249290935904939913786723)
                ·
                  refine ⟨88873936403857409870680085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59249290935904939913786723 88873936403857409870680085)
                  ·
                    refine ⟨4165965768930816087688129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88873936403857409870680085 4165965768930816087688129)
                    ·
                      refine ⟨3124474326698112065766097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4165965768930816087688129 3124474326698112065766097)
                      ·
                        rfl

theorem cell23_6084892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_6084892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084892 prefixEnd_6084892 := by exact prefixLift 6084892
  have htrace : WordTrace (prefixWord ++ tailWord_6084892) baseStart_6084892 baseEnd_6084892 := by
    simpa [prefixWord, tailWord_6084892, baseEnd_6084892] using wordTrace_append hprefix tailTrace_6084892
  have hstable : (prefixWord ++ tailWord_6084892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084892).length < 2 ^ (prefixWord ++ tailWord_6084892).sum := by decide
  have hdescent : baseEnd_6084892 < baseStart_6084892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084935 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_6084935 : Nat := 118140960795 + 6084935 * 2 ^ 59
def prefixEnd_6084935 : Nat := 4983230072969 + 3 ^ 40 * 6084935 * 2
def baseEnd_6084935 : Nat := 3124496406366255397528399

theorem tailTrace_6084935 : CollatzResearch.WordTrace tailWord_6084935 prefixEnd_6084935 3124496406366255397528399 := by
  unfold tailWord_6084935
  simp only [CollatzResearch.WordTrace]
  refine ⟨221935812210327194006248259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147957208140218129337498839 221935812210327194006248259)
  ·
    refine ⟨332903718315490791009372389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221935812210327194006248259 332903718315490791009372389)
    ·
      refine ⟨62419447184154523314257323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332903718315490791009372389 62419447184154523314257323)
      ·
        refine ⟨93629170776231784971385985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62419447184154523314257323 93629170776231784971385985)
        ·
          refine ⟨70221878082173838728539489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93629170776231784971385985 70221878082173838728539489)
          ·
            refine ⟨52666408561630379046404617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70221878082173838728539489 52666408561630379046404617)
            ·
              refine ⟨39499806421222784284803463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52666408561630379046404617 39499806421222784284803463)
              ·
                refine ⟨59249709631834176427205195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39499806421222784284803463 59249709631834176427205195)
                ·
                  refine ⟨88874564447751264640807793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59249709631834176427205195 88874564447751264640807793)
                  ·
                    refine ⟨66655923335813448480605845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88874564447751264640807793 66655923335813448480605845)
                    ·
                      refine ⟨3124496406366255397528399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66655923335813448480605845 3124496406366255397528399)
                      ·
                        rfl

theorem cell23_6084935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_6084935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084935 prefixEnd_6084935 := by exact prefixLift 6084935
  have htrace : WordTrace (prefixWord ++ tailWord_6084935) baseStart_6084935 baseEnd_6084935 := by
    simpa [prefixWord, tailWord_6084935, baseEnd_6084935] using wordTrace_append hprefix tailTrace_6084935
  have hstable : (prefixWord ++ tailWord_6084935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084935).length < 2 ^ (prefixWord ++ tailWord_6084935).sum := by decide
  have hdescent : baseEnd_6084935 < baseStart_6084935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084936 : List Nat := [2, 1, 3, 1, 1, 2, 6, 2, 1, 4]
def baseStart_6084936 : Nat := 118140960795 + 6084936 * 2 ^ 59
def prefixEnd_6084936 : Nat := 4983230072969 + 3 ^ 40 * 6084936 * 2
def baseEnd_6084936 : Nat := 1041498973282303297871965

theorem tailTrace_6084936 : CollatzResearch.WordTrace tailWord_6084936 prefixEnd_6084936 1041498973282303297871965 := by
  unfold tailWord_6084936
  simp only [CollatzResearch.WordTrace]
  refine ⟨110967924341661785588517331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147957232455549047451356441 110967924341661785588517331)
  ·
    refine ⟨166451886512492678382775997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110967924341661785588517331 166451886512492678382775997)
    ·
      refine ⟨62419457442184754393540999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166451886512492678382775997 62419457442184754393540999)
      ·
        refine ⟨93629186163277131590311499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62419457442184754393540999 93629186163277131590311499)
        ·
          refine ⟨140443779244915697385467249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93629186163277131590311499 140443779244915697385467249)
          ·
            refine ⟨105332834433686773039100437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140443779244915697385467249 105332834433686773039100437)
            ·
              refine ⟨4937476614079067486207833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105332834433686773039100437 4937476614079067486207833)
              ·
                refine ⟨3703107460559300614655875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4937476614079067486207833 3703107460559300614655875)
                ·
                  refine ⟨5554661190838950921983813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703107460559300614655875 5554661190838950921983813)
                  ·
                    refine ⟨1041498973282303297871965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554661190838950921983813 1041498973282303297871965)
                    ·
                      rfl

theorem cell23_6084936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_6084936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084936 prefixEnd_6084936 := by exact prefixLift 6084936
  have htrace : WordTrace (prefixWord ++ tailWord_6084936) baseStart_6084936 baseEnd_6084936 := by
    simpa [prefixWord, tailWord_6084936, baseEnd_6084936] using wordTrace_append hprefix tailTrace_6084936
  have hstable : (prefixWord ++ tailWord_6084936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084936).length < 2 ^ (prefixWord ++ tailWord_6084936).sum := by decide
  have hdescent : baseEnd_6084936 < baseStart_6084936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084975 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 3, 6]
def baseStart_6084975 : Nat := 118140960795 + 6084975 * 2 ^ 59
def prefixEnd_6084975 : Nat := 4983230072969 + 3 ^ 40 * 6084975 * 2
def baseEnd_6084975 : Nat := 1041505648530811747009405

theorem tailTrace_6084975 : CollatzResearch.WordTrace tailWord_6084975 prefixEnd_6084975 1041505648530811747009405 := by
  unfold tailWord_6084975
  simp only [CollatzResearch.WordTrace]
  refine ⟨221937271130182280837704379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147958180753454853891802919 221937271130182280837704379)
  ·
    refine ⟨332905906695273421256556569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221937271130182280837704379 332905906695273421256556569)
    ·
      refine ⟨249679430021455065942417427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332905906695273421256556569 249679430021455065942417427)
      ·
        refine ⟨374519145032182598913626141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249679430021455065942417427 374519145032182598913626141)
        ·
          refine ⟨140444679387068474592609803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374519145032182598913626141 140444679387068474592609803)
          ·
            refine ⟨210667019080602711888914705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140444679387068474592609803 210667019080602711888914705)
            ·
              refine ⟨158000264310452033916686029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210667019080602711888914705 158000264310452033916686029)
              ·
                refine ⟨59250099116419512718757261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158000264310452033916686029 59250099116419512718757261)
                ·
                  refine ⟨22218787168657317269533973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59250099116419512718757261 22218787168657317269533973)
                  ·
                    refine ⟨1041505648530811747009405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22218787168657317269533973 1041505648530811747009405)
                    ·
                      rfl

theorem cell23_6084975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_6084975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084975 prefixEnd_6084975 := by exact prefixLift 6084975
  have htrace : WordTrace (prefixWord ++ tailWord_6084975) baseStart_6084975 baseEnd_6084975 := by
    simpa [prefixWord, tailWord_6084975, baseEnd_6084975] using wordTrace_append hprefix tailTrace_6084975
  have hstable : (prefixWord ++ tailWord_6084975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084975).length < 2 ^ (prefixWord ++ tailWord_6084975).sum := by decide
  have hdescent : baseEnd_6084975 < baseStart_6084975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084976 : List Nat := [2, 1, 1, 1, 4, 3, 1, 5, 1, 1, 3]
def baseStart_6084976 : Nat := 118140960795 + 6084976 * 2 ^ 59
def prefixEnd_6084976 : Nat := 4983230072969 + 3 ^ 40 * 6084976 * 2
def baseEnd_6084976 : Nat := 3124517459073089737115711

theorem tailTrace_6084976 : CollatzResearch.WordTrace tailWord_6084976 prefixEnd_6084976 3124517459073089737115711 := by
  unfold tailWord_6084976
  simp only [CollatzResearch.WordTrace]
  refine ⟨110968653801589329004245391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147958205068785772005660521 110968653801589329004245391)
  ·
    refine ⟨166452980702383993506368087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110968653801589329004245391 166452980702383993506368087)
    ·
      refine ⟨249679471053575990259552131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166452980702383993506368087 249679471053575990259552131)
      ·
        refine ⟨374519206580363985389328197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249679471053575990259552131 374519206580363985389328197)
        ·
          refine ⟨70222351233818247260499037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374519206580363985389328197 70222351233818247260499037)
          ·
            refine ⟨26333381712681842722687139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70222351233818247260499037 26333381712681842722687139)
            ·
              refine ⟨39500072569022764084030709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26333381712681842722687139 39500072569022764084030709)
              ·
                refine ⟨3703131803345884132877879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39500072569022764084030709 3703131803345884132877879)
                ·
                  refine ⟨5554697705018826199316819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703131803345884132877879 5554697705018826199316819)
                  ·
                    refine ⟨8332046557528239298975229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5554697705018826199316819 8332046557528239298975229)
                    ·
                      refine ⟨3124517459073089737115711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332046557528239298975229 3124517459073089737115711)
                      ·
                        rfl

theorem cell23_6084976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 1, 1, 3].length) (baseStart_6084976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084976 prefixEnd_6084976 := by exact prefixLift 6084976
  have htrace : WordTrace (prefixWord ++ tailWord_6084976) baseStart_6084976 baseEnd_6084976 := by
    simpa [prefixWord, tailWord_6084976, baseEnd_6084976] using wordTrace_append hprefix tailTrace_6084976
  have hstable : (prefixWord ++ tailWord_6084976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084976).length < 2 ^ (prefixWord ++ tailWord_6084976).sum := by decide
  have hdescent : baseEnd_6084976 < baseStart_6084976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6084993 : List Nat := [1, 2, 4, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_6084993 : Nat := 118140960795 + 6084993 * 2 ^ 59
def prefixEnd_6084993 : Nat := 4983230072969 + 3 ^ 40 * 6084993 * 2
def baseEnd_6084993 : Nat := 3124526188244216170603133

theorem tailTrace_6084993 : CollatzResearch.WordTrace tailWord_6084993 prefixEnd_6084993 3124526188244216170603133 := by
  unfold tailWord_6084993
  simp only [CollatzResearch.WordTrace]
  refine ⟨221937927644117069911859633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147958618429411379941239755 221937927644117069911859633)
  ·
    refine ⟨166453445733087802433894725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221937927644117069911859633 166453445733087802433894725)
    ·
      refine ⟨31210021074953962956355261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166453445733087802433894725 31210021074953962956355261)
      ·
        refine ⟨11703757903107736108633223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31210021074953962956355261 11703757903107736108633223)
        ·
          refine ⟨17555636854661604162949835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11703757903107736108633223 17555636854661604162949835)
          ·
            refine ⟨26333455281992406244424753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17555636854661604162949835 26333455281992406244424753)
            ·
              refine ⟨19750091461494304683318565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26333455281992406244424753 19750091461494304683318565)
              ·
                refine ⟨3703142149030182128122231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19750091461494304683318565 3703142149030182128122231)
                ·
                  refine ⟨5554713223545273192183347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703142149030182128122231 5554713223545273192183347)
                  ·
                    refine ⟨8332069835317909788275021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5554713223545273192183347 8332069835317909788275021)
                    ·
                      refine ⟨3124526188244216170603133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332069835317909788275021 3124526188244216170603133)
                      ·
                        rfl

theorem cell23_6084993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_6084993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6084993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6084993 prefixEnd_6084993 := by exact prefixLift 6084993
  have htrace : WordTrace (prefixWord ++ tailWord_6084993) baseStart_6084993 baseEnd_6084993 := by
    simpa [prefixWord, tailWord_6084993, baseEnd_6084993] using wordTrace_append hprefix tailTrace_6084993
  have hstable : (prefixWord ++ tailWord_6084993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6084993).length < 2 ^ (prefixWord ++ tailWord_6084993).sum := by decide
  have hdescent : baseEnd_6084993 < baseStart_6084993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6084993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085016 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6085016 : Nat := 118140960795 + 6085016 * 2 ^ 59
def prefixEnd_6085016 : Nat := 4983230072969 + 3 ^ 40 * 6085016 * 2
def baseEnd_6085016 : Nat := 3124537998299269580615527

theorem tailTrace_6085016 : CollatzResearch.WordTrace tailWord_6085016 prefixEnd_6085016 3124537998299269580615527 := by
  unfold tailWord_6085016
  simp only [CollatzResearch.WordTrace]
  refine ⟨110969383261516872419973451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147959177682022496559964601 110969383261516872419973451)
  ·
    refine ⟨166454074892275308629960177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110969383261516872419973451 166454074892275308629960177)
    ·
      refine ⟨124840556169206481472470133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166454074892275308629960177 124840556169206481472470133)
      ·
        refine ⟨11703802140863107638044075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124840556169206481472470133 11703802140863107638044075)
        ·
          refine ⟨17555703211294661457066113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11703802140863107638044075 17555703211294661457066113)
          ·
            refine ⟨13166777408470996092799585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17555703211294661457066113 13166777408470996092799585)
            ·
              refine ⟨9875083056353247069599689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13166777408470996092799585 9875083056353247069599689)
              ·
                refine ⟨7406312292264935302199767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9875083056353247069599689 7406312292264935302199767)
                ·
                  refine ⟨11109468438397402953299651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7406312292264935302199767 11109468438397402953299651)
                  ·
                    refine ⟨16664202657596104429949477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11109468438397402953299651 16664202657596104429949477)
                    ·
                      refine ⟨3124537998299269580615527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16664202657596104429949477 3124537998299269580615527)
                      ·
                        rfl

theorem cell23_6085016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6085016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085016 prefixEnd_6085016 := by exact prefixLift 6085016
  have htrace : WordTrace (prefixWord ++ tailWord_6085016) baseStart_6085016 baseEnd_6085016 := by
    simpa [prefixWord, tailWord_6085016, baseEnd_6085016] using wordTrace_append hprefix tailTrace_6085016
  have hstable : (prefixWord ++ tailWord_6085016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085016).length < 2 ^ (prefixWord ++ tailWord_6085016).sum := by decide
  have hdescent : baseEnd_6085016 < baseStart_6085016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085044 : List Nat := [2, 5, 2, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6085044 : Nat := 118140960795 + 6085044 * 2 ^ 59
def prefixEnd_6085044 : Nat := 4983230072969 + 3 ^ 40 * 6085044 * 2
def baseEnd_6085044 : Nat := 3124552375757595471065399

theorem tailTrace_6085044 : CollatzResearch.WordTrace tailWord_6085044 prefixEnd_6085044 3124552375757595471065399 := by
  unfold tailWord_6085044
  simp only [CollatzResearch.WordTrace]
  refine ⟨110969893883466152810983093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147959858511288203747977457 110969893883466152810983093)
  ·
    refine ⟨10403427551574951826029665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110969893883466152810983093 10403427551574951826029665)
    ·
      refine ⟨7802570663681213869522249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10403427551574951826029665 7802570663681213869522249)
      ·
        refine ⟨5851927997760910402141687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7802570663681213869522249 5851927997760910402141687)
        ·
          refine ⟨8777891996641365603212531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851927997760910402141687 8777891996641365603212531)
          ·
            refine ⟨13166837994962048404818797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8777891996641365603212531 13166837994962048404818797)
            ·
              refine ⟨4937564248110768151807049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13166837994962048404818797 4937564248110768151807049)
              ·
                refine ⟨3703173186083076113855287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4937564248110768151807049 3703173186083076113855287)
                ·
                  refine ⟨5554759779124614170782931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703173186083076113855287 5554759779124614170782931)
                  ·
                    refine ⟨8332139668686921256174397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5554759779124614170782931 8332139668686921256174397)
                    ·
                      refine ⟨3124552375757595471065399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332139668686921256174397 3124552375757595471065399)
                      ·
                        rfl

theorem cell23_6085044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6085044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085044 prefixEnd_6085044 := by exact prefixLift 6085044
  have htrace : WordTrace (prefixWord ++ tailWord_6085044) baseStart_6085044 baseEnd_6085044 := by
    simpa [prefixWord, tailWord_6085044, baseEnd_6085044] using wordTrace_append hprefix tailTrace_6085044
  have hstable : (prefixWord ++ tailWord_6085044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085044).length < 2 ^ (prefixWord ++ tailWord_6085044).sum := by decide
  have hdescent : baseEnd_6085044 < baseStart_6085044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085059 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 3, 3, 2]
def baseStart_6085059 : Nat := 118140960795 + 6085059 * 2 ^ 59
def prefixEnd_6085059 : Nat := 4983230072969 + 3 ^ 40 * 6085059 * 2
def baseEnd_6085059 : Nat := 3124560077967412912377829

theorem tailTrace_6085059 : CollatzResearch.WordTrace tailWord_6085059 prefixEnd_6085059 3124560077967412912377829 := by
  unfold tailWord_6085059
  simp only [CollatzResearch.WordTrace]
  refine ⟨221940334861877963183762231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147960223241251975455841487 221940334861877963183762231)
  ·
    refine ⟨332910502292816944775643347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221940334861877963183762231 332910502292816944775643347)
    ·
      refine ⟨499365753439225417163465021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332910502292816944775643347 499365753439225417163465021)
      ·
        refine ⟨187262157539709531436299383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 499365753439225417163465021 187262157539709531436299383)
        ·
          refine ⟨280893236309564297154449075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187262157539709531436299383 280893236309564297154449075)
          ·
            refine ⟨421339854464346445731673613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280893236309564297154449075 421339854464346445731673613)
            ·
              refine ⟨158002445424129917149377605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421339854464346445731673613 158002445424129917149377605)
              ·
                refine ⟨29625458517024359465508301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158002445424129917149377605 29625458517024359465508301)
                ·
                  refine ⟨11109546943884134799565613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29625458517024359465508301 11109546943884134799565613)
                  ·
                    refine ⟨4166080103956550549837105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11109546943884134799565613 4166080103956550549837105)
                    ·
                      refine ⟨3124560077967412912377829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4166080103956550549837105 3124560077967412912377829)
                      ·
                        rfl

theorem cell23_6085059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_6085059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085059 prefixEnd_6085059 := by exact prefixLift 6085059
  have htrace : WordTrace (prefixWord ++ tailWord_6085059) baseStart_6085059 baseEnd_6085059 := by
    simpa [prefixWord, tailWord_6085059, baseEnd_6085059] using wordTrace_append hprefix tailTrace_6085059
  have hstable : (prefixWord ++ tailWord_6085059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085059).length < 2 ^ (prefixWord ++ tailWord_6085059).sum := by decide
  have hdescent : baseEnd_6085059 < baseStart_6085059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085060 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_6085060 : Nat := 118140960795 + 6085060 * 2 ^ 59
def prefixEnd_6085060 : Nat := 4983230072969 + 3 ^ 40 * 6085060 * 2
def baseEnd_6085060 : Nat := 1041520197149355802821775

theorem tailTrace_6085060 : CollatzResearch.WordTrace tailWord_6085060 prefixEnd_6085060 1041520197149355802821775 := by
  unfold tailWord_6085060
  simp only [CollatzResearch.WordTrace]
  refine ⟨110970185667437170177274317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147960247556582893569699089 110970185667437170177274317)
  ·
    refine ⟨41613819625288938816477869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110970185667437170177274317 41613819625288938816477869)
    ·
      refine ⟨15605182359483352056179201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41613819625288938816477869 15605182359483352056179201)
      ·
        refine ⟨11703886769612514042134401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15605182359483352056179201 11703886769612514042134401)
        ·
          refine ⟨8777915077209385531600801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11703886769612514042134401 8777915077209385531600801)
          ·
            refine ⟨6583436307907039148700601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8777915077209385531600801 6583436307907039148700601)
            ·
              refine ⟨4937577230930279361525451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6583436307907039148700601 4937577230930279361525451)
              ·
                refine ⟨7406365846395419042288177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937577230930279361525451 7406365846395419042288177)
                ·
                  refine ⟨5554774384796564281716133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7406365846395419042288177 5554774384796564281716133)
                  ·
                    refine ⟨1041520197149355802821775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554774384796564281716133 1041520197149355802821775)
                    ·
                      rfl

theorem cell23_6085060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_6085060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085060 prefixEnd_6085060 := by exact prefixLift 6085060
  have htrace : WordTrace (prefixWord ++ tailWord_6085060) baseStart_6085060 baseEnd_6085060 := by
    simpa [prefixWord, tailWord_6085060, baseEnd_6085060] using wordTrace_append hprefix tailTrace_6085060
  have hstable : (prefixWord ++ tailWord_6085060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085060).length < 2 ^ (prefixWord ++ tailWord_6085060).sum := by decide
  have hdescent : baseEnd_6085060 < baseStart_6085060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085066 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_6085066 : Nat := 118140960795 + 6085066 * 2 ^ 59
def prefixEnd_6085066 : Nat := 4983230072969 + 3 ^ 40 * 6085066 * 2
def baseEnd_6085066 : Nat := 3124563672331994384990297

theorem tailTrace_6085066 : CollatzResearch.WordTrace tailWord_6085066 prefixEnd_6085066 3124563672331994384990297 := by
  unfold tailWord_6085066
  simp only [CollatzResearch.WordTrace]
  refine ⟨55485147543213150844816763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147960393448568402252844701 55485147543213150844816763)
  ·
    refine ⟨83227721314819726267225145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55485147543213150844816763 83227721314819726267225145)
    ·
      refine ⟨62420790986114794700418859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83227721314819726267225145 62420790986114794700418859)
      ·
        refine ⟨93631186479172192050628289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62420790986114794700418859 93631186479172192050628289)
        ·
          refine ⟨70223389859379144037971217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93631186479172192050628289 70223389859379144037971217)
          ·
            refine ⟨52667542394534358028478413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70223389859379144037971217 52667542394534358028478413)
            ·
              refine ⟨19750328397950384260679405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52667542394534358028478413 19750328397950384260679405)
              ·
                refine ⟨7406373149231394097754777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19750328397950384260679405 7406373149231394097754777)
                ·
                  refine ⟨5554779861923545573316083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7406373149231394097754777 5554779861923545573316083)
                  ·
                    refine ⟨8332169792885318359974125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5554779861923545573316083 8332169792885318359974125)
                    ·
                      refine ⟨3124563672331994384990297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332169792885318359974125 3124563672331994384990297)
                      ·
                        rfl

theorem cell23_6085066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_6085066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085066 prefixEnd_6085066 := by exact prefixLift 6085066
  have htrace : WordTrace (prefixWord ++ tailWord_6085066) baseStart_6085066 baseEnd_6085066 := by
    simpa [prefixWord, tailWord_6085066, baseEnd_6085066] using wordTrace_append hprefix tailTrace_6085066
  have hstable : (prefixWord ++ tailWord_6085066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085066).length < 2 ^ (prefixWord ++ tailWord_6085066).sum := by decide
  have hdescent : baseEnd_6085066 < baseStart_6085066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085112 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 7]
def baseStart_6085112 : Nat := 118140960795 + 6085112 * 2 ^ 59
def prefixEnd_6085112 : Nat := 4983230072969 + 3 ^ 40 * 6085112 * 2
def baseEnd_6085112 : Nat := 347176365826900133890565

theorem tailTrace_6085112 : CollatzResearch.WordTrace tailWord_6085112 prefixEnd_6085112 347176365826900133890565 := by
  unfold tailWord_6085112
  simp only [CollatzResearch.WordTrace]
  refine ⟨110971133965342976617720795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147961511953790635490294393 110971133965342976617720795)
  ·
    refine ⟨166456700948014464926581193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110971133965342976617720795 166456700948014464926581193)
    ·
      refine ⟨124842525711010848694935895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166456700948014464926581193 124842525711010848694935895)
      ·
        refine ⟨187263788566516273042403843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124842525711010848694935895 187263788566516273042403843)
        ·
          refine ⟨280895682849774409563605765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187263788566516273042403843 280895682849774409563605765)
          ·
            refine ⟨52667940534332701793176081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280895682849774409563605765 52667940534332701793176081)
            ·
              refine ⟨39500955400749526344882061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52667940534332701793176081 39500955400749526344882061)
              ·
                refine ⟨14812858275281072379330773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39500955400749526344882061 14812858275281072379330773)
                ·
                  refine ⟨347176365826900133890565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14812858275281072379330773 347176365826900133890565)
                  ·
                    rfl

theorem cell23_6085112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 7].length) (baseStart_6085112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085112 prefixEnd_6085112 := by exact prefixLift 6085112
  have htrace : WordTrace (prefixWord ++ tailWord_6085112) baseStart_6085112 baseEnd_6085112 := by
    simpa [prefixWord, tailWord_6085112, baseEnd_6085112] using wordTrace_append hprefix tailTrace_6085112
  have hstable : (prefixWord ++ tailWord_6085112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085112).length < 2 ^ (prefixWord ++ tailWord_6085112).sum := by decide
  have hdescent : baseEnd_6085112 < baseStart_6085112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085179 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 5, 6, 2]
def baseStart_6085179 : Nat := 118140960795 + 6085179 * 2 ^ 59
def prefixEnd_6085179 : Nat := 4983230072969 + 3 ^ 40 * 6085179 * 2
def baseEnd_6085179 : Nat := 3124621695645952442877277

theorem tailTrace_6085179 : CollatzResearch.WordTrace tailWord_6085179 prefixEnd_6085179 3124621695645952442877277 := by
  unfold tailWord_6085179
  simp only [CollatzResearch.WordTrace]
  refine ⟨221944711621443223678130591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147963141080962149118753727 221944711621443223678130591)
  ·
    refine ⟨332917067432164835517195887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221944711621443223678130591 332917067432164835517195887)
    ·
      refine ⟨499375601148247253275793831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332917067432164835517195887 499375601148247253275793831)
      ·
        refine ⟨749063401722370879913690747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499375601148247253275793831 749063401722370879913690747)
        ·
          refine ⟨1123595102583556319870536121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749063401722370879913690747 1123595102583556319870536121)
          ·
            refine ⟨842696326937667239902902091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123595102583556319870536121 842696326937667239902902091)
            ·
              refine ⟨1264044490406500859854353137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842696326937667239902902091 1264044490406500859854353137)
              ·
                refine ⟨948033367804875644890764853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264044490406500859854353137 948033367804875644890764853)
                ·
                  refine ⟨88878128231707091708509205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 948033367804875644890764853 88878128231707091708509205)
                  ·
                    refine ⟨4166162260861269923836369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88878128231707091708509205 4166162260861269923836369)
                    ·
                      refine ⟨3124621695645952442877277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4166162260861269923836369 3124621695645952442877277)
                      ·
                        rfl

theorem cell23_6085179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 6, 2].length) (baseStart_6085179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085179 prefixEnd_6085179 := by exact prefixLift 6085179
  have htrace : WordTrace (prefixWord ++ tailWord_6085179) baseStart_6085179 baseEnd_6085179 := by
    simpa [prefixWord, tailWord_6085179, baseEnd_6085179] using wordTrace_append hprefix tailTrace_6085179
  have hstable : (prefixWord ++ tailWord_6085179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085179).length < 2 ^ (prefixWord ++ tailWord_6085179).sum := by decide
  have hdescent : baseEnd_6085179 < baseStart_6085179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085199 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 3]
def baseStart_6085199 : Nat := 118140960795 + 6085199 * 2 ^ 59
def prefixEnd_6085199 : Nat := 4983230072969 + 3 ^ 40 * 6085199 * 2
def baseEnd_6085199 : Nat := 3124631965259042364627185

theorem tailTrace_6085199 : CollatzResearch.WordTrace tailWord_6085199 prefixEnd_6085199 3124631965259042364627185 := by
  unfold tailWord_6085199
  simp only [CollatzResearch.WordTrace]
  refine ⟨221945441081370767093858651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147963627387580511395905767 221945441081370767093858651)
  ·
    refine ⟨332918161622056150640787977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221945441081370767093858651 332918161622056150640787977)
    ·
      refine ⟨249688621216542112980590983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332918161622056150640787977 249688621216542112980590983)
      ·
        refine ⟨374532931824813169470886475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249688621216542112980590983 374532931824813169470886475)
        ·
          refine ⟨561799397737219754206329713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374532931824813169470886475 561799397737219754206329713)
          ·
            refine ⟨421349548302914815654747285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561799397737219754206329713 421349548302914815654747285)
            ·
              refine ⟨19750760076699131983816279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 421349548302914815654747285 19750760076699131983816279)
              ·
                refine ⟨29626140115048697975724419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19750760076699131983816279 29626140115048697975724419)
                ·
                  refine ⟨44439210172573046963586629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29626140115048697975724419 44439210172573046963586629)
                  ·
                    refine ⟨8332351907357446305672493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44439210172573046963586629 8332351907357446305672493)
                    ·
                      refine ⟨3124631965259042364627185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332351907357446305672493 3124631965259042364627185)
                      ·
                        rfl

theorem cell23_6085199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 3].length) (baseStart_6085199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085199 prefixEnd_6085199 := by exact prefixLift 6085199
  have htrace : WordTrace (prefixWord ++ tailWord_6085199) baseStart_6085199 baseEnd_6085199 := by
    simpa [prefixWord, tailWord_6085199, baseEnd_6085199] using wordTrace_append hprefix tailTrace_6085199
  have hstable : (prefixWord ++ tailWord_6085199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085199).length < 2 ^ (prefixWord ++ tailWord_6085199).sum := by decide
  have hdescent : baseEnd_6085199 < baseStart_6085199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085214 : List Nat := [4, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_6085214 : Nat := 118140960795 + 6085214 * 2 ^ 59
def prefixEnd_6085214 : Nat := 4983230072969 + 3 ^ 40 * 6085214 * 2
def baseEnd_6085214 : Nat := 347182185274317756215513

theorem tailTrace_6085214 : CollatzResearch.WordTrace tailWord_6085214 prefixEnd_6085214 347182185274317756215513 := by
  unfold tailWord_6085214
  simp only [CollatzResearch.WordTrace]
  refine ⟨27743248522039553081956837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147963992117544283103769797 27743248522039553081956837)
  ·
    refine ⟨5201859097882416202866907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27743248522039553081956837 5201859097882416202866907)
    ·
      refine ⟨7802788646823624304300361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5201859097882416202866907 7802788646823624304300361)
      ·
        refine ⟨5852091485117718228225271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7802788646823624304300361 5852091485117718228225271)
        ·
          refine ⟨8778137227676577342337907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5852091485117718228225271 8778137227676577342337907)
          ·
            refine ⟨13167205841514866013506861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8778137227676577342337907 13167205841514866013506861)
            ·
              refine ⟨4937702190568074755065073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13167205841514866013506861 4937702190568074755065073)
              ·
                refine ⟨3703276642926056066298805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4937702190568074755065073 3703276642926056066298805)
                ·
                  refine ⟨347182185274317756215513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3703276642926056066298805 347182185274317756215513)
                  ·
                    rfl

theorem cell23_6085214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_6085214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085214 prefixEnd_6085214 := by exact prefixLift 6085214
  have htrace : WordTrace (prefixWord ++ tailWord_6085214) baseStart_6085214 baseEnd_6085214 := by
    simpa [prefixWord, tailWord_6085214, baseEnd_6085214] using wordTrace_append hprefix tailTrace_6085214
  have hstable : (prefixWord ++ tailWord_6085214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085214).length < 2 ^ (prefixWord ++ tailWord_6085214).sum := by decide
  have hdescent : baseEnd_6085214 < baseStart_6085214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085219 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 6]
def baseStart_6085219 : Nat := 118140960795 + 6085219 * 2 ^ 59
def prefixEnd_6085219 : Nat := 4983230072969 + 3 ^ 40 * 6085219 * 2
def baseEnd_6085219 : Nat := 347182470541348031819677

theorem tailTrace_6085219 : CollatzResearch.WordTrace tailWord_6085219 prefixEnd_6085219 347182470541348031819677 := by
  unfold tailWord_6085219
  simp only [CollatzResearch.WordTrace]
  refine ⟨221946170541298310509586711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147964113694198873673057807 221946170541298310509586711)
  ·
    refine ⟨332919255811947465764380067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221946170541298310509586711 332919255811947465764380067)
    ·
      refine ⟨499378883717921198646570101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332919255811947465764380067 499378883717921198646570101)
      ·
        refine ⟨46816770348555112373115947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 499378883717921198646570101 46816770348555112373115947)
        ·
          refine ⟨70225155522832668559673921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46816770348555112373115947 70225155522832668559673921)
          ·
            refine ⟨52668866642124501419755441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70225155522832668559673921 52668866642124501419755441)
            ·
              refine ⟨39501649981593376064816581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52668866642124501419755441 39501649981593376064816581)
              ·
                refine ⟨7406559371548758012153109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39501649981593376064816581 7406559371548758012153109)
                ·
                  refine ⟨347182470541348031819677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7406559371548758012153109 347182470541348031819677)
                  ·
                    rfl

theorem cell23_6085219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 6].length) (baseStart_6085219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085219 prefixEnd_6085219 := by exact prefixLift 6085219
  have htrace : WordTrace (prefixWord ++ tailWord_6085219) baseStart_6085219 baseEnd_6085219 := by
    simpa [prefixWord, tailWord_6085219, baseEnd_6085219] using wordTrace_append hprefix tailTrace_6085219
  have hstable : (prefixWord ++ tailWord_6085219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085219).length < 2 ^ (prefixWord ++ tailWord_6085219).sum := by decide
  have hdescent : baseEnd_6085219 < baseStart_6085219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085274 : List Nat := [3, 1, 1, 6, 1, 2, 2, 2, 1, 4]
def baseStart_6085274 : Nat := 118140960795 + 6085274 * 2 ^ 59
def prefixEnd_6085274 : Nat := 4983230072969 + 3 ^ 40 * 6085274 * 2
def baseEnd_6085274 : Nat := 1041556825436043190396447

theorem tailTrace_6085274 : CollatzResearch.WordTrace tailWord_6085274 prefixEnd_6085274 1041556825436043190396447 := by
  unfold tailWord_6085274
  simp only [CollatzResearch.WordTrace]
  refine ⟨55487044139024763725709719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147965451037399369935225917 55487044139024763725709719)
  ·
    refine ⟨83230566208537145588564579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55487044139024763725709719 83230566208537145588564579)
    ·
      refine ⟨124845849312805718382846869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83230566208537145588564579 124845849312805718382846869)
      ·
        refine ⟨5852149186537768049195947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124845849312805718382846869 5852149186537768049195947)
        ·
          refine ⟨8778223779806652073793921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5852149186537768049195947 8778223779806652073793921)
          ·
            refine ⟨6583667834854989055345441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8778223779806652073793921 6583667834854989055345441)
            ·
              refine ⟨4937750876141241791509081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6583667834854989055345441 4937750876141241791509081)
              ·
                refine ⟨3703313157105931343631811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4937750876141241791509081 3703313157105931343631811)
                ·
                  refine ⟨5554969735658897015447717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703313157105931343631811 5554969735658897015447717)
                  ·
                    refine ⟨1041556825436043190396447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554969735658897015447717 1041556825436043190396447)
                    ·
                      rfl

theorem cell23_6085274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_6085274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085274 prefixEnd_6085274 := by exact prefixLift 6085274
  have htrace : WordTrace (prefixWord ++ tailWord_6085274) baseStart_6085274 baseEnd_6085274 := by
    simpa [prefixWord, tailWord_6085274, baseEnd_6085274] using wordTrace_append hprefix tailTrace_6085274
  have hstable : (prefixWord ++ tailWord_6085274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085274).length < 2 ^ (prefixWord ++ tailWord_6085274).sum := by decide
  have hdescent : baseEnd_6085274 < baseStart_6085274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085289 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 2, 6, 3]
def baseStart_6085289 : Nat := 118140960795 + 6085289 * 2 ^ 59
def prefixEnd_6085289 : Nat := 4983230072969 + 3 ^ 40 * 6085289 * 2
def baseEnd_6085289 : Nat := 3124678178517947012501771

theorem tailTrace_6085289 : CollatzResearch.WordTrace tailWord_6085289 prefixEnd_6085289 3124678178517947012501771 := by
  unfold tailWord_6085289
  simp only [CollatzResearch.WordTrace]
  refine ⟨221948723651044712464634921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147965815767363141643089947 221948723651044712464634921)
  ·
    refine ⟨166461542738283534348476191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221948723651044712464634921 166461542738283534348476191)
    ·
      refine ⟨249692314107425301522714287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166461542738283534348476191 249692314107425301522714287)
      ·
        refine ⟨374538471161137952284071431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249692314107425301522714287 374538471161137952284071431)
        ·
          refine ⟨561807706741706928426107147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374538471161137952284071431 561807706741706928426107147)
          ·
            refine ⟨842711560112560392639160721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561807706741706928426107147 842711560112560392639160721)
            ·
              refine ⟨632033670084420294479370541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842711560112560392639160721 632033670084420294479370541)
              ·
                refine ⟨237012626281657610429763953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 632033670084420294479370541 237012626281657610429763953)
                ·
                  refine ⟨177759469711243207822322965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237012626281657610429763953 177759469711243207822322965)
                  ·
                    refine ⟨8332475142714525366671389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 177759469711243207822322965 8332475142714525366671389)
                    ·
                      refine ⟨3124678178517947012501771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332475142714525366671389 3124678178517947012501771)
                      ·
                        rfl

theorem cell23_6085289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6, 3].length) (baseStart_6085289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085289 prefixEnd_6085289 := by exact prefixLift 6085289
  have htrace : WordTrace (prefixWord ++ tailWord_6085289) baseStart_6085289 baseEnd_6085289 := by
    simpa [prefixWord, tailWord_6085289, baseEnd_6085289] using wordTrace_append hprefix tailTrace_6085289
  have hstable : (prefixWord ++ tailWord_6085289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085289).length < 2 ^ (prefixWord ++ tailWord_6085289).sum := by decide
  have hdescent : baseEnd_6085289 < baseStart_6085289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085306 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3]
def baseStart_6085306 : Nat := 118140960795 + 6085306 * 2 ^ 59
def prefixEnd_6085306 : Nat := 4983230072969 + 3 ^ 40 * 6085306 * 2
def baseEnd_6085306 : Nat := 3124686907689073445989193

theorem tailTrace_6085306 : CollatzResearch.WordTrace tailWord_6085306 prefixEnd_6085306 3124686907689073445989193 := by
  unfold tailWord_6085306
  simp only [CollatzResearch.WordTrace]
  refine ⟨55487335922995781092000943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147966229127988749578669181 55487335922995781092000943)
  ·
    refine ⟨83231003884493671638001415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55487335922995781092000943 83231003884493671638001415)
    ·
      refine ⟨124846505826740507457002123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83231003884493671638001415 124846505826740507457002123)
      ·
        refine ⟨187269758740110761185503185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124846505826740507457002123 187269758740110761185503185)
        ·
          refine ⟨140452319055083070889127389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187269758740110761185503185 140452319055083070889127389)
          ·
            refine ⟨52669619645656151583422771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140452319055083070889127389 52669619645656151583422771)
            ·
              refine ⟨79004429468484227375134157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52669619645656151583422771 79004429468484227375134157)
              ·
                refine ⟨29626661050681585265675309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79004429468484227375134157 29626661050681585265675309)
                ·
                  refine ⟨11109997894005594474628241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29626661050681585265675309 11109997894005594474628241)
                  ·
                    refine ⟨8332498420504195855971181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11109997894005594474628241 8332498420504195855971181)
                    ·
                      refine ⟨3124686907689073445989193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332498420504195855971181 3124686907689073445989193)
                      ·
                        rfl

theorem cell23_6085306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_6085306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085306 prefixEnd_6085306 := by exact prefixLift 6085306
  have htrace : WordTrace (prefixWord ++ tailWord_6085306) baseStart_6085306 baseEnd_6085306 := by
    simpa [prefixWord, tailWord_6085306, baseEnd_6085306] using wordTrace_append hprefix tailTrace_6085306
  have hstable : (prefixWord ++ tailWord_6085306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085306).length < 2 ^ (prefixWord ++ tailWord_6085306).sum := by decide
  have hdescent : baseEnd_6085306 < baseStart_6085306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085320 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 1, 1, 4]
def baseStart_6085320 : Nat := 118140960795 + 6085320 * 2 ^ 59
def prefixEnd_6085320 : Nat := 4983230072969 + 3 ^ 40 * 6085320 * 2
def baseEnd_6085320 : Nat := 3124694096418236391214129

theorem tailTrace_6085320 : CollatzResearch.WordTrace tailWord_6085320 prefixEnd_6085320 3124694096418236391214129 := by
  unfold tailWord_6085320
  simp only [CollatzResearch.WordTrace]
  refine ⟨110974927156966202379506707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147966569542621603172675609 110974927156966202379506707)
  ·
    refine ⟨166462390735449303569260061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110974927156966202379506707 166462390735449303569260061)
    ·
      refine ⟨62423396525793488838472523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166462390735449303569260061 62423396525793488838472523)
      ·
        refine ⟨93635094788690233257708785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62423396525793488838472523 93635094788690233257708785)
        ·
          refine ⟨70226321091517674943281589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93635094788690233257708785 70226321091517674943281589)
          ·
            refine ⟨6583717602329782025932649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70226321091517674943281589 6583717602329782025932649)
            ·
              refine ⟨4937788201747336519449487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6583717602329782025932649 4937788201747336519449487)
              ·
                refine ⟨7406682302621004779174231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937788201747336519449487 7406682302621004779174231)
                ·
                  refine ⟨11110023453931507168761347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7406682302621004779174231 11110023453931507168761347)
                  ·
                    refine ⟨16665035180897260753142021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11110023453931507168761347 16665035180897260753142021)
                    ·
                      refine ⟨3124694096418236391214129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16665035180897260753142021 3124694096418236391214129)
                      ·
                        rfl

theorem cell23_6085320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_6085320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085320 prefixEnd_6085320 := by exact prefixLift 6085320
  have htrace : WordTrace (prefixWord ++ tailWord_6085320) baseStart_6085320 baseEnd_6085320 := by
    simpa [prefixWord, tailWord_6085320, baseEnd_6085320] using wordTrace_append hprefix tailTrace_6085320
  have hstable : (prefixWord ++ tailWord_6085320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085320).length < 2 ^ (prefixWord ++ tailWord_6085320).sum := by decide
  have hdescent : baseEnd_6085320 < baseStart_6085320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085353 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 2, 1, 3]
def baseStart_6085353 : Nat := 118140960795 + 6085353 * 2 ^ 59
def prefixEnd_6085353 : Nat := 4983230072969 + 3 ^ 40 * 6085353 * 2
def baseEnd_6085353 : Nat := 3124711041279834762101477

theorem tailTrace_6085353 : CollatzResearch.WordTrace tailWord_6085353 prefixEnd_6085353 3124711041279834762101477 := by
  unfold tailWord_6085353
  simp only [CollatzResearch.WordTrace]
  refine ⟨221951057922812851394964713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147967371948541900929976475 221951057922812851394964713)
  ·
    refine ⟨166463293442109638546223535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221951057922812851394964713 166463293442109638546223535)
    ·
      refine ⟨249694940163164457819335303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166463293442109638546223535 249694940163164457819335303)
      ·
        refine ⟨374542410244746686729002955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249694940163164457819335303 374542410244746686729002955)
        ·
          refine ⟨561813615367120030093504433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374542410244746686729002955 561813615367120030093504433)
          ·
            refine ⟨421360211525340022570128325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561813615367120030093504433 421360211525340022570128325)
            ·
              refine ⟨79005039661001254231899061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 421360211525340022570128325 79005039661001254231899061)
              ·
                refine ⟨7406722468218867584240537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79005039661001254231899061 7406722468218867584240537)
                ·
                  refine ⟨5555041851164150688180403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7406722468218867584240537 5555041851164150688180403)
                  ·
                    refine ⟨8332562776746226032270605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5555041851164150688180403 8332562776746226032270605)
                    ·
                      refine ⟨3124711041279834762101477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332562776746226032270605 3124711041279834762101477)
                      ·
                        rfl

theorem cell23_6085353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 1, 3].length) (baseStart_6085353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085353 prefixEnd_6085353 := by exact prefixLift 6085353
  have htrace : WordTrace (prefixWord ++ tailWord_6085353) baseStart_6085353 baseEnd_6085353 := by
    simpa [prefixWord, tailWord_6085353, baseEnd_6085353] using wordTrace_append hprefix tailTrace_6085353
  have hstable : (prefixWord ++ tailWord_6085353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085353).length < 2 ^ (prefixWord ++ tailWord_6085353).sum := by decide
  have hdescent : baseEnd_6085353 < baseStart_6085353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085366 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_6085366 : Nat := 118140960795 + 6085366 * 2 ^ 59
def prefixEnd_6085366 : Nat := 4983230072969 + 3 ^ 40 * 6085366 * 2
def baseEnd_6085366 : Nat := 3124717716528343211238917

theorem tailTrace_6085366 : CollatzResearch.WordTrace tailWord_6085366 prefixEnd_6085366 3124717716528343211238917 := by
  unfold tailWord_6085366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871970754485359663449247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147967688047843836410125301 13871970754485359663449247)
  ·
    refine ⟨20807956131728039495173871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13871970754485359663449247 20807956131728039495173871)
    ·
      refine ⟨31211934197592059242760807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20807956131728039495173871 31211934197592059242760807)
      ·
        refine ⟨46817901296388088864141211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31211934197592059242760807 46817901296388088864141211)
        ·
          refine ⟨70226851944582133296211817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46817901296388088864141211 70226851944582133296211817)
          ·
            refine ⟨52670138958436599972158863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70226851944582133296211817 52670138958436599972158863)
            ·
              refine ⟨79005208437654899958238295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52670138958436599972158863 79005208437654899958238295)
              ·
                refine ⟨118507812656482349937357443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79005208437654899958238295 118507812656482349937357443)
                ·
                  refine ⟨177761718984723524906036165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118507812656482349937357443 177761718984723524906036165)
                  ·
                    refine ⟨33330322309635660919881781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177761718984723524906036165 33330322309635660919881781)
                    ·
                      refine ⟨3124717716528343211238917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33330322309635660919881781 3124717716528343211238917)
                      ·
                        rfl

theorem cell23_6085366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_6085366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085366 prefixEnd_6085366 := by exact prefixLift 6085366
  have htrace : WordTrace (prefixWord ++ tailWord_6085366) baseStart_6085366 baseEnd_6085366 := by
    simpa [prefixWord, tailWord_6085366, baseEnd_6085366] using wordTrace_append hprefix tailTrace_6085366
  have hstable : (prefixWord ++ tailWord_6085366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085366).length < 2 ^ (prefixWord ++ tailWord_6085366).sum := by decide
  have hdescent : baseEnd_6085366 < baseStart_6085366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085369 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 1, 8]
def baseStart_6085369 : Nat := 118140960795 + 6085369 * 2 ^ 59
def prefixEnd_6085369 : Nat := 4983230072969 + 3 ^ 40 * 6085369 * 2
def baseEnd_6085369 : Nat := 1041573085656768899833801

theorem tailTrace_6085369 : CollatzResearch.WordTrace tailWord_6085369 prefixEnd_6085369 1041573085656768899833801 := by
  unfold tailWord_6085369
  simp only [CollatzResearch.WordTrace]
  refine ⟨221951641490754886127547161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147967760993836590751698107 221951641490754886127547161)
  ·
    refine ⟨166463731118066164595660371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221951641490754886127547161 166463731118066164595660371)
    ·
      refine ⟨249695596677099246893490557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166463731118066164595660371 249695596677099246893490557)
      ·
        refine ⟨93635848753912217585058959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249695596677099246893490557 93635848753912217585058959)
        ·
          refine ⟨140453773130868326377588439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93635848753912217585058959 140453773130868326377588439)
          ·
            refine ⟨210680659696302489566382659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140453773130868326377588439 210680659696302489566382659)
            ·
              refine ⟨316020989544453734349573989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210680659696302489566382659 316020989544453734349573989)
              ·
                refine ⟨59253935539585075190545123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316020989544453734349573989 59253935539585075190545123)
                ·
                  refine ⟨88880903309377612785817685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59253935539585075190545123 88880903309377612785817685)
                  ·
                    refine ⟨1041573085656768899833801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88880903309377612785817685 1041573085656768899833801)
                    ·
                      rfl

theorem cell23_6085369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_6085369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085369 prefixEnd_6085369 := by exact prefixLift 6085369
  have htrace : WordTrace (prefixWord ++ tailWord_6085369) baseStart_6085369 baseEnd_6085369 := by
    simpa [prefixWord, tailWord_6085369, baseEnd_6085369] using wordTrace_append hprefix tailTrace_6085369
  have hstable : (prefixWord ++ tailWord_6085369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085369).length < 2 ^ (prefixWord ++ tailWord_6085369).sum := by decide
  have hdescent : baseEnd_6085369 < baseStart_6085369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085380 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_6085380 : Nat := 118140960795 + 6085380 * 2 ^ 59
def prefixEnd_6085380 : Nat := 4983230072969 + 3 ^ 40 * 6085380 * 2
def baseEnd_6085380 : Nat := 3124724905257506156463853

theorem tailTrace_6085380 : CollatzResearch.WordTrace tailWord_6085380 prefixEnd_6085380 3124724905257506156463853 := by
  unfold tailWord_6085380
  simp only [CollatzResearch.WordTrace]
  refine ⟨110976021346857517503098797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147968028462476690004131729 110976021346857517503098797)
  ·
    refine ⟨41616008005071569063662049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110976021346857517503098797 41616008005071569063662049)
    ·
      refine ⟨31212006003803676797746537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41616008005071569063662049 31212006003803676797746537)
      ·
        refine ⟨23409004502852757598309903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31212006003803676797746537 23409004502852757598309903)
        ·
          refine ⟨35113506754279136397464855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23409004502852757598309903 35113506754279136397464855)
          ·
            refine ⟨52670260131418704596197283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35113506754279136397464855 52670260131418704596197283)
            ·
              refine ⟨79005390197128056894295925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52670260131418704596197283 79005390197128056894295925)
              ·
                refine ⟨7406755330980755333840243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79005390197128056894295925 7406755330980755333840243)
                ·
                  refine ⟨11110132996471133000760365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7406755330980755333840243 11110132996471133000760365)
                  ·
                    refine ⟨4166299873676674875285137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11110132996471133000760365 4166299873676674875285137)
                    ·
                      refine ⟨3124724905257506156463853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4166299873676674875285137 3124724905257506156463853)
                      ·
                        rfl

theorem cell23_6085380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_6085380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085380 prefixEnd_6085380 := by exact prefixLift 6085380
  have htrace : WordTrace (prefixWord ++ tailWord_6085380) baseStart_6085380 baseEnd_6085380 := by
    simpa [prefixWord, tailWord_6085380, baseEnd_6085380] using wordTrace_append hprefix tailTrace_6085380
  have hstable : (prefixWord ++ tailWord_6085380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085380).length < 2 ^ (prefixWord ++ tailWord_6085380).sum := by decide
  have hdescent : baseEnd_6085380 < baseStart_6085380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085416 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 9]
def baseStart_6085416 : Nat := 118140960795 + 6085416 * 2 ^ 59
def prefixEnd_6085416 : Nat := 4983230072969 + 3 ^ 40 * 6085416 * 2
def baseEnd_6085416 : Nat := 347193710062340890623743

theorem tailTrace_6085416 : CollatzResearch.WordTrace tailWord_6085416 prefixEnd_6085416 347193710062340890623743 := by
  unfold tailWord_6085416
  simp only [CollatzResearch.WordTrace]
  refine ⟨110976677860792306577254051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147968903814389742103005401 110976677860792306577254051)
  ·
    refine ⟨166465016791188459865881077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110976677860792306577254051 166465016791188459865881077)
    ·
      refine ⟨15606095324173918112426351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166465016791188459865881077 15606095324173918112426351)
      ·
        refine ⟨23409142986260877168639527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15606095324173918112426351 23409142986260877168639527)
        ·
          refine ⟨35113714479391315752959291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23409142986260877168639527 35113714479391315752959291)
          ·
            refine ⟨52670571719086973629438937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35113714479391315752959291 52670571719086973629438937)
            ·
              refine ⟨39502928789315230222079203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52670571719086973629438937 39502928789315230222079203)
              ·
                refine ⟨59254393183972845333118805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39502928789315230222079203 59254393183972845333118805)
                ·
                  refine ⟨347193710062340890623743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59254393183972845333118805 347193710062340890623743)
                  ·
                    rfl

theorem cell23_6085416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 9].length) (baseStart_6085416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085416 prefixEnd_6085416 := by exact prefixLift 6085416
  have htrace : WordTrace (prefixWord ++ tailWord_6085416) baseStart_6085416 baseEnd_6085416 := by
    simpa [prefixWord, tailWord_6085416, baseEnd_6085416] using wordTrace_append hprefix tailTrace_6085416
  have hstable : (prefixWord ++ tailWord_6085416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085416).length < 2 ^ (prefixWord ++ tailWord_6085416).sum := by decide
  have hdescent : baseEnd_6085416 < baseStart_6085416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085456 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_6085456 : Nat := 118140960795 + 6085456 * 2 ^ 59
def prefixEnd_6085456 : Nat := 4983230072969 + 3 ^ 40 * 6085456 * 2
def baseEnd_6085456 : Nat := 3124763929787247859113503

theorem tailTrace_6085456 : CollatzResearch.WordTrace tailWord_6085456 prefixEnd_6085456 3124763929787247859113503 := by
  unfold tailWord_6085456
  simp only [CollatzResearch.WordTrace]
  refine ⟨110977407320719849992982111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147969876427626466657309481 110977407320719849992982111)
  ·
    refine ⟨166466110981079774989473167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110977407320719849992982111 166466110981079774989473167)
    ·
      refine ⟨249699166471619662484209751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166466110981079774989473167 249699166471619662484209751)
      ·
        refine ⟨374548749707429493726314627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249699166471619662484209751 374548749707429493726314627)
        ·
          refine ⟨561823124561144240589471941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374548749707429493726314627 561823124561144240589471941)
          ·
            refine ⟨105341835855214545110525989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 561823124561144240589471941 105341835855214545110525989)
            ·
              refine ⟨19751594222852727208223623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105341835855214545110525989 19751594222852727208223623)
              ·
                refine ⟨29627391334279090812335435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19751594222852727208223623 29627391334279090812335435)
                ·
                  refine ⟨44441087001418636218503153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29627391334279090812335435 44441087001418636218503153)
                  ·
                    refine ⟨33330815251063977163877365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44441087001418636218503153 33330815251063977163877365)
                    ·
                      refine ⟨3124763929787247859113503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33330815251063977163877365 3124763929787247859113503)
                      ·
                        rfl

theorem cell23_6085456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_6085456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085456 prefixEnd_6085456 := by exact prefixLift 6085456
  have htrace : WordTrace (prefixWord ++ tailWord_6085456) baseStart_6085456 baseEnd_6085456 := by
    simpa [prefixWord, tailWord_6085456, baseEnd_6085456] using wordTrace_append hprefix tailTrace_6085456
  have hstable : (prefixWord ++ tailWord_6085456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085456).length < 2 ^ (prefixWord ++ tailWord_6085456).sum := by decide
  have hdescent : baseEnd_6085456 < baseStart_6085456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085460 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_6085460 : Nat := 118140960795 + 6085460 * 2 ^ 59
def prefixEnd_6085460 : Nat := 4983230072969 + 3 ^ 40 * 6085460 * 2
def baseEnd_6085460 : Nat := 3124765983709865843463485

theorem tailTrace_6085460 : CollatzResearch.WordTrace tailWord_6085460 prefixEnd_6085460 3124765983709865843463485 := by
  unfold tailWord_6085460
  simp only [CollatzResearch.WordTrace]
  refine ⟨110977480266712604334554917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147969973688950139112739889 110977480266712604334554917)
  ·
    refine ⟨20808277550008613312729047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110977480266712604334554917 20808277550008613312729047)
    ·
      refine ⟨31212416325012919969093571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20808277550008613312729047 31212416325012919969093571)
      ·
        refine ⟨46818624487519379953640357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31212416325012919969093571 46818624487519379953640357)
        ·
          refine ⟨8778492091409883741307567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46818624487519379953640357 8778492091409883741307567)
          ·
            refine ⟨13167738137114825611961351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8778492091409883741307567 13167738137114825611961351)
            ·
              refine ⟨19751607205672238417942027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13167738137114825611961351 19751607205672238417942027)
              ·
                refine ⟨29627410808508357626913041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19751607205672238417942027 29627410808508357626913041)
                ·
                  refine ⟨22220558106381268220184781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29627410808508357626913041 22220558106381268220184781)
                  ·
                    refine ⟨8332709289892975582569293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22220558106381268220184781 8332709289892975582569293)
                    ·
                      refine ⟨3124765983709865843463485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332709289892975582569293 3124765983709865843463485)
                      ·
                        rfl

theorem cell23_6085460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_6085460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085460 prefixEnd_6085460 := by exact prefixLift 6085460
  have htrace : WordTrace (prefixWord ++ tailWord_6085460) baseStart_6085460 baseEnd_6085460 := by
    simpa [prefixWord, tailWord_6085460, baseEnd_6085460] using wordTrace_append hprefix tailTrace_6085460
  have hstable : (prefixWord ++ tailWord_6085460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085460).length < 2 ^ (prefixWord ++ tailWord_6085460).sum := by decide
  have hdescent : baseEnd_6085460 < baseStart_6085460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085480 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 2, 5]
def baseStart_6085480 : Nat := 118140960795 + 6085480 * 2 ^ 59
def prefixEnd_6085480 : Nat := 4983230072969 + 3 ^ 40 * 6085480 * 2
def baseEnd_6085480 : Nat := 1041592084440985255071131

theorem tailTrace_6085480 : CollatzResearch.WordTrace tailWord_6085480 prefixEnd_6085480 1041592084440985255071131 := by
  unfold tailWord_6085480
  simp only [CollatzResearch.WordTrace]
  refine ⟨110977844996676376042418947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147970459995568501389891929 110977844996676376042418947)
  ·
    refine ⟨166466767495014564063628421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110977844996676376042418947 166466767495014564063628421)
    ·
      refine ⟨31212518905315230761930329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166466767495014564063628421 31212518905315230761930329)
      ·
        refine ⟨23409389178986423071447747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31212518905315230761930329 23409389178986423071447747)
        ·
          refine ⟨35114083768479634607171621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23409389178986423071447747 35114083768479634607171621)
          ·
            refine ⟨6583890706589931488844679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35114083768479634607171621 6583890706589931488844679)
            ·
              refine ⟨9875836059884897233267019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6583890706589931488844679 9875836059884897233267019)
              ·
                refine ⟨14813754089827345849900529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9875836059884897233267019 14813754089827345849900529)
                ·
                  refine ⟨11110315567370509387425397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14813754089827345849900529 11110315567370509387425397)
                  ·
                    refine ⟨1041592084440985255071131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11110315567370509387425397 1041592084440985255071131)
                    ·
                      rfl

theorem cell23_6085480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_6085480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085480 prefixEnd_6085480 := by exact prefixLift 6085480
  have htrace : WordTrace (prefixWord ++ tailWord_6085480) baseStart_6085480 baseEnd_6085480 := by
    simpa [prefixWord, tailWord_6085480, baseEnd_6085480] using wordTrace_append hprefix tailTrace_6085480
  have hstable : (prefixWord ++ tailWord_6085480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085480).length < 2 ^ (prefixWord ++ tailWord_6085480).sum := by decide
  have hdescent : baseEnd_6085480 < baseStart_6085480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085483 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 4]
def baseStart_6085483 : Nat := 118140960795 + 6085483 * 2 ^ 59
def prefixEnd_6085483 : Nat := 4983230072969 + 3 ^ 40 * 6085483 * 2
def baseEnd_6085483 : Nat := 3124777793764919253475879

theorem tailTrace_6085483 : CollatzResearch.WordTrace tailWord_6085483 prefixEnd_6085483 3124777793764919253475879 := by
  unfold tailWord_6085483
  simp only [CollatzResearch.WordTrace]
  refine ⟨221955799412341883597197103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147970532941561255731464735 221955799412341883597197103)
  ·
    refine ⟨332933699118512825395795655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221955799412341883597197103 332933699118512825395795655)
    ·
      refine ⟨499400548677769238093693483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332933699118512825395795655 499400548677769238093693483)
      ·
        refine ⟨749100823016653857140540225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499400548677769238093693483 749100823016653857140540225)
        ·
          refine ⟨561825617262490392855405169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749100823016653857140540225 561825617262490392855405169)
          ·
            refine ⟨421369212946867794641553877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561825617262490392855405169 421369212946867794641553877)
            ·
              refine ⟨9875840928442213936911419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 421369212946867794641553877 9875840928442213936911419)
              ·
                refine ⟨14813761392663320905367129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9875840928442213936911419 14813761392663320905367129)
                ·
                  refine ⟨11110321044497490679025347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14813761392663320905367129 11110321044497490679025347)
                  ·
                    refine ⟨16665481566746236018538021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11110321044497490679025347 16665481566746236018538021)
                    ·
                      refine ⟨3124777793764919253475879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16665481566746236018538021 3124777793764919253475879)
                      ·
                        rfl

theorem cell23_6085483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 4].length) (baseStart_6085483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085483 prefixEnd_6085483 := by exact prefixLift 6085483
  have htrace : WordTrace (prefixWord ++ tailWord_6085483) baseStart_6085483 baseEnd_6085483 := by
    simpa [prefixWord, tailWord_6085483, baseEnd_6085483] using wordTrace_append hprefix tailTrace_6085483
  have hstable : (prefixWord ++ tailWord_6085483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085483).length < 2 ^ (prefixWord ++ tailWord_6085483).sum := by decide
  have hdescent : baseEnd_6085483 < baseStart_6085483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085503 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 3]
def baseStart_6085503 : Nat := 118140960795 + 6085503 * 2 ^ 59
def prefixEnd_6085503 : Nat := 4983230072969 + 3 ^ 40 * 6085503 * 2
def baseEnd_6085503 : Nat := 3124788063378009175225787

theorem tailTrace_6085503 : CollatzResearch.WordTrace tailWord_6085503 prefixEnd_6085503 3124788063378009175225787 := by
  unfold tailWord_6085503
  simp only [CollatzResearch.WordTrace]
  refine ⟨221956528872269427012925163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147971019248179618008616775 221956528872269427012925163)
  ·
    refine ⟨332934793308404140519387745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221956528872269427012925163 332934793308404140519387745)
    ·
      refine ⟨249701094981303105389540809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332934793308404140519387745 249701094981303105389540809)
      ·
        refine ⟨187275821235977329042155607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249701094981303105389540809 187275821235977329042155607)
        ·
          refine ⟨280913731853965993563233411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187275821235977329042155607 280913731853965993563233411)
          ·
            refine ⟨421370597780948990344850117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280913731853965993563233411 421370597780948990344850117)
            ·
              refine ⟨79006987083927935689659397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 421370597780948990344850117 79006987083927935689659397)
              ·
                refine ⟨14813810078236487941811137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79006987083927935689659397 14813810078236487941811137)
                ·
                  refine ⟨11110357558677365956358353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14813810078236487941811137 11110357558677365956358353)
                  ·
                    refine ⟨8332768169008024467268765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11110357558677365956358353 8332768169008024467268765)
                    ·
                      refine ⟨3124788063378009175225787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332768169008024467268765 3124788063378009175225787)
                      ·
                        rfl

theorem cell23_6085503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_6085503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085503 prefixEnd_6085503 := by exact prefixLift 6085503
  have htrace : WordTrace (prefixWord ++ tailWord_6085503) baseStart_6085503 baseEnd_6085503 := by
    simpa [prefixWord, tailWord_6085503, baseEnd_6085503] using wordTrace_append hprefix tailTrace_6085503
  have hstable : (prefixWord ++ tailWord_6085503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085503).length < 2 ^ (prefixWord ++ tailWord_6085503).sum := by decide
  have hdescent : baseEnd_6085503 < baseStart_6085503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085533 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_6085533 : Nat := 118140960795 + 6085533 * 2 ^ 59
def prefixEnd_6085533 : Nat := 4983230072969 + 3 ^ 40 * 6085533 * 2
def baseEnd_6085533 : Nat := 3124803467797644057850649

theorem tailTrace_6085533 : CollatzResearch.WordTrace tailWord_6085533 prefixEnd_6085533 3124803467797644057850649 := by
  unfold tailWord_6085533
  simp only [CollatzResearch.WordTrace]
  refine ⟨221957623062160742136517253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147971748708107161424344835 221957623062160742136517253)
  ·
    refine ⟨41617054324155139150596985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221957623062160742136517253 41617054324155139150596985)
    ·
      refine ⟨31212790743116354362947739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41617054324155139150596985 31212790743116354362947739)
      ·
        refine ⟨46819186114674531544421609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31212790743116354362947739 46819186114674531544421609)
        ·
          refine ⟨35114389586005898658316207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46819186114674531544421609 35114389586005898658316207)
          ·
            refine ⟨52671584379008847987474311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35114389586005898658316207 52671584379008847987474311)
            ·
              refine ⟨79007376568513271981211467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52671584379008847987474311 79007376568513271981211467)
              ·
                refine ⟨118511064852769907971817201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79007376568513271981211467 118511064852769907971817201)
                ·
                  refine ⟨88883298639577430978862901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118511064852769907971817201 88883298639577430978862901)
                  ·
                    refine ⟨8332809247460384154268397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88883298639577430978862901 8332809247460384154268397)
                    ·
                      refine ⟨3124803467797644057850649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332809247460384154268397 3124803467797644057850649)
                      ·
                        rfl

theorem cell23_6085533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_6085533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085533 prefixEnd_6085533 := by exact prefixLift 6085533
  have htrace : WordTrace (prefixWord ++ tailWord_6085533) baseStart_6085533 baseEnd_6085533 := by
    simpa [prefixWord, tailWord_6085533, baseEnd_6085533] using wordTrace_append hprefix tailTrace_6085533
  have hstable : (prefixWord ++ tailWord_6085533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085533).length < 2 ^ (prefixWord ++ tailWord_6085533).sum := by decide
  have hdescent : baseEnd_6085533 < baseStart_6085533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085560 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 4, 3, 2]
def baseStart_6085560 : Nat := 118140960795 + 6085560 * 2 ^ 59
def prefixEnd_6085560 : Nat := 4983230072969 + 3 ^ 40 * 6085560 * 2
def baseEnd_6085560 : Nat := 3124817331775315452213025

theorem tailTrace_6085560 : CollatzResearch.WordTrace tailWord_6085560 prefixEnd_6085560 3124817331775315452213025 := by
  unfold tailWord_6085560
  simp only [CollatzResearch.WordTrace]
  refine ⟨110979303916531462873875067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147972405222041950498500089 110979303916531462873875067)
  ·
    refine ⟨166468955874797194310812601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110979303916531462873875067 166468955874797194310812601)
    ·
      refine ⟨124851716906097895733109451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166468955874797194310812601 124851716906097895733109451)
      ·
        refine ⟨187277575359146843599664177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124851716906097895733109451 187277575359146843599664177)
        ·
          refine ⟨140458181519360132699748133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187277575359146843599664177 140458181519360132699748133)
          ·
            refine ⟨26335909034880024881202775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140458181519360132699748133 26335909034880024881202775)
            ·
              refine ⟨39503863552320037321804163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26335909034880024881202775 39503863552320037321804163)
              ·
                refine ⟨59255795328480055982706245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39503863552320037321804163 59255795328480055982706245)
                ·
                  refine ⟨11110461624090010496757421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59255795328480055982706245 11110461624090010496757421)
                  ·
                    refine ⟨4166423109033753936284033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11110461624090010496757421 4166423109033753936284033)
                    ·
                      refine ⟨3124817331775315452213025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4166423109033753936284033 3124817331775315452213025)
                      ·
                        rfl

theorem cell23_6085560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_6085560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085560 prefixEnd_6085560 := by exact prefixLift 6085560
  have htrace : WordTrace (prefixWord ++ tailWord_6085560) baseStart_6085560 baseEnd_6085560 := by
    simpa [prefixWord, tailWord_6085560, baseEnd_6085560] using wordTrace_append hprefix tailTrace_6085560
  have hstable : (prefixWord ++ tailWord_6085560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085560).length < 2 ^ (prefixWord ++ tailWord_6085560).sum := by decide
  have hdescent : baseEnd_6085560 < baseStart_6085560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085610 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_6085610 : Nat := 118140960795 + 6085610 * 2 ^ 59
def prefixEnd_6085610 : Nat := 4983230072969 + 3 ^ 40 * 6085610 * 2
def baseEnd_6085610 : Nat := 3124843005808040256587795

theorem tailTrace_6085610 : CollatzResearch.WordTrace tailWord_6085610 prefixEnd_6085610 3124843005808040256587795 := by
  unfold tailWord_6085610
  simp only [CollatzResearch.WordTrace]
  refine ⟨55490107870720446071767571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147973620988587856191380189 55490107870720446071767571)
  ·
    refine ⟨83235161806080669107651357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55490107870720446071767571 83235161806080669107651357)
    ·
      refine ⟨31213185677280250915369259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83235161806080669107651357 31213185677280250915369259)
      ·
        refine ⟨46819778515920376373053889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31213185677280250915369259 46819778515920376373053889)
        ·
          refine ⟨35114833886940282279790417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46819778515920376373053889 35114833886940282279790417)
          ·
            refine ⟨26336125415205211709842813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35114833886940282279790417 26336125415205211709842813)
            ·
              refine ⟨9876047030701954391191055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26336125415205211709842813 9876047030701954391191055)
              ·
                refine ⟨14814070546052931586786583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9876047030701954391191055 14814070546052931586786583)
                ·
                  refine ⟨22221105819079397380179875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14814070546052931586786583 22221105819079397380179875)
                  ·
                    refine ⟨33331658728619096070269813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22221105819079397380179875 33331658728619096070269813)
                    ·
                      refine ⟨3124843005808040256587795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33331658728619096070269813 3124843005808040256587795)
                      ·
                        rfl

theorem cell23_6085610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_6085610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085610 prefixEnd_6085610 := by exact prefixLift 6085610
  have htrace : WordTrace (prefixWord ++ tailWord_6085610) baseStart_6085610 baseEnd_6085610 := by
    simpa [prefixWord, tailWord_6085610, baseEnd_6085610] using wordTrace_append hprefix tailTrace_6085610
  have hstable : (prefixWord ++ tailWord_6085610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085610).length < 2 ^ (prefixWord ++ tailWord_6085610).sum := by decide
  have hdescent : baseEnd_6085610 < baseStart_6085610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085617 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 2, 4]
def baseStart_6085617 : Nat := 118140960795 + 6085617 * 2 ^ 59
def prefixEnd_6085617 : Nat := 4983230072969 + 3 ^ 40 * 6085617 * 2
def baseEnd_6085617 : Nat := 1041615533390873909733421

theorem tailTrace_6085617 : CollatzResearch.WordTrace tailWord_6085617 prefixEnd_6085617 1041615533390873909733421 := by
  unfold tailWord_6085617
  simp only [CollatzResearch.WordTrace]
  refine ⟨221960686793856424482575105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147973791195904282988383403 221960686793856424482575105)
  ·
    refine ⟨166470515095392318361931329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221960686793856424482575105 166470515095392318361931329)
    ·
      refine ⟨124852886321544238771448497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166470515095392318361931329 124852886321544238771448497)
      ·
        refine ⟨93639664741158179078586373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124852886321544238771448497 93639664741158179078586373)
        ·
          refine ⟨17557437138967158577234945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93639664741158179078586373 17557437138967158577234945)
          ·
            refine ⟨13168077854225368932926209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17557437138967158577234945 13168077854225368932926209)
            ·
              refine ⟨9876058390669026699694657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13168077854225368932926209 9876058390669026699694657)
              ·
                refine ⟨7407043793001770024770993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9876058390669026699694657 7407043793001770024770993)
                ·
                  refine ⟨5555282844751327518578245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7407043793001770024770993 5555282844751327518578245)
                  ·
                    refine ⟨1041615533390873909733421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5555282844751327518578245 1041615533390873909733421)
                    ·
                      rfl

theorem cell23_6085617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_6085617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085617 prefixEnd_6085617 := by exact prefixLift 6085617
  have htrace : WordTrace (prefixWord ++ tailWord_6085617) baseStart_6085617 baseEnd_6085617 := by
    simpa [prefixWord, tailWord_6085617, baseEnd_6085617] using wordTrace_append hprefix tailTrace_6085617
  have hstable : (prefixWord ++ tailWord_6085617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085617).length < 2 ^ (prefixWord ++ tailWord_6085617).sum := by decide
  have hdescent : baseEnd_6085617 < baseStart_6085617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
