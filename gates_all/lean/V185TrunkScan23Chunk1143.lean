import V185TrunkScan23Chunk1142

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6770538 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_6770538 : Nat := 118140960795 + 6770538 * 2 ^ 59
def prefixEnd_6770538 : Nat := 4983230072969 + 3 ^ 40 * 6770538 * 2
def baseEnd_6770538 : Nat := 3476540283530736472637869

theorem tailTrace_6770538 : CollatzResearch.WordTrace tailWord_6770538 prefixEnd_6770538 3476540283530736472637869 := by
  unfold tailWord_6770538
  simp only [CollatzResearch.WordTrace]
  refine ⟨61735451986376154169126067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164627871963669744451002845 61735451986376154169126067)
  ·
    refine ⟨92603177979564231253689101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61735451986376154169126067 92603177979564231253689101)
    ·
      refine ⟨34726191742336586720133413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92603177979564231253689101 34726191742336586720133413)
      ·
        refine ⟨6511160951688110010025015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34726191742336586720133413 6511160951688110010025015)
        ·
          refine ⟨9766741427532165015037523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6511160951688110010025015 9766741427532165015037523)
          ·
            refine ⟨14650112141298247522556285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9766741427532165015037523 14650112141298247522556285)
            ·
              refine ⟨5493792052986842820958607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14650112141298247522556285 5493792052986842820958607)
              ·
                refine ⟨8240688079480264231437911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5493792052986842820958607 8240688079480264231437911)
                ·
                  refine ⟨12361032119220396347156867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8240688079480264231437911 12361032119220396347156867)
                  ·
                    refine ⟨18541548178830594520735301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12361032119220396347156867 18541548178830594520735301)
                    ·
                      refine ⟨3476540283530736472637869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18541548178830594520735301 3476540283530736472637869)
                      ·
                        rfl

theorem cell23_6770538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_6770538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770538 prefixEnd_6770538 := by exact prefixLift 6770538
  have htrace : WordTrace (prefixWord ++ tailWord_6770538) baseStart_6770538 baseEnd_6770538 := by
    simpa [prefixWord, tailWord_6770538, baseEnd_6770538] using wordTrace_append hprefix tailTrace_6770538
  have hstable : (prefixWord ++ tailWord_6770538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770538).length < 2 ^ (prefixWord ++ tailWord_6770538).sum := by decide
  have hdescent : baseEnd_6770538 < baseStart_6770538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770554 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3]
def baseStart_6770554 : Nat := 118140960795 + 6770554 * 2 ^ 59
def prefixEnd_6770554 : Nat := 4983230072969 + 3 ^ 40 * 6770554 * 2
def baseEnd_6770554 : Nat := 3476548499221208410037795

theorem tailTrace_6770554 : CollatzResearch.WordTrace tailWord_6770554 prefixEnd_6770554 3476548499221208410037795 := by
  unfold tailWord_6770554
  simp only [CollatzResearch.WordTrace]
  refine ⟨61735597878361662852271679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164628261008964434272724477 61735597878361662852271679)
  ·
    refine ⟨92603396817542494278407519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61735597878361662852271679 92603396817542494278407519)
    ·
      refine ⟨138905095226313741417611279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92603396817542494278407519 138905095226313741417611279)
      ·
        refine ⟨208357642839470612126416919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138905095226313741417611279 208357642839470612126416919)
        ·
          refine ⟨312536464259205918189625379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208357642839470612126416919 312536464259205918189625379)
          ·
            refine ⟨468804696388808877284438069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312536464259205918189625379 468804696388808877284438069)
            ·
              refine ⟨43950440286450832245416069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 468804696388808877284438069 43950440286450832245416069)
              ·
                refine ⟨8240707553709531046015513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43950440286450832245416069 8240707553709531046015513)
                ·
                  refine ⟨6180530665282148284511635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8240707553709531046015513 6180530665282148284511635)
                  ·
                    refine ⟨9270795997923222426767453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6180530665282148284511635 9270795997923222426767453)
                    ·
                      refine ⟨3476548499221208410037795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9270795997923222426767453 3476548499221208410037795)
                      ·
                        rfl

theorem cell23_6770554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_6770554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770554 prefixEnd_6770554 := by exact prefixLift 6770554
  have htrace : WordTrace (prefixWord ++ tailWord_6770554) baseStart_6770554 baseEnd_6770554 := by
    simpa [prefixWord, tailWord_6770554, baseEnd_6770554] using wordTrace_append hprefix tailTrace_6770554
  have hstable : (prefixWord ++ tailWord_6770554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770554).length < 2 ^ (prefixWord ++ tailWord_6770554).sum := by decide
  have hdescent : baseEnd_6770554 < baseStart_6770554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770560 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_6770560 : Nat := 118140960795 + 6770560 * 2 ^ 59
def prefixEnd_6770560 : Nat := 4983230072969 + 3 ^ 40 * 6770560 * 2
def baseEnd_6770560 : Nat := 3476551580105135386562767

theorem tailTrace_6770560 : CollatzResearch.WordTrace tailWord_6770560 prefixEnd_6770560 3476551580105135386562767 := by
  unfold tailWord_6770560
  simp only [CollatzResearch.WordTrace]
  refine ⟨123471305175712457216902567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164628406900949942955870089 123471305175712457216902567)
  ·
    refine ⟨185206957763568685825353851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123471305175712457216902567 185206957763568685825353851)
    ·
      refine ⟨277810436645353028738030777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185206957763568685825353851 277810436645353028738030777)
      ·
        refine ⟨208357827484014771553523083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277810436645353028738030777 208357827484014771553523083)
        ·
          refine ⟨312536741226022157330284625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208357827484014771553523083 312536741226022157330284625)
          ·
            refine ⟨234402555919516617997713469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312536741226022157330284625 234402555919516617997713469)
            ·
              refine ⟨87900958469818731749142551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234402555919516617997713469 87900958469818731749142551)
              ·
                refine ⟨131851437704728097623713827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87900958469818731749142551 131851437704728097623713827)
                ·
                  refine ⟨197777156557092146435570741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131851437704728097623713827 197777156557092146435570741)
                  ·
                    refine ⟨18541608427227388728334757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 197777156557092146435570741 18541608427227388728334757)
                    ·
                      refine ⟨3476551580105135386562767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18541608427227388728334757 3476551580105135386562767)
                      ·
                        rfl

theorem cell23_6770560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_6770560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770560 prefixEnd_6770560 := by exact prefixLift 6770560
  have htrace : WordTrace (prefixWord ++ tailWord_6770560) baseStart_6770560 baseEnd_6770560 := by
    simpa [prefixWord, tailWord_6770560, baseEnd_6770560] using wordTrace_append hprefix tailTrace_6770560
  have hstable : (prefixWord ++ tailWord_6770560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770560).length < 2 ^ (prefixWord ++ tailWord_6770560).sum := by decide
  have hdescent : baseEnd_6770560 < baseStart_6770560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770561 : List Nat := [1, 2, 4, 4, 2, 1, 1, 8]
def baseStart_6770561 : Nat := 118140960795 + 6770561 * 2 ^ 59
def prefixEnd_6770561 : Nat := 4983230072969 + 3 ^ 40 * 6770561 * 2
def baseEnd_6770561 : Nat := 128761188651325551209269

theorem tailTrace_6770561 : CollatzResearch.WordTrace tailWord_6770561 prefixEnd_6770561 128761188651325551209269 := by
  unfold tailWord_6770561
  simp only [CollatzResearch.WordTrace]
  refine ⟨246942646824421291604591537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164628431216280861069727691 246942646824421291604591537)
  ·
    refine ⟨185206985118315968703443653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246942646824421291604591537 185206985118315968703443653)
    ·
      refine ⟨34726309709684244131895685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185206985118315968703443653 34726309709684244131895685)
      ·
        refine ⟨6511183070565795774730441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34726309709684244131895685 6511183070565795774730441)
        ·
          refine ⟨4883387302924346831047831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6511183070565795774730441 4883387302924346831047831)
          ·
            refine ⟨7325080954386520246571747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883387302924346831047831 7325080954386520246571747)
            ·
              refine ⟨10987621431579780369857621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325080954386520246571747 10987621431579780369857621)
              ·
                refine ⟨128761188651325551209269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10987621431579780369857621 128761188651325551209269)
                ·
                  rfl

theorem cell23_6770561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 8].length) (baseStart_6770561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770561 prefixEnd_6770561 := by exact prefixLift 6770561
  have htrace : WordTrace (prefixWord ++ tailWord_6770561) baseStart_6770561 baseEnd_6770561 := by
    simpa [prefixWord, tailWord_6770561, baseEnd_6770561] using wordTrace_append hprefix tailTrace_6770561
  have hstable : (prefixWord ++ tailWord_6770561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770561).length < 2 ^ (prefixWord ++ tailWord_6770561).sum := by decide
  have hdescent : baseEnd_6770561 < baseStart_6770561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770564 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_6770564 : Nat := 118140960795 + 6770564 * 2 ^ 59
def prefixEnd_6770564 : Nat := 4983230072969 + 3 ^ 40 * 6770564 * 2
def baseEnd_6770564 : Nat := 3476553634027753370912749

theorem tailTrace_6770564 : CollatzResearch.WordTrace tailWord_6770564 prefixEnd_6770564 3476553634027753370912749 := by
  unfold tailWord_6770564
  simp only [CollatzResearch.WordTrace]
  refine ⟨123471378121705211558475373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164628504162273615411300497 123471378121705211558475373)
  ·
    refine ⟨46301766795639454334428265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123471378121705211558475373 46301766795639454334428265)
    ·
      refine ⟨34726325096729590750821199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46301766795639454334428265 34726325096729590750821199)
      ·
        refine ⟨52089487645094386126231799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34726325096729590750821199 52089487645094386126231799)
        ·
          refine ⟨78134231467641579189347699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52089487645094386126231799 78134231467641579189347699)
          ·
            refine ⟨117201347201462368784021549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78134231467641579189347699 117201347201462368784021549)
            ·
              refine ⟨43950505200548388294008081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117201347201462368784021549 43950505200548388294008081)
              ·
                refine ⟨32962878900411291220506061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43950505200548388294008081 32962878900411291220506061)
                ·
                  refine ⟨12361079587654234207689773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32962878900411291220506061 12361079587654234207689773)
                  ·
                    refine ⟨4635404845370337827883665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12361079587654234207689773 4635404845370337827883665)
                    ·
                      refine ⟨3476553634027753370912749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4635404845370337827883665 3476553634027753370912749)
                      ·
                        rfl

theorem cell23_6770564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_6770564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770564 prefixEnd_6770564 := by exact prefixLift 6770564
  have htrace : WordTrace (prefixWord ++ tailWord_6770564) baseStart_6770564 baseEnd_6770564 := by
    simpa [prefixWord, tailWord_6770564, baseEnd_6770564] using wordTrace_append hprefix tailTrace_6770564
  have hstable : (prefixWord ++ tailWord_6770564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770564).length < 2 ^ (prefixWord ++ tailWord_6770564).sum := by decide
  have hdescent : baseEnd_6770564 < baseStart_6770564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770617 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 7]
def baseStart_6770617 : Nat := 118140960795 + 6770617 * 2 ^ 59
def prefixEnd_6770617 : Nat := 4983230072969 + 3 ^ 40 * 6770617 * 2
def baseEnd_6770617 : Nat := 386286760944715740394445

theorem tailTrace_6770617 : CollatzResearch.WordTrace tailWord_6770617 prefixEnd_6770617 386286760944715740394445 := by
  unfold tailWord_6770617
  simp only [CollatzResearch.WordTrace]
  refine ⟨246944689312218413168630105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164629792874812275445753403 246944689312218413168630105)
  ·
    refine ⟨185208516984163809876472579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246944689312218413168630105 185208516984163809876472579)
    ·
      refine ⟨277812775476245714814708869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185208516984163809876472579 277812775476245714814708869)
      ·
        refine ⟨52089895401796071527757913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277812775476245714814708869 52089895401796071527757913)
        ·
          refine ⟨39067421551347053645818435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52089895401796071527757913 39067421551347053645818435)
          ·
            refine ⟨58601132327020580468727653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39067421551347053645818435 58601132327020580468727653)
            ·
              refine ⟨10987712311316358837886435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58601132327020580468727653 10987712311316358837886435)
              ·
                refine ⟨16481568466974538256829653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10987712311316358837886435 16481568466974538256829653)
                ·
                  refine ⟨386286760944715740394445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16481568466974538256829653 386286760944715740394445)
                  ·
                    rfl

theorem cell23_6770617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 7].length) (baseStart_6770617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770617 prefixEnd_6770617 := by exact prefixLift 6770617
  have htrace : WordTrace (prefixWord ++ tailWord_6770617) baseStart_6770617 baseEnd_6770617 := by
    simpa [prefixWord, tailWord_6770617, baseEnd_6770617] using wordTrace_append hprefix tailTrace_6770617
  have hstable : (prefixWord ++ tailWord_6770617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770617).length < 2 ^ (prefixWord ++ tailWord_6770617).sum := by decide
  have hdescent : baseEnd_6770617 < baseStart_6770617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770647 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 2, 5]
def baseStart_6770647 : Nat := 118140960795 + 6770647 * 2 ^ 59
def prefixEnd_6770647 : Nat := 4983230072969 + 3 ^ 40 * 6770647 * 2
def baseEnd_6770647 : Nat := 1158865417640692182058289

theorem tailTrace_6770647 : CollatzResearch.WordTrace tailWord_6770647 prefixEnd_6770647 1158865417640692182058289 := by
  unfold tailWord_6770647
  simp only [CollatzResearch.WordTrace]
  refine ⟨246945783502109728292222195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164630522334739818861481463 246945783502109728292222195)
  ·
    refine ⟨370418675253164592438333293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246945783502109728292222195 370418675253164592438333293)
    ·
      refine ⟨138907003219936722164374985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370418675253164592438333293 138907003219936722164374985)
      ·
        refine ⟨104180252414952541623281239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138907003219936722164374985 104180252414952541623281239)
        ·
          refine ⟨156270378622428812434921859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104180252414952541623281239 156270378622428812434921859)
          ·
            refine ⟨234405567933643218652382789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156270378622428812434921859 234405567933643218652382789)
            ·
              refine ⟨43951043987558103497321773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234405567933643218652382789 43951043987558103497321773)
              ·
                refine ⟨16481641495334288811495665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43951043987558103497321773 16481641495334288811495665)
                ·
                  refine ⟨12361231121500716608621749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16481641495334288811495665 12361231121500716608621749)
                  ·
                    refine ⟨1158865417640692182058289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12361231121500716608621749 1158865417640692182058289)
                    ·
                      rfl

theorem cell23_6770647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_6770647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770647 prefixEnd_6770647 := by exact prefixLift 6770647
  have htrace : WordTrace (prefixWord ++ tailWord_6770647) baseStart_6770647 baseEnd_6770647 := by
    simpa [prefixWord, tailWord_6770647, baseEnd_6770647] using wordTrace_append hprefix tailTrace_6770647
  have hstable : (prefixWord ++ tailWord_6770647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770647).length < 2 ^ (prefixWord ++ tailWord_6770647).sum := by decide
  have hdescent : baseEnd_6770647 < baseStart_6770647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770684 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 1, 6, 2]
def baseStart_6770684 : Nat := 118140960795 + 6770684 * 2 ^ 59
def prefixEnd_6770684 : Nat := 4983230072969 + 3 ^ 40 * 6770684 * 2
def baseEnd_6770684 : Nat := 3476615251706292901412197

theorem tailTrace_6770684 : CollatzResearch.WordTrace tailWord_6770684 prefixEnd_6770684 3476615251706292901412197 := by
  unfold tailWord_6770684
  simp only [CollatzResearch.WordTrace]
  refine ⟨123473566501487841805659553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164631422001983789074212737 123473566501487841805659553)
  ·
    refine ⟨92605174876115881354244665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123473566501487841805659553 92605174876115881354244665)
    ·
      refine ⟨69453881157086911015683499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92605174876115881354244665 69453881157086911015683499)
      ·
        refine ⟨104180821735630366523525249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69453881157086911015683499 104180821735630366523525249)
        ·
          refine ⟨78135616301722774892643937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104180821735630366523525249 78135616301722774892643937)
          ·
            refine ⟨58601712226292081169482953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78135616301722774892643937 58601712226292081169482953)
            ·
              refine ⟨43951284169719060877112215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58601712226292081169482953 43951284169719060877112215)
              ·
                refine ⟨65926926254578591315668323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43951284169719060877112215 65926926254578591315668323)
                ·
                  refine ⟨98890389381867886973502485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65926926254578591315668323 98890389381867886973502485)
                  ·
                    refine ⟨4635487002275057201882929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98890389381867886973502485 4635487002275057201882929)
                    ·
                      refine ⟨3476615251706292901412197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4635487002275057201882929 3476615251706292901412197)
                      ·
                        rfl

theorem cell23_6770684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_6770684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770684 prefixEnd_6770684 := by exact prefixLift 6770684
  have htrace : WordTrace (prefixWord ++ tailWord_6770684) baseStart_6770684 baseEnd_6770684 := by
    simpa [prefixWord, tailWord_6770684, baseEnd_6770684] using wordTrace_append hprefix tailTrace_6770684
  have hstable : (prefixWord ++ tailWord_6770684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770684).length < 2 ^ (prefixWord ++ tailWord_6770684).sum := by decide
  have hdescent : baseEnd_6770684 < baseStart_6770684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770687 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 3]
def baseStart_6770687 : Nat := 118140960795 + 6770687 * 2 ^ 59
def prefixEnd_6770687 : Nat := 4983230072969 + 3 ^ 40 * 6770687 * 2
def baseEnd_6770687 : Nat := 3476616792148256389674683

theorem tailTrace_6770687 : CollatzResearch.WordTrace tailWord_6770687 prefixEnd_6770687 3476616792148256389674683 := by
  unfold tailWord_6770687
  simp only [CollatzResearch.WordTrace]
  refine ⟨246947242421964815123678315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164631494947976543415785543 246947242421964815123678315)
  ·
    refine ⟨370420863632947222685517473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246947242421964815123678315 370420863632947222685517473)
    ·
      refine ⟨277815647724710417014138105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370420863632947222685517473 277815647724710417014138105)
      ·
        refine ⟨208361735793532812760603579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277815647724710417014138105 208361735793532812760603579)
        ·
          refine ⟨312542603690299219140905369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208361735793532812760603579 312542603690299219140905369)
          ·
            refine ⟨234406952767724414355679027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312542603690299219140905369 234406952767724414355679027)
            ·
              refine ⟨351610429151586621533518541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234406952767724414355679027 351610429151586621533518541)
              ·
                refine ⟨131853910931844983075069453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351610429151586621533518541 131853910931844983075069453)
                ·
                  refine ⟨49445216599441868653151045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131853910931844983075069453 49445216599441868653151045)
                  ·
                    refine ⟨9270978112395350372465821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49445216599441868653151045 9270978112395350372465821)
                    ·
                      refine ⟨3476616792148256389674683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9270978112395350372465821 3476616792148256389674683)
                      ·
                        rfl

theorem cell23_6770687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_6770687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770687 prefixEnd_6770687 := by exact prefixLift 6770687
  have htrace : WordTrace (prefixWord ++ tailWord_6770687) baseStart_6770687 baseEnd_6770687 := by
    simpa [prefixWord, tailWord_6770687, baseEnd_6770687] using wordTrace_append hprefix tailTrace_6770687
  have hstable : (prefixWord ++ tailWord_6770687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770687).length < 2 ^ (prefixWord ++ tailWord_6770687).sum := by decide
  have hdescent : baseEnd_6770687 < baseStart_6770687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770827 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 3, 9]
def baseStart_6770827 : Nat := 118140960795 + 6770827 * 2 ^ 59
def prefixEnd_6770827 : Nat := 4983230072969 + 3 ^ 40 * 6770827 * 2
def baseEnd_6770827 : Nat := 1158896226479961947308013

theorem tailTrace_6770827 : CollatzResearch.WordTrace tailWord_6770827 prefixEnd_6770827 1158896226479961947308013 := by
  unfold tailWord_6770827
  simp only [CollatzResearch.WordTrace]
  refine ⟨246952348641457619033774735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164634899094305079355849823 246952348641457619033774735)
  ·
    refine ⟨370428522962186428550662103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246952348641457619033774735 370428522962186428550662103)
    ·
      refine ⟨555642784443279642825993155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370428522962186428550662103 555642784443279642825993155)
      ·
        refine ⟨833464176664919464238989733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555642784443279642825993155 833464176664919464238989733)
        ·
          refine ⟨156274533124672399544810575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 833464176664919464238989733 156274533124672399544810575)
          ·
            refine ⟨234411799687008599317215863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156274533124672399544810575 234411799687008599317215863)
            ·
              refine ⟨351617699530512898975823795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234411799687008599317215863 351617699530512898975823795)
              ·
                refine ⟨527426549295769348463735693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351617699530512898975823795 527426549295769348463735693)
                ·
                  refine ⟨197784955985913505673900885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527426549295769348463735693 197784955985913505673900885)
                  ·
                    refine ⟨1158896226479961947308013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 197784955985913505673900885 1158896226479961947308013)
                    ·
                      rfl

theorem cell23_6770827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 9].length) (baseStart_6770827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770827 prefixEnd_6770827 := by exact prefixLift 6770827
  have htrace : WordTrace (prefixWord ++ tailWord_6770827) baseStart_6770827 baseEnd_6770827 := by
    simpa [prefixWord, tailWord_6770827, baseEnd_6770827] using wordTrace_append hprefix tailTrace_6770827
  have hstable : (prefixWord ++ tailWord_6770827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770827).length < 2 ^ (prefixWord ++ tailWord_6770827).sum := by decide
  have hdescent : baseEnd_6770827 < baseStart_6770827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770842 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2]
def baseStart_6770842 : Nat := 118140960795 + 6770842 * 2 ^ 59
def prefixEnd_6770842 : Nat := 4983230072969 + 3 ^ 40 * 6770842 * 2
def baseEnd_6770842 : Nat := 3476696381649703283236471

theorem tailTrace_6770842 : CollatzResearch.WordTrace tailWord_6770842 prefixEnd_6770842 3476696381649703283236471 := by
  unfold tailWord_6770842
  simp only [CollatzResearch.WordTrace]
  refine ⟨61738223934100819148892695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164635263824268851063713853 61738223934100819148892695)
  ·
    refine ⟨92607335901151228723339043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61738223934100819148892695 92607335901151228723339043)
    ·
      refine ⟨138911003851726843085008565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92607335901151228723339043 138911003851726843085008565)
      ·
        refine ⟨13022906611099391539219553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138911003851726843085008565 13022906611099391539219553)
        ·
          refine ⟨9767179958324543654414665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13022906611099391539219553 9767179958324543654414665)
          ·
            refine ⟨7325384968743407740810999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9767179958324543654414665 7325384968743407740810999)
            ·
              refine ⟨10988077453115111611216499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325384968743407740810999 10988077453115111611216499)
              ·
                refine ⟨16482116179672667416824749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10988077453115111611216499 16482116179672667416824749)
                ·
                  refine ⟨6180793567377250281309281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16482116179672667416824749 6180793567377250281309281)
                  ·
                    refine ⟨4635595175532937710981961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6180793567377250281309281 4635595175532937710981961)
                    ·
                      refine ⟨3476696381649703283236471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4635595175532937710981961 3476696381649703283236471)
                      ·
                        rfl

theorem cell23_6770842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_6770842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770842 prefixEnd_6770842 := by exact prefixLift 6770842
  have htrace : WordTrace (prefixWord ++ tailWord_6770842) baseStart_6770842 baseEnd_6770842 := by
    simpa [prefixWord, tailWord_6770842, baseEnd_6770842] using wordTrace_append hprefix tailTrace_6770842
  have hstable : (prefixWord ++ tailWord_6770842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770842).length < 2 ^ (prefixWord ++ tailWord_6770842).sum := by decide
  have hdescent : baseEnd_6770842 < baseStart_6770842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770844 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_6770844 : Nat := 118140960795 + 6770844 * 2 ^ 59
def prefixEnd_6770844 : Nat := 4983230072969 + 3 ^ 40 * 6770844 * 2
def baseEnd_6770844 : Nat := 1158899136203670758470487

theorem tailTrace_6770844 : CollatzResearch.WordTrace tailWord_6770844 prefixEnd_6770844 1158899136203670758470487 := by
  unfold tailWord_6770844
  simp only [CollatzResearch.WordTrace]
  refine ⟨123476484341198015468571793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164635312454930687291429057 123476484341198015468571793)
  ·
    refine ⟨92607363255898511601428845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123476484341198015468571793 92607363255898511601428845)
    ·
      refine ⟨34727761220961941850535817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92607363255898511601428845 34727761220961941850535817)
      ·
        refine ⟨26045820915721456387901863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34727761220961941850535817 26045820915721456387901863)
        ·
          refine ⟨39068731373582184581852795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26045820915721456387901863 39068731373582184581852795)
          ·
            refine ⟨58603097060373276872779193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39068731373582184581852795 58603097060373276872779193)
            ·
              refine ⟨43952322795279957654584395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58603097060373276872779193 43952322795279957654584395)
              ·
                refine ⟨65928484192919936481876593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43952322795279957654584395 65928484192919936481876593)
                ·
                  refine ⟨49446363144689952361407445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65928484192919936481876593 49446363144689952361407445)
                  ·
                    refine ⟨1158899136203670758470487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49446363144689952361407445 1158899136203670758470487)
                    ·
                      rfl

theorem cell23_6770844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_6770844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770844 prefixEnd_6770844 := by exact prefixLift 6770844
  have htrace : WordTrace (prefixWord ++ tailWord_6770844) baseStart_6770844 baseEnd_6770844 := by
    simpa [prefixWord, tailWord_6770844, baseEnd_6770844] using wordTrace_append hprefix tailTrace_6770844
  have hstable : (prefixWord ++ tailWord_6770844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770844).length < 2 ^ (prefixWord ++ tailWord_6770844).sum := by decide
  have hdescent : baseEnd_6770844 < baseStart_6770844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770852 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_6770852 : Nat := 118140960795 + 6770852 * 2 ^ 59
def prefixEnd_6770852 : Nat := 4983230072969 + 3 ^ 40 * 6770852 * 2
def baseEnd_6770852 : Nat := 1158900505485416081370475

theorem tailTrace_6770852 : CollatzResearch.WordTrace tailWord_6770852 prefixEnd_6770852 1158900505485416081370475 := by
  unfold tailWord_6770852
  simp only [CollatzResearch.WordTrace]
  refine ⟨123476630233183524151717405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164635506977578032202289873 123476630233183524151717405)
  ·
    refine ⟨46303736337443821556894027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123476630233183524151717405 46303736337443821556894027)
    ·
      refine ⟨69455604506165732335341041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46303736337443821556894027 69455604506165732335341041)
      ·
        refine ⟨52091703379624299251505781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69455604506165732335341041 52091703379624299251505781)
        ·
          refine ⟨4883597191839778054828667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52091703379624299251505781 4883597191839778054828667)
          ·
            refine ⟨7325395787759667082243001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883597191839778054828667 7325395787759667082243001)
            ·
              refine ⟨5494046840819750311682251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7325395787759667082243001 5494046840819750311682251)
              ·
                refine ⟨8241070261229625467523377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5494046840819750311682251 8241070261229625467523377)
                ·
                  refine ⟨6180802695922219100642533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8241070261229625467523377 6180802695922219100642533)
                  ·
                    refine ⟨1158900505485416081370475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6180802695922219100642533 1158900505485416081370475)
                    ·
                      rfl

theorem cell23_6770852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_6770852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770852 prefixEnd_6770852 := by exact prefixLift 6770852
  have htrace : WordTrace (prefixWord ++ tailWord_6770852) baseStart_6770852 baseEnd_6770852 := by
    simpa [prefixWord, tailWord_6770852, baseEnd_6770852] using wordTrace_append hprefix tailTrace_6770852
  have hstable : (prefixWord ++ tailWord_6770852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770852).length < 2 ^ (prefixWord ++ tailWord_6770852).sum := by decide
  have hdescent : baseEnd_6770852 < baseStart_6770852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770892 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6770892 : Nat := 118140960795 + 6770892 * 2 ^ 59
def prefixEnd_6770892 : Nat := 4983230072969 + 3 ^ 40 * 6770892 * 2
def baseEnd_6770892 : Nat := 3476722055682428087611241

theorem tailTrace_6770892 : CollatzResearch.WordTrace tailWord_6770892 prefixEnd_6770892 3476722055682428087611241 := by
  unfold tailWord_6770892
  simp only [CollatzResearch.WordTrace]
  refine ⟨123477359693111067567445465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164636479590814756756593953 123477359693111067567445465)
  ·
    refine ⟨92608019769833300675584099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123477359693111067567445465 92608019769833300675584099)
    ·
      refine ⟨138912029654749951013376149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92608019769833300675584099 138912029654749951013376149)
      ·
        refine ⟨6511501390066403953752007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138912029654749951013376149 6511501390066403953752007)
        ·
          refine ⟨9767252085099605930628011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6511501390066403953752007 9767252085099605930628011)
          ·
            refine ⟨14650878127649408895942017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9767252085099605930628011 14650878127649408895942017)
            ·
              refine ⟨10988158595737056671956513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14650878127649408895942017 10988158595737056671956513)
              ·
                refine ⟨8241118946802792503967385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10988158595737056671956513 8241118946802792503967385)
                ·
                  refine ⟨6180839210102094377975539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8241118946802792503967385 6180839210102094377975539)
                  ·
                    refine ⟨9271258815153141566963309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6180839210102094377975539 9271258815153141566963309)
                    ·
                      refine ⟨3476722055682428087611241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9271258815153141566963309 3476722055682428087611241)
                      ·
                        rfl

theorem cell23_6770892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6770892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770892 prefixEnd_6770892 := by exact prefixLift 6770892
  have htrace : WordTrace (prefixWord ++ tailWord_6770892) baseStart_6770892 baseEnd_6770892 := by
    simpa [prefixWord, tailWord_6770892, baseEnd_6770892] using wordTrace_append hprefix tailTrace_6770892
  have hstable : (prefixWord ++ tailWord_6770892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770892).length < 2 ^ (prefixWord ++ tailWord_6770892).sum := by decide
  have hdescent : baseEnd_6770892 < baseStart_6770892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770938 : List Nat := [3, 1, 1, 1, 1, 6, 2, 3, 5]
def baseStart_6770938 : Nat := 118140960795 + 6770938 * 2 ^ 59
def prefixEnd_6770938 : Nat := 4983230072969 + 3 ^ 40 * 6770938 * 2
def baseEnd_6770938 : Nat := 386305075088059434181781

theorem tailTrace_6770938 : CollatzResearch.WordTrace tailWord_6770938 prefixEnd_6770938 386305075088059434181781 := by
  unfold tailWord_6770938
  simp only [CollatzResearch.WordTrace]
  refine ⟨61739099286013871247766367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164637598096036989994043645 61739099286013871247766367)
  ·
    refine ⟨92608648929020806871649551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61739099286013871247766367 92608648929020806871649551)
    ·
      refine ⟨138912973393531210307474327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92608648929020806871649551 138912973393531210307474327)
      ·
        refine ⟨208369460090296815461211491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138912973393531210307474327 208369460090296815461211491)
        ·
          refine ⟨312554190135445223191817237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208369460090296815461211491 312554190135445223191817237)
          ·
            refine ⟨14650977662598994837116433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 312554190135445223191817237 14650977662598994837116433)
            ·
              refine ⟨10988233246949246127837325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14650977662598994837116433 10988233246949246127837325)
              ·
                refine ⟨4120587467605967297938997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10988233246949246127837325 4120587467605967297938997)
                ·
                  refine ⟨386305075088059434181781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4120587467605967297938997 386305075088059434181781)
                  ·
                    rfl

theorem cell23_6770938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_6770938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770938 prefixEnd_6770938 := by exact prefixLift 6770938
  have htrace : WordTrace (prefixWord ++ tailWord_6770938) baseStart_6770938 baseEnd_6770938 := by
    simpa [prefixWord, tailWord_6770938, baseEnd_6770938] using wordTrace_append hprefix tailTrace_6770938
  have hstable : (prefixWord ++ tailWord_6770938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770938).length < 2 ^ (prefixWord ++ tailWord_6770938).sum := by decide
  have hdescent : baseEnd_6770938 < baseStart_6770938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770944 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_6770944 : Nat := 118140960795 + 6770944 * 2 ^ 59
def prefixEnd_6770944 : Nat := 4983230072969 + 3 ^ 40 * 6770944 * 2
def baseEnd_6770944 : Nat := 3476748756676461884161001

theorem tailTrace_6770944 : CollatzResearch.WordTrace tailWord_6770944 prefixEnd_6770944 3476748756676461884161001 := by
  unfold tailWord_6770944
  simp only [CollatzResearch.WordTrace]
  refine ⟨123478307991016874007891943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164637743988022498677189257 123478307991016874007891943)
  ·
    refine ⟨185217461986525311011837915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123478307991016874007891943 185217461986525311011837915)
    ·
      refine ⟨277826192979787966517756873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185217461986525311011837915 277826192979787966517756873)
      ·
        refine ⟨208369644734840974888317655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277826192979787966517756873 208369644734840974888317655)
        ·
          refine ⟨312554467102261462332476483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208369644734840974888317655 312554467102261462332476483)
          ·
            refine ⟨468831700653392193498714725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312554467102261462332476483 468831700653392193498714725)
            ·
              refine ⟨87905943872511036281009011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 468831700653392193498714725 87905943872511036281009011)
              ·
                refine ⟨131858915808766554421513517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87905943872511036281009011 131858915808766554421513517)
                ·
                  refine ⟨49447093428287457908067569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131858915808766554421513517 49447093428287457908067569)
                  ·
                    refine ⟨37085320071215593431050677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49447093428287457908067569 37085320071215593431050677)
                    ·
                      refine ⟨3476748756676461884161001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37085320071215593431050677 3476748756676461884161001)
                      ·
                        rfl

theorem cell23_6770944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_6770944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770944 prefixEnd_6770944 := by exact prefixLift 6770944
  have htrace : WordTrace (prefixWord ++ tailWord_6770944) baseStart_6770944 baseEnd_6770944 := by
    simpa [prefixWord, tailWord_6770944, baseEnd_6770944] using wordTrace_append hprefix tailTrace_6770944
  have hstable : (prefixWord ++ tailWord_6770944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770944).length < 2 ^ (prefixWord ++ tailWord_6770944).sum := by decide
  have hdescent : baseEnd_6770944 < baseStart_6770944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770989 : List Nat := [1, 5, 3, 1, 3, 1, 1, 3, 5]
def baseStart_6770989 : Nat := 118140960795 + 6770989 * 2 ^ 59
def prefixEnd_6770989 : Nat := 4983230072969 + 3 ^ 40 * 6770989 * 2
def baseEnd_6770989 : Nat := 386307984811768245344255

theorem tailTrace_6770989 : CollatzResearch.WordTrace tailWord_6770989 prefixEnd_6770989 386307984811768245344255 := by
  unfold tailWord_6770989
  simp only [CollatzResearch.WordTrace]
  refine ⟨246958257266870720701172021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164638838177913813800781347 246958257266870720701172021)
  ·
    refine ⟨23152336618769130065734877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246958257266870720701172021 23152336618769130065734877)
    ·
      refine ⟨8682126232038423774650579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23152336618769130065734877 8682126232038423774650579)
      ·
        refine ⟨13023189348057635661975869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8682126232038423774650579 13023189348057635661975869)
        ·
          refine ⟨4883696005521613373240951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13023189348057635661975869 4883696005521613373240951)
          ·
            refine ⟨7325544008282420059861427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883696005521613373240951 7325544008282420059861427)
            ·
              refine ⟨10988316012423630089792141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325544008282420059861427 10988316012423630089792141)
              ·
                refine ⟨4120618504658861283672053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10988316012423630089792141 4120618504658861283672053)
                ·
                  refine ⟨386307984811768245344255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4120618504658861283672053 386307984811768245344255)
                  ·
                    rfl

theorem cell23_6770989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_6770989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770989 prefixEnd_6770989 := by exact prefixLift 6770989
  have htrace : WordTrace (prefixWord ++ tailWord_6770989) baseStart_6770989 baseEnd_6770989 := by
    simpa [prefixWord, tailWord_6770989, baseEnd_6770989] using wordTrace_append hprefix tailTrace_6770989
  have hstable : (prefixWord ++ tailWord_6770989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770989).length < 2 ^ (prefixWord ++ tailWord_6770989).sum := by decide
  have hdescent : baseEnd_6770989 < baseStart_6770989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770991 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 3]
def baseStart_6770991 : Nat := 118140960795 + 6770991 * 2 ^ 59
def prefixEnd_6770991 : Nat := 4983230072969 + 3 ^ 40 * 6770991 * 2
def baseEnd_6770991 : Nat := 3476772890267223200273285

theorem tailTrace_6770991 : CollatzResearch.WordTrace tailWord_6770991 prefixEnd_6770991 3476772890267223200273285 := by
  unfold tailWord_6770991
  simp only [CollatzResearch.WordTrace]
  refine ⟨246958330212863475042744827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164638886808575650028496551 246958330212863475042744827)
  ·
    refine ⟨370437495319295212564117241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246958330212863475042744827 370437495319295212564117241)
    ·
      refine ⟨277828121489471409423087931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370437495319295212564117241 277828121489471409423087931)
      ·
        refine ⟨416742182234207114134631897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277828121489471409423087931 416742182234207114134631897)
        ·
          refine ⟨312556636675655335600973923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416742182234207114134631897 312556636675655335600973923)
          ·
            refine ⟨468834955013483003401460885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312556636675655335600973923 468834955013483003401460885)
            ·
              refine ⟨21976638516257015784443479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 468834955013483003401460885 21976638516257015784443479)
              ·
                refine ⟨32964957774385523676665219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21976638516257015784443479 32964957774385523676665219)
                ·
                  refine ⟨49447436661578285514997829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32964957774385523676665219 49447436661578285514997829)
                  ·
                    refine ⟨9271394374045928534062093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49447436661578285514997829 9271394374045928534062093)
                    ·
                      refine ⟨3476772890267223200273285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9271394374045928534062093 3476772890267223200273285)
                      ·
                        rfl

theorem cell23_6770991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 3].length) (baseStart_6770991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770991 prefixEnd_6770991 := by exact prefixLift 6770991
  have htrace : WordTrace (prefixWord ++ tailWord_6770991) baseStart_6770991 baseEnd_6770991 := by
    simpa [prefixWord, tailWord_6770991, baseEnd_6770991] using wordTrace_append hprefix tailTrace_6770991
  have hstable : (prefixWord ++ tailWord_6770991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770991).length < 2 ^ (prefixWord ++ tailWord_6770991).sum := by decide
  have hdescent : baseEnd_6770991 < baseStart_6770991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771028 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 6]
def baseStart_6771028 : Nat := 118140960795 + 6771028 * 2 ^ 59
def prefixEnd_6771028 : Nat := 4983230072969 + 3 ^ 40 * 6771028 * 2
def baseEnd_6771028 : Nat := 386310209894604395056735

theorem tailTrace_6771028 : CollatzResearch.WordTrace tailWord_6771028 prefixEnd_6771028 386310209894604395056735 := by
  unfold tailWord_6771028
  simp only [CollatzResearch.WordTrace]
  refine ⟨123479839856864715180920869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164639786475819620241227825 123479839856864715180920869)
  ·
    refine ⟨23152469973162134096422663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123479839856864715180920869 23152469973162134096422663)
    ·
      refine ⟨34728704959743201144633995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23152469973162134096422663 34728704959743201144633995)
      ·
        refine ⟨52093057439614801716950993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34728704959743201144633995 52093057439614801716950993)
        ·
          refine ⟨39069793079711101287713245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52093057439614801716950993 39069793079711101287713245)
          ·
            refine ⟨14651172404891662982892467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39069793079711101287713245 14651172404891662982892467)
            ·
              refine ⟨21976758607337494474338701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14651172404891662982892467 21976758607337494474338701)
              ·
                refine ⟨8241284477751560427877013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21976758607337494474338701 8241284477751560427877013)
                ·
                  refine ⟨386310209894604395056735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8241284477751560427877013 386310209894604395056735)
                  ·
                    rfl

theorem cell23_6771028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_6771028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771028 prefixEnd_6771028 := by exact prefixLift 6771028
  have htrace : WordTrace (prefixWord ++ tailWord_6771028) baseStart_6771028 baseEnd_6771028 := by
    simpa [prefixWord, tailWord_6771028, baseEnd_6771028] using wordTrace_append hprefix tailTrace_6771028
  have hstable : (prefixWord ++ tailWord_6771028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771028).length < 2 ^ (prefixWord ++ tailWord_6771028).sum := by decide
  have hdescent : baseEnd_6771028 < baseStart_6771028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771062 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_6771062 : Nat := 118140960795 + 6771062 * 2 ^ 59
def prefixEnd_6771062 : Nat := 4983230072969 + 3 ^ 40 * 6771062 * 2
def baseEnd_6771062 : Nat := 386312149710410269165051

theorem tailTrace_6771062 : CollatzResearch.WordTrace tailWord_6771062 prefixEnd_6771062 386312149710410269165051 := by
  unfold tailWord_6771062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15435057487225390885536215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164640613197070836112386293 15435057487225390885536215)
  ·
    refine ⟨23152586230838086328304323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15435057487225390885536215 23152586230838086328304323)
    ·
      refine ⟨34728879346257129492456485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23152586230838086328304323 34728879346257129492456485)
      ·
        refine ⟨6511664877423211779835591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34728879346257129492456485 6511664877423211779835591)
        ·
          refine ⟨9767497316134817669753387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6511664877423211779835591 9767497316134817669753387)
          ·
            refine ⟨14651245974202226504630081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9767497316134817669753387 14651245974202226504630081)
            ·
              refine ⟨10988434480651669878472561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14651245974202226504630081 10988434480651669878472561)
              ·
                refine ⟨8241325860488752408854421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10988434480651669878472561 8241325860488752408854421)
                ·
                  refine ⟨386312149710410269165051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8241325860488752408854421 386312149710410269165051)
                  ·
                    rfl

theorem cell23_6771062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_6771062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771062 prefixEnd_6771062 := by exact prefixLift 6771062
  have htrace : WordTrace (prefixWord ++ tailWord_6771062) baseStart_6771062 baseEnd_6771062 := by
    simpa [prefixWord, tailWord_6771062, baseEnd_6771062] using wordTrace_append hprefix tailTrace_6771062
  have hstable : (prefixWord ++ tailWord_6771062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771062).length < 2 ^ (prefixWord ++ tailWord_6771062).sum := by decide
  have hdescent : baseEnd_6771062 < baseStart_6771062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771095 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 5, 2, 2]
def baseStart_6771095 : Nat := 118140960795 + 6771095 * 2 ^ 59
def prefixEnd_6771095 : Nat := 4983230072969 + 3 ^ 40 * 6771095 * 2
def baseEnd_6771095 : Nat := 3476826292255290793372807

theorem tailTrace_6771095 : CollatzResearch.WordTrace tailWord_6771095 prefixEnd_6771095 3476826292255290793372807 := by
  unfold tailWord_6771095
  simp only [CollatzResearch.WordTrace]
  refine ⟨246962123404486700804530739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164641415602991133869687159 246962123404486700804530739)
  ·
    refine ⟨370443185106730051206796109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246962123404486700804530739 370443185106730051206796109)
    ·
      refine ⟨138916194415023769202548541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370443185106730051206796109 138916194415023769202548541)
      ·
        refine ⟨52093572905633913450955703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138916194415023769202548541 52093572905633913450955703)
        ·
          refine ⟨78140359358450870176433555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52093572905633913450955703 78140359358450870176433555)
          ·
            refine ⟨117210539037676305264650333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78140359358450870176433555 117210539037676305264650333)
            ·
              refine ⟨43953952139128614474243875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117210539037676305264650333 43953952139128614474243875)
              ·
                refine ⟨65930928208692921711365813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43953952139128614474243875 65930928208692921711365813)
                ·
                  refine ⟨6181024519564961410440545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65930928208692921711365813 6181024519564961410440545)
                  ·
                    refine ⟨4635768389673721057830409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6181024519564961410440545 4635768389673721057830409)
                    ·
                      refine ⟨3476826292255290793372807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4635768389673721057830409 3476826292255290793372807)
                      ·
                        rfl

theorem cell23_6771095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_6771095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771095 prefixEnd_6771095 := by exact prefixLift 6771095
  have htrace : WordTrace (prefixWord ++ tailWord_6771095) baseStart_6771095 baseEnd_6771095 := by
    simpa [prefixWord, tailWord_6771095, baseEnd_6771095] using wordTrace_append hprefix tailTrace_6771095
  have hstable : (prefixWord ++ tailWord_6771095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771095).length < 2 ^ (prefixWord ++ tailWord_6771095).sum := by decide
  have hdescent : baseEnd_6771095 < baseStart_6771095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771108 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_6771108 : Nat := 118140960795 + 6771108 * 2 ^ 59
def prefixEnd_6771108 : Nat := 4983230072969 + 3 ^ 40 * 6771108 * 2
def baseEnd_6771108 : Nat := 3476832967503799242510247

theorem tailTrace_6771108 : CollatzResearch.WordTrace tailWord_6771108 prefixEnd_6771108 3476832967503799242510247 := by
  unfold tailWord_6771108
  simp only [CollatzResearch.WordTrace]
  refine ⟨123481298776719802012376989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164641731702293069349835985 123481298776719802012376989)
  ·
    refine ⟨46305487041269925754641371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123481298776719802012376989 46305487041269925754641371)
    ·
      refine ⟨69458230561904888631962057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46305487041269925754641371 69458230561904888631962057)
      ·
        refine ⟨52093672921428666473971543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69458230561904888631962057 52093672921428666473971543)
        ·
          refine ⟨78140509382142999710957315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52093672921428666473971543 78140509382142999710957315)
          ·
            refine ⟨117210764073214499566435973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78140509382142999710957315 117210764073214499566435973)
            ·
              refine ⟨21977018263727718668706745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117210764073214499566435973 21977018263727718668706745)
              ·
                refine ⟨16482763697795789001530059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21977018263727718668706745 16482763697795789001530059)
                ·
                  refine ⟨24724145546693683502295089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16482763697795789001530059 24724145546693683502295089)
                  ·
                    refine ⟨18543109160020262626721317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24724145546693683502295089 18543109160020262626721317)
                    ·
                      refine ⟨3476832967503799242510247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18543109160020262626721317 3476832967503799242510247)
                      ·
                        rfl

theorem cell23_6771108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_6771108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771108 prefixEnd_6771108 := by exact prefixLift 6771108
  have htrace : WordTrace (prefixWord ++ tailWord_6771108) baseStart_6771108 baseEnd_6771108 := by
    simpa [prefixWord, tailWord_6771108, baseEnd_6771108] using wordTrace_append hprefix tailTrace_6771108
  have hstable : (prefixWord ++ tailWord_6771108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771108).length < 2 ^ (prefixWord ++ tailWord_6771108).sum := by decide
  have hdescent : baseEnd_6771108 < baseStart_6771108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771112 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_6771112 : Nat := 118140960795 + 6771112 * 2 ^ 59
def prefixEnd_6771112 : Nat := 4983230072969 + 3 ^ 40 * 6771112 * 2
def baseEnd_6771112 : Nat := 3476835021426417226860229

theorem tailTrace_6771112 : CollatzResearch.WordTrace tailWord_6771112 prefixEnd_6771112 3476835021426417226860229 := by
  unfold tailWord_6771112
  simp only [CollatzResearch.WordTrace]
  refine ⟨123481371722712556353949795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164641828963616741805266393 123481371722712556353949795)
  ·
    refine ⟨185222057584068834530924693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123481371722712556353949795 185222057584068834530924693)
    ·
      refine ⟨8682283949253226618637095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185222057584068834530924693 8682283949253226618637095)
      ·
        refine ⟨13023425923879839927955643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8682283949253226618637095 13023425923879839927955643)
        ·
          refine ⟨19535138885819759891933465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13023425923879839927955643 19535138885819759891933465)
          ·
            refine ⟨14651354164364819918950099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19535138885819759891933465 14651354164364819918950099)
            ·
              refine ⟨21977031246547229878425149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14651354164364819918950099 21977031246547229878425149)
              ·
                refine ⟨8241386717455211204409431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21977031246547229878425149 8241386717455211204409431)
                ·
                  refine ⟨12362080076182816806614147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8241386717455211204409431 12362080076182816806614147)
                  ·
                    refine ⟨18543120114274225209921221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12362080076182816806614147 18543120114274225209921221)
                    ·
                      refine ⟨3476835021426417226860229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18543120114274225209921221 3476835021426417226860229)
                      ·
                        rfl

theorem cell23_6771112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_6771112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771112 prefixEnd_6771112 := by exact prefixLift 6771112
  have htrace : WordTrace (prefixWord ++ tailWord_6771112) baseStart_6771112 baseEnd_6771112 := by
    simpa [prefixWord, tailWord_6771112, baseEnd_6771112] using wordTrace_append hprefix tailTrace_6771112
  have hstable : (prefixWord ++ tailWord_6771112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771112).length < 2 ^ (prefixWord ++ tailWord_6771112).sum := by decide
  have hdescent : baseEnd_6771112 < baseStart_6771112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771129 : List Nat := [1, 2, 1, 4, 3, 1, 2, 4, 1, 2, 2]
def baseStart_6771129 : Nat := 118140960795 + 6771129 * 2 ^ 59
def prefixEnd_6771129 : Nat := 4983230072969 + 3 ^ 40 * 6771129 * 2
def baseEnd_6771129 : Nat := 3476843750597543660347651

theorem tailTrace_6771129 : CollatzResearch.WordTrace tailWord_6771129 prefixEnd_6771129 3476843750597543660347651 := by
  unfold tailWord_6771129
  simp only [CollatzResearch.WordTrace]
  refine ⟨246963363486363524611268441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164642242324242349740845627 246963363486363524611268441)
  ·
    refine ⟨185222522614772643458451331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246963363486363524611268441 185222522614772643458451331)
    ·
      refine ⟨277833783922158965187676997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185222522614772643458451331 277833783922158965187676997)
      ·
        refine ⟨52093834485404805972689437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277833783922158965187676997 52093834485404805972689437)
        ·
          refine ⟨19535187932026802239758539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52093834485404805972689437 19535187932026802239758539)
          ·
            refine ⟨29302781898040203359637809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19535187932026802239758539 29302781898040203359637809)
            ·
              refine ⟨21977086423530152519728357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29302781898040203359637809 21977086423530152519728357)
              ·
                refine ⟨4120703704411903597449067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21977086423530152519728357 4120703704411903597449067)
                ·
                  refine ⟨6181055556617855396173601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120703704411903597449067 6181055556617855396173601)
                  ·
                    refine ⟨4635791667463391547130201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6181055556617855396173601 4635791667463391547130201)
                    ·
                      refine ⟨3476843750597543660347651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4635791667463391547130201 3476843750597543660347651)
                      ·
                        rfl

theorem cell23_6771129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_6771129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771129 prefixEnd_6771129 := by exact prefixLift 6771129
  have htrace : WordTrace (prefixWord ++ tailWord_6771129) baseStart_6771129 baseEnd_6771129 := by
    simpa [prefixWord, tailWord_6771129, baseEnd_6771129] using wordTrace_append hprefix tailTrace_6771129
  have hstable : (prefixWord ++ tailWord_6771129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771129).length < 2 ^ (prefixWord ++ tailWord_6771129).sum := by decide
  have hdescent : baseEnd_6771129 < baseStart_6771129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771141 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_6771141 : Nat := 118140960795 + 6771141 * 2 ^ 59
def prefixEnd_6771141 : Nat := 4983230072969 + 3 ^ 40 * 6771141 * 2
def baseEnd_6771141 : Nat := 3476849912365397613397595

theorem tailTrace_6771141 : CollatzResearch.WordTrace tailWord_6771141 prefixEnd_6771141 3476849912365397613397595 := by
  unfold tailWord_6771141
  simp only [CollatzResearch.WordTrace]
  refine ⟨246963801162320050660705277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164642534108213367107136851 246963801162320050660705277)
  ·
    refine ⟨92611425435870018997764479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246963801162320050660705277 92611425435870018997764479)
    ·
      refine ⟨138917138153805028496646719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92611425435870018997764479 138917138153805028496646719)
      ·
        refine ⟨208375707230707542744970079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138917138153805028496646719 208375707230707542744970079)
        ·
          refine ⟨312563560846061314117455119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208375707230707542744970079 312563560846061314117455119)
          ·
            refine ⟨468845341269091971176182679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312563560846061314117455119 468845341269091971176182679)
            ·
              refine ⟨703268011903637956764274019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468845341269091971176182679 703268011903637956764274019)
              ·
                refine ⟨1054902017855456935146411029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703268011903637956764274019 1054902017855456935146411029)
                ·
                  refine ⟨49448532086974543834988017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1054902017855456935146411029 49448532086974543834988017)
                  ·
                    refine ⟨37086399065230907876241013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49448532086974543834988017 37086399065230907876241013)
                    ·
                      refine ⟨3476849912365397613397595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37086399065230907876241013 3476849912365397613397595)
                      ·
                        rfl

theorem cell23_6771141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_6771141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771141 prefixEnd_6771141 := by exact prefixLift 6771141
  have htrace : WordTrace (prefixWord ++ tailWord_6771141) baseStart_6771141 baseEnd_6771141 := by
    simpa [prefixWord, tailWord_6771141, baseEnd_6771141] using wordTrace_append hprefix tailTrace_6771141
  have hstable : (prefixWord ++ tailWord_6771141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771141).length < 2 ^ (prefixWord ++ tailWord_6771141).sum := by decide
  have hdescent : baseEnd_6771141 < baseStart_6771141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771145 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 2, 1, 3]
def baseStart_6771145 : Nat := 118140960795 + 6771145 * 2 ^ 59
def prefixEnd_6771145 : Nat := 4983230072969 + 3 ^ 40 * 6771145 * 2
def baseEnd_6771145 : Nat := 3476851966288015597747577

theorem tailTrace_6771145 : CollatzResearch.WordTrace tailWord_6771145 prefixEnd_6771145 3476851966288015597747577 := by
  unfold tailWord_6771145
  simp only [CollatzResearch.WordTrace]
  refine ⟨246963947054305559343850889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164642631369537039562567259 246963947054305559343850889)
  ·
    refine ⟨185222960290729169507888167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246963947054305559343850889 185222960290729169507888167)
    ·
      refine ⟨277834440436093754261832251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185222960290729169507888167 277834440436093754261832251)
      ·
        refine ⟨416751660654140631392748377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277834440436093754261832251 416751660654140631392748377)
        ·
          refine ⟨312563745490605473544561283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416751660654140631392748377 312563745490605473544561283)
          ·
            refine ⟨468845618235908210316841925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312563745490605473544561283 468845618235908210316841925)
            ·
              refine ⟨87908553419232789434407861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 468845618235908210316841925 87908553419232789434407861)
              ·
                refine ⟨8241426883053074009475737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87908553419232789434407861 8241426883053074009475737)
                ·
                  refine ⟨6181070162289805507106803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8241426883053074009475737 6181070162289805507106803)
                  ·
                    refine ⟨9271605243434708260660205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6181070162289805507106803 9271605243434708260660205)
                    ·
                      refine ⟨3476851966288015597747577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9271605243434708260660205 3476851966288015597747577)
                      ·
                        rfl

theorem cell23_6771145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 1, 3].length) (baseStart_6771145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771145 prefixEnd_6771145 := by exact prefixLift 6771145
  have htrace : WordTrace (prefixWord ++ tailWord_6771145) baseStart_6771145 baseEnd_6771145 := by
    simpa [prefixWord, tailWord_6771145, baseEnd_6771145] using wordTrace_append hprefix tailTrace_6771145
  have hstable : (prefixWord ++ tailWord_6771145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771145).length < 2 ^ (prefixWord ++ tailWord_6771145).sum := by decide
  have hdescent : baseEnd_6771145 < baseStart_6771145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771242 : List Nat := [3, 1, 4, 1, 1, 3, 1, 4, 5]
def baseStart_6771242 : Nat := 118140960795 + 6771242 * 2 ^ 59
def prefixEnd_6771242 : Nat := 4983230072969 + 3 ^ 40 * 6771242 * 2
def baseEnd_6771242 : Nat := 386322419323500190914959

theorem tailTrace_6771242 : CollatzResearch.WordTrace tailWord_6771242 prefixEnd_6771242 386322419323500190914959 := by
  unfold tailWord_6771242
  simp only [CollatzResearch.WordTrace]
  refine ⟨61741871233738536227532995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164644989956636096606754653 61741871233738536227532995)
  ·
    refine ⟨92612806850607804341299493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61741871233738536227532995 92612806850607804341299493)
    ·
      refine ⟨17364901284488963313993655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92612806850607804341299493 17364901284488963313993655)
      ·
        refine ⟨26047351926733444970990483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17364901284488963313993655 26047351926733444970990483)
        ·
          refine ⟨39071027890100167456485725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26047351926733444970990483 39071027890100167456485725)
          ·
            refine ⟨14651635458787562796182147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39071027890100167456485725 14651635458787562796182147)
            ·
              refine ⟨21977453188181344194273221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14651635458787562796182147 21977453188181344194273221)
              ·
                refine ⟨4120772472784002036426229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21977453188181344194273221 4120772472784002036426229)
                ·
                  refine ⟨386322419323500190914959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4120772472784002036426229 386322419323500190914959)
                  ·
                    rfl

theorem cell23_6771242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_6771242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771242 prefixEnd_6771242 := by exact prefixLift 6771242
  have htrace : WordTrace (prefixWord ++ tailWord_6771242) baseStart_6771242 baseEnd_6771242 := by
    simpa [prefixWord, tailWord_6771242, baseEnd_6771242] using wordTrace_append hprefix tailTrace_6771242
  have hstable : (prefixWord ++ tailWord_6771242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771242).length < 2 ^ (prefixWord ++ tailWord_6771242).sum := by decide
  have hdescent : baseEnd_6771242 < baseStart_6771242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771248 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_6771248 : Nat := 118140960795 + 6771248 * 2 ^ 59
def prefixEnd_6771248 : Nat := 4983230072969 + 3 ^ 40 * 6771248 * 2
def baseEnd_6771248 : Nat := 3476904854795428694759603

theorem tailTrace_6771248 : CollatzResearch.WordTrace tailWord_6771248 prefixEnd_6771248 3476904854795428694759603 := by
  unfold tailWord_6771248
  simp only [CollatzResearch.WordTrace]
  refine ⟨123483851886466203967425199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164645135848621605289900265 123483851886466203967425199)
  ·
    refine ⟨185225777829699305951137799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123483851886466203967425199 185225777829699305951137799)
    ·
      refine ⟨277838666744548958926706699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185225777829699305951137799 277838666744548958926706699)
      ·
        refine ⟨416758000116823438390060049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277838666744548958926706699 416758000116823438390060049)
        ·
          refine ⟨312568500087617578792545037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416758000116823438390060049 312568500087617578792545037)
          ·
            refine ⟨117213187532856592047204389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312568500087617578792545037 117213187532856592047204389)
            ·
              refine ⟨21977472662410611008850823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117213187532856592047204389 21977472662410611008850823)
              ·
                refine ⟨32966208993615916513276235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21977472662410611008850823 32966208993615916513276235)
                ·
                  refine ⟨49449313490423874769914353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32966208993615916513276235 49449313490423874769914353)
                  ·
                    refine ⟨37086985117817906077435765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49449313490423874769914353 37086985117817906077435765)
                    ·
                      refine ⟨3476904854795428694759603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37086985117817906077435765 3476904854795428694759603)
                      ·
                        rfl

theorem cell23_6771248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_6771248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771248 prefixEnd_6771248 := by exact prefixLift 6771248
  have htrace : WordTrace (prefixWord ++ tailWord_6771248) baseStart_6771248 baseEnd_6771248 := by
    simpa [prefixWord, tailWord_6771248, baseEnd_6771248] using wordTrace_append hprefix tailTrace_6771248
  have hstable : (prefixWord ++ tailWord_6771248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771248).length < 2 ^ (prefixWord ++ tailWord_6771248).sum := by decide
  have hdescent : baseEnd_6771248 < baseStart_6771248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771275 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 4]
def baseStart_6771275 : Nat := 118140960795 + 6771275 * 2 ^ 59
def prefixEnd_6771275 : Nat := 4983230072969 + 3 ^ 40 * 6771275 * 2
def baseEnd_6771275 : Nat := 3476918718773100089121979

theorem tailTrace_6771275 : CollatzResearch.WordTrace tailWord_6771275 prefixEnd_6771275 3476918718773100089121979 := by
  unfold tailWord_6771275
  simp only [CollatzResearch.WordTrace]
  refine ⟨246968688543834591546083279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164645792362556394364055519 246968688543834591546083279)
  ·
    refine ⟨370453032815751887319124919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246968688543834591546083279 370453032815751887319124919)
    ·
      refine ⟨555679549223627830978687379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370453032815751887319124919 555679549223627830978687379)
      ·
        refine ⟨833519323835441746468031069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555679549223627830978687379 833519323835441746468031069)
        ·
          refine ⟨312569746438290654925511651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 833519323835441746468031069 312569746438290654925511651)
          ·
            refine ⟨468854619657435982388267477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312569746438290654925511651 468854619657435982388267477)
            ·
              refine ⟨10988780148221155837225019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 468854619657435982388267477 10988780148221155837225019)
              ·
                refine ⟨16483170222331733755837529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10988780148221155837225019 16483170222331733755837529)
                ·
                  refine ⟨12362377666748800316878147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16483170222331733755837529 12362377666748800316878147)
                  ·
                    refine ⟨18543566500123200475317221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12362377666748800316878147 18543566500123200475317221)
                    ·
                      refine ⟨3476918718773100089121979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18543566500123200475317221 3476918718773100089121979)
                      ·
                        rfl

theorem cell23_6771275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 4].length) (baseStart_6771275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771275 prefixEnd_6771275 := by exact prefixLift 6771275
  have htrace : WordTrace (prefixWord ++ tailWord_6771275) baseStart_6771275 baseEnd_6771275 := by
    simpa [prefixWord, tailWord_6771275, baseEnd_6771275] using wordTrace_append hprefix tailTrace_6771275
  have hstable : (prefixWord ++ tailWord_6771275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771275).length < 2 ^ (prefixWord ++ tailWord_6771275).sum := by decide
  have hdescent : baseEnd_6771275 < baseStart_6771275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771288 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_6771288 : Nat := 118140960795 + 6771288 * 2 ^ 59
def prefixEnd_6771288 : Nat := 4983230072969 + 3 ^ 40 * 6771288 * 2
def baseEnd_6771288 : Nat := 3476925394021608538259419

theorem tailTrace_6771288 : CollatzResearch.WordTrace tailWord_6771288 prefixEnd_6771288 3476925394021608538259419 := by
  unfold tailWord_6771288
  simp only [CollatzResearch.WordTrace]
  refine ⟨123484581346393747383153259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164646108461858329844204345 123484581346393747383153259)
  ·
    refine ⟨185226872019590621074729889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123484581346393747383153259 185226872019590621074729889)
    ·
      refine ⟨138920154014692965806047417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185226872019590621074729889 138920154014692965806047417)
      ·
        refine ⟨104190115511019724354535563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138920154014692965806047417 104190115511019724354535563)
        ·
          refine ⟨156285173266529586531803345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104190115511019724354535563 156285173266529586531803345)
          ·
            refine ⟨117213879949897189898852509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156285173266529586531803345 117213879949897189898852509)
            ·
              refine ⟨43955204981211446212069691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117213879949897189898852509 43955204981211446212069691)
              ·
                refine ⟨65932807471817169318104537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43955204981211446212069691 65932807471817169318104537)
                ·
                  refine ⟨49449605603862876988578403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65932807471817169318104537 49449605603862876988578403)
                  ·
                    refine ⟨74174408405794315482867605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49449605603862876988578403 74174408405794315482867605)
                    ·
                      refine ⟨3476925394021608538259419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74174408405794315482867605 3476925394021608538259419)
                      ·
                        rfl

theorem cell23_6771288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_6771288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771288 prefixEnd_6771288 := by exact prefixLift 6771288
  have htrace : WordTrace (prefixWord ++ tailWord_6771288) baseStart_6771288 baseEnd_6771288 := by
    simpa [prefixWord, tailWord_6771288, baseEnd_6771288] using wordTrace_append hprefix tailTrace_6771288
  have hstable : (prefixWord ++ tailWord_6771288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771288).length < 2 ^ (prefixWord ++ tailWord_6771288).sum := by decide
  have hdescent : baseEnd_6771288 < baseStart_6771288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771295 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 3]
def baseStart_6771295 : Nat := 118140960795 + 6771295 * 2 ^ 59
def prefixEnd_6771295 : Nat := 4983230072969 + 3 ^ 40 * 6771295 * 2
def baseEnd_6771295 : Nat := 3476928988386190010871887

theorem tailTrace_6771295 : CollatzResearch.WordTrace tailWord_6771295 prefixEnd_6771295 3476928988386190010871887 := by
  unfold tailWord_6771295
  simp only [CollatzResearch.WordTrace]
  refine ⟨246969418003762134961811339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164646278669174756641207559 246969418003762134961811339)
  ·
    refine ⟨370454127005643202442717009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246969418003762134961811339 370454127005643202442717009)
    ·
      refine ⟨277840595254232401832037757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370454127005643202442717009 277840595254232401832037757)
      ·
        refine ⟨104190223220337150687014159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277840595254232401832037757 104190223220337150687014159)
        ·
          refine ⟨156285334830505726030521239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104190223220337150687014159 156285334830505726030521239)
          ·
            refine ⟨234428002245758589045781859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156285334830505726030521239 234428002245758589045781859)
            ·
              refine ⟨351642003368637883568672789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234428002245758589045781859 351642003368637883568672789)
              ·
                refine ⟨16483218907904900792281537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 351642003368637883568672789 16483218907904900792281537)
                ·
                  refine ⟨12362414180928675594211153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16483218907904900792281537 12362414180928675594211153)
                  ·
                    refine ⟨9271810635696506695658365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12362414180928675594211153 9271810635696506695658365)
                    ·
                      refine ⟨3476928988386190010871887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9271810635696506695658365 3476928988386190010871887)
                      ·
                        rfl

theorem cell23_6771295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_6771295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771295 prefixEnd_6771295 := by exact prefixLift 6771295
  have htrace : WordTrace (prefixWord ++ tailWord_6771295) baseStart_6771295 baseEnd_6771295 := by
    simpa [prefixWord, tailWord_6771295, baseEnd_6771295] using wordTrace_append hprefix tailTrace_6771295
  have hstable : (prefixWord ++ tailWord_6771295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771295).length < 2 ^ (prefixWord ++ tailWord_6771295).sum := by decide
  have hdescent : baseEnd_6771295 < baseStart_6771295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771365 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_6771365 : Nat := 118140960795 + 6771365 * 2 ^ 59
def prefixEnd_6771365 : Nat := 4983230072969 + 3 ^ 40 * 6771365 * 2
def baseEnd_6771365 : Nat := 3476964932032004736996565

theorem tailTrace_6771365 : CollatzResearch.WordTrace tailWord_6771365 prefixEnd_6771365 3476964932032004736996565 := by
  unfold tailWord_6771365
  simp only [CollatzResearch.WordTrace]
  refine ⟨246971971113508536916859549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164647980742339024611239699 246971971113508536916859549)
  ·
    refine ⟨92614489167565701343822331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246971971113508536916859549 92614489167565701343822331)
    ·
      refine ⟨138921733751348552015733497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92614489167565701343822331 138921733751348552015733497)
      ·
        refine ⟨104191300313511414011800123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138921733751348552015733497 104191300313511414011800123)
        ·
          refine ⟨156286950470267121017700185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104191300313511414011800123 156286950470267121017700185)
          ·
            refine ⟨117215212852700340763275139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156286950470267121017700185 117215212852700340763275139)
            ·
              refine ⟨175822819279050511144912709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117215212852700340763275139 175822819279050511144912709)
              ·
                refine ⟨32966778614821970839671133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175822819279050511144912709 32966778614821970839671133)
                ·
                  refine ⟨12362541980558239064876675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32966778614821970839671133 12362541980558239064876675)
                  ·
                    refine ⟨18543812970837358597315013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12362541980558239064876675 18543812970837358597315013)
                    ·
                      refine ⟨3476964932032004736996565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18543812970837358597315013 3476964932032004736996565)
                      ·
                        rfl

theorem cell23_6771365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_6771365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771365 prefixEnd_6771365 := by exact prefixLift 6771365
  have htrace : WordTrace (prefixWord ++ tailWord_6771365) baseStart_6771365 baseEnd_6771365 := by
    simpa [prefixWord, tailWord_6771365, baseEnd_6771365] using wordTrace_append hprefix tailTrace_6771365
  have hstable : (prefixWord ++ tailWord_6771365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771365).length < 2 ^ (prefixWord ++ tailWord_6771365).sum := by decide
  have hdescent : baseEnd_6771365 < baseStart_6771365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771402 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_6771402 : Nat := 118140960795 + 6771402 * 2 ^ 59
def prefixEnd_6771402 : Nat := 4983230072969 + 3 ^ 40 * 6771402 * 2
def baseEnd_6771402 : Nat := 3476983930816221092233895

theorem tailTrace_6771402 : CollatzResearch.WordTrace tailWord_6771402 prefixEnd_6771402 3476983930816221092233895 := by
  unfold tailWord_6771402
  simp only [CollatzResearch.WordTrace]
  refine ⟨61743330153593623058989115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164648880409582994823970973 61743330153593623058989115)
  ·
    refine ⟨92614995230390434588483673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61743330153593623058989115 92614995230390434588483673)
    ·
      refine ⟨69461246422792825941362755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92614995230390434588483673 69461246422792825941362755)
      ·
        refine ⟨104191869634189238912044133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69461246422792825941362755 104191869634189238912044133)
        ·
          refine ⟨19535975556410482296008275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104191869634189238912044133 19535975556410482296008275)
          ·
            refine ⟨29303963334615723444012413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19535975556410482296008275 29303963334615723444012413)
            ·
              refine ⟨10988986250480896291504655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29303963334615723444012413 10988986250480896291504655)
              ·
                refine ⟨16483479375721344437256983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10988986250480896291504655 16483479375721344437256983)
                ·
                  refine ⟨24725219063582016655885475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16483479375721344437256983 24725219063582016655885475)
                  ·
                    refine ⟨37087828595373024983828213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24725219063582016655885475 37087828595373024983828213)
                    ·
                      refine ⟨3476983930816221092233895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37087828595373024983828213 3476983930816221092233895)
                      ·
                        rfl

theorem cell23_6771402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_6771402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771402 prefixEnd_6771402 := by exact prefixLift 6771402
  have htrace : WordTrace (prefixWord ++ tailWord_6771402) baseStart_6771402 baseEnd_6771402 := by
    simpa [prefixWord, tailWord_6771402, baseEnd_6771402] using wordTrace_append hprefix tailTrace_6771402
  have hstable : (prefixWord ++ tailWord_6771402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771402).length < 2 ^ (prefixWord ++ tailWord_6771402).sum := by decide
  have hdescent : baseEnd_6771402 < baseStart_6771402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771410 : List Nat := [3, 2, 2, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_6771410 : Nat := 118140960795 + 6771410 * 2 ^ 59
def prefixEnd_6771410 : Nat := 4983230072969 + 3 ^ 40 * 6771410 * 2
def baseEnd_6771410 : Nat := 3476988038661457060933859

theorem tailTrace_6771410 : CollatzResearch.WordTrace tailWord_6771410 prefixEnd_6771410 3476988038661457060933859 := by
  unfold tailWord_6771410
  simp only [CollatzResearch.WordTrace]
  refine ⟨61743403099586377400561921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164649074932230339734831789 61743403099586377400561921)
  ·
    refine ⟨46307552324689783050421441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61743403099586377400561921 46307552324689783050421441)
    ·
      refine ⟨34730664243517337287816081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46307552324689783050421441 34730664243517337287816081)
      ·
        refine ⟨26047998182638002965862061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34730664243517337287816081 26047998182638002965862061)
        ·
          refine ⟨9767999318489251112198273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26047998182638002965862061 9767999318489251112198273)
          ·
            refine ⟨7325999488866938334148705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9767999318489251112198273 7325999488866938334148705)
            ·
              refine ⟨5494499616650203750611529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7325999488866938334148705 5494499616650203750611529)
              ·
                refine ⟨4120874712487652812958647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5494499616650203750611529 4120874712487652812958647)
                ·
                  refine ⟨6181312068731479219437971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120874712487652812958647 6181312068731479219437971)
                  ·
                    refine ⟨9271968103097218829156957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6181312068731479219437971 9271968103097218829156957)
                    ·
                      refine ⟨3476988038661457060933859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9271968103097218829156957 3476988038661457060933859)
                      ·
                        rfl

theorem cell23_6771410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_6771410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771410 prefixEnd_6771410 := by exact prefixLift 6771410
  have htrace : WordTrace (prefixWord ++ tailWord_6771410) baseStart_6771410 baseEnd_6771410 := by
    simpa [prefixWord, tailWord_6771410, baseEnd_6771410] using wordTrace_append hprefix tailTrace_6771410
  have hstable : (prefixWord ++ tailWord_6771410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771410).length < 2 ^ (prefixWord ++ tailWord_6771410).sum := by decide
  have hdescent : baseEnd_6771410 < baseStart_6771410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771465 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 2, 6]
def baseStart_6771465 : Nat := 118140960795 + 6771465 * 2 ^ 59
def prefixEnd_6771465 : Nat := 4983230072969 + 3 ^ 40 * 6771465 * 2
def baseEnd_6771465 : Nat := 1159005426699151448582035

theorem tailTrace_6771465 : CollatzResearch.WordTrace tailWord_6771465 prefixEnd_6771465 1159005426699151448582035 := by
  unfold tailWord_6771465
  simp only [CollatzResearch.WordTrace]
  refine ⟨246975618413146253995499849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164650412275430835996999899 246975618413146253995499849)
  ·
    refine ⟨185231713809859690496624887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246975618413146253995499849 185231713809859690496624887)
    ·
      refine ⟨277847570714789535744937331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185231713809859690496624887 277847570714789535744937331)
      ·
        refine ⟨416771356072184303617405997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277847570714789535744937331 416771356072184303617405997)
        ·
          refine ⟨156289258527069113856527249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416771356072184303617405997 156289258527069113856527249)
          ·
            refine ⟨117216943895301835392395437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156289258527069113856527249 117216943895301835392395437)
            ·
              refine ⟨43956353960738188272148289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117216943895301835392395437 43956353960738188272148289)
              ·
                refine ⟨32967265470553641204111217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43956353960738188272148289 32967265470553641204111217)
                ·
                  refine ⟨24725449102915230903083413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32967265470553641204111217 24725449102915230903083413)
                  ·
                    refine ⟨1159005426699151448582035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24725449102915230903083413 1159005426699151448582035)
                    ·
                      rfl

theorem cell23_6771465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_6771465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771465 prefixEnd_6771465 := by exact prefixLift 6771465
  have htrace : WordTrace (prefixWord ++ tailWord_6771465) baseStart_6771465 baseEnd_6771465 := by
    simpa [prefixWord, tailWord_6771465, baseEnd_6771465] using wordTrace_append hprefix tailTrace_6771465
  have hstable : (prefixWord ++ tailWord_6771465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771465).length < 2 ^ (prefixWord ++ tailWord_6771465).sum := by decide
  have hdescent : baseEnd_6771465 < baseStart_6771465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771525 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_6771525 : Nat := 118140960795 + 6771525 * 2 ^ 59
def prefixEnd_6771525 : Nat := 4983230072969 + 3 ^ 40 * 6771525 * 2
def baseEnd_6771525 : Nat := 1159015696312241370331943

theorem tailTrace_6771525 : CollatzResearch.WordTrace tailWord_6771525 prefixEnd_6771525 1159015696312241370331943 := by
  unfold tailWord_6771525
  simp only [CollatzResearch.WordTrace]
  refine ⟨246977806792928884242684029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164651871195285922828456019 246977806792928884242684029)
  ·
    refine ⟨92616677547348331591006511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246977806792928884242684029 92616677547348331591006511)
    ·
      refine ⟨138925016321022497386509767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92616677547348331591006511 138925016321022497386509767)
      ·
        refine ⟨208387524481533746079764651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138925016321022497386509767 208387524481533746079764651)
        ·
          refine ⟨312581286722300619119646977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208387524481533746079764651 312581286722300619119646977)
          ·
            refine ⟨234435965041725464339735233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312581286722300619119646977 234435965041725464339735233)
            ·
              refine ⟨175826973781294098254801425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234435965041725464339735233 175826973781294098254801425)
              ·
                refine ⟨131870230335970573691101069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175826973781294098254801425 131870230335970573691101069)
                ·
                  refine ⟨49451336375988965134162901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131870230335970573691101069 49451336375988965134162901)
                  ·
                    refine ⟨1159015696312241370331943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49451336375988965134162901 1159015696312241370331943)
                    ·
                      rfl

theorem cell23_6771525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_6771525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771525 prefixEnd_6771525 := by exact prefixLift 6771525
  have htrace : WordTrace (prefixWord ++ tailWord_6771525) baseStart_6771525 baseEnd_6771525 := by
    simpa [prefixWord, tailWord_6771525, baseEnd_6771525] using wordTrace_append hprefix tailTrace_6771525
  have hstable : (prefixWord ++ tailWord_6771525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771525).length < 2 ^ (prefixWord ++ tailWord_6771525).sum := by decide
  have hdescent : baseEnd_6771525 < baseStart_6771525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771559 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 2, 5]
def baseStart_6771559 : Nat := 118140960795 + 6771559 * 2 ^ 59
def prefixEnd_6771559 : Nat := 4983230072969 + 3 ^ 40 * 6771559 * 2
def baseEnd_6771559 : Nat := 1159021515759658992656891

theorem tailTrace_6771559 : CollatzResearch.WordTrace tailWord_6771559 prefixEnd_6771559 1159021515759658992656891 := by
  unfold tailWord_6771559
  simp only [CollatzResearch.WordTrace]
  refine ⟨246979046874805708049421731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164652697916537138699614487 246979046874805708049421731)
  ·
    refine ⟨370468570312208562074132597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246979046874805708049421731 370468570312208562074132597)
    ·
      refine ⟨34731428466769552694449931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 370468570312208562074132597 34731428466769552694449931)
      ·
        refine ⟨52097142700154329041674897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34731428466769552694449931 52097142700154329041674897)
        ·
          refine ⟨39072857025115746781256173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52097142700154329041674897 39072857025115746781256173)
          ·
            refine ⟨14652321384418405042971065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39072857025115746781256173 14652321384418405042971065)
            ·
              refine ⟨10989241038313803782228299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14652321384418405042971065 10989241038313803782228299)
              ·
                refine ⟨16483861557470705673342449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10989241038313803782228299 16483861557470705673342449)
                ·
                  refine ⟨12362896168103029255006837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16483861557470705673342449 12362896168103029255006837)
                  ·
                    refine ⟨1159021515759658992656891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12362896168103029255006837 1159021515759658992656891)
                    ·
                      rfl

theorem cell23_6771559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_6771559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771559 prefixEnd_6771559 := by exact prefixLift 6771559
  have htrace : WordTrace (prefixWord ++ tailWord_6771559) baseStart_6771559 baseEnd_6771559 := by
    simpa [prefixWord, tailWord_6771559, baseEnd_6771559] using wordTrace_append hprefix tailTrace_6771559
  have hstable : (prefixWord ++ tailWord_6771559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771559).length < 2 ^ (prefixWord ++ tailWord_6771559).sum := by decide
  have hdescent : baseEnd_6771559 < baseStart_6771559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771636 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 8]
def baseStart_6771636 : Nat := 118140960795 + 6771636 * 2 ^ 59
def prefixEnd_6771636 : Nat := 4983230072969 + 3 ^ 40 * 6771636 * 2
def baseEnd_6771636 : Nat := 386344898365485908523091

theorem tailTrace_6771636 : CollatzResearch.WordTrace tailWord_6771636 prefixEnd_6771636 386344898365485908523091 := by
  unfold tailWord_6771636
  simp only [CollatzResearch.WordTrace]
  refine ⟨123490927647763375099987381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164654570197017833466649841 123490927647763375099987381)
  ·
    refine ⟨11577274466977816415623817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123490927647763375099987381 11577274466977816415623817)
    ·
      refine ⟨8682955850233362311717863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11577274466977816415623817 8682955850233362311717863)
      ·
        refine ⟨13024433775350043467576795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8682955850233362311717863 13024433775350043467576795)
        ·
          refine ⟨19536650663025065201365193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13024433775350043467576795 19536650663025065201365193)
          ·
            refine ⟨14652487997268798901023895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19536650663025065201365193 14652487997268798901023895)
            ·
              refine ⟨21978731995903198351535843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14652487997268798901023895 21978731995903198351535843)
              ·
                refine ⟨32968097993854797527303765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21978731995903198351535843 32968097993854797527303765)
                ·
                  refine ⟨386344898365485908523091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32968097993854797527303765 386344898365485908523091)
                  ·
                    rfl

theorem cell23_6771636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_6771636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771636 prefixEnd_6771636 := by exact prefixLift 6771636
  have htrace : WordTrace (prefixWord ++ tailWord_6771636) baseStart_6771636 baseEnd_6771636 := by
    simpa [prefixWord, tailWord_6771636, baseEnd_6771636] using wordTrace_append hprefix tailTrace_6771636
  have hstable : (prefixWord ++ tailWord_6771636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771636).length < 2 ^ (prefixWord ++ tailWord_6771636).sum := by decide
  have hdescent : baseEnd_6771636 < baseStart_6771636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771666 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_6771666 : Nat := 118140960795 + 6771666 * 2 ^ 59
def prefixEnd_6771666 : Nat := 4983230072969 + 3 ^ 40 * 6771666 * 2
def baseEnd_6771666 : Nat := 1159039829903002686444227

theorem tailTrace_6771666 : CollatzResearch.WordTrace tailWord_6771666 prefixEnd_6771666 1159039829903002686444227 := by
  unfold tailWord_6771666
  simp only [CollatzResearch.WordTrace]
  refine ⟨61745737371354516330891713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164655299656945376882377901 61745737371354516330891713)
  ·
    refine ⟨46309303028515887248168785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61745737371354516330891713 46309303028515887248168785)
    ·
      refine ⟨34731977271386915436126589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46309303028515887248168785 34731977271386915436126589)
      ·
        refine ⟨13024491476770093288547471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34731977271386915436126589 13024491476770093288547471)
        ·
          refine ⟨19536737215155139932821207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13024491476770093288547471 19536737215155139932821207)
          ·
            refine ⟨29305105822732709899231811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19536737215155139932821207 29305105822732709899231811)
            ·
              refine ⟨43957658734099064848847717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29305105822732709899231811 43957658734099064848847717)
              ·
                refine ⟨8242061012643574659158947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43957658734099064848847717 8242061012643574659158947)
                ·
                  refine ⟨12363091518965361988738421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8242061012643574659158947 12363091518965361988738421)
                  ·
                    refine ⟨1159039829903002686444227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12363091518965361988738421 1159039829903002686444227)
                    ·
                      rfl

theorem cell23_6771666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_6771666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771666 prefixEnd_6771666 := by exact prefixLift 6771666
  have htrace : WordTrace (prefixWord ++ tailWord_6771666) baseStart_6771666 baseEnd_6771666 := by
    simpa [prefixWord, tailWord_6771666, baseEnd_6771666] using wordTrace_append hprefix tailTrace_6771666
  have hstable : (prefixWord ++ tailWord_6771666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771666).length < 2 ^ (prefixWord ++ tailWord_6771666).sum := by decide
  have hdescent : baseEnd_6771666 < baseStart_6771666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771713 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 2, 4]
def baseStart_6771713 : Nat := 118140960795 + 6771713 * 2 ^ 59
def prefixEnd_6771713 : Nat := 4983230072969 + 3 ^ 40 * 6771713 * 2
def baseEnd_6771713 : Nat := 1159047874433256458481655

theorem tailTrace_6771713 : CollatzResearch.WordTrace tailWord_6771713 prefixEnd_6771713 1159047874433256458481655 := by
  unfold tailWord_6771713
  simp only [CollatzResearch.WordTrace]
  refine ⟨246984663716247792350527793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164656442477498528233685195 246984663716247792350527793)
  ·
    refine ⟨185238497787185844262895845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246984663716247792350527793 185238497787185844262895845)
    ·
      refine ⟨34732218335097345799292971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185238497787185844262895845 34732218335097345799292971)
      ·
        refine ⟨52098327502646018698939457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34732218335097345799292971 52098327502646018698939457)
        ·
          refine ⟨39073745626984514024204593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52098327502646018698939457 39073745626984514024204593)
          ·
            refine ⟨29305309220238385518153445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39073745626984514024204593 29305309220238385518153445)
            ·
              refine ⟨5494745478794697284653771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29305309220238385518153445 5494745478794697284653771)
              ·
                refine ⟨8242118218192045926980657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5494745478794697284653771 8242118218192045926980657)
                ·
                  refine ⟨6181588663644034445235493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8242118218192045926980657 6181588663644034445235493)
                  ·
                    refine ⟨1159047874433256458481655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6181588663644034445235493 1159047874433256458481655)
                    ·
                      rfl

theorem cell23_6771713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_6771713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771713 prefixEnd_6771713 := by exact prefixLift 6771713
  have htrace : WordTrace (prefixWord ++ tailWord_6771713) baseStart_6771713 baseEnd_6771713 := by
    simpa [prefixWord, tailWord_6771713, baseEnd_6771713] using wordTrace_append hprefix tailTrace_6771713
  have hstable : (prefixWord ++ tailWord_6771713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771713).length < 2 ^ (prefixWord ++ tailWord_6771713).sum := by decide
  have hdescent : baseEnd_6771713 < baseStart_6771713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771723 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 1, 2, 3]
def baseStart_6771723 : Nat := 118140960795 + 6771723 * 2 ^ 59
def prefixEnd_6771723 : Nat := 4983230072969 + 3 ^ 40 * 6771723 * 2
def baseEnd_6771723 : Nat := 3477148758106314336319919

theorem tailTrace_6771723 : CollatzResearch.WordTrace tailWord_6771723 prefixEnd_6771723 3477148758106314336319919 := by
  unfold tailWord_6771723
  simp only [CollatzResearch.WordTrace]
  refine ⟨246985028446211564058391823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164656685630807709372261215 246985028446211564058391823)
  ·
    refine ⟨370477542669317346087587735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246985028446211564058391823 370477542669317346087587735)
    ·
      refine ⟨555716314003976019131381603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370477542669317346087587735 555716314003976019131381603)
      ·
        refine ⟨833574471005964028697072405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555716314003976019131381603 833574471005964028697072405)
        ·
          refine ⟨39073803328404563845175269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 833574471005964028697072405 39073803328404563845175269)
          ·
            refine ⟨7326338124075855720970363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39073803328404563845175269 7326338124075855720970363)
            ·
              refine ⟨10989507186113783581455545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7326338124075855720970363 10989507186113783581455545)
              ·
                refine ⟨8242130389585337686091659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10989507186113783581455545 8242130389585337686091659)
                ·
                  refine ⟨12363195584378006529137489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8242130389585337686091659 12363195584378006529137489)
                  ·
                    refine ⟨9272396688283504896853117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12363195584378006529137489 9272396688283504896853117)
                    ·
                      refine ⟨3477148758106314336319919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9272396688283504896853117 3477148758106314336319919)
                      ·
                        rfl

theorem cell23_6771723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 2, 3].length) (baseStart_6771723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771723 prefixEnd_6771723 := by exact prefixLift 6771723
  have htrace : WordTrace (prefixWord ++ tailWord_6771723) baseStart_6771723 baseEnd_6771723 := by
    simpa [prefixWord, tailWord_6771723, baseEnd_6771723] using wordTrace_append hprefix tailTrace_6771723
  have hstable : (prefixWord ++ tailWord_6771723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771723).length < 2 ^ (prefixWord ++ tailWord_6771723).sum := by decide
  have hdescent : baseEnd_6771723 < baseStart_6771723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771730 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6771730 : Nat := 118140960795 + 6771730 * 2 ^ 59
def prefixEnd_6771730 : Nat := 4983230072969 + 3 ^ 40 * 6771730 * 2
def baseEnd_6771730 : Nat := 1159050784156965269644129

theorem tailTrace_6771730 : CollatzResearch.WordTrace tailWord_6771730 prefixEnd_6771730 1159050784156965269644129 := by
  unfold tailWord_6771730
  simp only [CollatzResearch.WordTrace]
  refine ⟨61746320939296551063474161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164656855838124136169264429 61746320939296551063474161)
  ·
    refine ⟨46309740704472413297605621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61746320939296551063474161 46309740704472413297605621)
    ·
      refine ⟨4341538191044288746650527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46309740704472413297605621 4341538191044288746650527)
      ·
        refine ⟨6512307286566433119975791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4341538191044288746650527 6512307286566433119975791)
        ·
          refine ⟨9768460929849649679963687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6512307286566433119975791 9768460929849649679963687)
          ·
            refine ⟨14652691394774474519945531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9768460929849649679963687 14652691394774474519945531)
            ·
              refine ⟨21979037092161711779918297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14652691394774474519945531 21979037092161711779918297)
              ·
                refine ⟨16484277819121283834938723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21979037092161711779918297 16484277819121283834938723)
                ·
                  refine ⟨24726416728681925752408085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16484277819121283834938723 24726416728681925752408085)
                  ·
                    refine ⟨1159050784156965269644129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24726416728681925752408085 1159050784156965269644129)
                    ·
                      rfl

theorem cell23_6771730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6771730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771730 prefixEnd_6771730 := by exact prefixLift 6771730
  have htrace : WordTrace (prefixWord ++ tailWord_6771730) baseStart_6771730 baseEnd_6771730 := by
    simpa [prefixWord, tailWord_6771730, baseEnd_6771730] using wordTrace_append hprefix tailTrace_6771730
  have hstable : (prefixWord ++ tailWord_6771730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771730).length < 2 ^ (prefixWord ++ tailWord_6771730).sum := by decide
  have hdescent : baseEnd_6771730 < baseStart_6771730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771736 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 1, 3, 3]
def baseStart_6771736 : Nat := 118140960795 + 6771736 * 2 ^ 59
def prefixEnd_6771736 : Nat := 4983230072969 + 3 ^ 40 * 6771736 * 2
def baseEnd_6771736 : Nat := 3477155433354822785457359

theorem tailTrace_6771736 : CollatzResearch.WordTrace tailWord_6771736 prefixEnd_6771736 3477155433354822785457359 := by
  unfold tailWord_6771736
  simp only [CollatzResearch.WordTrace]
  refine ⟨123492751297582233639307531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164657001730109644852410041 123492751297582233639307531)
  ·
    refine ⟨185239126946373350458961297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123492751297582233639307531 185239126946373350458961297)
    ·
      refine ⟨138929345209780012844220973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185239126946373350458961297 138929345209780012844220973)
      ·
        refine ⟨52098504453667504816582865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138929345209780012844220973 52098504453667504816582865)
        ·
          refine ⟨39073878340250628612437149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52098504453667504816582865 39073878340250628612437149)
          ·
            refine ⟨14652704377593985729663931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39073878340250628612437149 14652704377593985729663931)
            ·
              refine ⟨21979056566390978594495897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14652704377593985729663931 21979056566390978594495897)
              ·
                refine ⟨16484292424793233945871923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21979056566390978594495897 16484292424793233945871923)
                ·
                  refine ⟨24726438637189850918807885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16484292424793233945871923 24726438637189850918807885)
                  ·
                    refine ⟨9272414488946194094552957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24726438637189850918807885 9272414488946194094552957)
                    ·
                      refine ⟨3477155433354822785457359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9272414488946194094552957 3477155433354822785457359)
                      ·
                        rfl

theorem cell23_6771736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_6771736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771736 prefixEnd_6771736 := by exact prefixLift 6771736
  have htrace : WordTrace (prefixWord ++ tailWord_6771736) baseStart_6771736 baseEnd_6771736 := by
    simpa [prefixWord, tailWord_6771736, baseEnd_6771736] using wordTrace_append hprefix tailTrace_6771736
  have hstable : (prefixWord ++ tailWord_6771736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771736).length < 2 ^ (prefixWord ++ tailWord_6771736).sum := by decide
  have hdescent : baseEnd_6771736 < baseStart_6771736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771740 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_6771740 : Nat := 118140960795 + 6771740 * 2 ^ 59
def prefixEnd_6771740 : Nat := 4983230072969 + 3 ^ 40 * 6771740 * 2
def baseEnd_6771740 : Nat := 3477157487277440769807341

theorem tailTrace_6771740 : CollatzResearch.WordTrace tailWord_6771740 prefixEnd_6771740 3477157487277440769807341 := by
  unfold tailWord_6771740
  simp only [CollatzResearch.WordTrace]
  refine ⟨123492824243574987980880337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164657098991433317307840449 123492824243574987980880337)
  ·
    refine ⟨92619618182681240985660253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123492824243574987980880337 92619618182681240985660253)
    ·
      refine ⟨34732356818505465369622595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92619618182681240985660253 34732356818505465369622595)
      ·
        refine ⟨52098535227758198054433893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34732356818505465369622595 52098535227758198054433893)
        ·
          refine ⟨9768475355204662135206355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52098535227758198054433893 9768475355204662135206355)
          ·
            refine ⟨14652713032806993202809533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9768475355204662135206355 14652713032806993202809533)
            ·
              refine ⟨5494767387302622451053575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14652713032806993202809533 5494767387302622451053575)
              ·
                refine ⟨8242151080953933676580363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5494767387302622451053575 8242151080953933676580363)
                ·
                  refine ⟨12363226621430900514870545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8242151080953933676580363 12363226621430900514870545)
                  ·
                    refine ⟨9272419966073175386152909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12363226621430900514870545 9272419966073175386152909)
                    ·
                      refine ⟨3477157487277440769807341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9272419966073175386152909 3477157487277440769807341)
                      ·
                        rfl

theorem cell23_6771740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_6771740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771740 prefixEnd_6771740 := by exact prefixLift 6771740
  have htrace : WordTrace (prefixWord ++ tailWord_6771740) baseStart_6771740 baseEnd_6771740 := by
    simpa [prefixWord, tailWord_6771740, baseEnd_6771740] using wordTrace_append hprefix tailTrace_6771740
  have hstable : (prefixWord ++ tailWord_6771740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771740).length < 2 ^ (prefixWord ++ tailWord_6771740).sum := by decide
  have hdescent : baseEnd_6771740 < baseStart_6771740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771769 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 1, 8]
def baseStart_6771769 : Nat := 118140960795 + 6771769 * 2 ^ 59
def prefixEnd_6771769 : Nat := 4983230072969 + 3 ^ 40 * 6771769 * 2
def baseEnd_6771769 : Nat := 1159057459405473718781569

theorem tailTrace_6771769 : CollatzResearch.WordTrace tailWord_6771769 prefixEnd_6771769 1159057459405473718781569 := by
  unfold tailWord_6771769
  simp only [CollatzResearch.WordTrace]
  refine ⟨246986706204044913914566361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164657804136029942609710907 246986706204044913914566361)
  ·
    refine ⟨185240029653033685435924771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246986706204044913914566361 185240029653033685435924771)
    ·
      refine ⟨277860044479550528153887157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185240029653033685435924771 277860044479550528153887157)
      ·
        refine ⟨26049379169957862014426921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 277860044479550528153887157 26049379169957862014426921)
        ·
          refine ⟨19537034377468396510820191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26049379169957862014426921 19537034377468396510820191)
          ·
            refine ⟨29305551566202594766230287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19537034377468396510820191 29305551566202594766230287)
            ·
              refine ⟨43958327349303892149345431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29305551566202594766230287 43958327349303892149345431)
              ·
                refine ⟨65937491023955838224018147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43958327349303892149345431 65937491023955838224018147)
                ·
                  refine ⟨98906236535933757336027221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65937491023955838224018147 98906236535933757336027221)
                  ·
                    refine ⟨1159057459405473718781569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98906236535933757336027221 1159057459405473718781569)
                    ·
                      rfl

theorem cell23_6771769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_6771769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771769 prefixEnd_6771769 := by exact prefixLift 6771769
  have htrace : WordTrace (prefixWord ++ tailWord_6771769) baseStart_6771769 baseEnd_6771769 := by
    simpa [prefixWord, tailWord_6771769, baseEnd_6771769] using wordTrace_append hprefix tailTrace_6771769
  have hstable : (prefixWord ++ tailWord_6771769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771769).length < 2 ^ (prefixWord ++ tailWord_6771769).sum := by decide
  have hdescent : baseEnd_6771769 < baseStart_6771769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771779 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 3]
def baseStart_6771779 : Nat := 118140960795 + 6771779 * 2 ^ 59
def prefixEnd_6771779 : Nat := 4983230072969 + 3 ^ 40 * 6771779 * 2
def baseEnd_6771779 : Nat := 3477177513022966117219661

theorem tailTrace_6771779 : CollatzResearch.WordTrace tailWord_6771779 prefixEnd_6771779 3477177513022966117219661 := by
  unfold tailWord_6771779
  simp only [CollatzResearch.WordTrace]
  refine ⟨246987070934008685622430391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164658047289339123748286927 246987070934008685622430391)
  ·
    refine ⟨370480606401013028433645587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246987070934008685622430391 370480606401013028433645587)
    ·
      refine ⟨555720909601519542650468381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370480606401013028433645587 555720909601519542650468381)
      ·
        refine ⟨208395341100569828493925643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555720909601519542650468381 208395341100569828493925643)
        ·
          refine ⟨312593011650854742740888465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208395341100569828493925643 312593011650854742740888465)
          ·
            refine ⟨234444758738141057055666349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312593011650854742740888465 234444758738141057055666349)
            ·
              refine ⟨87916784526802896395874881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234444758738141057055666349 87916784526802896395874881)
              ·
                refine ⟨65937588395102172296906161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87916784526802896395874881 65937588395102172296906161)
                ·
                  refine ⟨49453191296326629222679621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65937588395102172296906161 49453191296326629222679621)
                  ·
                    refine ⟨9272473368061242979252429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49453191296326629222679621 9272473368061242979252429)
                    ·
                      refine ⟨3477177513022966117219661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9272473368061242979252429 3477177513022966117219661)
                      ·
                        rfl

theorem cell23_6771779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_6771779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771779 prefixEnd_6771779 := by exact prefixLift 6771779
  have htrace : WordTrace (prefixWord ++ tailWord_6771779) baseStart_6771779 baseEnd_6771779 := by
    simpa [prefixWord, tailWord_6771779, baseEnd_6771779] using wordTrace_append hprefix tailTrace_6771779
  have hstable : (prefixWord ++ tailWord_6771779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771779).length < 2 ^ (prefixWord ++ tailWord_6771779).sum := by decide
  have hdescent : baseEnd_6771779 < baseStart_6771779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771826 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_6771826 : Nat := 118140960795 + 6771826 * 2 ^ 59
def prefixEnd_6771826 : Nat := 4983230072969 + 3 ^ 40 * 6771826 * 2
def baseEnd_6771826 : Nat := 3477201646613727433331945

theorem tailTrace_6771826 : CollatzResearch.WordTrace tailWord_6771826 prefixEnd_6771826 3477201646613727433331945 := by
  unfold tailWord_6771826
  simp only [CollatzResearch.WordTrace]
  refine ⟨61747196291209603162347833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164659190109892275099594221 61747196291209603162347833)
  ·
    refine ⟨46310397218407202371760875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61747196291209603162347833 46310397218407202371760875)
    ·
      refine ⟨69465595827610803557641313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46310397218407202371760875 69465595827610803557641313)
      ·
        refine ⟨52099196870708102668230985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69465595827610803557641313 52099196870708102668230985)
        ·
          refine ⟨39074397653031077001173239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52099196870708102668230985 39074397653031077001173239)
          ·
            refine ⟨58611596479546615501759859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39074397653031077001173239 58611596479546615501759859)
            ·
              refine ⟨87917394719319923252639789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58611596479546615501759859 87917394719319923252639789)
              ·
                refine ⟨32969023019744971219739921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87917394719319923252639789 32969023019744971219739921)
                ·
                  refine ⟨24726767264808728414804941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32969023019744971219739921 24726767264808728414804941)
                  ·
                    refine ⟨9272537724303273155551853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24726767264808728414804941 9272537724303273155551853)
                    ·
                      refine ⟨3477201646613727433331945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9272537724303273155551853 3477201646613727433331945)
                      ·
                        rfl

theorem cell23_6771826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_6771826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771826 prefixEnd_6771826 := by exact prefixLift 6771826
  have htrace : WordTrace (prefixWord ++ tailWord_6771826) baseStart_6771826 baseEnd_6771826 := by
    simpa [prefixWord, tailWord_6771826, baseEnd_6771826] using wordTrace_append hprefix tailTrace_6771826
  have hstable : (prefixWord ++ tailWord_6771826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771826).length < 2 ^ (prefixWord ++ tailWord_6771826).sum := by decide
  have hdescent : baseEnd_6771826 < baseStart_6771826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771909 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_6771909 : Nat := 118140960795 + 6771909 * 2 ^ 59
def prefixEnd_6771909 : Nat := 4983230072969 + 3 ^ 40 * 6771909 * 2
def baseEnd_6771909 : Nat := 3477244265508050608594063

theorem tailTrace_6771909 : CollatzResearch.WordTrace tailWord_6771909 prefixEnd_6771909 3477244265508050608594063 := by
  unfold tailWord_6771909
  simp only [CollatzResearch.WordTrace]
  refine ⟨246991812423537717824662781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164661208282358478549775187 246991812423537717824662781)
  ·
    refine ⟨92621929658826644184248543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246991812423537717824662781 92621929658826644184248543)
    ·
      refine ⟨138932894488239966276372815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92621929658826644184248543 138932894488239966276372815)
      ·
        refine ⟨208399341732359949414559223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138932894488239966276372815 208399341732359949414559223)
        ·
          refine ⟨312599012598539924121838835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208399341732359949414559223 312599012598539924121838835)
          ·
            refine ⟨468898518897809886182758253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312599012598539924121838835 468898518897809886182758253)
            ·
              refine ⟨175836944586678707318534345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468898518897809886182758253 175836944586678707318534345)
              ·
                refine ⟨131877708440009030488900759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175836944586678707318534345 131877708440009030488900759)
                ·
                  refine ⟨197816562660013545733351139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131877708440009030488900759 197816562660013545733351139)
                  ·
                    refine ⟨296724843990020318600026709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 197816562660013545733351139 296724843990020318600026709)
                    ·
                      refine ⟨3477244265508050608594063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 296724843990020318600026709 3477244265508050608594063)
                      ·
                        rfl

theorem cell23_6771909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_6771909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771909 prefixEnd_6771909 := by exact prefixLift 6771909
  have htrace : WordTrace (prefixWord ++ tailWord_6771909) baseStart_6771909 baseEnd_6771909 := by
    simpa [prefixWord, tailWord_6771909, baseEnd_6771909] using wordTrace_append hprefix tailTrace_6771909
  have hstable : (prefixWord ++ tailWord_6771909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771909).length < 2 ^ (prefixWord ++ tailWord_6771909).sum := by decide
  have hdescent : baseEnd_6771909 < baseStart_6771909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771936 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 3, 5]
def baseStart_6771936 : Nat := 118140960795 + 6771936 * 2 ^ 59
def prefixEnd_6771936 : Nat := 4983230072969 + 3 ^ 40 * 6771936 * 2
def baseEnd_6771936 : Nat := 1159086043161907334318813

theorem tailTrace_6771936 : CollatzResearch.WordTrace tailWord_6771936 prefixEnd_6771936 1159086043161907334318813 := by
  unfold tailWord_6771936
  simp only [CollatzResearch.WordTrace]
  refine ⟨123496398597219950717947831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164661864796293267623930441 123496398597219950717947831)
  ·
    refine ⟨185244597895829926076921747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123496398597219950717947831 185244597895829926076921747)
    ·
      refine ⟨277866896843744889115382621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185244597895829926076921747 277866896843744889115382621)
      ·
        refine ⟨104200086316404333418268483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277866896843744889115382621 104200086316404333418268483)
        ·
          refine ⟨156300129474606500127402725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104200086316404333418268483 156300129474606500127402725)
          ·
            refine ⟨29306274276488718773888011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156300129474606500127402725 29306274276488718773888011)
            ·
              refine ⟨43959411414733078160832017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29306274276488718773888011 43959411414733078160832017)
              ·
                refine ⟨32969558561049808620624013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43959411414733078160832017 32969558561049808620624013)
                ·
                  refine ⟨12363584460393678232734005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32969558561049808620624013 12363584460393678232734005)
                  ·
                    refine ⟨1159086043161907334318813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12363584460393678232734005 1159086043161907334318813)
                    ·
                      rfl

theorem cell23_6771936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_6771936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771936 prefixEnd_6771936 := by exact prefixLift 6771936
  have htrace : WordTrace (prefixWord ++ tailWord_6771936) baseStart_6771936 baseEnd_6771936 := by
    simpa [prefixWord, tailWord_6771936, baseEnd_6771936] using wordTrace_append hprefix tailTrace_6771936
  have hstable : (prefixWord ++ tailWord_6771936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771936).length < 2 ^ (prefixWord ++ tailWord_6771936).sum := by decide
  have hdescent : baseEnd_6771936 < baseStart_6771936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771967 : List Nat := [1, 1, 2, 2, 1, 6, 2, 3, 1, 1, 3]
def baseStart_6771967 : Nat := 118140960795 + 6771967 * 2 ^ 59
def prefixEnd_6771967 : Nat := 4983230072969 + 3 ^ 40 * 6771967 * 2
def baseEnd_6771967 : Nat := 3477274047386011381668797

theorem tailTrace_6771967 : CollatzResearch.WordTrace tailWord_6771967 prefixEnd_6771967 3477274047386011381668797 := by
  unfold tailWord_6771967
  simp only [CollatzResearch.WordTrace]
  refine ⟨246993927857327593730274155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164662618571551729153516103 246993927857327593730274155)
  ·
    refine ⟨370490891785991390595411233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246993927857327593730274155 370490891785991390595411233)
    ·
      refine ⟨277868168839493542946558425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370490891785991390595411233 277868168839493542946558425)
      ·
        refine ⟨208401126629620157209918819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277868168839493542946558425 208401126629620157209918819)
        ·
          refine ⟨312601689944430235814878229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208401126629620157209918819 312601689944430235814878229)
          ·
            refine ⟨14653204216145167303822417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 312601689944430235814878229 14653204216145167303822417)
            ·
              refine ⟨10989903162108875477866813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14653204216145167303822417 10989903162108875477866813)
              ·
                refine ⟨4121213685790828304200055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10989903162108875477866813 4121213685790828304200055)
                ·
                  refine ⟨6181820528686242456300083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4121213685790828304200055 6181820528686242456300083)
                  ·
                    refine ⟨9272730793029363684450125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6181820528686242456300083 9272730793029363684450125)
                    ·
                      refine ⟨3477274047386011381668797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9272730793029363684450125 3477274047386011381668797)
                      ·
                        rfl

theorem cell23_6771967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 1, 1, 3].length) (baseStart_6771967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771967 prefixEnd_6771967 := by exact prefixLift 6771967
  have htrace : WordTrace (prefixWord ++ tailWord_6771967) baseStart_6771967 baseEnd_6771967 := by
    simpa [prefixWord, tailWord_6771967, baseEnd_6771967] using wordTrace_append hprefix tailTrace_6771967
  have hstable : (prefixWord ++ tailWord_6771967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771967).length < 2 ^ (prefixWord ++ tailWord_6771967).sum := by decide
  have hdescent : baseEnd_6771967 < baseStart_6771967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6771973 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 4]
def baseStart_6771973 : Nat := 118140960795 + 6771973 * 2 ^ 59
def prefixEnd_6771973 : Nat := 4983230072969 + 3 ^ 40 * 6771973 * 2
def baseEnd_6771973 : Nat := 3477277128269938358193769

theorem tailTrace_6771973 : CollatzResearch.WordTrace tailWord_6771973 prefixEnd_6771973 3477277128269938358193769 := by
  unfold tailWord_6771973
  simp only [CollatzResearch.WordTrace]
  refine ⟨246994146695305856754992573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164662764463537237836661715 246994146695305856754992573)
  ·
    refine ⟨92622805010739696283122215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246994146695305856754992573 92622805010739696283122215)
    ·
      refine ⟨138934207516109544424683323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92622805010739696283122215 138934207516109544424683323)
      ·
        refine ⟨208401311274164316637024985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138934207516109544424683323 208401311274164316637024985)
        ·
          refine ⟨156300983455623237477768739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208401311274164316637024985 156300983455623237477768739)
          ·
            refine ⟨234451475183434856216653109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156300983455623237477768739 234451475183434856216653109)
            ·
              refine ⟨21979825798447017770311229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234451475183434856216653109 21979825798447017770311229)
              ·
                refine ⟨8242434674417631663866711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21979825798447017770311229 8242434674417631663866711)
                ·
                  refine ⟨12363652011626447495800067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8242434674417631663866711 12363652011626447495800067)
                  ·
                    refine ⟨18545478017439671243700101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12363652011626447495800067 18545478017439671243700101)
                    ·
                      refine ⟨3477277128269938358193769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18545478017439671243700101 3477277128269938358193769)
                      ·
                        rfl

theorem cell23_6771973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_6771973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6771973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6771973 prefixEnd_6771973 := by exact prefixLift 6771973
  have htrace : WordTrace (prefixWord ++ tailWord_6771973) baseStart_6771973 baseEnd_6771973 := by
    simpa [prefixWord, tailWord_6771973, baseEnd_6771973] using wordTrace_append hprefix tailTrace_6771973
  have hstable : (prefixWord ++ tailWord_6771973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6771973).length < 2 ^ (prefixWord ++ tailWord_6771973).sum := by decide
  have hdescent : baseEnd_6771973 < baseStart_6771973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6771973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772000 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 1, 6]
def baseStart_6772000 : Nat := 118140960795 + 6772000 * 2 ^ 59
def prefixEnd_6772000 : Nat := 4983230072969 + 3 ^ 40 * 6772000 * 2
def baseEnd_6772000 : Nat := 1159096997415869917518715

theorem tailTrace_6772000 : CollatzResearch.WordTrace tailWord_6772000 prefixEnd_6772000 1159096997415869917518715 := by
  unfold tailWord_6772000
  simp only [CollatzResearch.WordTrace]
  refine ⟨123497565733104020183112727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164663420977472026910816969 123497565733104020183112727)
  ·
    refine ⟨185246348599656030274669091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123497565733104020183112727 185246348599656030274669091)
    ·
      refine ⟨277869522899484045412003637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185246348599656030274669091 277869522899484045412003637)
      ·
        refine ⟨26050267771826629257375341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 277869522899484045412003637 26050267771826629257375341)
        ·
          refine ⟨9768850414434985971515753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26050267771826629257375341 9768850414434985971515753)
          ·
            refine ⟨7326637810826239478636815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9768850414434985971515753 7326637810826239478636815)
            ·
              refine ⟨10989956716239359217955223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7326637810826239478636815 10989956716239359217955223)
              ·
                refine ⟨16484935074359038826932835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10989956716239359217955223 16484935074359038826932835)
                ·
                  refine ⟨24727402611538558240399253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16484935074359038826932835 24727402611538558240399253)
                  ·
                    refine ⟨1159096997415869917518715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24727402611538558240399253 1159096997415869917518715)
                    ·
                      rfl

theorem cell23_6772000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 6].length) (baseStart_6772000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772000 prefixEnd_6772000 := by exact prefixLift 6772000
  have htrace : WordTrace (prefixWord ++ tailWord_6772000) baseStart_6772000 baseEnd_6772000 := by
    simpa [prefixWord, tailWord_6772000, baseEnd_6772000] using wordTrace_append hprefix tailTrace_6772000
  have hstable : (prefixWord ++ tailWord_6772000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772000).length < 2 ^ (prefixWord ++ tailWord_6772000).sum := by decide
  have hdescent : baseEnd_6772000 < baseStart_6772000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772003 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 4]
def baseStart_6772003 : Nat := 118140960795 + 6772003 * 2 ^ 59
def prefixEnd_6772003 : Nat := 4983230072969 + 3 ^ 40 * 6772003 * 2
def baseEnd_6772003 : Nat := 3477292532689573240818631

theorem tailTrace_6772003 : CollatzResearch.WordTrace tailWord_6772003 prefixEnd_6772003 3477292532689573240818631 := by
  unfold tailWord_6772003
  simp only [CollatzResearch.WordTrace]
  refine ⟨246995240885197171878584663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164663493923464781252389775 246995240885197171878584663)
  ·
    refine ⟨370492861327795757817876995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246995240885197171878584663 370492861327795757817876995)
    ·
      refine ⟨555739291991693636726815493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370492861327795757817876995 555739291991693636726815493)
      ·
        refine ⟨104201117248442556886277905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 555739291991693636726815493 104201117248442556886277905)
        ·
          refine ⟨78150837936331917664708429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104201117248442556886277905 78150837936331917664708429)
          ·
            refine ⟨29306564226124469124265661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78150837936331917664708429 29306564226124469124265661)
            ·
              refine ⟨10989961584796675921599623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29306564226124469124265661 10989961584796675921599623)
              ·
                refine ⟨16484942377195013882399435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10989961584796675921599623 16484942377195013882399435)
                ·
                  refine ⟨24727413565792520823599153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16484942377195013882399435 24727413565792520823599153)
                  ·
                    refine ⟨18545560174344390617699365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24727413565792520823599153 18545560174344390617699365)
                    ·
                      refine ⟨3477292532689573240818631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18545560174344390617699365 3477292532689573240818631)
                      ·
                        rfl

theorem cell23_6772003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_6772003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772003 prefixEnd_6772003 := by exact prefixLift 6772003
  have htrace : WordTrace (prefixWord ++ tailWord_6772003) baseStart_6772003 baseEnd_6772003 := by
    simpa [prefixWord, tailWord_6772003, baseEnd_6772003] using wordTrace_append hprefix tailTrace_6772003
  have hstable : (prefixWord ++ tailWord_6772003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772003).length < 2 ^ (prefixWord ++ tailWord_6772003).sum := by decide
  have hdescent : baseEnd_6772003 < baseStart_6772003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772040 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_6772040 : Nat := 118140960795 + 6772040 * 2 ^ 59
def prefixEnd_6772040 : Nat := 4983230072969 + 3 ^ 40 * 6772040 * 2
def baseEnd_6772040 : Nat := 3477311531473789596055961

theorem tailTrace_6772040 : CollatzResearch.WordTrace tailWord_6772040 prefixEnd_6772040 3477311531473789596055961 := by
  unfold tailWord_6772040
  simp only [CollatzResearch.WordTrace]
  refine ⟨123498295193031563598840787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164664393590708751465121049 123498295193031563598840787)
  ·
    refine ⟨185247442789547345398261181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123498295193031563598840787 185247442789547345398261181)
    ·
      refine ⟨69467791046080254524347943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185247442789547345398261181 69467791046080254524347943)
      ·
        refine ⟨104201686569120381786521915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69467791046080254524347943 104201686569120381786521915)
        ·
          refine ⟨156302529853680572679782873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104201686569120381786521915 156302529853680572679782873)
          ·
            refine ⟨117226897390260429509837155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156302529853680572679782873 117226897390260429509837155)
            ·
              refine ⟨175840346085390644264755733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117226897390260429509837155 175840346085390644264755733)
              ·
                refine ⟨8242516222752686449910425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 175840346085390644264755733 8242516222752686449910425)
                ·
                  refine ⟨6181887167064514837432819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8242516222752686449910425 6181887167064514837432819)
                  ·
                    refine ⟨9272830750596772256149229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6181887167064514837432819 9272830750596772256149229)
                    ·
                      refine ⟨3477311531473789596055961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9272830750596772256149229 3477311531473789596055961)
                      ·
                        rfl

theorem cell23_6772040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_6772040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772040 prefixEnd_6772040 := by exact prefixLift 6772040
  have htrace : WordTrace (prefixWord ++ tailWord_6772040) baseStart_6772040 baseEnd_6772040 := by
    simpa [prefixWord, tailWord_6772040, baseEnd_6772040] using wordTrace_append hprefix tailTrace_6772040
  have hstable : (prefixWord ++ tailWord_6772040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772040).length < 2 ^ (prefixWord ++ tailWord_6772040).sum := by decide
  have hdescent : baseEnd_6772040 < baseStart_6772040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772050 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_6772050 : Nat := 118140960795 + 6772050 * 2 ^ 59
def prefixEnd_6772050 : Nat := 4983230072969 + 3 ^ 40 * 6772050 * 2
def baseEnd_6772050 : Nat := 3477316666280334556930915

theorem tailTrace_6772050 : CollatzResearch.WordTrace tailWord_6772050 prefixEnd_6772050 3477316666280334556930915 := by
  unfold tailWord_6772050
  simp only [CollatzResearch.WordTrace]
  refine ⟨61749238779006724726386401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164664636744017932603697069 61749238779006724726386401)
  ·
    refine ⟨46311929084255043544789801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61749238779006724726386401 46311929084255043544789801)
    ·
      refine ⟨34733946813191282658592351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46311929084255043544789801 34733946813191282658592351)
      ·
        refine ⟨52100920219786923987888527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34733946813191282658592351 52100920219786923987888527)
        ·
          refine ⟨78151380329680385981832791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52100920219786923987888527 78151380329680385981832791)
          ·
            refine ⟨117227070494520578972749187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78151380329680385981832791 117227070494520578972749187)
            ·
              refine ⟨175840605741780868459123781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117227070494520578972749187 175840605741780868459123781)
              ·
                refine ⟨32970113576583912836085709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175840605741780868459123781 32970113576583912836085709)
                ·
                  refine ⟨12363792591218967313532141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32970113576583912836085709 12363792591218967313532141)
                  ·
                    refine ⟨4636422221707112742574553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12363792591218967313532141 4636422221707112742574553)
                    ·
                      refine ⟨3477316666280334556930915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636422221707112742574553 3477316666280334556930915)
                      ·
                        rfl

theorem cell23_6772050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_6772050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772050 prefixEnd_6772050 := by exact prefixLift 6772050
  have htrace : WordTrace (prefixWord ++ tailWord_6772050) baseStart_6772050 baseEnd_6772050 := by
    simpa [prefixWord, tailWord_6772050, baseEnd_6772050] using wordTrace_append hprefix tailTrace_6772050
  have hstable : (prefixWord ++ tailWord_6772050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772050).length < 2 ^ (prefixWord ++ tailWord_6772050).sum := by decide
  have hdescent : baseEnd_6772050 < baseStart_6772050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772056 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 1, 8]
def baseStart_6772056 : Nat := 118140960795 + 6772056 * 2 ^ 59
def prefixEnd_6772056 : Nat := 4983230072969 + 3 ^ 40 * 6772056 * 2
def baseEnd_6772056 : Nat := 1159106582388087177818629

theorem tailTrace_6772056 : CollatzResearch.WordTrace tailWord_6772056 prefixEnd_6772056 1159106582388087177818629 := by
  unfold tailWord_6772056
  simp only [CollatzResearch.WordTrace]
  refine ⟨123498586977002580965132011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164664782636003441286842681 123498586977002580965132011)
  ·
    refine ⟨185247880465503871447698017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123498586977002580965132011 185247880465503871447698017)
    ·
      refine ⟨138935910349127903585773513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185247880465503871447698017 138935910349127903585773513)
      ·
        refine ⟨104201932761845927689330135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138935910349127903585773513 104201932761845927689330135)
        ·
          refine ⟨156302899142768891533995203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104201932761845927689330135 156302899142768891533995203)
          ·
            refine ⟨234454348714153337300992805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156302899142768891533995203 234454348714153337300992805)
            ·
              refine ⟨43960190383903750743936151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234454348714153337300992805 43960190383903750743936151)
              ·
                refine ⟨65940285575855626115904227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43960190383903750743936151 65940285575855626115904227)
                ·
                  refine ⟨98910428363783439173856341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65940285575855626115904227 98910428363783439173856341)
                  ·
                    refine ⟨1159106582388087177818629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98910428363783439173856341 1159106582388087177818629)
                    ·
                      rfl

theorem cell23_6772056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_6772056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772056 prefixEnd_6772056 := by exact prefixLift 6772056
  have htrace : WordTrace (prefixWord ++ tailWord_6772056) baseStart_6772056 baseEnd_6772056 := by
    simpa [prefixWord, tailWord_6772056, baseEnd_6772056] using wordTrace_append hprefix tailTrace_6772056
  have hstable : (prefixWord ++ tailWord_6772056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772056).length < 2 ^ (prefixWord ++ tailWord_6772056).sum := by decide
  have hdescent : baseEnd_6772056 < baseStart_6772056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772057 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 2, 1, 3]
def baseStart_6772057 : Nat := 118140960795 + 6772057 * 2 ^ 59
def prefixEnd_6772057 : Nat := 4983230072969 + 3 ^ 40 * 6772057 * 2
def baseEnd_6772057 : Nat := 3477320260644916029543383

theorem tailTrace_6772057 : CollatzResearch.WordTrace tailWord_6772057 prefixEnd_6772057 3477320260644916029543383 := by
  unfold tailWord_6772057
  simp only [CollatzResearch.WordTrace]
  refine ⟨246997210427001539101050425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164664806951334359400700283 246997210427001539101050425)
  ·
    refine ⟨185247907820251154325787819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246997210427001539101050425 185247907820251154325787819)
    ·
      refine ⟨277871861730376731488681729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185247907820251154325787819 277871861730376731488681729)
      ·
        refine ⟨208403896297782548616511297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277871861730376731488681729 208403896297782548616511297)
        ·
          refine ⟨156302922223336911462383473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208403896297782548616511297 156302922223336911462383473)
          ·
            refine ⟨117227191667502683596787605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156302922223336911462383473 117227191667502683596787605)
            ·
              refine ⟨5495024609414188293599419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117227191667502683596787605 5495024609414188293599419)
              ·
                refine ⟨8242536914121282440399129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495024609414188293599419 8242536914121282440399129)
                ·
                  refine ⟨6181902685590961830299347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8242536914121282440399129 6181902685590961830299347)
                  ·
                    refine ⟨9272854028386442745449021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6181902685590961830299347 9272854028386442745449021)
                    ·
                      refine ⟨3477320260644916029543383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9272854028386442745449021 3477320260644916029543383)
                      ·
                        rfl

theorem cell23_6772057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_6772057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772057 prefixEnd_6772057 := by exact prefixLift 6772057
  have htrace : WordTrace (prefixWord ++ tailWord_6772057) baseStart_6772057 baseEnd_6772057 := by
    simpa [prefixWord, tailWord_6772057, baseEnd_6772057] using wordTrace_append hprefix tailTrace_6772057
  have hstable : (prefixWord ++ tailWord_6772057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772057).length < 2 ^ (prefixWord ++ tailWord_6772057).sum := by decide
  have hdescent : baseEnd_6772057 < baseStart_6772057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772067 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 1, 3, 2]
def baseStart_6772067 : Nat := 118140960795 + 6772067 * 2 ^ 59
def prefixEnd_6772067 : Nat := 4983230072969 + 3 ^ 40 * 6772067 * 2
def baseEnd_6772067 : Nat := 3477325395451460990418337

theorem tailTrace_6772067 : CollatzResearch.WordTrace tailWord_6772067 prefixEnd_6772067 3477325395451460990418337 := by
  unfold tailWord_6772067
  simp only [CollatzResearch.WordTrace]
  refine ⟨246997575156965310808914455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164665050104643540539276303 246997575156965310808914455)
  ·
    refine ⟨370496362735447966213371683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246997575156965310808914455 370496362735447966213371683)
    ·
      refine ⟨555744544103171949320057525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370496362735447966213371683 555744544103171949320057525)
      ·
        refine ⟨52101051009672370248755393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 555744544103171949320057525 52101051009672370248755393)
        ·
          refine ⟨39075788257254277686566545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52101051009672370248755393 39075788257254277686566545)
          ·
            refine ⟨29306841192940708264924909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39075788257254277686566545 29306841192940708264924909)
            ·
              refine ⟨10990065447352765599346841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29306841192940708264924909 10990065447352765599346841)
              ·
                refine ⟨8242549085514574199510131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10990065447352765599346841 8242549085514574199510131)
                ·
                  refine ⟨12363823628271861299265197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8242549085514574199510131 12363823628271861299265197)
                  ·
                    refine ⟨4636433860601947987224449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12363823628271861299265197 4636433860601947987224449)
                    ·
                      refine ⟨3477325395451460990418337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636433860601947987224449 3477325395451460990418337)
                      ·
                        rfl

theorem cell23_6772067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_6772067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772067 prefixEnd_6772067 := by exact prefixLift 6772067
  have htrace : WordTrace (prefixWord ++ tailWord_6772067) baseStart_6772067 baseEnd_6772067 := by
    simpa [prefixWord, tailWord_6772067, baseEnd_6772067] using wordTrace_append hprefix tailTrace_6772067
  have hstable : (prefixWord ++ tailWord_6772067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772067).length < 2 ^ (prefixWord ++ tailWord_6772067).sum := by decide
  have hdescent : baseEnd_6772067 < baseStart_6772067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772080 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 1, 4, 2]
def baseStart_6772080 : Nat := 118140960795 + 6772080 * 2 ^ 59
def prefixEnd_6772080 : Nat := 4983230072969 + 3 ^ 40 * 6772080 * 2
def baseEnd_6772080 : Nat := 3477332070699969439555777

theorem tailTrace_6772080 : CollatzResearch.WordTrace tailWord_6772080 prefixEnd_6772080 3477332070699969439555777 := by
  unfold tailWord_6772080
  simp only [CollatzResearch.WordTrace]
  refine ⟨123499024652959107014568847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164665366203945476019425129 123499024652959107014568847)
  ·
    refine ⟨185248536979438660521853271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123499024652959107014568847 185248536979438660521853271)
    ·
      refine ⟨277872805469157990782779907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185248536979438660521853271 277872805469157990782779907)
      ·
        refine ⟨416809208203736986174169861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277872805469157990782779907 416809208203736986174169861)
        ·
          refine ⟨78151726538200684907656849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 416809208203736986174169861 78151726538200684907656849)
          ·
            refine ⟨58613794903650513680742637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78151726538200684907656849 58613794903650513680742637)
            ·
              refine ⟨21980173088868942630278489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58613794903650513680742637 21980173088868942630278489)
              ·
                refine ⟨16485129816651706972708867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21980173088868942630278489 16485129816651706972708867)
                ·
                  refine ⟨24727694724977560459063301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16485129816651706972708867 24727694724977560459063301)
                  ·
                    refine ⟨4636442760933292586074369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24727694724977560459063301 4636442760933292586074369)
                    ·
                      refine ⟨3477332070699969439555777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636442760933292586074369 3477332070699969439555777)
                      ·
                        rfl

theorem cell23_6772080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 4, 2].length) (baseStart_6772080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772080 prefixEnd_6772080 := by exact prefixLift 6772080
  have htrace : WordTrace (prefixWord ++ tailWord_6772080) baseStart_6772080 baseEnd_6772080 := by
    simpa [prefixWord, tailWord_6772080, baseEnd_6772080] using wordTrace_append hprefix tailTrace_6772080
  have hstable : (prefixWord ++ tailWord_6772080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772080).length < 2 ^ (prefixWord ++ tailWord_6772080).sum := by decide
  have hdescent : baseEnd_6772080 < baseStart_6772080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772093 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_6772093 : Nat := 118140960795 + 6772093 * 2 ^ 59
def prefixEnd_6772093 : Nat := 4983230072969 + 3 ^ 40 * 6772093 * 2
def baseEnd_6772093 : Nat := 3477338745948477888693217

theorem tailTrace_6772093 : CollatzResearch.WordTrace tailWord_6772093 prefixEnd_6772093 3477338745948477888693217 := by
  unfold tailWord_6772093
  simp only [CollatzResearch.WordTrace]
  refine ⟨246998523454871117249360933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164665682303247411499573955 246998523454871117249360933)
  ·
    refine ⟨46312223147788334484255175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246998523454871117249360933 46312223147788334484255175)
    ·
      refine ⟨69468334721682501726382763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46312223147788334484255175 69468334721682501726382763)
      ·
        refine ⟨104202502082523752589574145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69468334721682501726382763 104202502082523752589574145)
        ·
          refine ⟨78151876561892814442180609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104202502082523752589574145 78151876561892814442180609)
          ·
            refine ⟨58613907421419610831635457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78151876561892814442180609 58613907421419610831635457)
            ·
              refine ⟨43960430566064708123726593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58613907421419610831635457 43960430566064708123726593)
              ·
                refine ⟨32970322924548531092794945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43960430566064708123726593 32970322924548531092794945)
                ·
                  refine ⟨24727742193411398319596209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32970322924548531092794945 24727742193411398319596209)
                  ·
                    refine ⟨18545806645058548739697157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24727742193411398319596209 18545806645058548739697157)
                    ·
                      refine ⟨3477338745948477888693217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18545806645058548739697157 3477338745948477888693217)
                      ·
                        rfl

theorem cell23_6772093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_6772093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772093 prefixEnd_6772093 := by exact prefixLift 6772093
  have htrace : WordTrace (prefixWord ++ tailWord_6772093) baseStart_6772093 baseEnd_6772093 := by
    simpa [prefixWord, tailWord_6772093, baseEnd_6772093] using wordTrace_append hprefix tailTrace_6772093
  have hstable : (prefixWord ++ tailWord_6772093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772093).length < 2 ^ (prefixWord ++ tailWord_6772093).sum := by decide
  have hdescent : baseEnd_6772093 < baseStart_6772093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772096 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_6772096 : Nat := 118140960795 + 6772096 * 2 ^ 59
def prefixEnd_6772096 : Nat := 4983230072969 + 3 ^ 40 * 6772096 * 2
def baseEnd_6772096 : Nat := 3477340286390441376955703

theorem tailTrace_6772096 : CollatzResearch.WordTrace tailWord_6772096 prefixEnd_6772096 3477340286390441376955703 := by
  unfold tailWord_6772096
  simp only [CollatzResearch.WordTrace]
  refine ⟨123499316436930124380860071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164665755249240165841146761 123499316436930124380860071)
  ·
    refine ⟨185248974655395186571290107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123499316436930124380860071 185248974655395186571290107)
    ·
      refine ⟨277873461983092779856935161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185248974655395186571290107 277873461983092779856935161)
      ·
        refine ⟨208405096487319584892701371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277873461983092779856935161 208405096487319584892701371)
        ·
          refine ⟨312607644730979377339052057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208405096487319584892701371 312607644730979377339052057)
          ·
            refine ⟨234455733548234533004289043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312607644730979377339052057 234455733548234533004289043)
            ·
              refine ⟨351683600322351799506433565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234455733548234533004289043 351683600322351799506433565)
              ·
                refine ⟨131881350120881924814912587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351683600322351799506433565 131881350120881924814912587)
                ·
                  refine ⟨197822025181322887222368881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131881350120881924814912587 197822025181322887222368881)
                  ·
                    refine ⟨148366518885992165416776661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197822025181322887222368881 148366518885992165416776661)
                    ·
                      refine ⟨3477340286390441376955703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148366518885992165416776661 3477340286390441376955703)
                      ·
                        rfl

theorem cell23_6772096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_6772096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772096 prefixEnd_6772096 := by exact prefixLift 6772096
  have htrace : WordTrace (prefixWord ++ tailWord_6772096) baseStart_6772096 baseEnd_6772096 := by
    simpa [prefixWord, tailWord_6772096, baseEnd_6772096] using wordTrace_append hprefix tailTrace_6772096
  have hstable : (prefixWord ++ tailWord_6772096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772096).length < 2 ^ (prefixWord ++ tailWord_6772096).sum := by decide
  have hdescent : baseEnd_6772096 < baseStart_6772096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772113 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 3]
def baseStart_6772113 : Nat := 118140960795 + 6772113 * 2 ^ 59
def prefixEnd_6772113 : Nat := 4983230072969 + 3 ^ 40 * 6772113 * 2
def baseEnd_6772113 : Nat := 3477349015561567810443125

theorem tailTrace_6772113 : CollatzResearch.WordTrace tailWord_6772113 prefixEnd_6772113 3477349015561567810443125 := by
  unfold tailWord_6772113
  simp only [CollatzResearch.WordTrace]
  refine ⟨246999252914798660665088993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164666168609865773776725995 246999252914798660665088993)
  ·
    refine ⟨185249439686098995498816745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246999252914798660665088993 185249439686098995498816745)
    ·
      refine ⟨138937079764574246624112559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185249439686098995498816745 138937079764574246624112559)
      ·
        refine ⟨208405619646861369936168839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138937079764574246624112559 208405619646861369936168839)
        ·
          refine ⟨312608429470292054904253259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208405619646861369936168839 312608429470292054904253259)
          ·
            refine ⟨468912644205438082356379889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312608429470292054904253259 468912644205438082356379889)
            ·
              refine ⟨351684483154078561767284917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468912644205438082356379889 351684483154078561767284917)
              ·
                refine ⟨32970420295694865165682961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351684483154078561767284917 32970420295694865165682961)
                ·
                  refine ⟨24727815221771148874262221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32970420295694865165682961 24727815221771148874262221)
                  ·
                    refine ⟨9272930708164180827848333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24727815221771148874262221 9272930708164180827848333)
                    ·
                      refine ⟨3477349015561567810443125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9272930708164180827848333 3477349015561567810443125)
                      ·
                        rfl

theorem cell23_6772113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_6772113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772113 prefixEnd_6772113 := by exact prefixLift 6772113
  have htrace : WordTrace (prefixWord ++ tailWord_6772113) baseStart_6772113 baseEnd_6772113 := by
    simpa [prefixWord, tailWord_6772113, baseEnd_6772113] using wordTrace_append hprefix tailTrace_6772113
  have hstable : (prefixWord ++ tailWord_6772113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772113).length < 2 ^ (prefixWord ++ tailWord_6772113).sum := by decide
  have hdescent : baseEnd_6772113 < baseStart_6772113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772120 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 7]
def baseStart_6772120 : Nat := 118140960795 + 6772120 * 2 ^ 59
def prefixEnd_6772120 : Nat := 4983230072969 + 3 ^ 40 * 6772120 * 2
def baseEnd_6772120 : Nat := 386372512214016587006177

theorem tailTrace_6772120 : CollatzResearch.WordTrace tailWord_6772120 prefixEnd_6772120 386372512214016587006177 := by
  unfold tailWord_6772120
  simp only [CollatzResearch.WordTrace]
  refine ⟨123499754112886650430296907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164666338817182200573729209 123499754112886650430296907)
  ·
    refine ⟨185249631169329975645445361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123499754112886650430296907 185249631169329975645445361)
    ·
      refine ⟨138937223376997481734084021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185249631169329975645445361 138937223376997481734084021)
      ·
        refine ⟨13025364691593513912570377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138937223376997481734084021 13025364691593513912570377)
        ·
          refine ⟨9769023518695135434427783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13025364691593513912570377 9769023518695135434427783)
          ·
            refine ⟨14653535278042703151641675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9769023518695135434427783 14653535278042703151641675)
            ·
              refine ⟨21980302917064054727462513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14653535278042703151641675 21980302917064054727462513)
              ·
                refine ⟨16485227187798041045596885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21980302917064054727462513 16485227187798041045596885)
                ·
                  refine ⟨386372512214016587006177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16485227187798041045596885 386372512214016587006177)
                  ·
                    rfl

theorem cell23_6772120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 7].length) (baseStart_6772120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772120 prefixEnd_6772120 := by exact prefixLift 6772120
  have htrace : WordTrace (prefixWord ++ tailWord_6772120) baseStart_6772120 baseEnd_6772120 := by
    simpa [prefixWord, tailWord_6772120, baseEnd_6772120] using wordTrace_append hprefix tailTrace_6772120
  have hstable : (prefixWord ++ tailWord_6772120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772120).length < 2 ^ (prefixWord ++ tailWord_6772120).sum := by decide
  have hdescent : baseEnd_6772120 < baseStart_6772120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772133 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_6772133 : Nat := 118140960795 + 6772133 * 2 ^ 59
def prefixEnd_6772133 : Nat := 4983230072969 + 3 ^ 40 * 6772133 * 2
def baseEnd_6772133 : Nat := 1159119761724885910731011

theorem tailTrace_6772133 : CollatzResearch.WordTrace tailWord_6772133 prefixEnd_6772133 1159119761724885910731011 := by
  unfold tailWord_6772133
  simp only [CollatzResearch.WordTrace]
  refine ⟨246999982374726204080817053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164666654916484136053878035 246999982374726204080817053)
  ·
    refine ⟨92624993390522326530306395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246999982374726204080817053 92624993390522326530306395)
    ·
      refine ⟨138937490085783489795459593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92624993390522326530306395 138937490085783489795459593)
      ·
        refine ⟨104203117564337617346594695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138937490085783489795459593 104203117564337617346594695)
        ·
          refine ⟨156304676346506426019892043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104203117564337617346594695 156304676346506426019892043)
          ·
            refine ⟨234457014519759639029838065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156304676346506426019892043 234457014519759639029838065)
            ·
              refine ⟨175842760889819729272378549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234457014519759639029838065 175842760889819729272378549)
              ·
                refine ⟨16485258833420599619285489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175842760889819729272378549 16485258833420599619285489)
                ·
                  refine ⟨12363944125065449714464117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16485258833420599619285489 12363944125065449714464117)
                  ·
                    refine ⟨1159119761724885910731011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12363944125065449714464117 1159119761724885910731011)
                    ·
                      rfl

theorem cell23_6772133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_6772133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772133 prefixEnd_6772133 := by exact prefixLift 6772133
  have htrace : WordTrace (prefixWord ++ tailWord_6772133) baseStart_6772133 baseEnd_6772133 := by
    simpa [prefixWord, tailWord_6772133, baseEnd_6772133] using wordTrace_append hprefix tailTrace_6772133
  have hstable : (prefixWord ++ tailWord_6772133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772133).length < 2 ^ (prefixWord ++ tailWord_6772133).sum := by decide
  have hdescent : baseEnd_6772133 < baseStart_6772133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772193 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 8]
def baseStart_6772193 : Nat := 118140960795 + 6772193 * 2 ^ 59
def prefixEnd_6772193 : Nat := 4983230072969 + 3 ^ 40 * 6772193 * 2
def baseEnd_6772193 : Nat := 386376677112658610826973

theorem tailTrace_6772193 : CollatzResearch.WordTrace tailWord_6772193 prefixEnd_6772193 386376677112658610826973 := by
  unfold tailWord_6772193
  simp only [CollatzResearch.WordTrace]
  refine ⟨247002170754508834328001233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164668113836339222885334155 247002170754508834328001233)
  ·
    refine ⟨185251628065881625746000925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247002170754508834328001233 185251628065881625746000925)
    ·
      refine ⟨69469360524705609654750347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185251628065881625746000925 69469360524705609654750347)
      ·
        refine ⟨104204040787058414482125521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69469360524705609654750347 104204040787058414482125521)
        ·
          refine ⟨78153030590293810861594141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104204040787058414482125521 78153030590293810861594141)
          ·
            refine ⟨29307386471360179073097803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78153030590293810861594141 29307386471360179073097803)
            ·
              refine ⟨43961079707040268609646705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29307386471360179073097803 43961079707040268609646705)
              ·
                refine ⟨32970809780280201457235029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43961079707040268609646705 32970809780280201457235029)
                ·
                  refine ⟨386376677112658610826973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32970809780280201457235029 386376677112658610826973)
                  ·
                    rfl

theorem cell23_6772193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 8].length) (baseStart_6772193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772193 prefixEnd_6772193 := by exact prefixLift 6772193
  have htrace : WordTrace (prefixWord ++ tailWord_6772193) baseStart_6772193 baseEnd_6772193 := by
    simpa [prefixWord, tailWord_6772193, baseEnd_6772193] using wordTrace_append hprefix tailTrace_6772193
  have hstable : (prefixWord ++ tailWord_6772193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772193).length < 2 ^ (prefixWord ++ tailWord_6772193).sum := by decide
  have hdescent : baseEnd_6772193 < baseStart_6772193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772210 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 8]
def baseStart_6772210 : Nat := 118140960795 + 6772210 * 2 ^ 59
def prefixEnd_6772210 : Nat := 4983230072969 + 3 ^ 40 * 6772210 * 2
def baseEnd_6772210 : Nat := 386377647020561547881131

theorem tailTrace_6772210 : CollatzResearch.WordTrace tailWord_6772210 prefixEnd_6772210 386377647020561547881131 := by
  unfold tailWord_6772210
  simp only [CollatzResearch.WordTrace]
  refine ⟨61750697698861811557842521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164668527196964830820913389 61750697698861811557842521)
  ·
    refine ⟨46313023274146358668381891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61750697698861811557842521 46313023274146358668381891)
    ·
      refine ⟨69469534911219538002572837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46313023274146358668381891 69469534911219538002572837)
      ·
        refine ⟨13025537795853663375482407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69469534911219538002572837 13025537795853663375482407)
        ·
          refine ⟨19538306693780495063223611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13025537795853663375482407 19538306693780495063223611)
          ·
            refine ⟨29307460040670742594835417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19538306693780495063223611 29307460040670742594835417)
            ·
              refine ⟨21980595030503056946126563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29307460040670742594835417 21980595030503056946126563)
              ·
                refine ⟨32970892545754585419189845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21980595030503056946126563 32970892545754585419189845)
                ·
                  refine ⟨386377647020561547881131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32970892545754585419189845 386377647020561547881131)
                  ·
                    rfl

theorem cell23_6772210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_6772210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772210 prefixEnd_6772210 := by exact prefixLift 6772210
  have htrace : WordTrace (prefixWord ++ tailWord_6772210) baseStart_6772210 baseEnd_6772210 := by
    simpa [prefixWord, tailWord_6772210, baseEnd_6772210] using wordTrace_append hprefix tailTrace_6772210
  have hstable : (prefixWord ++ tailWord_6772210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772210).length < 2 ^ (prefixWord ++ tailWord_6772210).sum := by decide
  have hdescent : baseEnd_6772210 < baseStart_6772210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772214 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_6772214 : Nat := 118140960795 + 6772214 * 2 ^ 59
def prefixEnd_6772214 : Nat := 4983230072969 + 3 ^ 40 * 6772214 * 2
def baseEnd_6772214 : Nat := 1159133625702557305093387

theorem tailTrace_6772214 : CollatzResearch.WordTrace tailWord_6772214 prefixEnd_6772214 1159133625702557305093387 := by
  unfold tailWord_6772214
  simp only [CollatzResearch.WordTrace]
  refine ⟨15437683542964547182157231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164668624458288503276343797 15437683542964547182157231)
  ·
    refine ⟨23156525314446820773235847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15437683542964547182157231 23156525314446820773235847)
    ·
      refine ⟨34734787971670231159853771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23156525314446820773235847 34734787971670231159853771)
      ·
        refine ⟨52102181957505346739780657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34734787971670231159853771 52102181957505346739780657)
        ·
          refine ⟨39076636468129010054835493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52102181957505346739780657 39076636468129010054835493)
          ·
            refine ⟨7326869337774189385281655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39076636468129010054835493 7326869337774189385281655)
            ·
              refine ⟨10990304006661284077922483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7326869337774189385281655 10990304006661284077922483)
              ·
                refine ⟨16485456009991926116883725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10990304006661284077922483 16485456009991926116883725)
                ·
                  refine ⟨6182046003746972293831397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16485456009991926116883725 6182046003746972293831397)
                  ·
                    refine ⟨1159133625702557305093387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6182046003746972293831397 1159133625702557305093387)
                    ·
                      rfl

theorem cell23_6772214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_6772214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772214 prefixEnd_6772214 := by exact prefixLift 6772214
  have htrace : WordTrace (prefixWord ++ tailWord_6772214) baseStart_6772214 baseEnd_6772214 := by
    simpa [prefixWord, tailWord_6772214, baseEnd_6772214] using wordTrace_append hprefix tailTrace_6772214
  have hstable : (prefixWord ++ tailWord_6772214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772214).length < 2 ^ (prefixWord ++ tailWord_6772214).sum := by decide
  have hdescent : baseEnd_6772214 < baseStart_6772214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772287 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 2, 4]
def baseStart_6772287 : Nat := 118140960795 + 6772287 * 2 ^ 59
def prefixEnd_6772287 : Nat := 4983230072969 + 3 ^ 40 * 6772287 * 2
def baseEnd_6772287 : Nat := 1159146120398483376555775

theorem tailTrace_6772287 : CollatzResearch.WordTrace tailWord_6772287 prefixEnd_6772287 1159146120398483376555775 := by
  unfold tailWord_6772287
  simp only [CollatzResearch.WordTrace]
  refine ⟨247005599216168288381923115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164670399477445525587948743 247005599216168288381923115)
  ·
    refine ⟨370508398824252432572884673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247005599216168288381923115 370508398824252432572884673)
    ·
      refine ⟨277881299118189324429663505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370508398824252432572884673 277881299118189324429663505)
      ·
        refine ⟨208410974338641993322247629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277881299118189324429663505 208410974338641993322247629)
        ·
          refine ⟨78154115376990747495842861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208410974338641993322247629 78154115376990747495842861)
          ·
            refine ⟨29307793266371530310941073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78154115376990747495842861 29307793266371530310941073)
            ·
              refine ⟨21980844949778647733205805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29307793266371530310941073 21980844949778647733205805)
              ·
                refine ⟨8242816856166992899952177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21980844949778647733205805 8242816856166992899952177)
                ·
                  refine ⟨6182112642125244674964133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8242816856166992899952177 6182112642125244674964133)
                  ·
                    refine ⟨1159146120398483376555775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6182112642125244674964133 1159146120398483376555775)
                    ·
                      rfl

theorem cell23_6772287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 4].length) (baseStart_6772287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772287 prefixEnd_6772287 := by exact prefixLift 6772287
  have htrace : WordTrace (prefixWord ++ tailWord_6772287) baseStart_6772287 baseEnd_6772287 := by
    simpa [prefixWord, tailWord_6772287, baseEnd_6772287] using wordTrace_append hprefix tailTrace_6772287
  have hstable : (prefixWord ++ tailWord_6772287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772287).length < 2 ^ (prefixWord ++ tailWord_6772287).sum := by decide
  have hdescent : baseEnd_6772287 < baseStart_6772287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772311 : List Nat := [1, 1, 3, 2, 2, 3, 1, 5, 1, 2, 2]
def baseStart_6772311 : Nat := 118140960795 + 6772311 * 2 ^ 59
def prefixEnd_6772311 : Nat := 4983230072969 + 3 ^ 40 * 6772311 * 2
def baseEnd_6772311 : Nat := 3477450684731158035767215

theorem tailTrace_6772311 : CollatzResearch.WordTrace tailWord_6772311 prefixEnd_6772311 3477450684731158035767215 := by
  unfold tailWord_6772311
  simp only [CollatzResearch.WordTrace]
  refine ⟨247006474568081340480796787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164670983045387560320531191 247006474568081340480796787)
  ·
    refine ⟨370509711852122010721195181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247006474568081340480796787 370509711852122010721195181)
    ·
      refine ⟨138941141944545754020448193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370509711852122010721195181 138941141944545754020448193)
      ·
        refine ⟨104205856458409315515336145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138941141944545754020448193 104205856458409315515336145)
        ·
          refine ⟨78154392343806986636502109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104205856458409315515336145 78154392343806986636502109)
          ·
            refine ⟨29307897128927619988688291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78154392343806986636502109 29307897128927619988688291)
            ·
              refine ⟨43961845693391429983032437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29307897128927619988688291 43961845693391429983032437)
              ·
                refine ⟨4121423033755446560909291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43961845693391429983032437 4121423033755446560909291)
                ·
                  refine ⟨6182134550633169841363937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4121423033755446560909291 6182134550633169841363937)
                  ·
                    refine ⟨4636600912974877381022953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6182134550633169841363937 4636600912974877381022953)
                    ·
                      refine ⟨3477450684731158035767215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636600912974877381022953 3477450684731158035767215)
                      ·
                        rfl

theorem cell23_6772311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_6772311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772311 prefixEnd_6772311 := by exact prefixLift 6772311
  have htrace : WordTrace (prefixWord ++ tailWord_6772311) baseStart_6772311 baseEnd_6772311 := by
    simpa [prefixWord, tailWord_6772311, baseEnd_6772311] using wordTrace_append hprefix tailTrace_6772311
  have hstable : (prefixWord ++ tailWord_6772311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772311).length < 2 ^ (prefixWord ++ tailWord_6772311).sum := by decide
  have hdescent : baseEnd_6772311 < baseStart_6772311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772328 : List Nat := [2, 1, 4, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6772328 : Nat := 118140960795 + 6772328 * 2 ^ 59
def prefixEnd_6772328 : Nat := 4983230072969 + 3 ^ 40 * 6772328 * 2
def baseEnd_6772328 : Nat := 3477459413902284469254637

theorem tailTrace_6772328 : CollatzResearch.WordTrace tailWord_6772328 prefixEnd_6772328 3477459413902284469254637 := by
  unfold tailWord_6772328
  simp only [CollatzResearch.WordTrace]
  refine ⟨123503547304509876192082819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164671396406013168256110425 123503547304509876192082819)
  ·
    refine ⟨185255320956764814288124229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123503547304509876192082819 185255320956764814288124229)
    ·
      refine ⟨34735372679393402679023293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185255320956764814288124229 34735372679393402679023293)
      ·
        refine ⟨13025764754772526004633735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34735372679393402679023293 13025764754772526004633735)
        ·
          refine ⟨19538647132158789006950603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13025764754772526004633735 19538647132158789006950603)
          ·
            refine ⟨29307970698238183510425905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19538647132158789006950603 29307970698238183510425905)
            ·
              refine ⟨21980978023678637632819429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29307970698238183510425905 21980978023678637632819429)
              ·
                refine ⟨4121433379439744556153643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21980978023678637632819429 4121433379439744556153643)
                ·
                  refine ⟨6182150069159616834230465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4121433379439744556153643 6182150069159616834230465)
                  ·
                    refine ⟨4636612551869712625672849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6182150069159616834230465 4636612551869712625672849)
                    ·
                      refine ⟨3477459413902284469254637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636612551869712625672849 3477459413902284469254637)
                      ·
                        rfl

theorem cell23_6772328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6772328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772328 prefixEnd_6772328 := by exact prefixLift 6772328
  have htrace : WordTrace (prefixWord ++ tailWord_6772328) baseStart_6772328 baseEnd_6772328 := by
    simpa [prefixWord, tailWord_6772328, baseEnd_6772328] using wordTrace_append hprefix tailTrace_6772328
  have hstable : (prefixWord ++ tailWord_6772328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772328).length < 2 ^ (prefixWord ++ tailWord_6772328).sum := by decide
  have hdescent : baseEnd_6772328 < baseStart_6772328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772337 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 5, 3, 2]
def baseStart_6772337 : Nat := 118140960795 + 6772337 * 2 ^ 59
def prefixEnd_6772337 : Nat := 4983230072969 + 3 ^ 40 * 6772337 * 2
def baseEnd_6772337 : Nat := 3477464035228174934042095

theorem tailTrace_6772337 : CollatzResearch.WordTrace tailWord_6772337 prefixEnd_6772337 3477464035228174934042095 := by
  unfold tailWord_6772337
  simp only [CollatzResearch.WordTrace]
  refine ⟨247007422865987146921243265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164671615243991431280828843 247007422865987146921243265)
  ·
    refine ⟨185255567149490360190932449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247007422865987146921243265 185255567149490360190932449)
    ·
      refine ⟨138941675362117770143199337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185255567149490360190932449 138941675362117770143199337)
      ·
        refine ⟨104206256521588327607399503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138941675362117770143199337 104206256521588327607399503)
        ·
          refine ⟨156309384782382491411099255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104206256521588327607399503 156309384782382491411099255)
          ·
            refine ⟨234464077173573737116648883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156309384782382491411099255 234464077173573737116648883)
            ·
              refine ⟨351696115760360605674973325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234464077173573737116648883 351696115760360605674973325)
              ·
                refine ⟨131886043410135227128114997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351696115760360605674973325 131886043410135227128114997)
                ·
                  refine ⟨12364316569700177543260781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131886043410135227128114997 12364316569700177543260781)
                  ·
                    refine ⟨4636618713637566578722793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12364316569700177543260781 4636618713637566578722793)
                    ·
                      refine ⟨3477464035228174934042095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636618713637566578722793 3477464035228174934042095)
                      ·
                        rfl

theorem cell23_6772337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_6772337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772337 prefixEnd_6772337 := by exact prefixLift 6772337
  have htrace : WordTrace (prefixWord ++ tailWord_6772337) baseStart_6772337 baseEnd_6772337 := by
    simpa [prefixWord, tailWord_6772337, baseEnd_6772337] using wordTrace_append hprefix tailTrace_6772337
  have hstable : (prefixWord ++ tailWord_6772337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772337).length < 2 ^ (prefixWord ++ tailWord_6772337).sum := by decide
  have hdescent : baseEnd_6772337 < baseStart_6772337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772397 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_6772397 : Nat := 118140960795 + 6772397 * 2 ^ 59
def prefixEnd_6772397 : Nat := 4983230072969 + 3 ^ 40 * 6772397 * 2
def baseEnd_6772397 : Nat := 3477494844067444699291819

theorem tailTrace_6772397 : CollatzResearch.WordTrace tailWord_6772397 prefixEnd_6772397 3477494844067444699291819 := by
  unfold tailWord_6772397
  simp only [CollatzResearch.WordTrace]
  refine ⟨247009611245769777168427445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164673074163846518112284963 247009611245769777168427445)
  ·
    refine ⟨23157151054290916609540073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247009611245769777168427445 23157151054290916609540073)
    ·
      refine ⟨17367863290718187457155055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23157151054290916609540073 17367863290718187457155055)
      ·
        refine ⟨26051794936077281185732583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17367863290718187457155055 26051794936077281185732583)
        ·
          refine ⟨39077692404115921778598875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26051794936077281185732583 39077692404115921778598875)
          ·
            refine ⟨58616538606173882667898313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39077692404115921778598875 58616538606173882667898313)
            ·
              refine ⟨43962403954630412000923735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58616538606173882667898313 43962403954630412000923735)
              ·
                refine ⟨65943605931945618001385603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43962403954630412000923735 65943605931945618001385603)
                ·
                  refine ⟨98915408897918427002078405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65943605931945618001385603 98915408897918427002078405)
                  ·
                    refine ⟨18546639168359705062889701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98915408897918427002078405 18546639168359705062889701)
                    ·
                      refine ⟨3477494844067444699291819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18546639168359705062889701 3477494844067444699291819)
                      ·
                        rfl

theorem cell23_6772397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_6772397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772397 prefixEnd_6772397 := by exact prefixLift 6772397
  have htrace : WordTrace (prefixWord ++ tailWord_6772397) baseStart_6772397 baseEnd_6772397 := by
    simpa [prefixWord, tailWord_6772397, baseEnd_6772397] using wordTrace_append hprefix tailTrace_6772397
  have hstable : (prefixWord ++ tailWord_6772397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772397).length < 2 ^ (prefixWord ++ tailWord_6772397).sum := by decide
  have hdescent : baseEnd_6772397 < baseStart_6772397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772405 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_6772405 : Nat := 118140960795 + 6772405 * 2 ^ 59
def prefixEnd_6772405 : Nat := 4983230072969 + 3 ^ 40 * 6772405 * 2
def baseEnd_6772405 : Nat := 3477498951912680667991783

theorem tailTrace_6772405 : CollatzResearch.WordTrace tailWord_6772405 prefixEnd_6772405 3477498951912680667991783 := by
  unfold tailWord_6772405
  simp only [CollatzResearch.WordTrace]
  refine ⟨247009903029740794534718669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164673268686493863023145779 247009903029740794534718669)
  ·
    refine ⟨92628713636152797950519501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247009903029740794534718669 92628713636152797950519501)
    ·
      refine ⟨34735767613557299231444813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92628713636152797950519501 34735767613557299231444813)
      ·
        refine ⟨13025912855083987211791805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34735767613557299231444813 13025912855083987211791805)
        ·
          refine ⟨4884717320656495204421927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13025912855083987211791805 4884717320656495204421927)
          ·
            refine ⟨7327075980984742806632891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4884717320656495204421927 7327075980984742806632891)
            ·
              refine ⟨10990613971477114209949337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7327075980984742806632891 10990613971477114209949337)
              ·
                refine ⟨8242960478607835657462003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10990613971477114209949337 8242960478607835657462003)
                ·
                  refine ⟨12364440717911753486193005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8242960478607835657462003 12364440717911753486193005)
                  ·
                    refine ⟨4636665269216907557322377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12364440717911753486193005 4636665269216907557322377)
                    ·
                      refine ⟨3477498951912680667991783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636665269216907557322377 3477498951912680667991783)
                      ·
                        rfl

theorem cell23_6772405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_6772405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772405 prefixEnd_6772405 := by exact prefixLift 6772405
  have htrace : WordTrace (prefixWord ++ tailWord_6772405) baseStart_6772405 baseEnd_6772405 := by
    simpa [prefixWord, tailWord_6772405, baseEnd_6772405] using wordTrace_append hprefix tailTrace_6772405
  have hstable : (prefixWord ++ tailWord_6772405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772405).length < 2 ^ (prefixWord ++ tailWord_6772405).sum := by decide
  have hdescent : baseEnd_6772405 < baseStart_6772405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772422 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_6772422 : Nat := 118140960795 + 6772422 * 2 ^ 59
def prefixEnd_6772422 : Nat := 4983230072969 + 3 ^ 40 * 6772422 * 2
def baseEnd_6772422 : Nat := 3477507681083807101479205

theorem tailTrace_6772422 : CollatzResearch.WordTrace tailWord_6772422 prefixEnd_6772422 3477507681083807101479205 := by
  unfold tailWord_6772422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7719078845958725201190235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 164673682047119470958725013 7719078845958725201190235)
  ·
    refine ⟨11578618268938087801785353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7719078845958725201190235 11578618268938087801785353)
    ·
      refine ⟨8683963701703565851339015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11578618268938087801785353 8683963701703565851339015)
      ·
        refine ⟨13025945552555348777008523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8683963701703565851339015 13025945552555348777008523)
        ·
          refine ⟨19538918328833023165512785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13025945552555348777008523 19538918328833023165512785)
          ·
            refine ⟨14654188746624767374134589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19538918328833023165512785 14654188746624767374134589)
            ·
              refine ⟨5495320779984287765300471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14654188746624767374134589 5495320779984287765300471)
              ·
                refine ⟨8242981169976431647950707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495320779984287765300471 8242981169976431647950707)
                ·
                  refine ⟨12364471754964647471926061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8242981169976431647950707 12364471754964647471926061)
                  ·
                    refine ⟨4636676908111742801972273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12364471754964647471926061 4636676908111742801972273)
                    ·
                      refine ⟨3477507681083807101479205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636676908111742801972273 3477507681083807101479205)
                      ·
                        rfl

theorem cell23_6772422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_6772422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772422 prefixEnd_6772422 := by exact prefixLift 6772422
  have htrace : WordTrace (prefixWord ++ tailWord_6772422) baseStart_6772422 baseEnd_6772422 := by
    simpa [prefixWord, tailWord_6772422, baseEnd_6772422] using wordTrace_append hprefix tailTrace_6772422
  have hstable : (prefixWord ++ tailWord_6772422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772422).length < 2 ^ (prefixWord ++ tailWord_6772422).sum := by decide
  have hdescent : baseEnd_6772422 < baseStart_6772422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772427 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 4, 5, 2]
def baseStart_6772427 : Nat := 118140960795 + 6772427 * 2 ^ 59
def prefixEnd_6772427 : Nat := 4983230072969 + 3 ^ 40 * 6772427 * 2
def baseEnd_6772427 : Nat := 3477510248487079581916681

theorem tailTrace_6772427 : CollatzResearch.WordTrace tailWord_6772427 prefixEnd_6772427 3477510248487079581916681 := by
  unfold tailWord_6772427
  simp only [CollatzResearch.WordTrace]
  refine ⟨247010705435661092292019535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164673803623774061528013023 247010705435661092292019535)
  ·
    refine ⟨370516058153491638438029303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247010705435661092292019535 370516058153491638438029303)
    ·
      refine ⟨555774087230237457657043955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370516058153491638438029303 555774087230237457657043955)
      ·
        refine ⟨833661130845356186485565933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555774087230237457657043955 833661130845356186485565933)
        ·
          refine ⟨312622924067008569932087225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 833661130845356186485565933 312622924067008569932087225)
          ·
            refine ⟨234467193050256427449065419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312622924067008569932087225 234467193050256427449065419)
            ·
              refine ⟨351700789575384641173598129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234467193050256427449065419 351700789575384641173598129)
              ·
                refine ⟨263775592181538480880198597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351700789575384641173598129 263775592181538480880198597)
                ·
                  refine ⟨49457923534038465165037237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263775592181538480880198597 49457923534038465165037237)
                  ·
                    refine ⟨4636680331316106109222241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49457923534038465165037237 4636680331316106109222241)
                    ·
                      refine ⟨3477510248487079581916681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636680331316106109222241 3477510248487079581916681)
                      ·
                        rfl

theorem cell23_6772427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 5, 2].length) (baseStart_6772427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772427 prefixEnd_6772427 := by exact prefixLift 6772427
  have htrace : WordTrace (prefixWord ++ tailWord_6772427) baseStart_6772427 baseEnd_6772427 := by
    simpa [prefixWord, tailWord_6772427, baseEnd_6772427] using wordTrace_append hprefix tailTrace_6772427
  have hstable : (prefixWord ++ tailWord_6772427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772427).length < 2 ^ (prefixWord ++ tailWord_6772427).sum := by decide
  have hdescent : baseEnd_6772427 < baseStart_6772427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772441 : List Nat := [1, 2, 1, 2, 3, 5, 2, 2, 5]
def baseStart_6772441 : Nat := 118140960795 + 6772441 * 2 ^ 59
def prefixEnd_6772441 : Nat := 4983230072969 + 3 ^ 40 * 6772441 * 2
def baseEnd_6772441 : Nat := 386390826357360280793513

theorem tailTrace_6772441 : CollatzResearch.WordTrace tailWord_6772441 prefixEnd_6772441 386390826357360280793513 := by
  unfold tailWord_6772441
  simp only [CollatzResearch.WordTrace]
  refine ⟨247011216057610372683029177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164674144038406915122019451 247011216057610372683029177)
  ·
    refine ⟨185258412043207779512271883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247011216057610372683029177 185258412043207779512271883)
    ·
      refine ⟨277887618064811669268407825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185258412043207779512271883 277887618064811669268407825)
      ·
        refine ⟨208415713548608751951305869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277887618064811669268407825 208415713548608751951305869)
        ·
          refine ⟨78155892580728281981739701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208415713548608751951305869 78155892580728281981739701)
          ·
            refine ⟨7327114929443276435788097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78155892580728281981739701 7327114929443276435788097)
            ·
              refine ⟨5495336197082457326841073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7327114929443276435788097 5495336197082457326841073)
              ·
                refine ⟨4121502147811842995130805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5495336197082457326841073 4121502147811842995130805)
                ·
                  refine ⟨386390826357360280793513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4121502147811842995130805 386390826357360280793513)
                  ·
                    rfl

theorem cell23_6772441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 5].length) (baseStart_6772441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772441 prefixEnd_6772441 := by exact prefixLift 6772441
  have htrace : WordTrace (prefixWord ++ tailWord_6772441) baseStart_6772441 baseEnd_6772441 := by
    simpa [prefixWord, tailWord_6772441, baseEnd_6772441] using wordTrace_append hprefix tailTrace_6772441
  have hstable : (prefixWord ++ tailWord_6772441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772441).length < 2 ^ (prefixWord ++ tailWord_6772441).sum := by decide
  have hdescent : baseEnd_6772441 < baseStart_6772441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772467 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 5, 4]
def baseStart_6772467 : Nat := 118140960795 + 6772467 * 2 ^ 59
def prefixEnd_6772467 : Nat := 4983230072969 + 3 ^ 40 * 6772467 * 2
def baseEnd_6772467 : Nat := 1159176929237753141805499

theorem tailTrace_6772467 : CollatzResearch.WordTrace tailWord_6772467 prefixEnd_6772467 1159176929237753141805499 := by
  unfold tailWord_6772467
  simp only [CollatzResearch.WordTrace]
  refine ⟨247012164355516179123475655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164674776237010786082317103 247012164355516179123475655)
  ·
    refine ⟨370518246533274268685213483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247012164355516179123475655 370518246533274268685213483)
    ·
      refine ⟨555777369799911403027820225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370518246533274268685213483 555777369799911403027820225)
      ·
        refine ⟨416833027349933552270865169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555777369799911403027820225 416833027349933552270865169)
        ·
          refine ⟨312624770512450164203148877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416833027349933552270865169 312624770512450164203148877)
          ·
            refine ⟨117234288942168811576180829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312624770512450164203148877 117234288942168811576180829)
            ·
              refine ⟨43962858353313304341067811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117234288942168811576180829 43962858353313304341067811)
              ·
                refine ⟨65944287529969956511601717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43962858353313304341067811 65944287529969956511601717)
                ·
                  refine ⟨6182276955934683422962661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65944287529969956511601717 6182276955934683422962661)
                  ·
                    refine ⟨1159176929237753141805499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6182276955934683422962661 1159176929237753141805499)
                    ·
                      rfl

theorem cell23_6772467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 4].length) (baseStart_6772467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772467 prefixEnd_6772467 := by exact prefixLift 6772467
  have htrace : WordTrace (prefixWord ++ tailWord_6772467) baseStart_6772467 baseEnd_6772467 := by
    simpa [prefixWord, tailWord_6772467, baseEnd_6772467] using wordTrace_append hprefix tailTrace_6772467
  have hstable : (prefixWord ++ tailWord_6772467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772467).length < 2 ^ (prefixWord ++ tailWord_6772467).sum := by decide
  have hdescent : baseEnd_6772467 < baseStart_6772467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772480 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 10]
def baseStart_6772480 : Nat := 118140960795 + 6772480 * 2 ^ 59
def prefixEnd_6772480 : Nat := 4983230072969 + 3 ^ 40 * 6772480 * 2
def baseEnd_6772480 : Nat := 386393051440196430505993

theorem tailTrace_6772480 : CollatzResearch.WordTrace tailWord_6772480 prefixEnd_6772480 386393051440196430505993 := by
  unfold tailWord_6772480
  simp only [CollatzResearch.WordTrace]
  refine ⟨123506319252234541171849447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164675092336312721562465929 123506319252234541171849447)
  ·
    refine ⟨185259478878351811757774171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123506319252234541171849447 185259478878351811757774171)
    ·
      refine ⟨277889218317527717636661257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185259478878351811757774171 277889218317527717636661257)
      ·
        refine ⟨208416913738145788227495943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277889218317527717636661257 208416913738145788227495943)
        ·
          refine ⟨312625370607218682341243915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208416913738145788227495943 312625370607218682341243915)
          ·
            refine ⟨468938055910828023511865873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312625370607218682341243915 468938055910828023511865873)
            ·
              refine ⟨351703541933121017633899405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468938055910828023511865873 351703541933121017633899405)
              ·
                refine ⟨131888828224920381612712277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351703541933121017633899405 131888828224920381612712277)
                ·
                  refine ⟨386393051440196430505993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 131888828224920381612712277 386393051440196430505993)
                  ·
                    rfl

theorem cell23_6772480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 10].length) (baseStart_6772480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772480 prefixEnd_6772480 := by exact prefixLift 6772480
  have htrace : WordTrace (prefixWord ++ tailWord_6772480) baseStart_6772480 baseEnd_6772480 := by
    simpa [prefixWord, tailWord_6772480, baseEnd_6772480] using wordTrace_append hprefix tailTrace_6772480
  have hstable : (prefixWord ++ tailWord_6772480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772480).length < 2 ^ (prefixWord ++ tailWord_6772480).sum := by decide
  have hdescent : baseEnd_6772480 < baseStart_6772480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772494 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_6772494 : Nat := 118140960795 + 6772494 * 2 ^ 59
def prefixEnd_6772494 : Nat := 4983230072969 + 3 ^ 40 * 6772494 * 2
def baseEnd_6772494 : Nat := 3477544651690930819778873

theorem tailTrace_6772494 : CollatzResearch.WordTrace tailWord_6772494 prefixEnd_6772494 3477544651690930819778873 := by
  unfold tailWord_6772494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30876643640802295341838567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164675432750945575156472357 30876643640802295341838567)
  ·
    refine ⟨46314965461203443012757851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30876643640802295341838567 46314965461203443012757851)
    ·
      refine ⟨69472448191805164519136777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46314965461203443012757851 69472448191805164519136777)
      ·
        refine ⟨52104336143853873389352583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69472448191805164519136777 52104336143853873389352583)
        ·
          refine ⟨78156504215780810084028875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52104336143853873389352583 78156504215780810084028875)
          ·
            refine ⟨117234756323671215126043313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78156504215780810084028875 117234756323671215126043313)
            ·
              refine ⟨87926067242753411344532485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117234756323671215126043313 87926067242753411344532485)
              ·
                refine ⟨16486137608016264627099841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87926067242753411344532485 16486137608016264627099841)
                ·
                  refine ⟨12364603206012198470324881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16486137608016264627099841 12364603206012198470324881)
                  ·
                    refine ⟨9273452404509148852743661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12364603206012198470324881 9273452404509148852743661)
                    ·
                      refine ⟨3477544651690930819778873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9273452404509148852743661 3477544651690930819778873)
                      ·
                        rfl

theorem cell23_6772494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_6772494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772494 prefixEnd_6772494 := by exact prefixLift 6772494
  have htrace : WordTrace (prefixWord ++ tailWord_6772494) baseStart_6772494 baseEnd_6772494 := by
    simpa [prefixWord, tailWord_6772494, baseEnd_6772494] using wordTrace_append hprefix tailTrace_6772494
  have hstable : (prefixWord ++ tailWord_6772494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772494).length < 2 ^ (prefixWord ++ tailWord_6772494).sum := by decide
  have hdescent : baseEnd_6772494 < baseStart_6772494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772501 : List Nat := [1, 3, 2, 1, 2, 3, 2, 4, 1, 4]
def baseStart_6772501 : Nat := 118140960795 + 6772501 * 2 ^ 59
def prefixEnd_6772501 : Nat := 4983230072969 + 3 ^ 40 * 6772501 * 2
def baseEnd_6772501 : Nat := 1159182748685170764130447

theorem tailTrace_6772501 : CollatzResearch.WordTrace tailWord_6772501 prefixEnd_6772501 1159182748685170764130447 := by
  unfold tailWord_6772501
  simp only [CollatzResearch.WordTrace]
  refine ⟨247013404437393002930213357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164675602958262001953475571 247013404437393002930213357)
  ·
    refine ⟨92630026664022376098830009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247013404437393002930213357 92630026664022376098830009)
    ·
      refine ⟨69472519998016782074122507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92630026664022376098830009 69472519998016782074122507)
      ·
        refine ⟨104208779997025173111183761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69472519998016782074122507 104208779997025173111183761)
        ·
          refine ⟨78156584997768879833387821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104208779997025173111183761 78156584997768879833387821)
          ·
            refine ⟨29308719374163329937520433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78156584997768879833387821 29308719374163329937520433)
            ·
              refine ⟨21981539530622497453140325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29308719374163329937520433 21981539530622497453140325)
              ·
                refine ⟨4121538661991718272463811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21981539530622497453140325 4121538661991718272463811)
                ·
                  refine ⟨6182307992987577408695717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4121538661991718272463811 6182307992987577408695717)
                  ·
                    refine ⟨1159182748685170764130447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6182307992987577408695717 1159182748685170764130447)
                    ·
                      rfl

theorem cell23_6772501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_6772501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772501 prefixEnd_6772501 := by exact prefixLift 6772501
  have htrace : WordTrace (prefixWord ++ tailWord_6772501) baseStart_6772501 baseEnd_6772501 := by
    simpa [prefixWord, tailWord_6772501, baseEnd_6772501] using wordTrace_append hprefix tailTrace_6772501
  have hstable : (prefixWord ++ tailWord_6772501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772501).length < 2 ^ (prefixWord ++ tailWord_6772501).sum := by decide
  have hdescent : baseEnd_6772501 < baseStart_6772501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772577 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_6772577 : Nat := 118140960795 + 6772577 * 2 ^ 59
def prefixEnd_6772577 : Nat := 4983230072969 + 3 ^ 40 * 6772577 * 2
def baseEnd_6772577 : Nat := 3477587270585253995040991

theorem tailTrace_6772577 : CollatzResearch.WordTrace tailWord_6772577 prefixEnd_6772577 3477587270585253995040991 := by
  unfold tailWord_6772577
  simp only [CollatzResearch.WordTrace]
  refine ⟨247016176385117667909979985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164677450923411778606653323 247016176385117667909979985)
  ·
    refine ⟨185262132288838250932484989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247016176385117667909979985 185262132288838250932484989)
    ·
      refine ⟨69473299608314344099681871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185262132288838250932484989 69473299608314344099681871)
      ·
        refine ⟨104209949412471516149522807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69473299608314344099681871 104209949412471516149522807)
        ·
          refine ⟨156314924118707274224284211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104209949412471516149522807 156314924118707274224284211)
          ·
            refine ⟨234472386178060911336426317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156314924118707274224284211 234472386178060911336426317)
            ·
              refine ⟨87927144816772841751159869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234472386178060911336426317 87927144816772841751159869)
              ·
                refine ⟨32972679306289815656684951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87927144816772841751159869 32972679306289815656684951)
                ·
                  refine ⟨49459018959434723485027427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32972679306289815656684951 49459018959434723485027427)
                  ·
                    refine ⟨74188528439152085227541141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49459018959434723485027427 74188528439152085227541141)
                    ·
                      refine ⟨3477587270585253995040991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74188528439152085227541141 3477587270585253995040991)
                      ·
                        rfl

theorem cell23_6772577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_6772577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772577 prefixEnd_6772577 := by exact prefixLift 6772577
  have htrace : WordTrace (prefixWord ++ tailWord_6772577) baseStart_6772577 baseEnd_6772577 := by
    simpa [prefixWord, tailWord_6772577, baseEnd_6772577] using wordTrace_append hprefix tailTrace_6772577
  have hstable : (prefixWord ++ tailWord_6772577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772577).length < 2 ^ (prefixWord ++ tailWord_6772577).sum := by decide
  have hdescent : baseEnd_6772577 < baseStart_6772577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772578 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_6772578 : Nat := 118140960795 + 6772578 * 2 ^ 59
def prefixEnd_6772578 : Nat := 4983230072969 + 3 ^ 40 * 6772578 * 2
def baseEnd_6772578 : Nat := 1159195928021969497042829

theorem tailTrace_6772578 : CollatzResearch.WordTrace tailWord_6772578 prefixEnd_6772578 1159195928021969497042829 := by
  unfold tailWord_6772578
  simp only [CollatzResearch.WordTrace]
  refine ⟨61754053214528511270191597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164677475238742696720510925 61754053214528511270191597)
  ·
    refine ⟨23157769955448191726321849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61754053214528511270191597 23157769955448191726321849)
    ·
      refine ⟨17368327466586143794741387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23157769955448191726321849 17368327466586143794741387)
      ·
        refine ⟨26052491199879215692112081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17368327466586143794741387 26052491199879215692112081)
        ·
          refine ⟨19539368399909411769084061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26052491199879215692112081 19539368399909411769084061)
          ·
            refine ⟨7327263149966029413406523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19539368399909411769084061 7327263149966029413406523)
            ·
              refine ⟨10990894724949044120109785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7327263149966029413406523 10990894724949044120109785)
              ·
                refine ⟨8243171043711783090082339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10990894724949044120109785 8243171043711783090082339)
                ·
                  refine ⟨12364756565567674635123509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8243171043711783090082339 12364756565567674635123509)
                  ·
                    refine ⟨1159195928021969497042829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12364756565567674635123509 1159195928021969497042829)
                    ·
                      rfl

theorem cell23_6772578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_6772578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772578 prefixEnd_6772578 := by exact prefixLift 6772578
  have htrace : WordTrace (prefixWord ++ tailWord_6772578) baseStart_6772578 baseEnd_6772578 := by
    simpa [prefixWord, tailWord_6772578, baseEnd_6772578] using wordTrace_append hprefix tailTrace_6772578
  have hstable : (prefixWord ++ tailWord_6772578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772578).length < 2 ^ (prefixWord ++ tailWord_6772578).sum := by decide
  have hdescent : baseEnd_6772578 < baseStart_6772578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772581 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 5, 2, 2]
def baseStart_6772581 : Nat := 118140960795 + 6772581 * 2 ^ 59
def prefixEnd_6772581 : Nat := 4983230072969 + 3 ^ 40 * 6772581 * 2
def baseEnd_6772581 : Nat := 3477589324507871979390973

theorem tailTrace_6772581 : CollatzResearch.WordTrace tailWord_6772581 prefixEnd_6772581 3477589324507871979390973 := by
  unfold tailWord_6772581
  simp only [CollatzResearch.WordTrace]
  refine ⟨247016322277103176593125597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164677548184735451062083731 247016322277103176593125597)
  ·
    refine ⟨92631120853913691222422099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247016322277103176593125597 92631120853913691222422099)
    ·
      refine ⟨138946681280870536833633149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92631120853913691222422099 138946681280870536833633149)
      ·
        refine ⟨52105005480326451312612431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138946681280870536833633149 52105005480326451312612431)
        ·
          refine ⟨78157508220489676968918647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52105005480326451312612431 78157508220489676968918647)
          ·
            refine ⟨117236262330734515453377971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78157508220489676968918647 117236262330734515453377971)
            ·
              refine ⟨175854393496101773180066957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117236262330734515453377971 175854393496101773180066957)
              ·
                refine ⟨65945397561038164942525109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175854393496101773180066957 65945397561038164942525109)
                ·
                  refine ⟨6182381021347327963361729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65945397561038164942525109 6182381021347327963361729)
                  ·
                    refine ⟨4636785766010495972521297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6182381021347327963361729 4636785766010495972521297)
                    ·
                      refine ⟨3477589324507871979390973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636785766010495972521297 3477589324507871979390973)
                      ·
                        rfl

theorem cell23_6772581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_6772581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772581 prefixEnd_6772581 := by exact prefixLift 6772581
  have htrace : WordTrace (prefixWord ++ tailWord_6772581) baseStart_6772581 baseEnd_6772581 := by
    simpa [prefixWord, tailWord_6772581, baseEnd_6772581] using wordTrace_append hprefix tailTrace_6772581
  have hstable : (prefixWord ++ tailWord_6772581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772581).length < 2 ^ (prefixWord ++ tailWord_6772581).sum := by decide
  have hdescent : baseEnd_6772581 < baseStart_6772581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772609 : List Nat := [1, 2, 4, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_6772609 : Nat := 118140960795 + 6772609 * 2 ^ 59
def prefixEnd_6772609 : Nat := 4983230072969 + 3 ^ 40 * 6772609 * 2
def baseEnd_6772609 : Nat := 3477603701966197869840845

theorem tailTrace_6772609 : CollatzResearch.WordTrace tailWord_6772609 prefixEnd_6772609 3477603701966197869840845 := by
  unfold tailWord_6772609
  simp only [CollatzResearch.WordTrace]
  refine ⟨247017343521001737375144881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164678229014001158250096587 247017343521001737375144881)
  ·
    refine ⟨185263007640751303031358661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247017343521001737375144881 185263007640751303031358661)
    ·
      refine ⟨34736813932640869318379749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185263007640751303031358661 34736813932640869318379749)
      ·
        refine ⟨6513152612370162997196203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34736813932640869318379749 6513152612370162997196203)
        ·
          refine ⟨9769728918555244495794305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6513152612370162997196203 9769728918555244495794305)
          ·
            refine ⟨7327296688916433371845729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9769728918555244495794305 7327296688916433371845729)
            ·
              refine ⟨5495472516687325028884297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7327296688916433371845729 5495472516687325028884297)
              ·
                refine ⟨4121604387515493771663223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5495472516687325028884297 4121604387515493771663223)
                ·
                  refine ⟨6182406581273240657494835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4121604387515493771663223 6182406581273240657494835)
                  ·
                    refine ⟨9273609871909860986242253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6182406581273240657494835 9273609871909860986242253)
                    ·
                      refine ⟨3477603701966197869840845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9273609871909860986242253 3477603701966197869840845)
                      ·
                        rfl

theorem cell23_6772609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_6772609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772609 prefixEnd_6772609 := by exact prefixLift 6772609
  have htrace : WordTrace (prefixWord ++ tailWord_6772609) baseStart_6772609 baseEnd_6772609 := by
    simpa [prefixWord, tailWord_6772609, baseEnd_6772609] using wordTrace_append hprefix tailTrace_6772609
  have hstable : (prefixWord ++ tailWord_6772609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772609).length < 2 ^ (prefixWord ++ tailWord_6772609).sum := by decide
  have hdescent : baseEnd_6772609 < baseStart_6772609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772617 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 1, 9]
def baseStart_6772617 : Nat := 118140960795 + 6772617 * 2 ^ 59
def prefixEnd_6772617 : Nat := 4983230072969 + 3 ^ 40 * 6772617 * 2
def baseEnd_6772617 : Nat := 1159202603270477946180269

theorem tailTrace_6772617 : CollatzResearch.WordTrace tailWord_6772617 prefixEnd_6772617 1159202603270477946180269 := by
  unfold tailWord_6772617
  simp only [CollatzResearch.WordTrace]
  refine ⟨247017635304972754741436105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164678423536648503160957403 247017635304972754741436105)
  ·
    refine ⟨185263226478729566056077079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247017635304972754741436105 185263226478729566056077079)
    ·
      refine ⟨277894839718094349084115619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185263226478729566056077079 277894839718094349084115619)
      ·
        refine ⟨416842259577141523626173429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277894839718094349084115619 416842259577141523626173429)
        ·
          refine ⟨39078961835357017839953759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 416842259577141523626173429 39078961835357017839953759)
          ·
            refine ⟨58618442753035526759930639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39078961835357017839953759 58618442753035526759930639)
            ·
              refine ⟨87927664129553290139895959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58618442753035526759930639 87927664129553290139895959)
              ·
                refine ⟨131891496194329935209843939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87927664129553290139895959 131891496194329935209843939)
                ·
                  refine ⟨197837244291494902814765909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131891496194329935209843939 197837244291494902814765909)
                  ·
                    refine ⟨1159202603270477946180269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 197837244291494902814765909 1159202603270477946180269)
                    ·
                      rfl

theorem cell23_6772617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_6772617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772617 prefixEnd_6772617 := by exact prefixLift 6772617
  have htrace : WordTrace (prefixWord ++ tailWord_6772617) baseStart_6772617 baseEnd_6772617 := by
    simpa [prefixWord, tailWord_6772617, baseEnd_6772617] using wordTrace_append hprefix tailTrace_6772617
  have hstable : (prefixWord ++ tailWord_6772617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772617).length < 2 ^ (prefixWord ++ tailWord_6772617).sum := by decide
  have hdescent : baseEnd_6772617 < baseStart_6772617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772624 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 2, 7, 2]
def baseStart_6772624 : Nat := 118140960795 + 6772624 * 2 ^ 59
def prefixEnd_6772624 : Nat := 4983230072969 + 3 ^ 40 * 6772624 * 2
def baseEnd_6772624 : Nat := 3477611404176015311153275

theorem tailTrace_6772624 : CollatzResearch.WordTrace tailWord_6772624 prefixEnd_6772624 3477611404176015311153275 := by
  unfold tailWord_6772624
  simp only [CollatzResearch.WordTrace]
  refine ⟨123508945307973697468470463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164678593743964929957960617 123508945307973697468470463)
  ·
    refine ⟨185263417961960546202705695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123508945307973697468470463 185263417961960546202705695)
    ·
      refine ⟨277895126942940819304058543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185263417961960546202705695 277895126942940819304058543)
      ·
        refine ⟨416842690414411228956087815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277895126942940819304058543 416842690414411228956087815)
        ·
          refine ⟨625264035621616843434131723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416842690414411228956087815 625264035621616843434131723)
          ·
            refine ⟨937896053432425265151197585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625264035621616843434131723 937896053432425265151197585)
            ·
              refine ⟨703422040074318948863398189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937896053432425265151197585 703422040074318948863398189)
              ·
                refine ⟨263783265027869605823774321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 703422040074318948863398189 263783265027869605823774321)
                ·
                  refine ⟨197837448770902204367830741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263783265027869605823774321 197837448770902204367830741)
                  ·
                    refine ⟨4636815205568020414871033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 197837448770902204367830741 4636815205568020414871033)
                    ·
                      refine ⟨3477611404176015311153275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636815205568020414871033 3477611404176015311153275)
                      ·
                        rfl

theorem cell23_6772624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 7, 2].length) (baseStart_6772624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772624 prefixEnd_6772624 := by exact prefixLift 6772624
  have htrace : WordTrace (prefixWord ++ tailWord_6772624) baseStart_6772624 baseEnd_6772624 := by
    simpa [prefixWord, tailWord_6772624, baseEnd_6772624] using wordTrace_append hprefix tailTrace_6772624
  have hstable : (prefixWord ++ tailWord_6772624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772624).length < 2 ^ (prefixWord ++ tailWord_6772624).sum := by decide
  have hdescent : baseEnd_6772624 < baseStart_6772624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772631 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 3]
def baseStart_6772631 : Nat := 118140960795 + 6772631 * 2 ^ 59
def prefixEnd_6772631 : Nat := 4983230072969 + 3 ^ 40 * 6772631 * 2
def baseEnd_6772631 : Nat := 3477614998540596783765743

theorem tailTrace_6772631 : CollatzResearch.WordTrace tailWord_6772631 prefixEnd_6772631 3477614998540596783765743 := by
  unfold tailWord_6772631
  simp only [CollatzResearch.WordTrace]
  refine ⟨247018145926922035132445747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164678763951281356754963831 247018145926922035132445747)
  ·
    refine ⟨370527218890383052698668621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247018145926922035132445747 370527218890383052698668621)
    ·
      refine ⟨138947707083893644762000733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370527218890383052698668621 138947707083893644762000733)
      ·
        refine ⟨52105390156460116785750275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138947707083893644762000733 52105390156460116785750275)
        ·
          refine ⟨78158085234690175178625413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52105390156460116785750275 78158085234690175178625413)
          ·
            refine ⟨14654640981504407845992265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78158085234690175178625413 14654640981504407845992265)
            ·
              refine ⟨10990980736128305884494199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14654640981504407845992265 10990980736128305884494199)
              ·
                refine ⟨16486471104192458826741299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10990980736128305884494199 16486471104192458826741299)
                ·
                  refine ⟨24729706656288688240111949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16486471104192458826741299 24729706656288688240111949)
                  ·
                    refine ⟨9273639996108258090041981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24729706656288688240111949 9273639996108258090041981)
                    ·
                      refine ⟨3477614998540596783765743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9273639996108258090041981 3477614998540596783765743)
                      ·
                        rfl

theorem cell23_6772631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_6772631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772631 prefixEnd_6772631 := by exact prefixLift 6772631
  have htrace : WordTrace (prefixWord ++ tailWord_6772631) baseStart_6772631 baseEnd_6772631 := by
    simpa [prefixWord, tailWord_6772631, baseEnd_6772631] using wordTrace_append hprefix tailTrace_6772631
  have hstable : (prefixWord ++ tailWord_6772631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772631).length < 2 ^ (prefixWord ++ tailWord_6772631).sum := by decide
  have hdescent : baseEnd_6772631 < baseStart_6772631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772667 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 6]
def baseStart_6772667 : Nat := 118140960795 + 6772667 * 2 ^ 59
def prefixEnd_6772667 : Nat := 4983230072969 + 3 ^ 40 * 6772667 * 2
def baseEnd_6772667 : Nat := 3477633483844158642915577

theorem tailTrace_6772667 : CollatzResearch.WordTrace tailWord_6772667 prefixEnd_6772667 3477633483844158642915577 := by
  unfold tailWord_6772667
  simp only [CollatzResearch.WordTrace]
  refine ⟨247019458954791613280756255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164679639303194408853837503 247019458954791613280756255)
  ·
    refine ⟨370529188432187419921134383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247019458954791613280756255 370529188432187419921134383)
    ·
      refine ⟨555793782648281129881701575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370529188432187419921134383 555793782648281129881701575)
      ·
        refine ⟨833690673972421694822552363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555793782648281129881701575 833690673972421694822552363)
        ·
          refine ⟨1250536010958632542233828545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833690673972421694822552363 1250536010958632542233828545)
          ·
            refine ⟨937902008218974406675371409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1250536010958632542233828545 937902008218974406675371409)
            ·
              refine ⟨703426506164230805006528557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937902008218974406675371409 703426506164230805006528557)
              ·
                refine ⟨263784939811586551877448209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 703426506164230805006528557 263784939811586551877448209)
                ·
                  refine ⟨197838704858689913908086157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263784939811586551877448209 197838704858689913908086157)
                  ·
                    refine ⟨74189514322008717715532309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197838704858689913908086157 74189514322008717715532309)
                    ·
                      refine ⟨3477633483844158642915577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74189514322008717715532309 3477633483844158642915577)
                      ·
                        rfl

theorem cell23_6772667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_6772667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772667 prefixEnd_6772667 := by exact prefixLift 6772667
  have htrace : WordTrace (prefixWord ++ tailWord_6772667) baseStart_6772667 baseEnd_6772667 := by
    simpa [prefixWord, tailWord_6772667, baseEnd_6772667] using wordTrace_append hprefix tailTrace_6772667
  have hstable : (prefixWord ++ tailWord_6772667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772667).length < 2 ^ (prefixWord ++ tailWord_6772667).sum := by decide
  have hdescent : baseEnd_6772667 < baseStart_6772667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772688 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 2, 2, 2]
def baseStart_6772688 : Nat := 118140960795 + 6772688 * 2 ^ 59
def prefixEnd_6772688 : Nat := 4983230072969 + 3 ^ 40 * 6772688 * 2
def baseEnd_6772688 : Nat := 3477644266937903060752981

theorem tailTrace_6772688 : CollatzResearch.WordTrace tailWord_6772688 prefixEnd_6772688 3477644266937903060752981 := by
  unfold tailWord_6772688
  simp only [CollatzResearch.WordTrace]
  refine ⟨123510112443857766933635359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164680149925143689244847145 123510112443857766933635359)
  ·
    refine ⟨185265168665786650400453039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123510112443857766933635359 185265168665786650400453039)
    ·
      refine ⟨277897752998679975600679559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185265168665786650400453039 277897752998679975600679559)
      ·
        refine ⟨416846629498019963401019339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277897752998679975600679559 416846629498019963401019339)
        ·
          refine ⟨625269944247029945101529009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416846629498019963401019339 625269944247029945101529009)
          ·
            refine ⟨468952458185272458826146757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625269944247029945101529009 468952458185272458826146757)
            ·
              refine ⟨87928585909738586029902517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 468952458185272458826146757 87928585909738586029902517)
              ·
                refine ⟨8243304929037992440303361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87928585909738586029902517 8243304929037992440303361)
                ·
                  refine ⟨6182478696778494330227521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8243304929037992440303361 6182478696778494330227521)
                  ·
                    refine ⟨4636859022583870747670641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6182478696778494330227521 4636859022583870747670641)
                    ·
                      refine ⟨3477644266937903060752981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636859022583870747670641 3477644266937903060752981)
                      ·
                        rfl

theorem cell23_6772688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2, 2, 2].length) (baseStart_6772688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772688 prefixEnd_6772688 := by exact prefixLift 6772688
  have htrace : WordTrace (prefixWord ++ tailWord_6772688) baseStart_6772688 baseEnd_6772688 := by
    simpa [prefixWord, tailWord_6772688, baseEnd_6772688] using wordTrace_append hprefix tailTrace_6772688
  have hstable : (prefixWord ++ tailWord_6772688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772688).length < 2 ^ (prefixWord ++ tailWord_6772688).sum := by decide
  have hdescent : baseEnd_6772688 < baseStart_6772688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772704 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 3]
def baseStart_6772704 : Nat := 118140960795 + 6772704 * 2 ^ 59
def prefixEnd_6772704 : Nat := 4983230072969 + 3 ^ 40 * 6772704 * 2
def baseEnd_6772704 : Nat := 3477652482628374998152907

theorem tailTrace_6772704 : CollatzResearch.WordTrace tailWord_6772704 prefixEnd_6772704 3477652482628374998152907 := by
  unfold tailWord_6772704
  simp only [CollatzResearch.WordTrace]
  refine ⟨123510404227828784299926583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164680538970438379066568777 123510404227828784299926583)
  ·
    refine ⟨185265606341743176449889875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123510404227828784299926583 185265606341743176449889875)
    ·
      refine ⟨277898409512614764674834813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185265606341743176449889875 277898409512614764674834813)
      ·
        refine ⟨104211903567230536753063055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277898409512614764674834813 104211903567230536753063055)
        ·
          refine ⟨156317855350845805129594583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104211903567230536753063055 156317855350845805129594583)
          ·
            refine ⟨234476783026268707694391875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156317855350845805129594583 234476783026268707694391875)
            ·
              refine ⟨351715174539403061541587813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234476783026268707694391875 351715174539403061541587813)
              ·
                refine ⟨65946595226138074039047715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351715174539403061541587813 65946595226138074039047715)
                ·
                  refine ⟨98919892839207111058571573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65946595226138074039047715 98919892839207111058571573)
                  ·
                    refine ⟨9273739953675666661741085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98919892839207111058571573 9273739953675666661741085)
                    ·
                      refine ⟨3477652482628374998152907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9273739953675666661741085 3477652482628374998152907)
                      ·
                        rfl

theorem cell23_6772704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_6772704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772704 prefixEnd_6772704 := by exact prefixLift 6772704
  have htrace : WordTrace (prefixWord ++ tailWord_6772704) baseStart_6772704 baseEnd_6772704 := by
    simpa [prefixWord, tailWord_6772704, baseEnd_6772704] using wordTrace_append hprefix tailTrace_6772704
  have hstable : (prefixWord ++ tailWord_6772704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772704).length < 2 ^ (prefixWord ++ tailWord_6772704).sum := by decide
  have hdescent : baseEnd_6772704 < baseStart_6772704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772761 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 4, 4, 2]
def baseStart_6772761 : Nat := 118140960795 + 6772761 * 2 ^ 59
def prefixEnd_6772761 : Nat := 4983230072969 + 3 ^ 40 * 6772761 * 2
def baseEnd_6772761 : Nat := 3477681751025681275140145

theorem tailTrace_6772761 : CollatzResearch.WordTrace tailWord_6772761 prefixEnd_6772761 3477681751025681275140145 := by
  unfold tailWord_6772761
  simp only [CollatzResearch.WordTrace]
  refine ⟨247022887416451067334678137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164681924944300711556452091 247022887416451067334678137)
  ·
    refine ⟨185267165562338300501008603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247022887416451067334678137 185267165562338300501008603)
    ·
      refine ⟨277900748343507450751512905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185267165562338300501008603 277900748343507450751512905)
      ·
        refine ⟨208425561257630588063634679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277900748343507450751512905 208425561257630588063634679)
        ·
          refine ⟨312638341886445882095452019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208425561257630588063634679 312638341886445882095452019)
          ·
            refine ⟨468957512829668823143178029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312638341886445882095452019 468957512829668823143178029)
            ·
              refine ⟨175859067311125808678691761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468957512829668823143178029 175859067311125808678691761)
              ·
                refine ⟨131894300483344356509018821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175859067311125808678691761 131894300483344356509018821)
                ·
                  refine ⟨24730181340627066845441029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131894300483344356509018821 24730181340627066845441029)
                  ·
                    refine ⟨4636909001367575033520193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24730181340627066845441029 4636909001367575033520193)
                    ·
                      refine ⟨3477681751025681275140145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636909001367575033520193 3477681751025681275140145)
                      ·
                        rfl

theorem cell23_6772761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_6772761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772761 prefixEnd_6772761 := by exact prefixLift 6772761
  have htrace : WordTrace (prefixWord ++ tailWord_6772761) baseStart_6772761 baseEnd_6772761 := by
    simpa [prefixWord, tailWord_6772761, baseEnd_6772761] using wordTrace_append hprefix tailTrace_6772761
  have hstable : (prefixWord ++ tailWord_6772761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772761).length < 2 ^ (prefixWord ++ tailWord_6772761).sum := by decide
  have hdescent : baseEnd_6772761 < baseStart_6772761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772778 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_6772778 : Nat := 118140960795 + 6772778 * 2 ^ 59
def prefixEnd_6772778 : Nat := 4983230072969 + 3 ^ 40 * 6772778 * 2
def baseEnd_6772778 : Nat := 3477690480196807708627567

theorem tailTrace_6772778 : CollatzResearch.WordTrace tailWord_6772778 prefixEnd_6772778 3477690480196807708627567 := by
  unfold tailWord_6772778
  simp only [CollatzResearch.WordTrace]
  refine ⟨61755876864347369809511747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164682338304926319492031325 61755876864347369809511747)
  ·
    refine ⟨92633815296521054714267621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61755876864347369809511747 92633815296521054714267621)
    ·
      refine ⟨17368840368097697758925179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92633815296521054714267621 17368840368097697758925179)
      ·
        refine ⟨26053260552146546638387769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17368840368097697758925179 26053260552146546638387769)
        ·
          refine ⟨19539945414109909978790827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26053260552146546638387769 19539945414109909978790827)
          ·
            refine ⟨29309918121164864968186241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19539945414109909978790827 29309918121164864968186241)
            ·
              refine ⟨21982438590873648726139681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29309918121164864968186241 21982438590873648726139681)
              ·
                refine ⟨16486828943155236544604761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21982438590873648726139681 16486828943155236544604761)
                ·
                  refine ⟨12365121707366427408453571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16486828943155236544604761 12365121707366427408453571)
                  ·
                    refine ⟨18547682561049641112680357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12365121707366427408453571 18547682561049641112680357)
                    ·
                      refine ⟨3477690480196807708627567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18547682561049641112680357 3477690480196807708627567)
                      ·
                        rfl

theorem cell23_6772778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_6772778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772778 prefixEnd_6772778 := by exact prefixLift 6772778
  have htrace : WordTrace (prefixWord ++ tailWord_6772778) baseStart_6772778 baseEnd_6772778 := by
    simpa [prefixWord, tailWord_6772778, baseEnd_6772778] using wordTrace_append hprefix tailTrace_6772778
  have hstable : (prefixWord ++ tailWord_6772778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772778).length < 2 ^ (prefixWord ++ tailWord_6772778).sum := by decide
  have hdescent : baseEnd_6772778 < baseStart_6772778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772845 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_6772845 : Nat := 118140960795 + 6772845 * 2 ^ 59
def prefixEnd_6772845 : Nat := 4983230072969 + 3 ^ 40 * 6772845 * 2
def baseEnd_6772845 : Nat := 3477724883400658946489759

theorem tailTrace_6772845 : CollatzResearch.WordTrace tailWord_6772845 prefixEnd_6772845 3477724883400658946489759 := by
  unfold tailWord_6772845
  simp only [CollatzResearch.WordTrace]
  refine ⟨247025951148146749680735989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164683967432097833120490659 247025951148146749680735989)
  ·
    refine ⟨23158682920138757782568999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247025951148146749680735989 23158682920138757782568999)
    ·
      refine ⟨34738024380208136673853499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23158682920138757782568999 34738024380208136673853499)
      ·
        refine ⟨52107036570312205010780249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34738024380208136673853499 52107036570312205010780249)
        ·
          refine ⟨39080277427734153758085187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52107036570312205010780249 39080277427734153758085187)
          ·
            refine ⟨58620416141601230637127781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39080277427734153758085187 58620416141601230637127781)
            ·
              refine ⟨10991328026550230744461459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58620416141601230637127781 10991328026550230744461459)
              ·
                refine ⟨16486992039825346116692189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10991328026550230744461459 16486992039825346116692189)
                ·
                  refine ⟨6182622014934504793759571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16486992039825346116692189 6182622014934504793759571)
                  ·
                    refine ⟨9273933022401757190639357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6182622014934504793759571 9273933022401757190639357)
                    ·
                      refine ⟨3477724883400658946489759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9273933022401757190639357 3477724883400658946489759)
                      ·
                        rfl

theorem cell23_6772845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_6772845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772845 prefixEnd_6772845 := by exact prefixLift 6772845
  have htrace : WordTrace (prefixWord ++ tailWord_6772845) baseStart_6772845 baseEnd_6772845 := by
    simpa [prefixWord, tailWord_6772845, baseEnd_6772845] using wordTrace_append hprefix tailTrace_6772845
  have hstable : (prefixWord ++ tailWord_6772845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772845).length < 2 ^ (prefixWord ++ tailWord_6772845).sum := by decide
  have hdescent : baseEnd_6772845 < baseStart_6772845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772865 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 1, 5]
def baseStart_6772865 : Nat := 118140960795 + 6772865 * 2 ^ 59
def prefixEnd_6772865 : Nat := 4983230072969 + 3 ^ 40 * 6772865 * 2
def baseEnd_6772865 : Nat := 1159245051004582956079889

theorem tailTrace_6772865 : CollatzResearch.WordTrace tailWord_6772865 prefixEnd_6772865 1159245051004582956079889 := by
  unfold tailWord_6772865
  simp only [CollatzResearch.WordTrace]
  refine ⟨247026680608074293096464049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164684453738716195397642699 247026680608074293096464049)
  ·
    refine ⟨185270010456055719822348037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247026680608074293096464049 185270010456055719822348037)
    ·
      refine ⟨34738126960510447466690257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185270010456055719822348037 34738126960510447466690257)
      ·
        refine ⟨26053595220382835600017693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34738126960510447466690257 26053595220382835600017693)
        ·
          refine ⟨9770098207643563350006635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26053595220382835600017693 9770098207643563350006635)
          ·
            refine ⟨14655147311465345025009953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9770098207643563350006635 14655147311465345025009953)
            ·
              refine ⟨10991360483599008768757465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14655147311465345025009953 10991360483599008768757465)
              ·
                refine ⟨8243520362699256576568099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10991360483599008768757465 8243520362699256576568099)
                ·
                  refine ⟨12365280544048884864852149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8243520362699256576568099 12365280544048884864852149)
                  ·
                    refine ⟨1159245051004582956079889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12365280544048884864852149 1159245051004582956079889)
                    ·
                      rfl

theorem cell23_6772865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_6772865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772865 prefixEnd_6772865 := by exact prefixLift 6772865
  have htrace : WordTrace (prefixWord ++ tailWord_6772865) baseStart_6772865 baseEnd_6772865 := by
    simpa [prefixWord, tailWord_6772865, baseEnd_6772865] using wordTrace_append hprefix tailTrace_6772865
  have hstable : (prefixWord ++ tailWord_6772865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772865).length < 2 ^ (prefixWord ++ tailWord_6772865).sum := by decide
  have hdescent : baseEnd_6772865 < baseStart_6772865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772868 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_6772868 : Nat := 118140960795 + 6772868 * 2 ^ 59
def prefixEnd_6772868 : Nat := 4983230072969 + 3 ^ 40 * 6772868 * 2
def baseEnd_6772868 : Nat := 3477736693455712356502153

theorem tailTrace_6772868 : CollatzResearch.WordTrace tailWord_6772868 prefixEnd_6772868 3477736693455712356502153 := by
  unfold tailWord_6772868
  simp only [CollatzResearch.WordTrace]
  refine ⟨123513395013531712304411629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164684526684708949739215505 123513395013531712304411629)
  ·
    refine ⟨46317523130074392114154361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123513395013531712304411629 46317523130074392114154361)
    ·
      refine ⟨34738142347555794085615771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46317523130074392114154361 34738142347555794085615771)
      ·
        refine ⟨52107213521333691128423657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34738142347555794085615771 52107213521333691128423657)
        ·
          refine ⟨39080410141000268346317743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52107213521333691128423657 39080410141000268346317743)
          ·
            refine ⟨58620615211500402519476615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39080410141000268346317743 58620615211500402519476615)
            ·
              refine ⟨87930922817250603779214923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58620615211500402519476615 87930922817250603779214923)
              ·
                refine ⟨131896384225875905668822385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87930922817250603779214923 131896384225875905668822385)
                ·
                  refine ⟨98922288169406929251616789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131896384225875905668822385 98922288169406929251616789)
                  ·
                    refine ⟨4636982257940949808669537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98922288169406929251616789 4636982257940949808669537)
                    ·
                      refine ⟨3477736693455712356502153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4636982257940949808669537 3477736693455712356502153)
                      ·
                        rfl

theorem cell23_6772868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_6772868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772868 prefixEnd_6772868 := by exact prefixLift 6772868
  have htrace : WordTrace (prefixWord ++ tailWord_6772868) baseStart_6772868 baseEnd_6772868 := by
    simpa [prefixWord, tailWord_6772868, baseEnd_6772868] using wordTrace_append hprefix tailTrace_6772868
  have hstable : (prefixWord ++ tailWord_6772868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772868).length < 2 ^ (prefixWord ++ tailWord_6772868).sum := by decide
  have hdescent : baseEnd_6772868 < baseStart_6772868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772898 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_6772898 : Nat := 118140960795 + 6772898 * 2 ^ 59
def prefixEnd_6772898 : Nat := 4983230072969 + 3 ^ 40 * 6772898 * 2
def baseEnd_6772898 : Nat := 3477752097875347239127015

theorem tailTrace_6772898 : CollatzResearch.WordTrace tailWord_6772898 prefixEnd_6772898 3477752097875347239127015 := by
  unfold tailWord_6772898
  simp only [CollatzResearch.WordTrace]
  refine ⟨61756971054238684933103837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164685256144636493154943565 61756971054238684933103837)
  ·
    refine ⟨23158864145339506849913939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61756971054238684933103837 23158864145339506849913939)
    ·
      refine ⟨34738296218009260274870909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23158864145339506849913939 34738296218009260274870909)
      ·
        refine ⟨13026861081753472603076591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34738296218009260274870909 13026861081753472603076591)
        ·
          refine ⟨19540291622630208904614887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13026861081753472603076591 19540291622630208904614887)
          ·
            refine ⟨29310437433945313356922331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19540291622630208904614887 29310437433945313356922331)
            ·
              refine ⟨43965656150917970035383497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29310437433945313356922331 43965656150917970035383497)
              ·
                refine ⟨32974242113188477526537623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43965656150917970035383497 32974242113188477526537623)
                ·
                  refine ⟨49461363169782716289806435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32974242113188477526537623 49461363169782716289806435)
                  ·
                    refine ⟨74192044754674074434709653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49461363169782716289806435 74192044754674074434709653)
                    ·
                      refine ⟨3477752097875347239127015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74192044754674074434709653 3477752097875347239127015)
                      ·
                        rfl

theorem cell23_6772898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_6772898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772898 prefixEnd_6772898 := by exact prefixLift 6772898
  have htrace : WordTrace (prefixWord ++ tailWord_6772898) baseStart_6772898 baseEnd_6772898 := by
    simpa [prefixWord, tailWord_6772898, baseEnd_6772898] using wordTrace_append hprefix tailTrace_6772898
  have hstable : (prefixWord ++ tailWord_6772898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772898).length < 2 ^ (prefixWord ++ tailWord_6772898).sum := by decide
  have hdescent : baseEnd_6772898 < baseStart_6772898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772916 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6772916 : Nat := 118140960795 + 6772916 * 2 ^ 59
def prefixEnd_6772916 : Nat := 4983230072969 + 3 ^ 40 * 6772916 * 2
def baseEnd_6772916 : Nat := 1159253780175709389567311

theorem tailTrace_6772916 : CollatzResearch.WordTrace tailWord_6772916 prefixEnd_6772916 1159253780175709389567311 := by
  unfold tailWord_6772916
  simp only [CollatzResearch.WordTrace]
  refine ⟨123514270365444764403285301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164685693820593019204380401 123514270365444764403285301)
  ·
    refine ⟨11579462846760446662807997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123514270365444764403285301 11579462846760446662807997)
    ·
      refine ⟨4342298567535167498552999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11579462846760446662807997 4342298567535167498552999)
      ·
        refine ⟨6513447851302751247829499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4342298567535167498552999 6513447851302751247829499)
        ·
          refine ⟨9770171776954126871744249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6513447851302751247829499 9770171776954126871744249)
          ·
            refine ⟨7327628832715595153808187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9770171776954126871744249 7327628832715595153808187)
            ·
              refine ⟨10991443249073392730712281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7327628832715595153808187 10991443249073392730712281)
              ·
                refine ⟨8243582436805044548034211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10991443249073392730712281 8243582436805044548034211)
                ·
                  refine ⟨12365373655207566822051317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8243582436805044548034211 12365373655207566822051317)
                  ·
                    refine ⟨1159253780175709389567311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12365373655207566822051317 1159253780175709389567311)
                    ·
                      rfl

theorem cell23_6772916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6772916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772916 prefixEnd_6772916 := by exact prefixLift 6772916
  have htrace : WordTrace (prefixWord ++ tailWord_6772916) baseStart_6772916 baseEnd_6772916 := by
    simpa [prefixWord, tailWord_6772916, baseEnd_6772916] using wordTrace_append hprefix tailTrace_6772916
  have hstable : (prefixWord ++ tailWord_6772916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772916).length < 2 ^ (prefixWord ++ tailWord_6772916).sum := by decide
  have hdescent : baseEnd_6772916 < baseStart_6772916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772945 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 1, 3, 2]
def baseStart_6772945 : Nat := 118140960795 + 6772945 * 2 ^ 59
def prefixEnd_6772945 : Nat := 4983230072969 + 3 ^ 40 * 6772945 * 2
def baseEnd_6772945 : Nat := 3477776231466108555239299

theorem tailTrace_6772945 : CollatzResearch.WordTrace tailWord_6772945 prefixEnd_6772945 3477776231466108555239299 := by
  unfold tailWord_6772945
  simp only [CollatzResearch.WordTrace]
  refine ⟨247029598447784466759376289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164686398965189644506250859 247029598447784466759376289)
  ·
    refine ⟨185272198835838350069532217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247029598447784466759376289 185272198835838350069532217)
    ·
      refine ⟨138954149126878762552149163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185272198835838350069532217 138954149126878762552149163)
      ·
        refine ⟨208431223690318143828223745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138954149126878762552149163 208431223690318143828223745)
        ·
          refine ⟨156323417767738607871167809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208431223690318143828223745 156323417767738607871167809)
          ·
            refine ⟨117242563325803955903375857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156323417767738607871167809 117242563325803955903375857)
            ·
              refine ⟨87931922494352966927531893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117242563325803955903375857 87931922494352966927531893)
              ·
                refine ⟨8243617733845590649456115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87931922494352966927531893 8243617733845590649456115)
                ·
                  refine ⟨12365426600768385974184173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8243617733845590649456115 12365426600768385974184173)
                  ·
                    refine ⟨4637034975288144740319065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12365426600768385974184173 4637034975288144740319065)
                    ·
                      refine ⟨3477776231466108555239299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637034975288144740319065 3477776231466108555239299)
                      ·
                        rfl

theorem cell23_6772945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_6772945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772945 prefixEnd_6772945 := by exact prefixLift 6772945
  have htrace : WordTrace (prefixWord ++ tailWord_6772945) baseStart_6772945 baseEnd_6772945 := by
    simpa [prefixWord, tailWord_6772945, baseEnd_6772945] using wordTrace_append hprefix tailTrace_6772945
  have hstable : (prefixWord ++ tailWord_6772945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772945).length < 2 ^ (prefixWord ++ tailWord_6772945).sum := by decide
  have hdescent : baseEnd_6772945 < baseStart_6772945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772951 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 2, 6]
def baseStart_6772951 : Nat := 118140960795 + 6772951 * 2 ^ 59
def prefixEnd_6772951 : Nat := 4983230072969 + 3 ^ 40 * 6772951 * 2
def baseEnd_6772951 : Nat := 1159259770783345177254757

theorem tailTrace_6772951 : CollatzResearch.WordTrace tailWord_6772951 prefixEnd_6772951 1159259770783345177254757 := by
  unfold tailWord_6772951
  simp only [CollatzResearch.WordTrace]
  refine ⟨247029817285762729784094707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164686544857175153189396471 247029817285762729784094707)
  ·
    refine ⟨370544725928644094676142061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247029817285762729784094707 370544725928644094676142061)
    ·
      refine ⟨138954272223241535503553273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370544725928644094676142061 138954272223241535503553273)
      ·
        refine ⟨104215704167431151627664955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138954272223241535503553273 104215704167431151627664955)
        ·
          refine ⟨156323556251146727441497433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104215704167431151627664955 156323556251146727441497433)
          ·
            refine ⟨117242667188360045581123075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156323556251146727441497433 117242667188360045581123075)
            ·
              refine ⟨175864000782540068371684613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117242667188360045581123075 175864000782540068371684613)
              ·
                refine ⟨32974500146726262819690865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175864000782540068371684613 32974500146726262819690865)
                ·
                  refine ⟨24730875110044697114768149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32974500146726262819690865 24730875110044697114768149)
                  ·
                    refine ⟨1159259770783345177254757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24730875110044697114768149 1159259770783345177254757)
                    ·
                      rfl

theorem cell23_6772951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_6772951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772951 prefixEnd_6772951 := by exact prefixLift 6772951
  have htrace : WordTrace (prefixWord ++ tailWord_6772951) baseStart_6772951 baseEnd_6772951 := by
    simpa [prefixWord, tailWord_6772951, baseEnd_6772951] using wordTrace_append hprefix tailTrace_6772951
  have hstable : (prefixWord ++ tailWord_6772951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772951).length < 2 ^ (prefixWord ++ tailWord_6772951).sum := by decide
  have hdescent : baseEnd_6772951 < baseStart_6772951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772952 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 2, 1, 3]
def baseStart_6772952 : Nat := 118140960795 + 6772952 * 2 ^ 59
def prefixEnd_6772952 : Nat := 4983230072969 + 3 ^ 40 * 6772952 * 2
def baseEnd_6772952 : Nat := 3477779825830690027851767

theorem tailTrace_6772952 : CollatzResearch.WordTrace tailWord_6772952 prefixEnd_6772952 3477779825830690027851767 := by
  unfold tailWord_6772952
  simp only [CollatzResearch.WordTrace]
  refine ⟨123514926879379553477440555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164686569172506071303254073 123514926879379553477440555)
  ·
    refine ⟨185272390319069330216160833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123514926879379553477440555 185272390319069330216160833)
    ·
      refine ⟨138954292739301997662120625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185272390319069330216160833 138954292739301997662120625)
      ·
        refine ⟨104215719554476498246590469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138954292739301997662120625 104215719554476498246590469)
        ·
          refine ⟨19540447416464343421235713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104215719554476498246590469 19540447416464343421235713)
          ·
            refine ⟨14655335562348257565926785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19540447416464343421235713 14655335562348257565926785)
            ·
              refine ⟨10991501671761193174445089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14655335562348257565926785 10991501671761193174445089)
              ·
                refine ⟨8243626253820894880833817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10991501671761193174445089 8243626253820894880833817)
                ·
                  refine ⟨6182719690365671160625363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8243626253820894880833817 6182719690365671160625363)
                  ·
                    refine ⟨9274079535548506740938045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6182719690365671160625363 9274079535548506740938045)
                    ·
                      refine ⟨3477779825830690027851767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9274079535548506740938045 3477779825830690027851767)
                      ·
                        rfl

theorem cell23_6772952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_6772952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772952 prefixEnd_6772952 := by exact prefixLift 6772952
  have htrace : WordTrace (prefixWord ++ tailWord_6772952) baseStart_6772952 baseEnd_6772952 := by
    simpa [prefixWord, tailWord_6772952, baseEnd_6772952] using wordTrace_append hprefix tailTrace_6772952
  have hstable : (prefixWord ++ tailWord_6772952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772952).length < 2 ^ (prefixWord ++ tailWord_6772952).sum := by decide
  have hdescent : baseEnd_6772952 < baseStart_6772952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772968 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 2, 6]
def baseStart_6772968 : Nat := 118140960795 + 6772968 * 2 ^ 59
def prefixEnd_6772968 : Nat := 4983230072969 + 3 ^ 40 * 6772968 * 2
def baseEnd_6772968 : Nat := 1159262680507053988417231

theorem tailTrace_6772968 : CollatzResearch.WordTrace tailWord_6772968 prefixEnd_6772968 1159262680507053988417231 := by
  unfold tailWord_6772968
  simp only [CollatzResearch.WordTrace]
  refine ⟨123515218663350570843731779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164686958217800761124975705 123515218663350570843731779)
  ·
    refine ⟨185272827995025856265597669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123515218663350570843731779 185272827995025856265597669)
    ·
      refine ⟨34738655249067348049799563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185272827995025856265597669 34738655249067348049799563)
      ·
        refine ⟨52107982873601022074699345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34738655249067348049799563 52107982873601022074699345)
        ·
          refine ⟨39080987155200766556024509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52107982873601022074699345 39080987155200766556024509)
          ·
            refine ⟨14655370183200287458509191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39080987155200766556024509 14655370183200287458509191)
            ·
              refine ⟨21983055274800431187763787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14655370183200287458509191 21983055274800431187763787)
              ·
                refine ⟨32974582912200646781645681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21983055274800431187763787 32974582912200646781645681)
                ·
                  refine ⟨24730937184150485086234261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32974582912200646781645681 24730937184150485086234261)
                  ·
                    refine ⟨1159262680507053988417231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24730937184150485086234261 1159262680507053988417231)
                    ·
                      rfl

theorem cell23_6772968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_6772968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772968 prefixEnd_6772968 := by exact prefixLift 6772968
  have htrace : WordTrace (prefixWord ++ tailWord_6772968) baseStart_6772968 baseEnd_6772968 := by
    simpa [prefixWord, tailWord_6772968, baseEnd_6772968] using wordTrace_append hprefix tailTrace_6772968
  have hstable : (prefixWord ++ tailWord_6772968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772968).length < 2 ^ (prefixWord ++ tailWord_6772968).sum := by decide
  have hdescent : baseEnd_6772968 < baseStart_6772968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772975 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 1, 4, 2]
def baseStart_6772975 : Nat := 118140960795 + 6772975 * 2 ^ 59
def prefixEnd_6772975 : Nat := 4983230072969 + 3 ^ 40 * 6772975 * 2
def baseEnd_6772975 : Nat := 3477791635885743437864161

theorem tailTrace_6772975 : CollatzResearch.WordTrace tailWord_6772975 prefixEnd_6772975 3477791635885743437864161 := by
  unfold tailWord_6772975
  simp only [CollatzResearch.WordTrace]
  refine ⟨247030692637675781882968379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164687128425117187921978919 247030692637675781882968379)
  ·
    refine ⟨370546038956513672824452569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247030692637675781882968379 370546038956513672824452569)
    ·
      refine ⟨277909529217385254618339427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370546038956513672824452569 277909529217385254618339427)
      ·
        refine ⟨416864293826077881927509141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277909529217385254618339427 416864293826077881927509141)
        ·
          refine ⟨19540513773097400715351991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 416864293826077881927509141 19540513773097400715351991)
          ·
            refine ⟨29310770659646101073027987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19540513773097400715351991 29310770659646101073027987)
            ·
              refine ⟨43966155989469151609541981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29310770659646101073027987 43966155989469151609541981)
              ·
                refine ⟨16487308496050931853578243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43966155989469151609541981 16487308496050931853578243)
                ·
                  refine ⟨24730962744076397780367365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16487308496050931853578243 24730962744076397780367365)
                  ·
                    refine ⟨4637055514514324583818881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24730962744076397780367365 4637055514514324583818881)
                    ·
                      refine ⟨3477791635885743437864161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637055514514324583818881 3477791635885743437864161)
                      ·
                        rfl

theorem cell23_6772975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 4, 2].length) (baseStart_6772975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772975 prefixEnd_6772975 := by exact prefixLift 6772975
  have htrace : WordTrace (prefixWord ++ tailWord_6772975) baseStart_6772975 baseEnd_6772975 := by
    simpa [prefixWord, tailWord_6772975, baseEnd_6772975] using wordTrace_append hprefix tailTrace_6772975
  have hstable : (prefixWord ++ tailWord_6772975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772975).length < 2 ^ (prefixWord ++ tailWord_6772975).sum := by decide
  have hdescent : baseEnd_6772975 < baseStart_6772975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6772996 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_6772996 : Nat := 118140960795 + 6772996 * 2 ^ 59
def prefixEnd_6772996 : Nat := 4983230072969 + 3 ^ 40 * 6772996 * 2
def baseEnd_6772996 : Nat := 3477802418979487855701565

theorem tailTrace_6772996 : CollatzResearch.WordTrace tailWord_6772996 prefixEnd_6772996 3477802418979487855701565 := by
  unfold tailWord_6772996
  simp only [CollatzResearch.WordTrace]
  refine ⟨123515729285299851234741421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164687639047066468312988561 123515729285299851234741421)
  ·
    refine ⟨46318398481987444213028033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123515729285299851234741421 46318398481987444213028033)
    ·
      refine ⟨34738798861490583159771025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46318398481987444213028033 34738798861490583159771025)
      ·
        refine ⟨26054099146117937369828269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34738798861490583159771025 26054099146117937369828269)
        ·
          refine ⟨9770287179794226513685601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26054099146117937369828269 9770287179794226513685601)
          ·
            refine ⟨7327715384845669885264201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9770287179794226513685601 7327715384845669885264201)
            ·
              refine ⟨5495786538634252413948151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7327715384845669885264201 5495786538634252413948151)
              ·
                refine ⟨8243679807951378620922227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495786538634252413948151 8243679807951378620922227)
                ·
                  refine ⟨12365519711927067931383341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8243679807951378620922227 12365519711927067931383341)
                  ·
                    refine ⟨4637069891972650474268753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12365519711927067931383341 4637069891972650474268753)
                    ·
                      refine ⟨3477802418979487855701565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637069891972650474268753 3477802418979487855701565)
                      ·
                        rfl

theorem cell23_6772996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_6772996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6772996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6772996 prefixEnd_6772996 := by exact prefixLift 6772996
  have htrace : WordTrace (prefixWord ++ tailWord_6772996) baseStart_6772996 baseEnd_6772996 := by
    simpa [prefixWord, tailWord_6772996, baseEnd_6772996] using wordTrace_append hprefix tailTrace_6772996
  have hstable : (prefixWord ++ tailWord_6772996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6772996).length < 2 ^ (prefixWord ++ tailWord_6772996).sum := by decide
  have hdescent : baseEnd_6772996 < baseStart_6772996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6772996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773009 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 2, 2, 2]
def baseStart_6773009 : Nat := 118140960795 + 6773009 * 2 ^ 59
def prefixEnd_6773009 : Nat := 4983230072969 + 3 ^ 40 * 6773009 * 2
def baseEnd_6773009 : Nat := 3477809094227996304839005

theorem tailTrace_6773009 : CollatzResearch.WordTrace tailWord_6773009 prefixEnd_6773009 3477809094227996304839005 := by
  unfold tailWord_6773009
  simp only [CollatzResearch.WordTrace]
  refine ⟨247031932719552605689706081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164687955146368403793137387 247031932719552605689706081)
  ·
    refine ⟨185273949539664454267279561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247031932719552605689706081 185273949539664454267279561)
    ·
      refine ⟨138955462154748340700459671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185273949539664454267279561 138955462154748340700459671)
      ·
        refine ⟨208433193232122511050689507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138955462154748340700459671 208433193232122511050689507)
        ·
          refine ⟨312649789848183766576034261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208433193232122511050689507 312649789848183766576034261)
          ·
            refine ⟨7327729449566807029125803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 312649789848183766576034261 7327729449566807029125803)
            ·
              refine ⟨10991594174350210543688705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7327729449566807029125803 10991594174350210543688705)
              ·
                refine ⟨8243695630762657907766529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10991594174350210543688705 8243695630762657907766529)
                ·
                  refine ⟨6182771723071993430824897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8243695630762657907766529 6182771723071993430824897)
                  ·
                    refine ⟨4637078792303995073118673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6182771723071993430824897 4637078792303995073118673)
                    ·
                      refine ⟨3477809094227996304839005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637078792303995073118673 3477809094227996304839005)
                      ·
                        rfl

theorem cell23_6773009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_6773009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773009 prefixEnd_6773009 := by exact prefixLift 6773009
  have htrace : WordTrace (prefixWord ++ tailWord_6773009) baseStart_6773009 baseEnd_6773009 := by
    simpa [prefixWord, tailWord_6773009, baseEnd_6773009] using wordTrace_append hprefix tailTrace_6773009
  have hstable : (prefixWord ++ tailWord_6773009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773009).length < 2 ^ (prefixWord ++ tailWord_6773009).sum := by decide
  have hdescent : baseEnd_6773009 < baseStart_6773009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773015 : List Nat := [1, 1, 3, 4, 1, 2, 2, 4, 5]
def baseStart_6773015 : Nat := 118140960795 + 6773015 * 2 ^ 59
def prefixEnd_6773015 : Nat := 4983230072969 + 3 ^ 40 * 6773015 * 2
def baseEnd_6773015 : Nat := 386423575012435920151553

theorem tailTrace_6773015 : CollatzResearch.WordTrace tailWord_6773015 prefixEnd_6773015 386423575012435920151553 := by
  unfold tailWord_6773015
  simp only [CollatzResearch.WordTrace]
  refine ⟨247032151557530868714424499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164688101038353912476282999 247032151557530868714424499)
  ·
    refine ⟨370548227336296303071636749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247032151557530868714424499 370548227336296303071636749)
    ·
      refine ⟨138955585251111113651863781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370548227336296303071636749 138955585251111113651863781)
      ·
        refine ⟨26054172234583333809724459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138955585251111113651863781 26054172234583333809724459)
        ·
          refine ⟨39081258351875000714586689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26054172234583333809724459 39081258351875000714586689)
          ·
            refine ⟨29310943763906250535940017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39081258351875000714586689 29310943763906250535940017)
            ·
              refine ⟨21983207822929687901955013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29310943763906250535940017 21983207822929687901955013)
              ·
                refine ⟨4121851466799316481616565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21983207822929687901955013 4121851466799316481616565)
                ·
                  refine ⟨386423575012435920151553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4121851466799316481616565 386423575012435920151553)
                  ·
                    rfl

theorem cell23_6773015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 5].length) (baseStart_6773015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773015 prefixEnd_6773015 := by exact prefixLift 6773015
  have htrace : WordTrace (prefixWord ++ tailWord_6773015) baseStart_6773015 baseEnd_6773015 := by
    simpa [prefixWord, tailWord_6773015, baseEnd_6773015] using wordTrace_append hprefix tailTrace_6773015
  have hstable : (prefixWord ++ tailWord_6773015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773015).length < 2 ^ (prefixWord ++ tailWord_6773015).sum := by decide
  have hdescent : baseEnd_6773015 < baseStart_6773015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773022 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_6773022 : Nat := 118140960795 + 6773022 * 2 ^ 59
def prefixEnd_6773022 : Nat := 4983230072969 + 3 ^ 40 * 6773022 * 2
def baseEnd_6773022 : Nat := 3477815769476504753976445

theorem tailTrace_6773022 : CollatzResearch.WordTrace tailWord_6773022 prefixEnd_6773022 3477815769476504753976445 := by
  unfold tailWord_6773022
  simp only [CollatzResearch.WordTrace]
  refine ⟨30879050858563188613741165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164688271245670339273286213 30879050858563188613741165)
  ·
    refine ⟨11579644071961195730152937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30879050858563188613741165 11579644071961195730152937)
    ·
      refine ⟨8684733053970896797614703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11579644071961195730152937 8684733053970896797614703)
      ·
        refine ⟨13027099580956345196422055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8684733053970896797614703 13027099580956345196422055)
        ·
          refine ⟨19540649371434517794633083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13027099580956345196422055 19540649371434517794633083)
          ·
            refine ⟨29310974057151776691949625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19540649371434517794633083 29310974057151776691949625)
            ·
              refine ⟨21983230542863832518962219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29310974057151776691949625 21983230542863832518962219)
              ·
                refine ⟨32974845814295748778443329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21983230542863832518962219 32974845814295748778443329)
                ·
                  refine ⟨24731134360721811583832497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32974845814295748778443329 24731134360721811583832497)
                  ·
                    refine ⟨18548350770541358687874373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24731134360721811583832497 18548350770541358687874373)
                    ·
                      refine ⟨3477815769476504753976445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18548350770541358687874373 3477815769476504753976445)
                      ·
                        rfl

theorem cell23_6773022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_6773022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773022 prefixEnd_6773022 := by exact prefixLift 6773022
  have htrace : WordTrace (prefixWord ++ tailWord_6773022) baseStart_6773022 baseEnd_6773022 := by
    simpa [prefixWord, tailWord_6773022, baseEnd_6773022] using wordTrace_append hprefix tailTrace_6773022
  have hstable : (prefixWord ++ tailWord_6773022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773022).length < 2 ^ (prefixWord ++ tailWord_6773022).sum := by decide
  have hdescent : baseEnd_6773022 < baseStart_6773022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773026 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_6773026 : Nat := 118140960795 + 6773026 * 2 ^ 59
def prefixEnd_6773026 : Nat := 4983230072969 + 3 ^ 40 * 6773026 * 2
def baseEnd_6773026 : Nat := 3477817823399122738326427

theorem tailTrace_6773026 : CollatzResearch.WordTrace tailWord_6773026 prefixEnd_6773026 3477817823399122738326427 := by
  unfold tailWord_6773026
  simp only [CollatzResearch.WordTrace]
  refine ⟨61758138190122754398268733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164688368506994011728716621 61758138190122754398268733)
  ·
    refine ⟨23159301821296032899350775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61758138190122754398268733 23159301821296032899350775)
    ·
      refine ⟨34738952731944049349026163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23159301821296032899350775 34738952731944049349026163)
      ·
        refine ⟨52108429097916074023539245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34738952731944049349026163 52108429097916074023539245)
        ·
          refine ⟨19540660911718527758827217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52108429097916074023539245 19540660911718527758827217)
          ·
            refine ⟨14655495683788895819120413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19540660911718527758827217 14655495683788895819120413)
            ·
              refine ⟨5495810881420835932170155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14655495683788895819120413 5495810881420835932170155)
              ·
                refine ⟨8243716322131253898255233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495810881420835932170155 8243716322131253898255233)
                ·
                  refine ⟨6182787241598440423691425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8243716322131253898255233 6182787241598440423691425)
                  ·
                    refine ⟨4637090431198830317768569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6182787241598440423691425 4637090431198830317768569)
                    ·
                      refine ⟨3477817823399122738326427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637090431198830317768569 3477817823399122738326427)
                      ·
                        rfl

theorem cell23_6773026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_6773026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773026 prefixEnd_6773026 := by exact prefixLift 6773026
  have htrace : WordTrace (prefixWord ++ tailWord_6773026) baseStart_6773026 baseEnd_6773026 := by
    simpa [prefixWord, tailWord_6773026, baseEnd_6773026] using wordTrace_append hprefix tailTrace_6773026
  have hstable : (prefixWord ++ tailWord_6773026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773026).length < 2 ^ (prefixWord ++ tailWord_6773026).sum := by decide
  have hdescent : baseEnd_6773026 < baseStart_6773026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773028 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_6773028 : Nat := 118140960795 + 6773028 * 2 ^ 59
def prefixEnd_6773028 : Nat := 4983230072969 + 3 ^ 40 * 6773028 * 2
def baseEnd_6773028 : Nat := 1159272950120143910167139

theorem tailTrace_6773028 : CollatzResearch.WordTrace tailWord_6773028 prefixEnd_6773028 1159272950120143910167139 := by
  unfold tailWord_6773028
  simp only [CollatzResearch.WordTrace]
  refine ⟨123516312853241885967323869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164688417137655847956431825 123516312853241885967323869)
  ·
    refine ⟨46318617319965707237746451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123516312853241885967323869 46318617319965707237746451)
    ·
      refine ⟨69477925979948560856619677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46318617319965707237746451 69477925979948560856619677)
      ·
        refine ⟨26054222242480710321232379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69477925979948560856619677 26054222242480710321232379)
        ·
          refine ⟨39081333363721065481848569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26054222242480710321232379 39081333363721065481848569)
          ·
            refine ⟨29311000022790799111386427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39081333363721065481848569 29311000022790799111386427)
            ·
              refine ⟨43966500034186198667079641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29311000022790799111386427 43966500034186198667079641)
              ·
                refine ⟨32974875025639649000309731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43966500034186198667079641 32974875025639649000309731)
                ·
                  refine ⟨49462312538459473500464597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32974875025639649000309731 49462312538459473500464597)
                  ·
                    refine ⟨1159272950120143910167139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49462312538459473500464597 1159272950120143910167139)
                    ·
                      rfl

theorem cell23_6773028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_6773028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773028 prefixEnd_6773028 := by exact prefixLift 6773028
  have htrace : WordTrace (prefixWord ++ tailWord_6773028) baseStart_6773028 baseEnd_6773028 := by
    simpa [prefixWord, tailWord_6773028, baseEnd_6773028] using wordTrace_append hprefix tailTrace_6773028
  have hstable : (prefixWord ++ tailWord_6773028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773028).length < 2 ^ (prefixWord ++ tailWord_6773028).sum := by decide
  have hdescent : baseEnd_6773028 < baseStart_6773028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773048 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_6773048 : Nat := 118140960795 + 6773048 * 2 ^ 59
def prefixEnd_6773048 : Nat := 4983230072969 + 3 ^ 40 * 6773048 * 2
def baseEnd_6773048 : Nat := 3477829119973521652251325

theorem tailTrace_6773048 : CollatzResearch.WordTrace tailWord_6773048 prefixEnd_6773048 3477829119973521652251325 := by
  unfold tailWord_6773048
  simp only [CollatzResearch.WordTrace]
  refine ⟨123516677583205657675187899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164688903444274210233583865 123516677583205657675187899)
  ·
    refine ⟨185275016374808486512781849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123516677583205657675187899 185275016374808486512781849)
    ·
      refine ⟨138956262281106364884586387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185275016374808486512781849 138956262281106364884586387)
      ·
        refine ⟨208434393421659547326879581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138956262281106364884586387 208434393421659547326879581)
        ·
          refine ⟨78162897533122330247579843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208434393421659547326879581 78162897533122330247579843)
          ·
            refine ⟨117244346299683495371369765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78162897533122330247579843 117244346299683495371369765)
            ·
              refine ⟨21983314931190655382131831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117244346299683495371369765 21983314931190655382131831)
              ·
                refine ⟨32974972396785983073197747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21983314931190655382131831 32974972396785983073197747)
                ·
                  refine ⟨49462458595178974609796621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32974972396785983073197747 49462458595178974609796621)
                  ·
                    refine ⟨18548421973192115478673733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49462458595178974609796621 18548421973192115478673733)
                    ·
                      refine ⟨3477829119973521652251325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18548421973192115478673733 3477829119973521652251325)
                      ·
                        rfl

theorem cell23_6773048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_6773048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773048 prefixEnd_6773048 := by exact prefixLift 6773048
  have htrace : WordTrace (prefixWord ++ tailWord_6773048) baseStart_6773048 baseEnd_6773048 := by
    simpa [prefixWord, tailWord_6773048, baseEnd_6773048] using wordTrace_append hprefix tailTrace_6773048
  have hstable : (prefixWord ++ tailWord_6773048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773048).length < 2 ^ (prefixWord ++ tailWord_6773048).sum := by decide
  have hdescent : baseEnd_6773048 < baseStart_6773048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773125 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 3, 5, 2]
def baseStart_6773125 : Nat := 118140960795 + 6773125 * 2 ^ 59
def prefixEnd_6773125 : Nat := 4983230072969 + 3 ^ 40 * 6773125 * 2
def baseEnd_6773125 : Nat := 3477868657983917850988471

theorem tailTrace_6773125 : CollatzResearch.WordTrace tailWord_6773125 prefixEnd_6773125 3477868657983917850988471 := by
  unfold tailWord_6773125
  simp only [CollatzResearch.WordTrace]
  refine ⟨247036163587132357500928829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164690775724754905000619219 247036163587132357500928829)
  ·
    refine ⟨92638561345174634062848311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247036163587132357500928829 92638561345174634062848311)
    ·
      refine ⟨138957842017761951094272467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92638561345174634062848311 138957842017761951094272467)
      ·
        refine ⟨208436763026642926641408701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138957842017761951094272467 208436763026642926641408701)
        ·
          refine ⟨78163786134991097490528263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208436763026642926641408701 78163786134991097490528263)
          ·
            refine ⟨117245679202486646235792395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78163786134991097490528263 117245679202486646235792395)
            ·
              refine ⟨175868518803729969353688593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117245679202486646235792395 175868518803729969353688593)
              ·
                refine ⟨131901389102797477015266445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175868518803729969353688593 131901389102797477015266445)
                ·
                  refine ⟨49463020913549053880724917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131901389102797477015266445 49463020913549053880724917)
                  ·
                    refine ⟨4637158210645223801317961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49463020913549053880724917 4637158210645223801317961)
                    ·
                      refine ⟨3477868657983917850988471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637158210645223801317961 3477868657983917850988471)
                      ·
                        rfl

theorem cell23_6773125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_6773125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773125 prefixEnd_6773125 := by exact prefixLift 6773125
  have htrace : WordTrace (prefixWord ++ tailWord_6773125) baseStart_6773125 baseEnd_6773125 := by
    simpa [prefixWord, tailWord_6773125, baseEnd_6773125] using wordTrace_append hprefix tailTrace_6773125
  have hstable : (prefixWord ++ tailWord_6773125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773125).length < 2 ^ (prefixWord ++ tailWord_6773125).sum := by decide
  have hdescent : baseEnd_6773125 < baseStart_6773125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773149 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_6773149 : Nat := 118140960795 + 6773149 * 2 ^ 59
def prefixEnd_6773149 : Nat := 4983230072969 + 3 ^ 40 * 6773149 * 2
def baseEnd_6773149 : Nat := 3477880981519625757088361

theorem tailTrace_6773149 : CollatzResearch.WordTrace tailWord_6773149 prefixEnd_6773149 3477880981519625757088361 := by
  unfold tailWord_6773149
  simp only [CollatzResearch.WordTrace]
  refine ⟨247037038939045409599802501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164691359292696939733201667 247037038939045409599802501)
  ·
    refine ⟨46319444801071014299962969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247037038939045409599802501 46319444801071014299962969)
    ·
      refine ⟨34739583600803260724972227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46319444801071014299962969 34739583600803260724972227)
      ·
        refine ⟨52109375401204891087458341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34739583600803260724972227 52109375401204891087458341)
        ·
          refine ⟨9770507887725917078898439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52109375401204891087458341 9770507887725917078898439)
          ·
            refine ⟨14655761831588875618347659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9770507887725917078898439 14655761831588875618347659)
            ·
              refine ⟨21983642747383313427521489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14655761831588875618347659 21983642747383313427521489)
              ·
                refine ⟨16487732060537485070641117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21983642747383313427521489 16487732060537485070641117)
                ·
                  refine ⟨6182899522701556901490419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16487732060537485070641117 6182899522701556901490419)
                  ·
                    refine ⟨9274349284052335352235629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6182899522701556901490419 9274349284052335352235629)
                    ·
                      refine ⟨3477880981519625757088361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9274349284052335352235629 3477880981519625757088361)
                      ·
                        rfl

theorem cell23_6773149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_6773149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773149 prefixEnd_6773149 := by exact prefixLift 6773149
  have htrace : WordTrace (prefixWord ++ tailWord_6773149) baseStart_6773149 baseEnd_6773149 := by
    simpa [prefixWord, tailWord_6773149, baseEnd_6773149] using wordTrace_append hprefix tailTrace_6773149
  have hstable : (prefixWord ++ tailWord_6773149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773149).length < 2 ^ (prefixWord ++ tailWord_6773149).sum := by decide
  have hdescent : baseEnd_6773149 < baseStart_6773149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773155 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 4]
def baseStart_6773155 : Nat := 118140960795 + 6773155 * 2 ^ 59
def prefixEnd_6773155 : Nat := 4983230072969 + 3 ^ 40 * 6773155 * 2
def baseEnd_6773155 : Nat := 3477884062403552733613333

theorem tailTrace_6773155 : CollatzResearch.WordTrace tailWord_6773155 prefixEnd_6773155 3477884062403552733613333 := by
  unfold tailWord_6773155
  simp only [CollatzResearch.WordTrace]
  refine ⟨247037257777023672624520919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164691505184682448416347279 247037257777023672624520919)
  ·
    refine ⟨370555886665535508936781379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247037257777023672624520919 370555886665535508936781379)
    ·
      refine ⟨555833829998303263405172069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370555886665535508936781379 555833829998303263405172069)
      ·
        refine ⟨104218843124681861888469763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 555833829998303263405172069 104218843124681861888469763)
        ·
          refine ⟨156328264687022792832704645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104218843124681861888469763 156328264687022792832704645)
          ·
            refine ⟨29311549628816773656132121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156328264687022792832704645 29311549628816773656132121)
            ·
              refine ⟨21983662221612580242099091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29311549628816773656132121 21983662221612580242099091)
              ·
                refine ⟨32975493332418870363148637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21983662221612580242099091 32975493332418870363148637)
                ·
                  refine ⟨12365809999657076386180739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32975493332418870363148637 12365809999657076386180739)
                  ·
                    refine ⟨18548714999485614579271109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12365809999657076386180739 18548714999485614579271109)
                    ·
                      refine ⟨3477884062403552733613333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18548714999485614579271109 3477884062403552733613333)
                      ·
                        rfl

theorem cell23_6773155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_6773155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773155 prefixEnd_6773155 := by exact prefixLift 6773155
  have htrace : WordTrace (prefixWord ++ tailWord_6773155) baseStart_6773155 baseEnd_6773155 := by
    simpa [prefixWord, tailWord_6773155, baseEnd_6773155] using wordTrace_append hprefix tailTrace_6773155
  have hstable : (prefixWord ++ tailWord_6773155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773155).length < 2 ^ (prefixWord ++ tailWord_6773155).sum := by decide
  have hdescent : baseEnd_6773155 < baseStart_6773155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773159 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_6773159 : Nat := 118140960795 + 6773159 * 2 ^ 59
def prefixEnd_6773159 : Nat := 4983230072969 + 3 ^ 40 * 6773159 * 2
def baseEnd_6773159 : Nat := 3477886116326170717963315

theorem tailTrace_6773159 : CollatzResearch.WordTrace tailWord_6773159 prefixEnd_6773159 3477886116326170717963315 := by
  unfold tailWord_6773159
  simp only [CollatzResearch.WordTrace]
  refine ⟨247037403669009181307666531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164691602446006120871777687 247037403669009181307666531)
  ·
    refine ⟨370556105503513771961499797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247037403669009181307666531 370556105503513771961499797)
    ·
      refine ⟨17369817445477208060695303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 370556105503513771961499797 17369817445477208060695303)
      ·
        refine ⟨26054726168215812091042955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17369817445477208060695303 26054726168215812091042955)
        ·
          refine ⟨39082089252323718136564433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26054726168215812091042955 39082089252323718136564433)
          ·
            refine ⟨29311566939242788602423325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39082089252323718136564433 29311566939242788602423325)
            ·
              refine ⟨10991837602216045725908747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29311566939242788602423325 10991837602216045725908747)
              ·
                refine ⟨16487756403324068588863121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10991837602216045725908747 16487756403324068588863121)
                ·
                  refine ⟨12365817302493051441647341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16487756403324068588863121 12365817302493051441647341)
                  ·
                    refine ⟨4637181488434894290617753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12365817302493051441647341 4637181488434894290617753)
                    ·
                      refine ⟨3477886116326170717963315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637181488434894290617753 3477886116326170717963315)
                      ·
                        rfl

theorem cell23_6773159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_6773159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773159 prefixEnd_6773159 := by exact prefixLift 6773159
  have htrace : WordTrace (prefixWord ++ tailWord_6773159) baseStart_6773159 baseEnd_6773159 := by
    simpa [prefixWord, tailWord_6773159, baseEnd_6773159] using wordTrace_append hprefix tailTrace_6773159
  have hstable : (prefixWord ++ tailWord_6773159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773159).length < 2 ^ (prefixWord ++ tailWord_6773159).sum := by decide
  have hdescent : baseEnd_6773159 < baseStart_6773159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773168 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_6773168 : Nat := 118140960795 + 6773168 * 2 ^ 59
def prefixEnd_6773168 : Nat := 4983230072969 + 3 ^ 40 * 6773168 * 2
def baseEnd_6773168 : Nat := 3477890737652061182750773

theorem tailTrace_6773168 : CollatzResearch.WordTrace tailWord_6773168 prefixEnd_6773168 3477890737652061182750773 := by
  unfold tailWord_6773168
  simp only [CollatzResearch.WordTrace]
  refine ⟨123518865962988287922372079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164691821283984383896496105 123518865962988287922372079)
  ·
    refine ⟨185278298944482431883558119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123518865962988287922372079 185278298944482431883558119)
    ·
      refine ⟨277917448416723647825337179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185278298944482431883558119 277917448416723647825337179)
      ·
        refine ⟨416876172625085471738005769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277917448416723647825337179 416876172625085471738005769)
        ·
          refine ⟨312657129468814103803504327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416876172625085471738005769 312657129468814103803504327)
          ·
            refine ⟨468985694203221155705256491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312657129468814103803504327 468985694203221155705256491)
            ·
              refine ⟨703478541304831733557884737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468985694203221155705256491 703478541304831733557884737)
              ·
                refine ⟨527608905978623800168413553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703478541304831733557884737 527608905978623800168413553)
                ·
                  refine ⟨395706679483967850126310165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527608905978623800168413553 395706679483967850126310165)
                  ·
                    refine ⟨18548750600810992974670789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 395706679483967850126310165 18548750600810992974670789)
                    ·
                      refine ⟨3477890737652061182750773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18548750600810992974670789 3477890737652061182750773)
                      ·
                        rfl

theorem cell23_6773168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_6773168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773168 prefixEnd_6773168 := by exact prefixLift 6773168
  have htrace : WordTrace (prefixWord ++ tailWord_6773168) baseStart_6773168 baseEnd_6773168 := by
    simpa [prefixWord, tailWord_6773168, baseEnd_6773168] using wordTrace_append hprefix tailTrace_6773168
  have hstable : (prefixWord ++ tailWord_6773168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773168).length < 2 ^ (prefixWord ++ tailWord_6773168).sum := by decide
  have hdescent : baseEnd_6773168 < baseStart_6773168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773169 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 1, 5]
def baseStart_6773169 : Nat := 118140960795 + 6773169 * 2 ^ 59
def prefixEnd_6773169 : Nat := 4983230072969 + 3 ^ 40 * 6773169 * 2
def baseEnd_6773169 : Nat := 1159297083710905226279423

theorem tailTrace_6773169 : CollatzResearch.WordTrace tailWord_6773169 prefixEnd_6773169 1159297083710905226279423 := by
  unfold tailWord_6773169
  simp only [CollatzResearch.WordTrace]
  refine ⟨247037768398972953015530561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164691845599315302010353707 247037768398972953015530561)
  ·
    refine ⟨185278326299229714761647921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247037768398972953015530561 185278326299229714761647921)
    ·
      refine ⟨138958744724422286071235941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185278326299229714761647921 138958744724422286071235941)
      ·
        refine ⟨26054764635829178638356739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138958744724422286071235941 26054764635829178638356739)
        ·
          refine ⟨39082146953743767957535109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26054764635829178638356739 39082146953743767957535109)
          ·
            refine ⟨7327902553826956492037833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39082146953743767957535109 7327902553826956492037833)
            ·
              refine ⟨5495926915370217369028375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7327902553826956492037833 5495926915370217369028375)
              ·
                refine ⟨8243890373055326053542563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495926915370217369028375 8243890373055326053542563)
                ·
                  refine ⟨12365835559582989080313845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8243890373055326053542563 12365835559582989080313845)
                  ·
                    refine ⟨1159297083710905226279423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12365835559582989080313845 1159297083710905226279423)
                    ·
                      rfl

theorem cell23_6773169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_6773169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773169 prefixEnd_6773169 := by exact prefixLift 6773169
  have htrace : WordTrace (prefixWord ++ tailWord_6773169) baseStart_6773169 baseEnd_6773169 := by
    simpa [prefixWord, tailWord_6773169, baseEnd_6773169] using wordTrace_append hprefix tailTrace_6773169
  have hstable : (prefixWord ++ tailWord_6773169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773169).length < 2 ^ (prefixWord ++ tailWord_6773169).sum := by decide
  have hdescent : baseEnd_6773169 < baseStart_6773169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773206 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_6773206 : Nat := 118140960795 + 6773206 * 2 ^ 59
def prefixEnd_6773206 : Nat := 4983230072969 + 3 ^ 40 * 6773206 * 2
def baseEnd_6773206 : Nat := 3477910249916932034075599

theorem tailTrace_6773206 : CollatzResearch.WordTrace tailWord_6773206 prefixEnd_6773206 3477910249916932034075599 := by
  unfold tailWord_6773206
  simp only [CollatzResearch.WordTrace]
  refine ⟨15439944868739931770914217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164692745266559272223084981 15439944868739931770914217)
  ·
    refine ⟨11579958651554948828185663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15439944868739931770914217 11579958651554948828185663)
    ·
      refine ⟨17369937977332423242278495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11579958651554948828185663 17369937977332423242278495)
      ·
        refine ⟨26054906965998634863417743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17369937977332423242278495 26054906965998634863417743)
        ·
          refine ⟨39082360448997952295126615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26054906965998634863417743 39082360448997952295126615)
          ·
            refine ⟨58623540673496928442689923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39082360448997952295126615 58623540673496928442689923)
            ·
              refine ⟨87935311010245392664034885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58623540673496928442689923 87935311010245392664034885)
              ·
                refine ⟨16487870814421011124506541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87935311010245392664034885 16487870814421011124506541)
                ·
                  refine ⟨6182951555407879171689953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16487870814421011124506541 6182951555407879171689953)
                  ·
                    refine ⟨4637213666555909378767465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6182951555407879171689953 4637213666555909378767465)
                    ·
                      refine ⟨3477910249916932034075599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637213666555909378767465 3477910249916932034075599)
                      ·
                        rfl

theorem cell23_6773206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_6773206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773206 prefixEnd_6773206 := by exact prefixLift 6773206
  have htrace : WordTrace (prefixWord ++ tailWord_6773206) baseStart_6773206 baseEnd_6773206 := by
    simpa [prefixWord, tailWord_6773206, baseEnd_6773206] using wordTrace_append hprefix tailTrace_6773206
  have hstable : (prefixWord ++ tailWord_6773206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773206).length < 2 ^ (prefixWord ++ tailWord_6773206).sum := by decide
  have hdescent : baseEnd_6773206 < baseStart_6773206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773245 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_6773245 : Nat := 118140960795 + 6773245 * 2 ^ 59
def prefixEnd_6773245 : Nat := 4983230072969 + 3 ^ 40 * 6773245 * 2
def baseEnd_6773245 : Nat := 3477930275662457381487919

theorem tailTrace_6773245 : CollatzResearch.WordTrace tailWord_6773245 prefixEnd_6773245 3477930275662457381487919 := by
  unfold tailWord_6773245
  simp only [CollatzResearch.WordTrace]
  refine ⟨247040540346697617995297189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164693693564465078663531459 247040540346697617995297189)
  ·
    refine ⟨46320101315005803374118223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247040540346697617995297189 46320101315005803374118223)
    ·
      refine ⟨69480151972508705061177335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46320101315005803374118223 69480151972508705061177335)
      ·
        refine ⟨104220227958763057591766003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69480151972508705061177335 104220227958763057591766003)
        ·
          refine ⟨156330341938144586387649005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104220227958763057591766003 156330341938144586387649005)
          ·
            refine ⟨58623878226804219895368377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156330341938144586387649005 58623878226804219895368377)
            ·
              refine ⟨43967908670103164921526283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58623878226804219895368377 43967908670103164921526283)
              ·
                refine ⟨65951863005154747382289425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43967908670103164921526283 65951863005154747382289425)
                ·
                  refine ⟨49463897253866060536717069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65951863005154747382289425 49463897253866060536717069)
                  ·
                    refine ⟨18548961470199772701268901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49463897253866060536717069 18548961470199772701268901)
                    ·
                      refine ⟨3477930275662457381487919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18548961470199772701268901 3477930275662457381487919)
                      ·
                        rfl

theorem cell23_6773245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_6773245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773245 prefixEnd_6773245 := by exact prefixLift 6773245
  have htrace : WordTrace (prefixWord ++ tailWord_6773245) baseStart_6773245 baseEnd_6773245 := by
    simpa [prefixWord, tailWord_6773245, baseEnd_6773245] using wordTrace_append hprefix tailTrace_6773245
  have hstable : (prefixWord ++ tailWord_6773245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773245).length < 2 ^ (prefixWord ++ tailWord_6773245).sum := by decide
  have hdescent : baseEnd_6773245 < baseStart_6773245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773250 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_6773250 : Nat := 118140960795 + 6773250 * 2 ^ 59
def prefixEnd_6773250 : Nat := 4983230072969 + 3 ^ 40 * 6773250 * 2
def baseEnd_6773250 : Nat := 1159310947688576620641799

theorem tailTrace_6773250 : CollatzResearch.WordTrace tailWord_6773250 prefixEnd_6773250 1159310947688576620641799 := by
  unfold tailWord_6773250
  simp only [CollatzResearch.WordTrace]
  refine ⟨61760180677919875962307301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164693815141119669232819469 61760180677919875962307301)
  ·
    refine ⟨11580033877109976742932619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61760180677919875962307301 11580033877109976742932619)
    ·
      refine ⟨17370050815664965114398929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11580033877109976742932619 17370050815664965114398929)
      ·
        refine ⟨13027538111748723835799197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17370050815664965114398929 13027538111748723835799197)
        ·
          refine ⟨4885326791905771438424699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13027538111748723835799197 4885326791905771438424699)
          ·
            refine ⟨7327990187858657157637049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4885326791905771438424699 7327990187858657157637049)
            ·
              refine ⟨5495992640893992868227787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7327990187858657157637049 5495992640893992868227787)
              ·
                refine ⟨8243988961340989302341681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495992640893992868227787 8243988961340989302341681)
                ·
                  refine ⟨6182991721005741976756261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8243988961340989302341681 6182991721005741976756261)
                  ·
                    refine ⟨1159310947688576620641799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6182991721005741976756261 1159310947688576620641799)
                    ·
                      rfl

theorem cell23_6773250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_6773250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773250 prefixEnd_6773250 := by exact prefixLift 6773250
  have htrace : WordTrace (prefixWord ++ tailWord_6773250) baseStart_6773250 baseEnd_6773250 := by
    simpa [prefixWord, tailWord_6773250, baseEnd_6773250] using wordTrace_append hprefix tailTrace_6773250
  have hstable : (prefixWord ++ tailWord_6773250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773250).length < 2 ^ (prefixWord ++ tailWord_6773250).sum := by decide
  have hdescent : baseEnd_6773250 < baseStart_6773250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773265 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 3]
def baseStart_6773265 : Nat := 118140960795 + 6773265 * 2 ^ 59
def prefixEnd_6773265 : Nat := 4983230072969 + 3 ^ 40 * 6773265 * 2
def baseEnd_6773265 : Nat := 3477940545275547303237827

theorem tailTrace_6773265 : CollatzResearch.WordTrace tailWord_6773265 prefixEnd_6773265 3477940545275547303237827 := by
  unfold tailWord_6773265
  simp only [CollatzResearch.WordTrace]
  refine ⟨247041269806625161411025249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164694179871083440940683499 247041269806625161411025249)
  ·
    refine ⟨185280952354968871058268937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247041269806625161411025249 185280952354968871058268937)
    ·
      refine ⟨138960714266226653293701703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185280952354968871058268937 138960714266226653293701703)
      ·
        refine ⟨208441071399339979940552555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138960714266226653293701703 208441071399339979940552555)
        ·
          refine ⟨312661607099009969910828833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208441071399339979940552555 312661607099009969910828833)
          ·
            refine ⟨234496205324257477433121625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312661607099009969910828833 234496205324257477433121625)
            ·
              refine ⟨175872153993193108074841219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234496205324257477433121625 175872153993193108074841219)
              ·
                refine ⟨263808230989789662112261829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175872153993193108074841219 263808230989789662112261829)
                ·
                  refine ⟨49464043310585561646049093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263808230989789662112261829 49464043310585561646049093)
                  ·
                    refine ⟨9274508120734792808634205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49464043310585561646049093 9274508120734792808634205)
                    ·
                      refine ⟨3477940545275547303237827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9274508120734792808634205 3477940545275547303237827)
                      ·
                        rfl

theorem cell23_6773265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_6773265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773265 prefixEnd_6773265 := by exact prefixLift 6773265
  have htrace : WordTrace (prefixWord ++ tailWord_6773265) baseStart_6773265 baseEnd_6773265 := by
    simpa [prefixWord, tailWord_6773265, baseEnd_6773265] using wordTrace_append hprefix tailTrace_6773265
  have hstable : (prefixWord ++ tailWord_6773265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773265).length < 2 ^ (prefixWord ++ tailWord_6773265).sum := by decide
  have hdescent : baseEnd_6773265 < baseStart_6773265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773295 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 3]
def baseStart_6773295 : Nat := 118140960795 + 6773295 * 2 ^ 59
def prefixEnd_6773295 : Nat := 4983230072969 + 3 ^ 40 * 6773295 * 2
def baseEnd_6773295 : Nat := 3477955949695182185862689

theorem tailTrace_6773295 : CollatzResearch.WordTrace tailWord_6773295 prefixEnd_6773295 3477955949695182185862689 := by
  unfold tailWord_6773295
  simp only [CollatzResearch.WordTrace]
  refine ⟨247042363996516476534617339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164694909331010984356411559 247042363996516476534617339)
  ·
    refine ⟨370563545994774714801926009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247042363996516476534617339 370563545994774714801926009)
    ·
      refine ⟨277922659496081036101444507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370563545994774714801926009 277922659496081036101444507)
      ·
        refine ⟨416883989244121554152166761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277922659496081036101444507 416883989244121554152166761)
        ·
          refine ⟨312662991933091165614125071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416883989244121554152166761 312662991933091165614125071)
          ·
            refine ⟨468994487899636748421187607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312662991933091165614125071 468994487899636748421187607)
            ·
              refine ⟨703491731849455122631781411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468994487899636748421187607 703491731849455122631781411)
              ·
                refine ⟨1055237597774182683947672117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703491731849455122631781411 1055237597774182683947672117)
                ·
                  refine ⟨98928524791329626620094261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1055237597774182683947672117 98928524791329626620094261)
                  ·
                    refine ⟨9274549199187152495633837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98928524791329626620094261 9274549199187152495633837)
                    ·
                      refine ⟨3477955949695182185862689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9274549199187152495633837 3477955949695182185862689)
                      ·
                        rfl

theorem cell23_6773295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 3].length) (baseStart_6773295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773295 prefixEnd_6773295 := by exact prefixLift 6773295
  have htrace : WordTrace (prefixWord ++ tailWord_6773295) baseStart_6773295 baseEnd_6773295 := by
    simpa [prefixWord, tailWord_6773295, baseEnd_6773295] using wordTrace_append hprefix tailTrace_6773295
  have hstable : (prefixWord ++ tailWord_6773295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773295).length < 2 ^ (prefixWord ++ tailWord_6773295).sum := by decide
  have hdescent : baseEnd_6773295 < baseStart_6773295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773315 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 4, 5]
def baseStart_6773315 : Nat := 118140960795 + 6773315 * 2 ^ 59
def prefixEnd_6773315 : Nat := 4983230072969 + 3 ^ 40 * 6773315 * 2
def baseEnd_6773315 : Nat := 1159322073102757369204199

theorem tailTrace_6773315 : CollatzResearch.WordTrace tailWord_6773315 prefixEnd_6773315 1159322073102757369204199 := by
  unfold tailWord_6773315
  simp only [CollatzResearch.WordTrace]
  refine ⟨247043093456444019950345399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164695395637629346633563599 247043093456444019950345399)
  ·
    refine ⟨370564640184666029925518099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247043093456444019950345399 370564640184666029925518099)
    ·
      refine ⟨555846960276999044888277149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370564640184666029925518099 555846960276999044888277149)
      ·
        refine ⟨208442610103874641833103931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555846960276999044888277149 208442610103874641833103931)
        ·
          refine ⟨312663915155811962749655897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208442610103874641833103931 312663915155811962749655897)
          ·
            refine ⟨234497936366858972062241923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312663915155811962749655897 234497936366858972062241923)
            ·
              refine ⟨351746904550288458093362885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234497936366858972062241923 351746904550288458093362885)
              ·
                refine ⟨65952544603179085892505541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351746904550288458093362885 65952544603179085892505541)
                ·
                  refine ⟨12366102113096078604844789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65952544603179085892505541 12366102113096078604844789)
                  ·
                    refine ⟨1159322073102757369204199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12366102113096078604844789 1159322073102757369204199)
                    ·
                      rfl

theorem cell23_6773315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 5].length) (baseStart_6773315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773315 prefixEnd_6773315 := by exact prefixLift 6773315
  have htrace : WordTrace (prefixWord ++ tailWord_6773315) baseStart_6773315 baseEnd_6773315 := by
    simpa [prefixWord, tailWord_6773315, baseEnd_6773315] using wordTrace_append hprefix tailTrace_6773315
  have hstable : (prefixWord ++ tailWord_6773315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773315).length < 2 ^ (prefixWord ++ tailWord_6773315).sum := by decide
  have hdescent : baseEnd_6773315 < baseStart_6773315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773332 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_6773332 : Nat := 118140960795 + 6773332 * 2 ^ 59
def prefixEnd_6773332 : Nat := 4983230072969 + 3 ^ 40 * 6773332 * 2
def baseEnd_6773332 : Nat := 1159324982826466180366673

theorem tailTrace_6773332 : CollatzResearch.WordTrace tailWord_6773332 prefixEnd_6773332 1159324982826466180366673 := by
  unfold tailWord_6773332
  simp only [CollatzResearch.WordTrace]
  refine ⟨123521856748691215926857125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164695808998254954569142833 123521856748691215926857125)
  ·
    refine ⟨23160348140379602986285711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123521856748691215926857125 23160348140379602986285711)
    ·
      refine ⟨34740522210569404479428567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23160348140379602986285711 34740522210569404479428567)
      ·
        refine ⟨52110783315854106719142851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34740522210569404479428567 52110783315854106719142851)
        ·
          refine ⟨78166174973781160078714277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52110783315854106719142851 78166174973781160078714277)
          ·
            refine ⟨14656157807583967514758927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78166174973781160078714277 14656157807583967514758927)
            ·
              refine ⟨21984236711375951272138391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14656157807583967514758927 21984236711375951272138391)
              ·
                refine ⟨32976355067063926908207587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21984236711375951272138391 32976355067063926908207587)
                ·
                  refine ⟨49464532600595890362311381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32976355067063926908207587 49464532600595890362311381)
                  ·
                    refine ⟨1159324982826466180366673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49464532600595890362311381 1159324982826466180366673)
                    ·
                      rfl

theorem cell23_6773332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_6773332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773332 prefixEnd_6773332 := by exact prefixLift 6773332
  have htrace : WordTrace (prefixWord ++ tailWord_6773332) baseStart_6773332 baseEnd_6773332 := by
    simpa [prefixWord, tailWord_6773332, baseEnd_6773332] using wordTrace_append hprefix tailTrace_6773332
  have hstable : (prefixWord ++ tailWord_6773332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773332).length < 2 ^ (prefixWord ++ tailWord_6773332).sum := by decide
  have hdescent : baseEnd_6773332 < baseStart_6773332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773369 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 2, 4, 2]
def baseStart_6773369 : Nat := 118140960795 + 6773369 * 2 ^ 59
def prefixEnd_6773369 : Nat := 4983230072969 + 3 ^ 40 * 6773369 * 2
def baseEnd_6773369 : Nat := 3477993947263614896337349

theorem tailTrace_6773369 : CollatzResearch.WordTrace tailWord_6773369 prefixEnd_6773369 3477993947263614896337349 := by
  unfold tailWord_6773369
  simp only [CollatzResearch.WordTrace]
  refine ⟨247045062998248387172811161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164696708665498924781874107 247045062998248387172811161)
  ·
    refine ⟨185283797248686290379608371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247045062998248387172811161 185283797248686290379608371)
    ·
      refine ⟨277925695873029435569412557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185283797248686290379608371 277925695873029435569412557)
      ·
        refine ⟨104222135952386038338529709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277925695873029435569412557 104222135952386038338529709)
        ·
          refine ⟨39083300982144764376948641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104222135952386038338529709 39083300982144764376948641)
          ·
            refine ⟨29312475736608573282711481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39083300982144764376948641 29312475736608573282711481)
            ·
              refine ⟨21984356802456429962033611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29312475736608573282711481 21984356802456429962033611)
              ·
                refine ⟨32976535203684644943050417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21984356802456429962033611 32976535203684644943050417)
                ·
                  refine ⟨24732401402763483707287813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32976535203684644943050417 24732401402763483707287813)
                  ·
                    refine ⟨4637325263018153195116465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24732401402763483707287813 4637325263018153195116465)
                    ·
                      refine ⟨3477993947263614896337349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637325263018153195116465 3477993947263614896337349)
                      ·
                        rfl

theorem cell23_6773369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_6773369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773369 prefixEnd_6773369 := by exact prefixLift 6773369
  have htrace : WordTrace (prefixWord ++ tailWord_6773369) baseStart_6773369 baseEnd_6773369 := by
    simpa [prefixWord, tailWord_6773369, baseEnd_6773369] using wordTrace_append hprefix tailTrace_6773369
  have hstable : (prefixWord ++ tailWord_6773369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773369).length < 2 ^ (prefixWord ++ tailWord_6773369).sum := by decide
  have hdescent : baseEnd_6773369 < baseStart_6773369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773372 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_6773372 : Nat := 118140960795 + 6773372 * 2 ^ 59
def prefixEnd_6773372 : Nat := 4983230072969 + 3 ^ 40 * 6773372 * 2
def baseEnd_6773372 : Nat := 3477995487705578384599835

theorem tailTrace_6773372 : CollatzResearch.WordTrace tailWord_6773372 prefixEnd_6773372 3477995487705578384599835 := by
  unfold tailWord_6773372
  simp only [CollatzResearch.WordTrace]
  refine ⟨123522586208618759342585185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164696781611491679123446913 123522586208618759342585185)
  ·
    refine ⟨92641939656464069506938889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123522586208618759342585185 92641939656464069506938889)
    ·
      refine ⟨69481454742348052130204167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92641939656464069506938889 69481454742348052130204167)
      ·
        refine ⟨104222182113522078195306251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69481454742348052130204167 104222182113522078195306251)
        ·
          refine ⟨156333273170283117292959377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104222182113522078195306251 156333273170283117292959377)
          ·
            refine ⟨117249954877712337969719533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156333273170283117292959377 117249954877712337969719533)
            ·
              refine ⟨43968733079142126738644825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117249954877712337969719533 43968733079142126738644825)
              ·
                refine ⟨32976549809356595053983619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43968733079142126738644825 32976549809356595053983619)
                ·
                  refine ⟨49464824714034892580975429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32976549809356595053983619 49464824714034892580975429)
                  ·
                    refine ⟨9274654633881542358932893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49464824714034892580975429 9274654633881542358932893)
                    ·
                      refine ⟨3477995487705578384599835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9274654633881542358932893 3477995487705578384599835)
                      ·
                        rfl

theorem cell23_6773372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_6773372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773372 prefixEnd_6773372 := by exact prefixLift 6773372
  have htrace : WordTrace (prefixWord ++ tailWord_6773372) baseStart_6773372 baseEnd_6773372 := by
    simpa [prefixWord, tailWord_6773372, baseEnd_6773372] using wordTrace_append hprefix tailTrace_6773372
  have hstable : (prefixWord ++ tailWord_6773372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773372).length < 2 ^ (prefixWord ++ tailWord_6773372).sum := by decide
  have hdescent : baseEnd_6773372 < baseStart_6773372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773395 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 6]
def baseStart_6773395 : Nat := 118140960795 + 6773395 * 2 ^ 59
def prefixEnd_6773395 : Nat := 4983230072969 + 3 ^ 40 * 6773395 * 2
def baseEnd_6773395 : Nat := 3478007297760631794612229

theorem tailTrace_6773395 : CollatzResearch.WordTrace tailWord_6773395 prefixEnd_6773395 3478007297760631794612229 := by
  unfold tailWord_6773395
  simp only [CollatzResearch.WordTrace]
  refine ⟨247046011296154193613257639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164697340864102795742171759 247046011296154193613257639)
  ·
    refine ⟨370569016944231290419886459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247046011296154193613257639 370569016944231290419886459)
    ·
      refine ⟨555853525416346935629829689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370569016944231290419886459 555853525416346935629829689)
      ·
        refine ⟨416890144062260201722372267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555853525416346935629829689 416890144062260201722372267)
        ·
          refine ⟨625335216093390302583558401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416890144062260201722372267 625335216093390302583558401)
          ·
            refine ⟨469001412070042726937668801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625335216093390302583558401 469001412070042726937668801)
            ·
              refine ⟨351751059052532045203251601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469001412070042726937668801 351751059052532045203251601)
              ·
                refine ⟨263813294289399033902438701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351751059052532045203251601 263813294289399033902438701)
                ·
                  refine ⟨98929985358524637713414513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263813294289399033902438701 98929985358524637713414513)
                  ·
                    refine ⟨74197489018893478285060885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98929985358524637713414513 74197489018893478285060885)
                    ·
                      refine ⟨3478007297760631794612229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74197489018893478285060885 3478007297760631794612229)
                      ·
                        rfl

theorem cell23_6773395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_6773395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773395 prefixEnd_6773395 := by exact prefixLift 6773395
  have htrace : WordTrace (prefixWord ++ tailWord_6773395) baseStart_6773395 baseEnd_6773395 := by
    simpa [prefixWord, tailWord_6773395, baseEnd_6773395] using wordTrace_append hprefix tailTrace_6773395
  have hstable : (prefixWord ++ tailWord_6773395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773395).length < 2 ^ (prefixWord ++ tailWord_6773395).sum := by decide
  have hdescent : baseEnd_6773395 < baseStart_6773395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773406 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_6773406 : Nat := 118140960795 + 6773406 * 2 ^ 59
def prefixEnd_6773406 : Nat := 4983230072969 + 3 ^ 40 * 6773406 * 2
def baseEnd_6773406 : Nat := 3478012946047831251574679

theorem tailTrace_6773406 : CollatzResearch.WordTrace tailWord_6773406 prefixEnd_6773406 3478012946047831251574679 := by
  unfold tailWord_6773406
  simp only [CollatzResearch.WordTrace]
  refine ⟨30880801562389292811488509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164697608332742894994605381 30880801562389292811488509)
  ·
    refine ⟨11580300585895984804308191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30880801562389292811488509 11580300585895984804308191)
    ·
      refine ⟨17370450878843977206462287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11580300585895984804308191 17370450878843977206462287)
      ·
        refine ⟨26055676318265965809693431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17370450878843977206462287 26055676318265965809693431)
        ·
          refine ⟨39083514477398948714540147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26055676318265965809693431 39083514477398948714540147)
          ·
            refine ⟨58625271716098423071810221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39083514477398948714540147 58625271716098423071810221)
            ·
              refine ⟨21984476893536908651928833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58625271716098423071810221 21984476893536908651928833)
              ·
                refine ⟨16488357670152681488946625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21984476893536908651928833 16488357670152681488946625)
                ·
                  refine ⟨12366268252614511116709969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16488357670152681488946625 12366268252614511116709969)
                  ·
                    refine ⟨9274701189460883337532477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12366268252614511116709969 9274701189460883337532477)
                    ·
                      refine ⟨3478012946047831251574679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9274701189460883337532477 3478012946047831251574679)
                      ·
                        rfl

theorem cell23_6773406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_6773406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773406 prefixEnd_6773406 := by exact prefixLift 6773406
  have htrace : WordTrace (prefixWord ++ tailWord_6773406) baseStart_6773406 baseEnd_6773406 := by
    simpa [prefixWord, tailWord_6773406, baseEnd_6773406] using wordTrace_append hprefix tailTrace_6773406
  have hstable : (prefixWord ++ tailWord_6773406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773406).length < 2 ^ (prefixWord ++ tailWord_6773406).sum := by decide
  have hdescent : baseEnd_6773406 < baseStart_6773406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773439 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 1, 5]
def baseStart_6773439 : Nat := 118140960795 + 6773439 * 2 ^ 59
def prefixEnd_6773439 : Nat := 4983230072969 + 3 ^ 40 * 6773439 * 2
def baseEnd_6773439 : Nat := 1159343296969809874154009

theorem tailTrace_6773439 : CollatzResearch.WordTrace tailWord_6773439 prefixEnd_6773439 1159343296969809874154009 := by
  unfold tailWord_6773439
  simp only [CollatzResearch.WordTrace]
  refine ⟨247047616107994789127859371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164698410738663192751906247 247047616107994789127859371)
  ·
    refine ⟨370571424161992183691789057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247047616107994789127859371 370571424161992183691789057)
    ·
      refine ⟨277928568121494137768841793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370571424161992183691789057 277928568121494137768841793)
      ·
        refine ⟨208446426091120603326631345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277928568121494137768841793 208446426091120603326631345)
        ·
          refine ⟨156334819568340452494973509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208446426091120603326631345 156334819568340452494973509)
          ·
            refine ⟨29312778669063834842807533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156334819568340452494973509 29312778669063834842807533)
            ·
              refine ⟨10992292000898938066052825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29312778669063834842807533 10992292000898938066052825)
              ·
                refine ⟨8244219000674203549539619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10992292000898938066052825 8244219000674203549539619)
                ·
                  refine ⟨12366328501011305324309429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8244219000674203549539619 12366328501011305324309429)
                  ·
                    refine ⟨1159343296969809874154009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12366328501011305324309429 1159343296969809874154009)
                    ·
                      rfl

theorem cell23_6773439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 5].length) (baseStart_6773439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773439 prefixEnd_6773439 := by exact prefixLift 6773439
  have htrace : WordTrace (prefixWord ++ tailWord_6773439) baseStart_6773439 baseEnd_6773439 := by
    simpa [prefixWord, tailWord_6773439, baseEnd_6773439] using wordTrace_append hprefix tailTrace_6773439
  have hstable : (prefixWord ++ tailWord_6773439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773439).length < 2 ^ (prefixWord ++ tailWord_6773439).sum := by decide
  have hdescent : baseEnd_6773439 < baseStart_6773439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773472 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_6773472 : Nat := 118140960795 + 6773472 * 2 ^ 59
def prefixEnd_6773472 : Nat := 4983230072969 + 3 ^ 40 * 6773472 * 2
def baseEnd_6773472 : Nat := 3478046835771027993349375

theorem tailTrace_6773472 : CollatzResearch.WordTrace tailWord_6773472 prefixEnd_6773472 3478046835771027993349375 := by
  unfold tailWord_6773472
  simp only [CollatzResearch.WordTrace]
  refine ⟨123524409858437617881905335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164699213144583490509207113 123524409858437617881905335)
  ·
    refine ⟨185286614787656426822858003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123524409858437617881905335 185286614787656426822858003)
    ·
      refine ⟨277929922181484640234287005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185286614787656426822858003 277929922181484640234287005)
      ·
        refine ⟨104223720818056740087857627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277929922181484640234287005 104223720818056740087857627)
        ·
          refine ⟨156335581227085110131786441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104223720818056740087857627 156335581227085110131786441)
          ·
            refine ⟨117251685920313832598839831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156335581227085110131786441 117251685920313832598839831)
            ·
              refine ⟨175877528880470748898259747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117251685920313832598839831 175877528880470748898259747)
              ·
                refine ⟨263816293320706123347389621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175877528880470748898259747 263816293320706123347389621)
                ·
                  refine ⟨24732777498816199063817777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263816293320706123347389621 24732777498816199063817777)
                  ·
                    refine ⟨18549583124112149297863333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24732777498816199063817777 18549583124112149297863333)
                    ·
                      refine ⟨3478046835771027993349375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18549583124112149297863333 3478046835771027993349375)
                      ·
                        rfl

theorem cell23_6773472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_6773472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773472 prefixEnd_6773472 := by exact prefixLift 6773472
  have htrace : WordTrace (prefixWord ++ tailWord_6773472) baseStart_6773472 baseEnd_6773472 := by
    simpa [prefixWord, tailWord_6773472, baseEnd_6773472] using wordTrace_append hprefix tailTrace_6773472
  have hstable : (prefixWord ++ tailWord_6773472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773472).length < 2 ^ (prefixWord ++ tailWord_6773472).sum := by decide
  have hdescent : baseEnd_6773472 < baseStart_6773472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773486 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_6773486 : Nat := 118140960795 + 6773486 * 2 ^ 59
def prefixEnd_6773486 : Nat := 4983230072969 + 3 ^ 40 * 6773486 * 2
def baseEnd_6773486 : Nat := 1159351341500063646191437

theorem tailTrace_6773486 : CollatzResearch.WordTrace tailWord_6773486 prefixEnd_6773486 1159351341500063646191437 := by
  unfold tailWord_6773486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30881166292353064519352539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164699553559216344103213541 30881166292353064519352539)
  ·
    refine ⟨46321749438529596779028809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30881166292353064519352539 46321749438529596779028809)
    ·
      refine ⟨34741312078897197584271607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46321749438529596779028809 34741312078897197584271607)
      ·
        refine ⟨52111968118345796376407411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34741312078897197584271607 52111968118345796376407411)
        ·
          refine ⟨78167952177518694564611117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52111968118345796376407411 78167952177518694564611117)
          ·
            refine ⟨29312982066569510461729169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78167952177518694564611117 29312982066569510461729169)
            ·
              refine ⟨21984736549927132846296877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29312982066569510461729169 21984736549927132846296877)
              ·
                refine ⟨8244276206222674817361329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21984736549927132846296877 8244276206222674817361329)
                ·
                  refine ⟨6183207154667006113020997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8244276206222674817361329 6183207154667006113020997)
                  ·
                    refine ⟨1159351341500063646191437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6183207154667006113020997 1159351341500063646191437)
                    ·
                      rfl

theorem cell23_6773486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_6773486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773486 prefixEnd_6773486 := by exact prefixLift 6773486
  have htrace : WordTrace (prefixWord ++ tailWord_6773486) baseStart_6773486 baseEnd_6773486 := by
    simpa [prefixWord, tailWord_6773486, baseEnd_6773486] using wordTrace_append hprefix tailTrace_6773486
  have hstable : (prefixWord ++ tailWord_6773486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773486).length < 2 ^ (prefixWord ++ tailWord_6773486).sum := by decide
  have hdescent : baseEnd_6773486 < baseStart_6773486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773489 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 4]
def baseStart_6773489 : Nat := 118140960795 + 6773489 * 2 ^ 59
def prefixEnd_6773489 : Nat := 4983230072969 + 3 ^ 40 * 6773489 * 2
def baseEnd_6773489 : Nat := 3478055564942154426836797

theorem tailTrace_6773489 : CollatzResearch.WordTrace tailWord_6773489 prefixEnd_6773489 3478055564942154426836797 := by
  unfold tailWord_6773489
  simp only [CollatzResearch.WordTrace]
  refine ⟨247049439757813647667179521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164699626505209098444786347 247049439757813647667179521)
  ·
    refine ⟨185287079818360235750384641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247049439757813647667179521 185287079818360235750384641)
    ·
      refine ⟨138965309863770176812788481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185287079818360235750384641 138965309863770176812788481)
      ·
        refine ⟨104223982397827632609591361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138965309863770176812788481 104223982397827632609591361)
        ·
          refine ⟨78167986798370724457193521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104223982397827632609591361 78167986798370724457193521)
          ·
            refine ⟨58625990098778043342895141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78167986798370724457193521 58625990098778043342895141)
            ·
              refine ⟨10992373143520883126792839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58625990098778043342895141 10992373143520883126792839)
              ·
                refine ⟨16488559715281324690189259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10992373143520883126792839 16488559715281324690189259)
                ·
                  refine ⟨24732839572921987035283889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16488559715281324690189259 24732839572921987035283889)
                  ·
                    refine ⟨18549629679691490276462917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24732839572921987035283889 18549629679691490276462917)
                    ·
                      refine ⟨3478055564942154426836797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18549629679691490276462917 3478055564942154426836797)
                      ·
                        rfl

theorem cell23_6773489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_6773489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773489 prefixEnd_6773489 := by exact prefixLift 6773489
  have htrace : WordTrace (prefixWord ++ tailWord_6773489) baseStart_6773489 baseEnd_6773489 := by
    simpa [prefixWord, tailWord_6773489, baseEnd_6773489] using wordTrace_append hprefix tailTrace_6773489
  have hstable : (prefixWord ++ tailWord_6773489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773489).length < 2 ^ (prefixWord ++ tailWord_6773489).sum := by decide
  have hdescent : baseEnd_6773489 < baseStart_6773489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773506 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_6773506 : Nat := 118140960795 + 6773506 * 2 ^ 59
def prefixEnd_6773506 : Nat := 4983230072969 + 3 ^ 40 * 6773506 * 2
def baseEnd_6773506 : Nat := 3478064294113280860324219

theorem tailTrace_6773506 : CollatzResearch.WordTrace tailWord_6773506 prefixEnd_6773506 3478064294113280860324219 := by
  unfold tailWord_6773506
  simp only [CollatzResearch.WordTrace]
  refine ⟨61762514949688014892637093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164700039865834706380365581 61762514949688014892637093)
  ·
    refine ⟨11580471553066502792369455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61762514949688014892637093 11580471553066502792369455)
    ·
      refine ⟨17370707329599754188554183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11580471553066502792369455 17370707329599754188554183)
      ·
        refine ⟨26056060994399631282831275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17370707329599754188554183 26056060994399631282831275)
        ·
          refine ⟨39084091491599446924246913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26056060994399631282831275 39084091491599446924246913)
          ·
            refine ⟨29313068618699585193185185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39084091491599446924246913 29313068618699585193185185)
            ·
              refine ⟨21984801464024688894888889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29313068618699585193185185 21984801464024688894888889)
              ·
                refine ⟨16488601098018516671166667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21984801464024688894888889 16488601098018516671166667)
                ·
                  refine ⟨24732901647027775006750001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16488601098018516671166667 24732901647027775006750001)
                  ·
                    refine ⟨18549676235270831255062501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24732901647027775006750001 18549676235270831255062501)
                    ·
                      refine ⟨3478064294113280860324219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18549676235270831255062501 3478064294113280860324219)
                      ·
                        rfl

theorem cell23_6773506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_6773506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773506 prefixEnd_6773506 := by exact prefixLift 6773506
  have htrace : WordTrace (prefixWord ++ tailWord_6773506) baseStart_6773506 baseEnd_6773506 := by
    simpa [prefixWord, tailWord_6773506, baseEnd_6773506] using wordTrace_append hprefix tailTrace_6773506
  have hstable : (prefixWord ++ tailWord_6773506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773506).length < 2 ^ (prefixWord ++ tailWord_6773506).sum := by decide
  have hdescent : baseEnd_6773506 < baseStart_6773506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773552 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_6773552 : Nat := 118140960795 + 6773552 * 2 ^ 59
def prefixEnd_6773552 : Nat := 4983230072969 + 3 ^ 40 * 6773552 * 2
def baseEnd_6773552 : Nat := 3478087914223387680349007

theorem tailTrace_6773552 : CollatzResearch.WordTrace tailWord_6773552 prefixEnd_6773552 3478087914223387680349007 := by
  unfold tailWord_6773552
  simp only [CollatzResearch.WordTrace]
  refine ⟨123525868778292704713361455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164701158371056939617815273 123525868778292704713361455)
  ·
    refine ⟨185288803167439057070042183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123525868778292704713361455 185288803167439057070042183)
    ·
      refine ⟨277933204751158585605063275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185288803167439057070042183 277933204751158585605063275)
      ·
        refine ⟨416899807126737878407594913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277933204751158585605063275 416899807126737878407594913)
        ·
          refine ⟨312674855345053408805696185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416899807126737878407594913 312674855345053408805696185)
          ·
            refine ⟨234506141508790056604272139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312674855345053408805696185 234506141508790056604272139)
            ·
              refine ⟨351759212263185084906408209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234506141508790056604272139 351759212263185084906408209)
              ·
                refine ⟨263819409197388813679806157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351759212263185084906408209 263819409197388813679806157)
                ·
                  refine ⟨98932278449020805129927309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263819409197388813679806157 98932278449020805129927309)
                  ·
                    refine ⟨37099604418382801923722741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98932278449020805129927309 37099604418382801923722741)
                    ·
                      refine ⟨3478087914223387680349007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37099604418382801923722741 3478087914223387680349007)
                      ·
                        rfl

theorem cell23_6773552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_6773552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773552 prefixEnd_6773552 := by exact prefixLift 6773552
  have htrace : WordTrace (prefixWord ++ tailWord_6773552) baseStart_6773552 baseEnd_6773552 := by
    simpa [prefixWord, tailWord_6773552, baseEnd_6773552] using wordTrace_append hprefix tailTrace_6773552
  have hstable : (prefixWord ++ tailWord_6773552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773552).length < 2 ^ (prefixWord ++ tailWord_6773552).sum := by decide
  have hdescent : baseEnd_6773552 < baseStart_6773552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773553 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 1, 3, 2]
def baseStart_6773553 : Nat := 118140960795 + 6773553 * 2 ^ 59
def prefixEnd_6773553 : Nat := 4983230072969 + 3 ^ 40 * 6773553 * 2
def baseEnd_6773553 : Nat := 3478088427704042176436503

theorem tailTrace_6773553 : CollatzResearch.WordTrace tailWord_6773553 prefixEnd_6773553 3478088427704042176436503 := by
  unfold tailWord_6773553
  simp only [CollatzResearch.WordTrace]
  refine ⟨247051774029581786597509313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164701182686387857731672875 247051774029581786597509313)
  ·
    refine ⟨185288830522186339948131985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247051774029581786597509313 185288830522186339948131985)
    ·
      refine ⟨138966622891639754961098989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185288830522186339948131985 138966622891639754961098989)
      ·
        refine ⟨52112483584364908110412121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138966622891639754961098989 52112483584364908110412121)
        ·
          refine ⟨39084362688273681082809091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52112483584364908110412121 39084362688273681082809091)
          ·
            refine ⟨58626544032410521624213637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39084362688273681082809091 58626544032410521624213637)
            ·
              refine ⟨10992477006076972804540057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58626544032410521624213637 10992477006076972804540057)
              ·
                refine ⟨8244357754557729603405043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10992477006076972804540057 8244357754557729603405043)
                ·
                  refine ⟨12366536631836594405107565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8244357754557729603405043 12366536631836594405107565)
                  ·
                    refine ⟨4637451236938722901915337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12366536631836594405107565 4637451236938722901915337)
                    ·
                      refine ⟨3478088427704042176436503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637451236938722901915337 3478088427704042176436503)
                      ·
                        rfl

theorem cell23_6773553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_6773553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773553 prefixEnd_6773553 := by exact prefixLift 6773553
  have htrace : WordTrace (prefixWord ++ tailWord_6773553) baseStart_6773553 baseEnd_6773553 := by
    simpa [prefixWord, tailWord_6773553, baseEnd_6773553] using wordTrace_append hprefix tailTrace_6773553
  have hstable : (prefixWord ++ tailWord_6773553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773553).length < 2 ^ (prefixWord ++ tailWord_6773553).sum := by decide
  have hdescent : baseEnd_6773553 < baseStart_6773553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773599 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 3]
def baseStart_6773599 : Nat := 118140960795 + 6773599 * 2 ^ 59
def prefixEnd_6773599 : Nat := 4983230072969 + 3 ^ 40 * 6773599 * 2
def baseEnd_6773599 : Nat := 3478112047814148996461291

theorem tailTrace_6773599 : CollatzResearch.WordTrace tailWord_6773599 prefixEnd_6773599 3478112047814148996461291 := by
  unfold tailWord_6773599
  simp only [CollatzResearch.WordTrace]
  refine ⟨247053451787415136453683851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164702301191610090969122567 247053451787415136453683851)
  ·
    refine ⟨370580177681122704680525777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247053451787415136453683851 370580177681122704680525777)
    ·
      refine ⟨277935133260842028510394333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370580177681122704680525777 277935133260842028510394333)
      ·
        refine ⟨104225674972815760691397875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277935133260842028510394333 104225674972815760691397875)
        ·
          refine ⟨156338512459223641037096813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104225674972815760691397875 156338512459223641037096813)
          ·
            refine ⟨58626942172208865388911305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156338512459223641037096813 58626942172208865388911305)
            ·
              refine ⟨43970206629156649041683479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58626942172208865388911305 43970206629156649041683479)
              ·
                refine ⟨65955309943734973562525219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43970206629156649041683479 65955309943734973562525219)
                ·
                  refine ⟨98932964915602460343787829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65955309943734973562525219 98932964915602460343787829)
                  ·
                    refine ⟨9274965460837730657230109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98932964915602460343787829 9274965460837730657230109)
                    ·
                      refine ⟨3478112047814148996461291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9274965460837730657230109 3478112047814148996461291)
                      ·
                        rfl

theorem cell23_6773599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_6773599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773599 prefixEnd_6773599 := by exact prefixLift 6773599
  have htrace : WordTrace (prefixWord ++ tailWord_6773599) baseStart_6773599 baseEnd_6773599 := by
    simpa [prefixWord, tailWord_6773599, baseEnd_6773599] using wordTrace_append hprefix tailTrace_6773599
  have hstable : (prefixWord ++ tailWord_6773599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773599).length < 2 ^ (prefixWord ++ tailWord_6773599).sum := by decide
  have hdescent : baseEnd_6773599 < baseStart_6773599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773619 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 2, 5]
def baseStart_6773619 : Nat := 118140960795 + 6773619 * 2 ^ 59
def prefixEnd_6773619 : Nat := 4983230072969 + 3 ^ 40 * 6773619 * 2
def baseEnd_6773619 : Nat := 1159374105809079639403733

theorem tailTrace_6773619 : CollatzResearch.WordTrace tailWord_6773619 prefixEnd_6773619 1159374105809079639403733 := by
  unfold tailWord_6773619
  simp only [CollatzResearch.WordTrace]
  refine ⟨247054181247342679869411911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164702787498228453246274607 247054181247342679869411911)
  ·
    refine ⟨370581271871014019804117867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247054181247342679869411911 370581271871014019804117867)
    ·
      refine ⟨555871907806521029706176801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370581271871014019804117867 555871907806521029706176801)
      ·
        refine ⟨416903930854890772279632601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555871907806521029706176801 416903930854890772279632601)
        ·
          refine ⟨312677948141168079209724451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416903930854890772279632601 312677948141168079209724451)
          ·
            refine ⟨469016922211752118814586677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312677948141168079209724451 469016922211752118814586677)
            ·
              refine ⟨43970336457351761138867501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 469016922211752118814586677 43970336457351761138867501)
              ·
                refine ⟨16488876171506910427075313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43970336457351761138867501 16488876171506910427075313)
                ·
                  refine ⟨12366657128630182820306485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16488876171506910427075313 12366657128630182820306485)
                  ·
                    refine ⟨1159374105809079639403733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12366657128630182820306485 1159374105809079639403733)
                    ·
                      rfl

theorem cell23_6773619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 5].length) (baseStart_6773619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773619 prefixEnd_6773619 := by exact prefixLift 6773619
  have htrace : WordTrace (prefixWord ++ tailWord_6773619) baseStart_6773619 baseEnd_6773619 := by
    simpa [prefixWord, tailWord_6773619, baseEnd_6773619] using wordTrace_append hprefix tailTrace_6773619
  have hstable : (prefixWord ++ tailWord_6773619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773619).length < 2 ^ (prefixWord ++ tailWord_6773619).sum := by decide
  have hdescent : baseEnd_6773619 < baseStart_6773619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773629 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_6773629 : Nat := 118140960795 + 6773629 * 2 ^ 59
def prefixEnd_6773629 : Nat := 4983230072969 + 3 ^ 40 * 6773629 * 2
def baseEnd_6773629 : Nat := 3478127452233783879086153

theorem tailTrace_6773629 : CollatzResearch.WordTrace tailWord_6773629 prefixEnd_6773629 3478127452233783879086153 := by
  unfold tailWord_6773629
  simp only [CollatzResearch.WordTrace]
  refine ⟨247054545977306451577275941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164703030651537634384850627 247054545977306451577275941)
  ·
    refine ⟨46322727370744959670739239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247054545977306451577275941 46322727370744959670739239)
    ·
      refine ⟨69484091056117439506108859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46322727370744959670739239 69484091056117439506108859)
      ·
        refine ⟨104226136584176159259163289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69484091056117439506108859 104226136584176159259163289)
        ·
          refine ⟨78169602438132119444372467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104226136584176159259163289 78169602438132119444372467)
          ·
            refine ⟨117254403657198179166558701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78169602438132119444372467 117254403657198179166558701)
            ·
              refine ⟨43970401371449317187459513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117254403657198179166558701 43970401371449317187459513)
              ·
                refine ⟨32977801028586987890594635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43970401371449317187459513 32977801028586987890594635)
                ·
                  refine ⟨49466701542880481835891953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32977801028586987890594635 49466701542880481835891953)
                  ·
                    refine ⟨37100026157160361376918965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49466701542880481835891953 37100026157160361376918965)
                    ·
                      refine ⟨3478127452233783879086153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37100026157160361376918965 3478127452233783879086153)
                      ·
                        rfl

theorem cell23_6773629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_6773629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773629 prefixEnd_6773629 := by exact prefixLift 6773629
  have htrace : WordTrace (prefixWord ++ tailWord_6773629) baseStart_6773629 baseEnd_6773629 := by
    simpa [prefixWord, tailWord_6773629, baseEnd_6773629] using wordTrace_append hprefix tailTrace_6773629
  have hstable : (prefixWord ++ tailWord_6773629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773629).length < 2 ^ (prefixWord ++ tailWord_6773629).sum := by decide
  have hdescent : baseEnd_6773629 < baseStart_6773629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773640 : List Nat := [2, 1, 3, 3, 2, 3, 2, 2, 5]
def baseStart_6773640 : Nat := 118140960795 + 6773640 * 2 ^ 59
def prefixEnd_6773640 : Nat := 4983230072969 + 3 ^ 40 * 6773640 * 2
def baseEnd_6773640 : Nat := 386459233391220370672067

theorem tailTrace_6773640 : CollatzResearch.WordTrace tailWord_6773640 prefixEnd_6773640 386459233391220370672067 := by
  unfold tailWord_6773640
  simp only [CollatzResearch.WordTrace]
  refine ⟨123527473590133300227963187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164703298120177733637284249 123527473590133300227963187)
  ·
    refine ⟨185291210385199950341944781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123527473590133300227963187 185291210385199950341944781)
    ·
      refine ⟨69484203894449981378229293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185291210385199950341944781 69484203894449981378229293)
      ·
        refine ⟨26056576460418743016835985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69484203894449981378229293 26056576460418743016835985)
        ·
          refine ⟨19542432345314057262626989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26056576460418743016835985 19542432345314057262626989)
          ·
            refine ⟨7328412129492771473485121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19542432345314057262626989 7328412129492771473485121)
            ·
              refine ⟨5496309097119578605113841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7328412129492771473485121 5496309097119578605113841)
              ·
                refine ⟨4122231822839683953835381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5496309097119578605113841 4122231822839683953835381)
                ·
                  refine ⟨386459233391220370672067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4122231822839683953835381 386459233391220370672067)
                  ·
                    rfl

theorem cell23_6773640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 5].length) (baseStart_6773640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773640 prefixEnd_6773640 := by exact prefixLift 6773640
  have htrace : WordTrace (prefixWord ++ tailWord_6773640) baseStart_6773640 baseEnd_6773640 := by
    simpa [prefixWord, tailWord_6773640, baseEnd_6773640] using wordTrace_append hprefix tailTrace_6773640
  have hstable : (prefixWord ++ tailWord_6773640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773640).length < 2 ^ (prefixWord ++ tailWord_6773640).sum := by decide
  have hdescent : baseEnd_6773640 < baseStart_6773640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773696 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 6]
def baseStart_6773696 : Nat := 118140960795 + 6773696 * 2 ^ 59
def prefixEnd_6773696 : Nat := 4983230072969 + 3 ^ 40 * 6773696 * 2
def baseEnd_6773696 : Nat := 386462428381959457438705

theorem tailTrace_6773696 : CollatzResearch.WordTrace tailWord_6773696 prefixEnd_6773696 386462428381959457438705 := by
  unfold tailWord_6773696
  simp only [CollatzResearch.WordTrace]
  refine ⟨123528494834031861009982471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164704659778709148013309961 123528494834031861009982471)
  ·
    refine ⟨185292742251047791514973707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123528494834031861009982471 185292742251047791514973707)
    ·
      refine ⟨277939113376571687272460561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185292742251047791514973707 277939113376571687272460561)
      ·
        refine ⟨208454335032428765454345421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277939113376571687272460561 208454335032428765454345421)
        ·
          refine ⟨78170375637160787045379533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208454335032428765454345421 78170375637160787045379533)
          ·
            refine ⟨29313890863935295142017325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78170375637160787045379533 29313890863935295142017325)
            ·
              refine ⟨10992709073975735678256497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29313890863935295142017325 10992709073975735678256497)
              ·
                refine ⟨8244531805481801758692373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10992709073975735678256497 8244531805481801758692373)
                ·
                  refine ⟨386462428381959457438705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8244531805481801758692373 386462428381959457438705)
                  ·
                    rfl

theorem cell23_6773696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 6].length) (baseStart_6773696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773696 prefixEnd_6773696 := by exact prefixLift 6773696
  have htrace : WordTrace (prefixWord ++ tailWord_6773696) baseStart_6773696 baseEnd_6773696 := by
    simpa [prefixWord, tailWord_6773696, baseEnd_6773696] using wordTrace_append hprefix tailTrace_6773696
  have hstable : (prefixWord ++ tailWord_6773696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773696).length < 2 ^ (prefixWord ++ tailWord_6773696).sum := by decide
  have hdescent : baseEnd_6773696 < baseStart_6773696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773750 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_6773750 : Nat := 118140960795 + 6773750 * 2 ^ 59
def prefixEnd_6773750 : Nat := 4983230072969 + 3 ^ 40 * 6773750 * 2
def baseEnd_6773750 : Nat := 3478189583392977905673097

theorem tailTrace_6773750 : CollatzResearch.WordTrace tailWord_6773750 prefixEnd_6773750 3478189583392977905673097 := by
  unfold tailWord_6773750
  simp only [CollatzResearch.WordTrace]
  refine ⟨15441184950616755577651919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164705972806578726161620469 15441184950616755577651919)
  ·
    refine ⟨23161777425925133366477879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15441184950616755577651919 23161777425925133366477879)
    ·
      refine ⟨34742666138887700049716819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23161777425925133366477879 34742666138887700049716819)
      ·
        refine ⟨52113999208331550074575229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34742666138887700049716819 52113999208331550074575229)
        ·
          refine ⟨19542749703124331277965711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52113999208331550074575229 19542749703124331277965711)
          ·
            refine ⟨29314124554686496916948567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19542749703124331277965711 29314124554686496916948567)
            ·
              refine ⟨43971186832029745375422851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29314124554686496916948567 43971186832029745375422851)
              ·
                refine ⟨65956780248044618063134277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43971186832029745375422851 65956780248044618063134277)
                ·
                  refine ⟨12366896296508365886837677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65956780248044618063134277 12366896296508365886837677)
                  ·
                    refine ⟨4637586111190637207564129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12366896296508365886837677 4637586111190637207564129)
                    ·
                      refine ⟨3478189583392977905673097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637586111190637207564129 3478189583392977905673097)
                      ·
                        rfl

theorem cell23_6773750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_6773750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773750 prefixEnd_6773750 := by exact prefixLift 6773750
  have htrace : WordTrace (prefixWord ++ tailWord_6773750) baseStart_6773750 baseEnd_6773750 := by
    simpa [prefixWord, tailWord_6773750, baseEnd_6773750] using wordTrace_append hprefix tailTrace_6773750
  have hstable : (prefixWord ++ tailWord_6773750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773750).length < 2 ^ (prefixWord ++ tailWord_6773750).sum := by decide
  have hdescent : baseEnd_6773750 < baseStart_6773750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773793 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6773793 : Nat := 118140960795 + 6773793 * 2 ^ 59
def prefixEnd_6773793 : Nat := 4983230072969 + 3 ^ 40 * 6773793 * 2
def baseEnd_6773793 : Nat := 3478211663061121237435399

theorem tailTrace_6773793 : CollatzResearch.WordTrace tailWord_6773793 prefixEnd_6773793 3478211663061121237435399 := by
  unfold tailWord_6773793
  simp only [CollatzResearch.WordTrace]
  refine ⟨247060527548712307586246033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164707018365808205057497355 247060527548712307586246033)
  ·
    refine ⟨185295395661534230689684525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247060527548712307586246033 185295395661534230689684525)
    ·
      refine ⟨69485773373075336508631697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185295395661534230689684525 69485773373075336508631697)
      ·
        refine ⟨52114330029806502381473773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69485773373075336508631697 52114330029806502381473773)
        ·
          refine ⟨19542873761177438393052665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52114330029806502381473773 19542873761177438393052665)
          ·
            refine ⟨14657155320883078794789499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19542873761177438393052665 14657155320883078794789499)
            ·
              refine ⟨21985732981324618192184249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14657155320883078794789499 21985732981324618192184249)
              ·
                refine ⟨16489299735993463644138187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21985732981324618192184249 16489299735993463644138187)
                ·
                  refine ⟨24733949603990195466207281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16489299735993463644138187 24733949603990195466207281)
                  ·
                    refine ⟨18550462202992646599655461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24733949603990195466207281 18550462202992646599655461)
                    ·
                      refine ⟨3478211663061121237435399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18550462202992646599655461 3478211663061121237435399)
                      ·
                        rfl

theorem cell23_6773793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6773793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773793 prefixEnd_6773793 := by exact prefixLift 6773793
  have htrace : WordTrace (prefixWord ++ tailWord_6773793) baseStart_6773793 baseEnd_6773793 := by
    simpa [prefixWord, tailWord_6773793, baseEnd_6773793] using wordTrace_append hprefix tailTrace_6773793
  have hstable : (prefixWord ++ tailWord_6773793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773793).length < 2 ^ (prefixWord ++ tailWord_6773793).sum := by decide
  have hdescent : baseEnd_6773793 < baseStart_6773793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773797 : List Nat := [1, 3, 1, 2, 2, 2, 2, 5, 1, 2, 2]
def baseStart_6773797 : Nat := 118140960795 + 6773797 * 2 ^ 59
def prefixEnd_6773797 : Nat := 4983230072969 + 3 ^ 40 * 6773797 * 2
def baseEnd_6773797 : Nat := 3478213716983739221785381

theorem tailTrace_6773797 : CollatzResearch.WordTrace tailWord_6773797 prefixEnd_6773797 3478213716983739221785381 := by
  unfold tailWord_6773797
  simp only [CollatzResearch.WordTrace]
  refine ⟨247060673440697816269391645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164707115627131877512927763 247060673440697816269391645)
  ·
    refine ⟨92647752540261681101021867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247060673440697816269391645 92647752540261681101021867)
    ·
      refine ⟨138971628810392521651532801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92647752540261681101021867 138971628810392521651532801)
      ·
        refine ⟨104228721607794391238649601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138971628810392521651532801 104228721607794391238649601)
        ·
          refine ⟨78171541205845793428987201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104228721607794391238649601 78171541205845793428987201)
          ·
            refine ⟨58628655904384345071740401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78171541205845793428987201 58628655904384345071740401)
            ·
              refine ⟨43971491928288258803805301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58628655904384345071740401 43971491928288258803805301)
              ·
                refine ⟨4122327368277024262856747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43971491928288258803805301 4122327368277024262856747)
                ·
                  refine ⟨6183491052415536394285121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122327368277024262856747 6183491052415536394285121)
                  ·
                    refine ⟨4637618289311652295713841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6183491052415536394285121 4637618289311652295713841)
                    ·
                      refine ⟨3478213716983739221785381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637618289311652295713841 3478213716983739221785381)
                      ·
                        rfl

theorem cell23_6773797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_6773797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773797 prefixEnd_6773797 := by exact prefixLift 6773797
  have htrace : WordTrace (prefixWord ++ tailWord_6773797) baseStart_6773797 baseEnd_6773797 := by
    simpa [prefixWord, tailWord_6773797, baseEnd_6773797] using wordTrace_append hprefix tailTrace_6773797
  have hstable : (prefixWord ++ tailWord_6773797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773797).length < 2 ^ (prefixWord ++ tailWord_6773797).sum := by decide
  have hdescent : baseEnd_6773797 < baseStart_6773797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773816 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 2, 7]
def baseStart_6773816 : Nat := 118140960795 + 6773816 * 2 ^ 59
def prefixEnd_6773816 : Nat := 4983230072969 + 3 ^ 40 * 6773816 * 2
def baseEnd_6773816 : Nat := 1159407824372058215815931

theorem tailTrace_6773816 : CollatzResearch.WordTrace tailWord_6773816 prefixEnd_6773816 1159407824372058215815931 := by
  unfold tailWord_6773816
  simp only [CollatzResearch.WordTrace]
  refine ⟨123530683213814491257166651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164707577618419321676222201 123530683213814491257166651)
  ·
    refine ⟨185296024820721736885749977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123530683213814491257166651 185296024820721736885749977)
    ·
      refine ⟨138972018615541302664312483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185296024820721736885749977 138972018615541302664312483)
      ·
        refine ⟨208458027923311953996468725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138972018615541302664312483 208458027923311953996468725)
        ·
          refine ⟨19542940117810495687168943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208458027923311953996468725 19542940117810495687168943)
          ·
            refine ⟨29314410176715743530753415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19542940117810495687168943 29314410176715743530753415)
            ·
              refine ⟨43971615265073615296130123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29314410176715743530753415 43971615265073615296130123)
              ·
                refine ⟨65957422897610422944195185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43971615265073615296130123 65957422897610422944195185)
                ·
                  refine ⟨49468067173207817208146389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65957422897610422944195185 49468067173207817208146389)
                  ·
                    refine ⟨1159407824372058215815931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49468067173207817208146389 1159407824372058215815931)
                    ·
                      rfl

theorem cell23_6773816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_6773816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773816 prefixEnd_6773816 := by exact prefixLift 6773816
  have htrace : WordTrace (prefixWord ++ tailWord_6773816) baseStart_6773816 baseEnd_6773816 := by
    simpa [prefixWord, tailWord_6773816, baseEnd_6773816] using wordTrace_append hprefix tailTrace_6773816
  have hstable : (prefixWord ++ tailWord_6773816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773816).length < 2 ^ (prefixWord ++ tailWord_6773816).sum := by decide
  have hdescent : baseEnd_6773816 < baseStart_6773816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773836 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_6773836 : Nat := 118140960795 + 6773836 * 2 ^ 59
def prefixEnd_6773836 : Nat := 4983230072969 + 3 ^ 40 * 6773836 * 2
def baseEnd_6773836 : Nat := 3478233742729264569197701

theorem tailTrace_6773836 : CollatzResearch.WordTrace tailWord_6773836 prefixEnd_6773836 3478233742729264569197701 := by
  unfold tailWord_6773836
  simp only [CollatzResearch.WordTrace]
  refine ⟨123531047943778262965030681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164708063925037683953374241 123531047943778262965030681)
  ·
    refine ⟨92648285957833697223773011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123531047943778262965030681 92648285957833697223773011)
    ·
      refine ⟨138972428936750545835659517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92648285957833697223773011 138972428936750545835659517)
      ·
        refine ⟨52114660851281454688372319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138972428936750545835659517 52114660851281454688372319)
        ·
          refine ⟨78171991276922182032558479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52114660851281454688372319 78171991276922182032558479)
          ·
            refine ⟨117257986915383273048837719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78171991276922182032558479 117257986915383273048837719)
            ·
              refine ⟨175886980373074909573256579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117257986915383273048837719 175886980373074909573256579)
              ·
                refine ⟨263830470559612364359884869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175886980373074909573256579 263830470559612364359884869)
                ·
                  refine ⟨49468213229927318317478413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263830470559612364359884869 49468213229927318317478413)
                  ·
                    refine ⟨18550579961222744369054405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49468213229927318317478413 18550579961222744369054405)
                    ·
                      refine ⟨3478233742729264569197701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18550579961222744369054405 3478233742729264569197701)
                      ·
                        rfl

theorem cell23_6773836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_6773836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773836 prefixEnd_6773836 := by exact prefixLift 6773836
  have htrace : WordTrace (prefixWord ++ tailWord_6773836) baseStart_6773836 baseEnd_6773836 := by
    simpa [prefixWord, tailWord_6773836, baseEnd_6773836] using wordTrace_append hprefix tailTrace_6773836
  have hstable : (prefixWord ++ tailWord_6773836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773836).length < 2 ^ (prefixWord ++ tailWord_6773836).sum := by decide
  have hdescent : baseEnd_6773836 < baseStart_6773836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773856 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_6773856 : Nat := 118140960795 + 6773856 * 2 ^ 59
def prefixEnd_6773856 : Nat := 4983230072969 + 3 ^ 40 * 6773856 * 2
def baseEnd_6773856 : Nat := 3478244012342354490947609

theorem tailTrace_6773856 : CollatzResearch.WordTrace tailWord_6773856 prefixEnd_6773856 3478244012342354490947609 := by
  unfold tailWord_6773856
  simp only [CollatzResearch.WordTrace]
  refine ⟨123531412673742034672894711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164708550231656046230526281 123531412673742034672894711)
  ·
    refine ⟨185297119010613052009342067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123531412673742034672894711 185297119010613052009342067)
    ·
      refine ⟨277945678515919578014013101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185297119010613052009342067 277945678515919578014013101)
      ·
        refine ⟨104229629443469841755254913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277945678515919578014013101 104229629443469841755254913)
        ·
          refine ⟨78172222082602381316441185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104229629443469841755254913 78172222082602381316441185)
          ·
            refine ⟨58629166561951785987330889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78172222082602381316441185 58629166561951785987330889)
            ·
              refine ⟨43971874921463839490498167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58629166561951785987330889 43971874921463839490498167)
              ·
                refine ⟨65957812382195759235747251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43971874921463839490498167 65957812382195759235747251)
                ·
                  refine ⟨98936718573293638853620877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65957812382195759235747251 98936718573293638853620877)
                  ·
                    refine ⟨37101269464985114570107829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98936718573293638853620877 37101269464985114570107829)
                    ·
                      refine ⟨3478244012342354490947609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37101269464985114570107829 3478244012342354490947609)
                      ·
                        rfl

theorem cell23_6773856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_6773856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773856 prefixEnd_6773856 := by exact prefixLift 6773856
  have htrace : WordTrace (prefixWord ++ tailWord_6773856) baseStart_6773856 baseEnd_6773856 := by
    simpa [prefixWord, tailWord_6773856, baseEnd_6773856] using wordTrace_append hprefix tailTrace_6773856
  have hstable : (prefixWord ++ tailWord_6773856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773856).length < 2 ^ (prefixWord ++ tailWord_6773856).sum := by decide
  have hdescent : baseEnd_6773856 < baseStart_6773856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773857 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 1, 3, 2]
def baseStart_6773857 : Nat := 118140960795 + 6773857 * 2 ^ 59
def prefixEnd_6773857 : Nat := 4983230072969 + 3 ^ 40 * 6773857 * 2
def baseEnd_6773857 : Nat := 3478244525823008987035105

theorem tailTrace_6773857 : CollatzResearch.WordTrace tailWord_6773857 prefixEnd_6773857 3478244525823008987035105 := by
  unfold tailWord_6773857
  simp only [CollatzResearch.WordTrace]
  refine ⟨247062861820480446516575825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164708574546986964344383883 247062861820480446516575825)
  ·
    refine ⟨185297146365360334887431869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247062861820480446516575825 185297146365360334887431869)
    ·
      refine ⟨69486429887010125582786951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185297146365360334887431869 69486429887010125582786951)
      ·
        refine ⟨104229644830515188374180427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69486429887010125582786951 104229644830515188374180427)
        ·
          refine ⟨156344467245772782561270641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104229644830515188374180427 156344467245772782561270641)
          ·
            refine ⟨117258350434329586920952981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156344467245772782561270641 117258350434329586920952981)
            ·
              refine ⟨5496485176609199386919671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117258350434329586920952981 5496485176609199386919671)
              ·
                refine ⟨8244727764913799080379507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5496485176609199386919671 8244727764913799080379507)
                ·
                  refine ⟨12367091647370698620569261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8244727764913799080379507 12367091647370698620569261)
                  ·
                    refine ⟨4637659367764011982713473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12367091647370698620569261 4637659367764011982713473)
                    ·
                      refine ⟨3478244525823008987035105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637659367764011982713473 3478244525823008987035105)
                      ·
                        rfl

theorem cell23_6773857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_6773857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773857 prefixEnd_6773857 := by exact prefixLift 6773857
  have htrace : WordTrace (prefixWord ++ tailWord_6773857) baseStart_6773857 baseEnd_6773857 := by
    simpa [prefixWord, tailWord_6773857, baseEnd_6773857] using wordTrace_append hprefix tailTrace_6773857
  have hstable : (prefixWord ++ tailWord_6773857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773857).length < 2 ^ (prefixWord ++ tailWord_6773857).sum := by decide
  have hdescent : baseEnd_6773857 < baseStart_6773857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773913 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 3, 7, 2]
def baseStart_6773913 : Nat := 118140960795 + 6773913 * 2 ^ 59
def prefixEnd_6773913 : Nat := 4983230072969 + 3 ^ 40 * 6773913 * 2
def baseEnd_6773913 : Nat := 3478273280739660767934847

theorem tailTrace_6773913 : CollatzResearch.WordTrace tailWord_6773913 prefixEnd_6773913 3478273280739660767934847 := by
  unfold tailWord_6773913
  simp only [CollatzResearch.WordTrace]
  refine ⟨247064904308277568080614393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164709936205518378720409595 247064904308277568080614393)
  ·
    refine ⟨185298678231208176060460795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247064904308277568080614393 185298678231208176060460795)
    ·
      refine ⟨277948017346812264090691193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185298678231208176060460795 277948017346812264090691193)
      ·
        refine ⟨208461013010109198068018395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277948017346812264090691193 208461013010109198068018395)
        ·
          refine ⟨312691519515163797102027593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208461013010109198068018395 312691519515163797102027593)
          ·
            refine ⟨234518639636372847826520695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312691519515163797102027593 234518639636372847826520695)
            ·
              refine ⟨351777959454559271739781043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234518639636372847826520695 351777959454559271739781043)
              ·
                refine ⟨527666939181838907609671565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351777959454559271739781043 527666939181838907609671565)
                ·
                  refine ⟨197875102193189590353626837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527666939181838907609671565 197875102193189590353626837)
                  ·
                    refine ⟨4637697707652881023913129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 197875102193189590353626837 4637697707652881023913129)
                    ·
                      refine ⟨3478273280739660767934847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637697707652881023913129 3478273280739660767934847)
                      ·
                        rfl

theorem cell23_6773913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_6773913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773913 prefixEnd_6773913 := by exact prefixLift 6773913
  have htrace : WordTrace (prefixWord ++ tailWord_6773913) baseStart_6773913 baseEnd_6773913 := by
    simpa [prefixWord, tailWord_6773913, baseEnd_6773913] using wordTrace_append hprefix tailTrace_6773913
  have hstable : (prefixWord ++ tailWord_6773913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773913).length < 2 ^ (prefixWord ++ tailWord_6773913).sum := by decide
  have hdescent : baseEnd_6773913 < baseStart_6773913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773943 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_6773943 : Nat := 118140960795 + 6773943 * 2 ^ 59
def prefixEnd_6773943 : Nat := 4983230072969 + 3 ^ 40 * 6773943 * 2
def baseEnd_6773943 : Nat := 3478288685159295650559709

theorem tailTrace_6773943 : CollatzResearch.WordTrace tailWord_6773943 prefixEnd_6773943 3478288685159295650559709 := by
  unfold tailWord_6773943
  simp only [CollatzResearch.WordTrace]
  refine ⟨247065998498168883204206483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164710665665445922136137655 247065998498168883204206483)
  ·
    refine ⟨370598997747253324806309725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247065998498168883204206483 370598997747253324806309725)
    ·
      refine ⟨138974624155219996802366147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370598997747253324806309725 138974624155219996802366147)
      ·
        refine ⟨208461936232829995203549221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138974624155219996802366147 208461936232829995203549221)
        ·
          refine ⟨39086613043655624100665479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208461936232829995203549221 39086613043655624100665479)
          ·
            refine ⟨58629919565483436150998219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39086613043655624100665479 58629919565483436150998219)
            ·
              refine ⟨87944879348225154226497329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58629919565483436150998219 87944879348225154226497329)
              ·
                refine ⟨65958659511168865669872997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87944879348225154226497329 65958659511168865669872997)
                ·
                  refine ⟨12367248658344162313101187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65958659511168865669872997 12367248658344162313101187)
                  ·
                    refine ⟨18550872987516243469651781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12367248658344162313101187 18550872987516243469651781)
                    ·
                      refine ⟨3478288685159295650559709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18550872987516243469651781 3478288685159295650559709)
                      ·
                        rfl

theorem cell23_6773943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_6773943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773943 prefixEnd_6773943 := by exact prefixLift 6773943
  have htrace : WordTrace (prefixWord ++ tailWord_6773943) baseStart_6773943 baseEnd_6773943 := by
    simpa [prefixWord, tailWord_6773943, baseEnd_6773943] using wordTrace_append hprefix tailTrace_6773943
  have hstable : (prefixWord ++ tailWord_6773943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773943).length < 2 ^ (prefixWord ++ tailWord_6773943).sum := by decide
  have hdescent : baseEnd_6773943 < baseStart_6773943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6773983 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 6]
def baseStart_6773983 : Nat := 118140960795 + 6773983 * 2 ^ 59
def prefixEnd_6773983 : Nat := 4983230072969 + 3 ^ 40 * 6773983 * 2
def baseEnd_6773983 : Nat := 386478802709497277117725

theorem tailTrace_6773983 : CollatzResearch.WordTrace tailWord_6773983 prefixEnd_6773983 386478802709497277117725 := by
  unfold tailWord_6773983
  simp only [CollatzResearch.WordTrace]
  refine ⟨247067457418023970035662603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164711638278682646690441735 247067457418023970035662603)
  ·
    refine ⟨370601186127035955053493905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247067457418023970035662603 370601186127035955053493905)
    ·
      refine ⟨277950889595276966290120429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370601186127035955053493905 277950889595276966290120429)
      ·
        refine ⟨104231583598228862358795161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277950889595276966290120429 104231583598228862358795161)
        ·
          refine ⟨78173687698671646769096371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104231583598228862358795161 78173687698671646769096371)
          ·
            refine ⟨117260531548007470153644557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78173687698671646769096371 117260531548007470153644557)
            ·
              refine ⟨43972699330502801307616709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117260531548007470153644557 43972699330502801307616709)
              ·
                refine ⟨8244881124469275245178133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43972699330502801307616709 8244881124469275245178133)
                ·
                  refine ⟨386478802709497277117725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8244881124469275245178133 386478802709497277117725)
                  ·
                    rfl

theorem cell23_6773983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 6].length) (baseStart_6773983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6773983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6773983 prefixEnd_6773983 := by exact prefixLift 6773983
  have htrace : WordTrace (prefixWord ++ tailWord_6773983) baseStart_6773983 baseEnd_6773983 := by
    simpa [prefixWord, tailWord_6773983, baseEnd_6773983] using wordTrace_append hprefix tailTrace_6773983
  have hstable : (prefixWord ++ tailWord_6773983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6773983).length < 2 ^ (prefixWord ++ tailWord_6773983).sum := by decide
  have hdescent : baseEnd_6773983 < baseStart_6773983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6773983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774014 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_6774014 : Nat := 118140960795 + 6774014 * 2 ^ 59
def prefixEnd_6774014 : Nat := 4983230072969 + 3 ^ 40 * 6774014 * 2
def baseEnd_6774014 : Nat := 3478325142285764872771883

theorem tailTrace_6774014 : CollatzResearch.WordTrace tailWord_6774014 prefixEnd_6774014 3478325142285764872771883 := by
  unfold tailWord_6774014
  simp only [CollatzResearch.WordTrace]
  refine ⟨30883573510113957791255137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164712392053941108220027397 30883573510113957791255137)
  ·
    refine ⟨23162680132585468343441353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30883573510113957791255137 23162680132585468343441353)
    ·
      refine ⟨17372010099439101257581015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23162680132585468343441353 17372010099439101257581015)
      ·
        refine ⟨26058015149158651886371523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17372010099439101257581015 26058015149158651886371523)
        ·
          refine ⟨39087022723737977829557285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26058015149158651886371523 39087022723737977829557285)
          ·
            refine ⟨7328816760700870843041991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39087022723737977829557285 7328816760700870843041991)
            ·
              refine ⟨10993225141051306264562987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7328816760700870843041991 10993225141051306264562987)
              ·
                refine ⟨16489837711576959396844481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10993225141051306264562987 16489837711576959396844481)
                ·
                  refine ⟨12367378283682719547633361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16489837711576959396844481 12367378283682719547633361)
                  ·
                    refine ⟨9275533712762039660725021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12367378283682719547633361 9275533712762039660725021)
                    ·
                      refine ⟨3478325142285764872771883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9275533712762039660725021 3478325142285764872771883)
                      ·
                        rfl

theorem cell23_6774014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_6774014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774014 prefixEnd_6774014 := by exact prefixLift 6774014
  have htrace : WordTrace (prefixWord ++ tailWord_6774014) baseStart_6774014 baseEnd_6774014 := by
    simpa [prefixWord, tailWord_6774014, baseEnd_6774014] using wordTrace_append hprefix tailTrace_6774014
  have hstable : (prefixWord ++ tailWord_6774014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774014).length < 2 ^ (prefixWord ++ tailWord_6774014).sum := by decide
  have hdescent : baseEnd_6774014 < baseStart_6774014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774044 : List Nat := [2, 2, 3, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_6774044 : Nat := 118140960795 + 6774044 * 2 ^ 59
def prefixEnd_6774044 : Nat := 4983230072969 + 3 ^ 40 * 6774044 * 2
def baseEnd_6774044 : Nat := 3478340546705399755396745

theorem tailTrace_6774044 : CollatzResearch.WordTrace tailWord_6774044 prefixEnd_6774044 3478340546705399755396745 := by
  unfold tailWord_6774044
  simp only [CollatzResearch.WordTrace]
  refine ⟨123534841135401488726816593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164713121513868651635755457 123534841135401488726816593)
  ·
    refine ⟨92651130851551116545112445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123534841135401488726816593 92651130851551116545112445)
    ·
      refine ⟨34744174069331668704417167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92651130851551116545112445 34744174069331668704417167)
      ·
        refine ⟨52116261103997503056625751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34744174069331668704417167 52116261103997503056625751)
        ·
          refine ⟨78174391655996254584938627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52116261103997503056625751 78174391655996254584938627)
          ·
            refine ⟨117261587483994381877407941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78174391655996254584938627 117261587483994381877407941)
            ·
              refine ⟨21986547653248946602013989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117261587483994381877407941 21986547653248946602013989)
              ·
                refine ⟨4122477684984177487877623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21986547653248946602013989 4122477684984177487877623)
                ·
                  refine ⟨6183716527476266231816435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122477684984177487877623 6183716527476266231816435)
                  ·
                    refine ⟨9275574791214399347724653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6183716527476266231816435 9275574791214399347724653)
                    ·
                      refine ⟨3478340546705399755396745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9275574791214399347724653 3478340546705399755396745)
                      ·
                        rfl

theorem cell23_6774044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_6774044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774044 prefixEnd_6774044 := by exact prefixLift 6774044
  have htrace : WordTrace (prefixWord ++ tailWord_6774044) baseStart_6774044 baseEnd_6774044 := by
    simpa [prefixWord, tailWord_6774044, baseEnd_6774044] using wordTrace_append hprefix tailTrace_6774044
  have hstable : (prefixWord ++ tailWord_6774044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774044).length < 2 ^ (prefixWord ++ tailWord_6774044).sum := by decide
  have hdescent : baseEnd_6774044 < baseStart_6774044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774067 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 4]
def baseStart_6774067 : Nat := 118140960795 + 6774067 * 2 ^ 59
def prefixEnd_6774067 : Nat := 4983230072969 + 3 ^ 40 * 6774067 * 2
def baseEnd_6774067 : Nat := 3478352356760453165409139

theorem tailTrace_6774067 : CollatzResearch.WordTrace tailWord_6774067 prefixEnd_6774067 3478352356760453165409139 := by
  unfold tailWord_6774067
  simp only [CollatzResearch.WordTrace]
  refine ⟨247070521149719652381720455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164713680766479768254480303 247070521149719652381720455)
  ·
    refine ⟨370605781724579478572580683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247070521149719652381720455 370605781724579478572580683)
    ·
      refine ⟨555908672586869217858871025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370605781724579478572580683 555908672586869217858871025)
      ·
        refine ⟨416931504440151913394153269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555908672586869217858871025 416931504440151913394153269)
        ·
          refine ⟨39087328541264241880701869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 416931504440151913394153269 39087328541264241880701869)
          ·
            refine ⟨14657748202974090705263201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39087328541264241880701869 14657748202974090705263201)
            ·
              refine ⟨10993311152230568028947401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14657748202974090705263201 10993311152230568028947401)
              ·
                refine ⟨8244983364172926021710551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10993311152230568028947401 8244983364172926021710551)
                ·
                  refine ⟨12367475046259389032565827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8244983364172926021710551 12367475046259389032565827)
                  ·
                    refine ⟨18551212569389083548848741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12367475046259389032565827 18551212569389083548848741)
                    ·
                      refine ⟨3478352356760453165409139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18551212569389083548848741 3478352356760453165409139)
                      ·
                        rfl

theorem cell23_6774067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 4].length) (baseStart_6774067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774067 prefixEnd_6774067 := by exact prefixLift 6774067
  have htrace : WordTrace (prefixWord ++ tailWord_6774067) baseStart_6774067 baseEnd_6774067 := by
    simpa [prefixWord, tailWord_6774067, baseEnd_6774067] using wordTrace_append hprefix tailTrace_6774067
  have hstable : (prefixWord ++ tailWord_6774067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774067).length < 2 ^ (prefixWord ++ tailWord_6774067).sum := by decide
  have hdescent : baseEnd_6774067 < baseStart_6774067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774084 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_6774084 : Nat := 118140960795 + 6774084 * 2 ^ 59
def prefixEnd_6774084 : Nat := 4983230072969 + 3 ^ 40 * 6774084 * 2
def baseEnd_6774084 : Nat := 3478361085931579598896561

theorem tailTrace_6774084 : CollatzResearch.WordTrace tailWord_6774084 prefixEnd_6774084 3478361085931579598896561 := by
  unfold tailWord_6774084
  simp only [CollatzResearch.WordTrace]
  refine ⟨123535570595329032142544653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164714094127105376190059537 123535570595329032142544653)
  ·
    refine ⟨46325838973248387053454245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123535570595329032142544653 46325838973248387053454245)
    ·
      refine ⟨8686094807484072572522671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46325838973248387053454245 8686094807484072572522671)
      ·
        refine ⟨13029142211226108858784007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8686094807484072572522671 13029142211226108858784007)
        ·
          refine ⟨19543713316839163288176011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13029142211226108858784007 19543713316839163288176011)
          ·
            refine ⟨29315569975258744932264017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19543713316839163288176011 29315569975258744932264017)
            ·
              refine ⟨21986677481444058699198013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29315569975258744932264017 21986677481444058699198013)
              ·
                refine ⟨8245004055541522012199255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21986677481444058699198013 8245004055541522012199255)
                ·
                  refine ⟨12367506083312283018298883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8245004055541522012199255 12367506083312283018298883)
                  ·
                    refine ⟨18551259124968424527448325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12367506083312283018298883 18551259124968424527448325)
                    ·
                      refine ⟨3478361085931579598896561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18551259124968424527448325 3478361085931579598896561)
                      ·
                        rfl

theorem cell23_6774084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_6774084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774084 prefixEnd_6774084 := by exact prefixLift 6774084
  have htrace : WordTrace (prefixWord ++ tailWord_6774084) baseStart_6774084 baseEnd_6774084 := by
    simpa [prefixWord, tailWord_6774084, baseEnd_6774084] using wordTrace_append hprefix tailTrace_6774084
  have hstable : (prefixWord ++ tailWord_6774084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774084).length < 2 ^ (prefixWord ++ tailWord_6774084).sum := by decide
  have hdescent : baseEnd_6774084 < baseStart_6774084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774087 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_6774087 : Nat := 118140960795 + 6774087 * 2 ^ 59
def prefixEnd_6774087 : Nat := 4983230072969 + 3 ^ 40 * 6774087 * 2
def baseEnd_6774087 : Nat := 3478362626373543087159047

theorem tailTrace_6774087 : CollatzResearch.WordTrace tailWord_6774087 prefixEnd_6774087 3478362626373543087159047 := by
  unfold tailWord_6774087
  simp only [CollatzResearch.WordTrace]
  refine ⟨247071250609647195797448515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164714167073098130531632343 247071250609647195797448515)
  ·
    refine ⟨370606875914470793696172773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247071250609647195797448515 370606875914470793696172773)
    ·
      refine ⟨69488789233963273818032395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370606875914470793696172773 69488789233963273818032395)
      ·
        refine ⟨104233183850944910727048593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69488789233963273818032395 104233183850944910727048593)
        ·
          refine ⟨78174887888208683045286445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104233183850944910727048593 78174887888208683045286445)
          ·
            refine ⟨29315582958078256141982417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78174887888208683045286445 29315582958078256141982417)
            ·
              refine ⟨21986687218558692106486813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29315582958078256141982417 21986687218558692106486813)
              ·
                refine ⟨8245007706959509539932555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21986687218558692106486813 8245007706959509539932555)
                ·
                  refine ⟨12367511560439264309898833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8245007706959509539932555 12367511560439264309898833)
                  ·
                    refine ⟨9275633670329448232424125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12367511560439264309898833 9275633670329448232424125)
                    ·
                      refine ⟨3478362626373543087159047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9275633670329448232424125 3478362626373543087159047)
                      ·
                        rfl

theorem cell23_6774087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_6774087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774087 prefixEnd_6774087 := by exact prefixLift 6774087
  have htrace : WordTrace (prefixWord ++ tailWord_6774087) baseStart_6774087 baseEnd_6774087 := by
    simpa [prefixWord, tailWord_6774087, baseEnd_6774087] using wordTrace_append hprefix tailTrace_6774087
  have hstable : (prefixWord ++ tailWord_6774087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774087).length < 2 ^ (prefixWord ++ tailWord_6774087).sum := by decide
  have hdescent : baseEnd_6774087 < baseStart_6774087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774101 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 3, 2, 2]
def baseStart_6774101 : Nat := 118140960795 + 6774101 * 2 ^ 59
def prefixEnd_6774101 : Nat := 4983230072969 + 3 ^ 40 * 6774101 * 2
def baseEnd_6774101 : Nat := 3478369815102706032383983

theorem tailTrace_6774101 : CollatzResearch.WordTrace tailWord_6774101 prefixEnd_6774101 3478369815102706032383983 := by
  unfold tailWord_6774101
  simp only [CollatzResearch.WordTrace]
  refine ⟨247071761231596476188458157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164714507487730984125638771 247071761231596476188458157)
  ·
    refine ⟨92651910461848678570671809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247071761231596476188458157 92651910461848678570671809)
    ·
      refine ⟨69488932846386508928003857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92651910461848678570671809 69488932846386508928003857)
      ·
        refine ⟨52116699634789881696002893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69488932846386508928003857 52116699634789881696002893)
        ·
          refine ⟨19543762363046205636001085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52116699634789881696002893 19543762363046205636001085)
          ·
            refine ⟨7328910886142327113500407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19543762363046205636001085 7328910886142327113500407)
            ·
              refine ⟨10993366329213490670250611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7328910886142327113500407 10993366329213490670250611)
              ·
                refine ⟨16490049493820236005375917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10993366329213490670250611 16490049493820236005375917)
                ·
                  refine ⟨6183768560182588502015969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16490049493820236005375917 6183768560182588502015969)
                  ·
                    refine ⟨4637826420136941376511977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6183768560182588502015969 4637826420136941376511977)
                    ·
                      refine ⟨3478369815102706032383983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637826420136941376511977 3478369815102706032383983)
                      ·
                        rfl

theorem cell23_6774101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_6774101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774101 prefixEnd_6774101 := by exact prefixLift 6774101
  have htrace : WordTrace (prefixWord ++ tailWord_6774101) baseStart_6774101 baseEnd_6774101 := by
    simpa [prefixWord, tailWord_6774101, baseEnd_6774101] using wordTrace_append hprefix tailTrace_6774101
  have hstable : (prefixWord ++ tailWord_6774101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774101).length < 2 ^ (prefixWord ++ tailWord_6774101).sum := by decide
  have hdescent : baseEnd_6774101 < baseStart_6774101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774127 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 3, 3, 2]
def baseStart_6774127 : Nat := 118140960795 + 6774127 * 2 ^ 59
def prefixEnd_6774127 : Nat := 4983230072969 + 3 ^ 40 * 6774127 * 2
def baseEnd_6774127 : Nat := 3478383165599722930658863

theorem tailTrace_6774127 : CollatzResearch.WordTrace tailWord_6774127 prefixEnd_6774127 3478383165599722930658863 := by
  unfold tailWord_6774127
  simp only [CollatzResearch.WordTrace]
  refine ⟨247072709529502282628904635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164715139686334855085936423 247072709529502282628904635)
  ·
    refine ⟨370609064294253423943356953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247072709529502282628904635 370609064294253423943356953)
    ·
      refine ⟨277956798220690067957517715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370609064294253423943356953 277956798220690067957517715)
      ·
        refine ⟨416935197331035101936276573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277956798220690067957517715 416935197331035101936276573)
        ·
          refine ⟨156350698999138163226103715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416935197331035101936276573 156350698999138163226103715)
          ·
            refine ⟨234526048498707244839155573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156350698999138163226103715 234526048498707244839155573)
            ·
              refine ⟨21986817046753804203670835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234526048498707244839155573 21986817046753804203670835)
              ·
                refine ⟨32980225570130706305506253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21986817046753804203670835 32980225570130706305506253)
                ·
                  refine ⟨12367584588799014864564845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32980225570130706305506253 12367584588799014864564845)
                  ·
                    refine ⟨4637844220799630574211817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12367584588799014864564845 4637844220799630574211817)
                    ·
                      refine ⟨3478383165599722930658863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4637844220799630574211817 3478383165599722930658863)
                      ·
                        rfl

theorem cell23_6774127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 3, 2].length) (baseStart_6774127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774127 prefixEnd_6774127 := by exact prefixLift 6774127
  have htrace : WordTrace (prefixWord ++ tailWord_6774127) baseStart_6774127 baseEnd_6774127 := by
    simpa [prefixWord, tailWord_6774127, baseEnd_6774127] using wordTrace_append hprefix tailTrace_6774127
  have hstable : (prefixWord ++ tailWord_6774127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774127).length < 2 ^ (prefixWord ++ tailWord_6774127).sum := by decide
  have hdescent : baseEnd_6774127 < baseStart_6774127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774163 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 13]
def baseStart_6774163 : Nat := 118140960795 + 6774163 * 2 ^ 59
def prefixEnd_6774163 : Nat := 4983230072969 + 3 ^ 40 * 6774163 * 2
def baseEnd_6774163 : Nat := 386489072322587198867633

theorem tailTrace_6774163 : CollatzResearch.WordTrace tailWord_6774163 prefixEnd_6774163 386489072322587198867633 := by
  unfold tailWord_6774163
  simp only [CollatzResearch.WordTrace]
  refine ⟨247074022557371860777215143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164716015038247907184810095 247074022557371860777215143)
  ·
    refine ⟨370611033836057791165822715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247074022557371860777215143 370611033836057791165822715)
    ·
      refine ⟨555916550754086686748734073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370611033836057791165822715 555916550754086686748734073)
      ·
        refine ⟨416937413065565015061550555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555916550754086686748734073 416937413065565015061550555)
        ·
          refine ⟨625406119598347522592325833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416937413065565015061550555 625406119598347522592325833)
          ·
            refine ⟨469054589698760641944244375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625406119598347522592325833 469054589698760641944244375)
            ·
              refine ⟨703581884548140962916366563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469054589698760641944244375 703581884548140962916366563)
              ·
                refine ⟨1055372826822211444374549845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703581884548140962916366563 1055372826822211444374549845)
                ·
                  refine ⟨386489072322587198867633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1055372826822211444374549845 386489072322587198867633)
                  ·
                    rfl

theorem cell23_6774163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 13].length) (baseStart_6774163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774163 prefixEnd_6774163 := by exact prefixLift 6774163
  have htrace : WordTrace (prefixWord ++ tailWord_6774163) baseStart_6774163 baseEnd_6774163 := by
    simpa [prefixWord, tailWord_6774163, baseEnd_6774163] using wordTrace_append hprefix tailTrace_6774163
  have hstable : (prefixWord ++ tailWord_6774163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774163).length < 2 ^ (prefixWord ++ tailWord_6774163).sum := by decide
  have hdescent : baseEnd_6774163 < baseStart_6774163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774247 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_6774247 : Nat := 118140960795 + 6774247 * 2 ^ 59
def prefixEnd_6774247 : Nat := 4983230072969 + 3 ^ 40 * 6774247 * 2
def baseEnd_6774247 : Nat := 3478444783278262461158311

theorem tailTrace_6774247 : CollatzResearch.WordTrace tailWord_6774247 prefixEnd_6774247 3478444783278262461158311 := by
  unfold tailWord_6774247
  simp only [CollatzResearch.WordTrace]
  refine ⟨247077086289067543123272995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164718057526045028748848663 247077086289067543123272995)
  ·
    refine ⟨370615629433601314684909493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247077086289067543123272995 370615629433601314684909493)
    ·
      refine ⟨34745215259400123251710265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 370615629433601314684909493 34745215259400123251710265)
      ·
        refine ⟨26058911444550092438782699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34745215259400123251710265 26058911444550092438782699)
        ·
          refine ⟨39088367166825138658174049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26058911444550092438782699 39088367166825138658174049)
          ·
            refine ⟨29316275375118853993630537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39088367166825138658174049 29316275375118853993630537)
            ·
              refine ⟨21987206531339140495222903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29316275375118853993630537 21987206531339140495222903)
              ·
                refine ⟨32980809797008710742834355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21987206531339140495222903 32980809797008710742834355)
                ·
                  refine ⟨49471214695513066114251533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32980809797008710742834355 49471214695513066114251533)
                  ·
                    refine ⟨18551705510817399792844325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49471214695513066114251533 18551705510817399792844325)
                    ·
                      refine ⟨3478444783278262461158311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18551705510817399792844325 3478444783278262461158311)
                      ·
                        rfl

theorem cell23_6774247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_6774247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774247 prefixEnd_6774247 := by exact prefixLift 6774247
  have htrace : WordTrace (prefixWord ++ tailWord_6774247) baseStart_6774247 baseEnd_6774247 := by
    simpa [prefixWord, tailWord_6774247, baseEnd_6774247] using wordTrace_append hprefix tailTrace_6774247
  have hstable : (prefixWord ++ tailWord_6774247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774247).length < 2 ^ (prefixWord ++ tailWord_6774247).sum := by decide
  have hdescent : baseEnd_6774247 < baseStart_6774247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774267 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 3]
def baseStart_6774267 : Nat := 118140960795 + 6774267 * 2 ^ 59
def prefixEnd_6774267 : Nat := 4983230072969 + 3 ^ 40 * 6774267 * 2
def baseEnd_6774267 : Nat := 3478455052891352382908219

theorem tailTrace_6774267 : CollatzResearch.WordTrace tailWord_6774267 prefixEnd_6774267 3478455052891352382908219 := by
  unfold tailWord_6774267
  simp only [CollatzResearch.WordTrace]
  refine ⟨247077815748995086539001055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164718543832663391026000703 247077815748995086539001055)
  ·
    refine ⟨370616723623492629808501583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247077815748995086539001055 370616723623492629808501583)
    ·
      refine ⟨555925085435238944712752375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370616723623492629808501583 555925085435238944712752375)
      ·
        refine ⟨833887628152858417069128563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555925085435238944712752375 833887628152858417069128563)
        ·
          refine ⟨1250831442229287625603692845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833887628152858417069128563 1250831442229287625603692845)
          ·
            refine ⟨469061790835982859601384817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1250831442229287625603692845 469061790835982859601384817)
            ·
              refine ⟨351796343126987144701038613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469061790835982859601384817 351796343126987144701038613)
              ·
                refine ⟨16490453584077522407861185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 351796343126987144701038613 16490453584077522407861185)
                ·
                  refine ⟨12367840188058141805895889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16490453584077522407861185 12367840188058141805895889)
                  ·
                    refine ⟨9275880141043606354421917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12367840188058141805895889 9275880141043606354421917)
                    ·
                      refine ⟨3478455052891352382908219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9275880141043606354421917 3478455052891352382908219)
                      ·
                        rfl

theorem cell23_6774267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 3].length) (baseStart_6774267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774267 prefixEnd_6774267 := by exact prefixLift 6774267
  have htrace : WordTrace (prefixWord ++ tailWord_6774267) baseStart_6774267 baseEnd_6774267 := by
    simpa [prefixWord, tailWord_6774267, baseEnd_6774267] using wordTrace_append hprefix tailTrace_6774267
  have hstable : (prefixWord ++ tailWord_6774267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774267).length < 2 ^ (prefixWord ++ tailWord_6774267).sum := by decide
  have hdescent : baseEnd_6774267 < baseStart_6774267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774347 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 6, 4]
def baseStart_6774347 : Nat := 118140960795 + 6774347 * 2 ^ 59
def prefixEnd_6774347 : Nat := 4983230072969 + 3 ^ 40 * 6774347 * 2
def baseEnd_6774347 : Nat := 1159498710447904023302617

theorem tailTrace_6774347 : CollatzResearch.WordTrace tailWord_6774347 prefixEnd_6774347 1159498710447904023302617 := by
  unfold tailWord_6774347
  simp only [CollatzResearch.WordTrace]
  refine ⟨247080733588705260201913295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164720489059136840134608863 247080733588705260201913295)
  ·
    refine ⟨370621100383057890302869943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247080733588705260201913295 370621100383057890302869943)
    ·
      refine ⟨555931650574586835454304915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370621100383057890302869943 555931650574586835454304915)
      ·
        refine ⟨833897475861880253181457373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555931650574586835454304915 833897475861880253181457373)
        ·
          refine ⟨312711553448205094943046515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 833897475861880253181457373 312711553448205094943046515)
          ·
            refine ⟨469067330172307642414569773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312711553448205094943046515 469067330172307642414569773)
            ·
              refine ⟨175900248814615365905463665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469067330172307642414569773 175900248814615365905463665)
              ·
                refine ⟨131925186610961524429097749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175900248814615365905463665 131925186610961524429097749)
                ·
                  refine ⟨6183993122388821457613957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131925186610961524429097749 6183993122388821457613957)
                  ·
                    refine ⟨1159498710447904023302617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6183993122388821457613957 1159498710447904023302617)
                    ·
                      rfl

theorem cell23_6774347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 4].length) (baseStart_6774347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774347 prefixEnd_6774347 := by exact prefixLift 6774347
  have htrace : WordTrace (prefixWord ++ tailWord_6774347) baseStart_6774347 baseEnd_6774347 := by
    simpa [prefixWord, tailWord_6774347, baseEnd_6774347] using wordTrace_append hprefix tailTrace_6774347
  have hstable : (prefixWord ++ tailWord_6774347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774347).length < 2 ^ (prefixWord ++ tailWord_6774347).sum := by decide
  have hdescent : baseEnd_6774347 < baseStart_6774347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774354 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_6774354 : Nat := 118140960795 + 6774354 * 2 ^ 59
def prefixEnd_6774354 : Nat := 4983230072969 + 3 ^ 40 * 6774354 * 2
def baseEnd_6774354 : Nat := 3478499725708293542520319

theorem tailTrace_6774354 : CollatzResearch.WordTrace tailWord_6774354 prefixEnd_6774354 3478499725708293542520319 := by
  unfold tailWord_6774354
  simp only [CollatzResearch.WordTrace]
  refine ⟨61770247224919975099354529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164720659266453266931612077 61770247224919975099354529)
  ·
    refine ⟨46327685418689981324515897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61770247224919975099354529 46327685418689981324515897)
    ·
      refine ⟨34745764064017485993386923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46327685418689981324515897 34745764064017485993386923)
      ·
        refine ⟨52118646096026228990080385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34745764064017485993386923 52118646096026228990080385)
        ·
          refine ⟨39088984572019671742560289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52118646096026228990080385 39088984572019671742560289)
          ·
            refine ⟨29316738429014753806920217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39088984572019671742560289 29316738429014753806920217)
            ·
              refine ⟨21987553821761065355190163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29316738429014753806920217 21987553821761065355190163)
              ·
                refine ⟨32981330732641598032785245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21987553821761065355190163 32981330732641598032785245)
                ·
                  refine ⟨12367999024740599262294467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32981330732641598032785245 12367999024740599262294467)
                  ·
                    refine ⟨18551998537110898893441701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12367999024740599262294467 18551998537110898893441701)
                    ·
                      refine ⟨3478499725708293542520319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18551998537110898893441701 3478499725708293542520319)
                      ·
                        rfl

theorem cell23_6774354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_6774354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774354 prefixEnd_6774354 := by exact prefixLift 6774354
  have htrace : WordTrace (prefixWord ++ tailWord_6774354) baseStart_6774354 baseEnd_6774354 := by
    simpa [prefixWord, tailWord_6774354, baseEnd_6774354] using wordTrace_append hprefix tailTrace_6774354
  have hstable : (prefixWord ++ tailWord_6774354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774354).length < 2 ^ (prefixWord ++ tailWord_6774354).sum := by decide
  have hdescent : baseEnd_6774354 < baseStart_6774354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774364 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_6774364 : Nat := 118140960795 + 6774364 * 2 ^ 59
def prefixEnd_6774364 : Nat := 4983230072969 + 3 ^ 40 * 6774364 * 2
def baseEnd_6774364 : Nat := 1159501620171612834465091

theorem tailTrace_6774364 : CollatzResearch.WordTrace tailWord_6774364 prefixEnd_6774364 1159501620171612834465091 := by
  unfold tailWord_6774364
  simp only [CollatzResearch.WordTrace]
  refine ⟨123540676814821836052641073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164720902419762448070188097 123540676814821836052641073)
  ·
    refine ⟨92655507611116377039480805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123540676814821836052641073 92655507611116377039480805)
    ·
      refine ⟨17372907677084320694902651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92655507611116377039480805 17372907677084320694902651)
      ·
        refine ⟨26059361515626481042353977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17372907677084320694902651 26059361515626481042353977)
        ·
          refine ⟨19544521136719860781765483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26059361515626481042353977 19544521136719860781765483)
          ·
            refine ⟨29316781705079791172648225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19544521136719860781765483 29316781705079791172648225)
            ·
              refine ⟨21987586278809843379486169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29316781705079791172648225 21987586278809843379486169)
              ·
                refine ⟨16490689709107382534614627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21987586278809843379486169 16490689709107382534614627)
                ·
                  refine ⟨24736034563661073801921941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16490689709107382534614627 24736034563661073801921941)
                  ·
                    refine ⟨1159501620171612834465091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24736034563661073801921941 1159501620171612834465091)
                    ·
                      rfl

theorem cell23_6774364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_6774364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774364 prefixEnd_6774364 := by exact prefixLift 6774364
  have htrace : WordTrace (prefixWord ++ tailWord_6774364) baseStart_6774364 baseEnd_6774364 := by
    simpa [prefixWord, tailWord_6774364, baseEnd_6774364] using wordTrace_append hprefix tailTrace_6774364
  have hstable : (prefixWord ++ tailWord_6774364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774364).length < 2 ^ (prefixWord ++ tailWord_6774364).sum := by decide
  have hdescent : baseEnd_6774364 < baseStart_6774364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774371 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 1, 1, 4]
def baseStart_6774371 : Nat := 118140960795 + 6774371 * 2 ^ 59
def prefixEnd_6774371 : Nat := 4983230072969 + 3 ^ 40 * 6774371 * 2
def baseEnd_6774371 : Nat := 3478508454879419976007741

theorem tailTrace_6774371 : CollatzResearch.WordTrace tailWord_6774371 prefixEnd_6774371 3478508454879419976007741 := by
  unfold tailWord_6774371
  simp only [CollatzResearch.WordTrace]
  refine ⟨247081608940618312300786967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164721072627078874867191311 247081608940618312300786967)
  ·
    refine ⟨370622413410927468451180451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247081608940618312300786967 370622413410927468451180451)
    ·
      refine ⟨555933620116391202676770677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370622413410927468451180451 555933620116391202676770677)
      ·
        refine ⟨52118776885911675250947251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 555933620116391202676770677 52118776885911675250947251)
        ·
          refine ⟨78178165328867512876420877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52118776885911675250947251 78178165328867512876420877)
          ·
            refine ⟨29316811998325317328657829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78178165328867512876420877 29316811998325317328657829)
            ·
              refine ⟨5496902249685996999123343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29316811998325317328657829 5496902249685996999123343)
              ·
                refine ⟨8245353374528995498685015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5496902249685996999123343 8245353374528995498685015)
                ·
                  refine ⟨12368030061793493248027523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8245353374528995498685015 12368030061793493248027523)
                  ·
                    refine ⟨18552045092690239872041285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12368030061793493248027523 18552045092690239872041285)
                    ·
                      refine ⟨3478508454879419976007741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18552045092690239872041285 3478508454879419976007741)
                      ·
                        rfl

theorem cell23_6774371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_6774371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774371 prefixEnd_6774371 := by exact prefixLift 6774371
  have htrace : WordTrace (prefixWord ++ tailWord_6774371) baseStart_6774371 baseEnd_6774371 := by
    simpa [prefixWord, tailWord_6774371, baseEnd_6774371] using wordTrace_append hprefix tailTrace_6774371
  have hstable : (prefixWord ++ tailWord_6774371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774371).length < 2 ^ (prefixWord ++ tailWord_6774371).sum := by decide
  have hdescent : baseEnd_6774371 < baseStart_6774371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774381 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_6774381 : Nat := 118140960795 + 6774381 * 2 ^ 59
def prefixEnd_6774381 : Nat := 4983230072969 + 3 ^ 40 * 6774381 * 2
def baseEnd_6774381 : Nat := 1159504529895321645627565

theorem tailTrace_6774381 : CollatzResearch.WordTrace tailWord_6774381 prefixEnd_6774381 1159504529895321645627565 := by
  unfold tailWord_6774381
  simp only [CollatzResearch.WordTrace]
  refine ⟨247081973670582084008650997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164721315780388056005767331 247081973670582084008650997)
  ·
    refine ⟨23163935031617070375811031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247081973670582084008650997 23163935031617070375811031)
    ·
      refine ⟨34745902547425605563716547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23163935031617070375811031 34745902547425605563716547)
      ·
        refine ⟨52118853821138408345574821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34745902547425605563716547 52118853821138408345574821)
        ·
          refine ⟨9772285091463451564795279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52118853821138408345574821 9772285091463451564795279)
          ·
            refine ⟨14658427637195177347192919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9772285091463451564795279 14658427637195177347192919)
            ·
              refine ⟨21987641455792766020789379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14658427637195177347192919 21987641455792766020789379)
              ·
                refine ⟨32981462183689149031184069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21987641455792766020789379 32981462183689149031184069)
                ·
                  refine ⟨6184024159441715443347013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32981462183689149031184069 6184024159441715443347013)
                  ·
                    refine ⟨1159504529895321645627565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184024159441715443347013 1159504529895321645627565)
                    ·
                      rfl

theorem cell23_6774381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_6774381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774381 prefixEnd_6774381 := by exact prefixLift 6774381
  have htrace : WordTrace (prefixWord ++ tailWord_6774381) baseStart_6774381 baseEnd_6774381 := by
    simpa [prefixWord, tailWord_6774381, baseEnd_6774381] using wordTrace_append hprefix tailTrace_6774381
  have hstable : (prefixWord ++ tailWord_6774381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774381).length < 2 ^ (prefixWord ++ tailWord_6774381).sum := by decide
  have hdescent : baseEnd_6774381 < baseStart_6774381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774401 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_6774401 : Nat := 118140960795 + 6774401 * 2 ^ 59
def prefixEnd_6774401 : Nat := 4983230072969 + 3 ^ 40 * 6774401 * 2
def baseEnd_6774401 : Nat := 3478523859299054858632603

theorem tailTrace_6774401 : CollatzResearch.WordTrace tailWord_6774401 prefixEnd_6774401 3478523859299054858632603 := by
  unfold tailWord_6774401
  simp only [CollatzResearch.WordTrace]
  refine ⟨247082703130509627424379057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164721802087006418282919371 247082703130509627424379057)
  ·
    refine ⟨185312027347882220568284293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247082703130509627424379057 185312027347882220568284293)
    ·
      refine ⟨34746005127727916356553305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185312027347882220568284293 34746005127727916356553305)
      ·
        refine ⟨26059503845795937267414979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34746005127727916356553305 26059503845795937267414979)
        ·
          refine ⟨39089255768693905901122469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26059503845795937267414979 39089255768693905901122469)
          ·
            refine ⟨7329235456630107356460463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39089255768693905901122469 7329235456630107356460463)
            ·
              refine ⟨10993853184945161034690695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7329235456630107356460463 10993853184945161034690695)
              ·
                refine ⟨16490779777417741552036043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10993853184945161034690695 16490779777417741552036043)
                ·
                  refine ⟨24736169666126612328054065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16490779777417741552036043 24736169666126612328054065)
                  ·
                    refine ⟨18552127249594959246040549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24736169666126612328054065 18552127249594959246040549)
                    ·
                      refine ⟨3478523859299054858632603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18552127249594959246040549 3478523859299054858632603)
                      ·
                        rfl

theorem cell23_6774401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_6774401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774401 prefixEnd_6774401 := by exact prefixLift 6774401
  have htrace : WordTrace (prefixWord ++ tailWord_6774401) baseStart_6774401 baseEnd_6774401 := by
    simpa [prefixWord, tailWord_6774401, baseEnd_6774401] using wordTrace_append hprefix tailTrace_6774401
  have hstable : (prefixWord ++ tailWord_6774401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774401).length < 2 ^ (prefixWord ++ tailWord_6774401).sum := by decide
  have hdescent : baseEnd_6774401 < baseStart_6774401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774437 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_6774437 : Nat := 118140960795 + 6774437 * 2 ^ 59
def prefixEnd_6774437 : Nat := 4983230072969 + 3 ^ 40 * 6774437 * 2
def baseEnd_6774437 : Nat := 1159514114867538905927479

theorem tailTrace_6774437 : CollatzResearch.WordTrace tailWord_6774437 prefixEnd_6774437 1159514114867538905927479 := by
  unfold tailWord_6774437
  simp only [CollatzResearch.WordTrace]
  refine ⟨247084016158379205572689565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164722677438919470381793043 247084016158379205572689565)
  ·
    refine ⟨92656506059392202089758587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247084016158379205572689565 92656506059392202089758587)
    ·
      refine ⟨138984759089088303134637881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92656506059392202089758587 138984759089088303134637881)
      ·
        refine ⟨104238569316816227350978411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138984759089088303134637881 104238569316816227350978411)
        ·
          refine ⟨156357853975224341026467617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104238569316816227350978411 156357853975224341026467617)
          ·
            refine ⟨117268390481418255769850713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156357853975224341026467617 117268390481418255769850713)
            ·
              refine ⟨87951292861063691827388035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117268390481418255769850713 87951292861063691827388035)
              ·
                refine ⟨131926939291595537741082053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87951292861063691827388035 131926939291595537741082053)
                ·
                  refine ⟨24736301117174163326452885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131926939291595537741082053 24736301117174163326452885)
                  ·
                    refine ⟨1159514114867538905927479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24736301117174163326452885 1159514114867538905927479)
                    ·
                      rfl

theorem cell23_6774437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_6774437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774437 prefixEnd_6774437 := by exact prefixLift 6774437
  have htrace : WordTrace (prefixWord ++ tailWord_6774437) baseStart_6774437 baseEnd_6774437 := by
    simpa [prefixWord, tailWord_6774437, baseEnd_6774437] using wordTrace_append hprefix tailTrace_6774437
  have hstable : (prefixWord ++ tailWord_6774437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774437).length < 2 ^ (prefixWord ++ tailWord_6774437).sum := by decide
  have hdescent : baseEnd_6774437 < baseStart_6774437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774447 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_6774447 : Nat := 118140960795 + 6774447 * 2 ^ 59
def prefixEnd_6774447 : Nat := 4983230072969 + 3 ^ 40 * 6774447 * 2
def baseEnd_6774447 : Nat := 3478547479409161678657391

theorem tailTrace_6774447 : CollatzResearch.WordTrace tailWord_6774447 prefixEnd_6774447 3478547479409161678657391 := by
  unfold tailWord_6774447
  simp only [CollatzResearch.WordTrace]
  refine ⟨247084380888342977280553595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164722920592228651520369063 247084380888342977280553595)
  ·
    refine ⟨370626571332514465920830393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247084380888342977280553595 370626571332514465920830393)
    ·
      refine ⟨277969928499385849440622795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370626571332514465920830393 277969928499385849440622795)
      ·
        refine ⟨416954892749078774160934193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277969928499385849440622795 416954892749078774160934193)
        ·
          refine ⟨312716169561809080620700645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416954892749078774160934193 312716169561809080620700645)
          ·
            refine ⟨58634281792839202616381371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312716169561809080620700645 58634281792839202616381371)
            ·
              refine ⟨87951422689258803924572057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58634281792839202616381371 87951422689258803924572057)
              ·
                refine ⟨65963567016944102943429043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87951422689258803924572057 65963567016944102943429043)
                ·
                  refine ⟨98945350525416154415143565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65963567016944102943429043 98945350525416154415143565)
                  ·
                    refine ⟨37104506447031057905678837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98945350525416154415143565 37104506447031057905678837)
                    ·
                      refine ⟨3478547479409161678657391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37104506447031057905678837 3478547479409161678657391)
                      ·
                        rfl

theorem cell23_6774447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_6774447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774447 prefixEnd_6774447 := by exact prefixLift 6774447
  have htrace : WordTrace (prefixWord ++ tailWord_6774447) baseStart_6774447 baseEnd_6774447 := by
    simpa [prefixWord, tailWord_6774447, baseEnd_6774447] using wordTrace_append hprefix tailTrace_6774447
  have hstable : (prefixWord ++ tailWord_6774447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774447).length < 2 ^ (prefixWord ++ tailWord_6774447).sum := by decide
  have hdescent : baseEnd_6774447 < baseStart_6774447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774455 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 2, 1, 3]
def baseStart_6774455 : Nat := 118140960795 + 6774455 * 2 ^ 59
def prefixEnd_6774455 : Nat := 4983230072969 + 3 ^ 40 * 6774455 * 2
def baseEnd_6774455 : Nat := 3478551587254397647357355

theorem tailTrace_6774455 : CollatzResearch.WordTrace tailWord_6774455 prefixEnd_6774455 3478551587254397647357355 := by
  unfold tailWord_6774455
  simp only [CollatzResearch.WordTrace]
  refine ⟨247084672672313994646844819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164723115114875996431229879 247084672672313994646844819)
  ·
    refine ⟨370627009008470991970267229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247084672672313994646844819 370627009008470991970267229)
    ·
      refine ⟨138985128378176621988850211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370627009008470991970267229 138985128378176621988850211)
      ·
        refine ⟨208477692567264932983275317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138985128378176621988850211 208477692567264932983275317)
        ·
          refine ⟨19544783678181087467182061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208477692567264932983275317 19544783678181087467182061)
          ·
            refine ⟨7329293879317907800193273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19544783678181087467182061 7329293879317907800193273)
            ·
              refine ⟨5496970409488430850144955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7329293879317907800193273 5496970409488430850144955)
              ·
                refine ⟨8245455614232646275217433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5496970409488430850144955 8245455614232646275217433)
                ·
                  refine ⟨6184091710674484706413075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8245455614232646275217433 6184091710674484706413075)
                  ·
                    refine ⟨9276137566011727059619613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6184091710674484706413075 9276137566011727059619613)
                    ·
                      refine ⟨3478551587254397647357355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9276137566011727059619613 3478551587254397647357355)
                      ·
                        rfl

theorem cell23_6774455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_6774455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774455 prefixEnd_6774455 := by exact prefixLift 6774455
  have htrace : WordTrace (prefixWord ++ tailWord_6774455) baseStart_6774455 baseEnd_6774455 := by
    simpa [prefixWord, tailWord_6774455, baseEnd_6774455] using wordTrace_append hprefix tailTrace_6774455
  have hstable : (prefixWord ++ tailWord_6774455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774455).length < 2 ^ (prefixWord ++ tailWord_6774455).sum := by decide
  have hdescent : baseEnd_6774455 < baseStart_6774455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774461 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 1, 4, 2]
def baseStart_6774461 : Nat := 118140960795 + 6774461 * 2 ^ 59
def prefixEnd_6774461 : Nat := 4983230072969 + 3 ^ 40 * 6774461 * 2
def baseEnd_6774461 : Nat := 3478554668138324623882327

theorem tailTrace_6774461 : CollatzResearch.WordTrace tailWord_6774461 prefixEnd_6774461 3478554668138324623882327 := by
  unfold tailWord_6774461
  simp only [CollatzResearch.WordTrace]
  refine ⟨247084891510292257671563237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164723261006861505114375491 247084891510292257671563237)
  ·
    refine ⟨46328417158179798313418107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247084891510292257671563237 46328417158179798313418107)
    ·
      refine ⟨69492625737269697470127161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46328417158179798313418107 69492625737269697470127161)
      ·
        refine ⟨52119469302952273102595371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69492625737269697470127161 52119469302952273102595371)
        ·
          refine ⟨78179203954428409653893057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52119469302952273102595371 78179203954428409653893057)
          ·
            refine ⟨58634402965821307240419793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78179203954428409653893057 58634402965821307240419793)
            ·
              refine ⟨43975802224365980430314845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58634402965821307240419793 43975802224365980430314845)
              ·
                refine ⟨16490925834137242661368067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43975802224365980430314845 16490925834137242661368067)
                ·
                  refine ⟨24736388751205863992052101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16490925834137242661368067 24736388751205863992052101)
                  ·
                    refine ⟨4638072890851099498509769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24736388751205863992052101 4638072890851099498509769)
                    ·
                      refine ⟨3478554668138324623882327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638072890851099498509769 3478554668138324623882327)
                      ·
                        rfl

theorem cell23_6774461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_6774461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774461 prefixEnd_6774461 := by exact prefixLift 6774461
  have htrace : WordTrace (prefixWord ++ tailWord_6774461) baseStart_6774461 baseEnd_6774461 := by
    simpa [prefixWord, tailWord_6774461, baseEnd_6774461] using wordTrace_append hprefix tailTrace_6774461
  have hstable : (prefixWord ++ tailWord_6774461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774461).length < 2 ^ (prefixWord ++ tailWord_6774461).sum := by decide
  have hdescent : baseEnd_6774461 < baseStart_6774461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774501 : List Nat := [1, 3, 1, 4, 1, 1, 3, 4, 5]
def baseStart_6774501 : Nat := 118140960795 + 6774501 * 2 ^ 59
def prefixEnd_6774501 : Nat := 4983230072969 + 3 ^ 40 * 6774501 * 2
def baseEnd_6774501 : Nat := 386508356373833829709127

theorem tailTrace_6774501 : CollatzResearch.WordTrace tailWord_6774501 prefixEnd_6774501 386508356373833829709127 := by
  unfold tailWord_6774501
  simp only [CollatzResearch.WordTrace]
  refine ⟨247086350430147344503019357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164724233620098229668679571 247086350430147344503019357)
  ·
    refine ⟨92657381411305254188632259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247086350430147344503019357 92657381411305254188632259)
    ·
      refine ⟨138986072116957881282948389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92657381411305254188632259 138986072116957881282948389)
      ·
        refine ⟨26059888521929602740552823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138986072116957881282948389 26059888521929602740552823)
        ·
          refine ⟨39089832782894404110829235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26059888521929602740552823 39089832782894404110829235)
          ·
            refine ⟨58634749174341606166243853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39089832782894404110829235 58634749174341606166243853)
            ·
              refine ⟨21988030940378102312341445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58634749174341606166243853 21988030940378102312341445)
              ·
                refine ⟨4122755801320894183564021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21988030940378102312341445 4122755801320894183564021)
                ·
                  refine ⟨386508356373833829709127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4122755801320894183564021 386508356373833829709127)
                  ·
                    rfl

theorem cell23_6774501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_6774501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774501 prefixEnd_6774501 := by exact prefixLift 6774501
  have htrace : WordTrace (prefixWord ++ tailWord_6774501) baseStart_6774501 baseEnd_6774501 := by
    simpa [prefixWord, tailWord_6774501, baseEnd_6774501] using wordTrace_append hprefix tailTrace_6774501
  have hstable : (prefixWord ++ tailWord_6774501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774501).length < 2 ^ (prefixWord ++ tailWord_6774501).sum := by decide
  have hdescent : baseEnd_6774501 < baseStart_6774501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774514 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_6774514 : Nat := 118140960795 + 6774514 * 2 ^ 59
def prefixEnd_6774514 : Nat := 4983230072969 + 3 ^ 40 * 6774514 * 2
def baseEnd_6774514 : Nat := 1159527294204337638839861

theorem tailTrace_6774514 : CollatzResearch.WordTrace tailWord_6774514 prefixEnd_6774514 1159527294204337638839861 := by
  unfold tailWord_6774514
  simp only [CollatzResearch.WordTrace]
  refine ⟨61771706144775061930810649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164724549719400165148828397 61771706144775061930810649)
  ·
    refine ⟨46328779608581296448107987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61771706144775061930810649 46328779608581296448107987)
    ·
      refine ⟨69493169412871944672161981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46328779608581296448107987 69493169412871944672161981)
      ·
        refine ⟨26059938529826979252060743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69493169412871944672161981 26059938529826979252060743)
        ·
          refine ⟨39089907794740468878091115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26059938529826979252060743 39089907794740468878091115)
          ·
            refine ⟨58634861692110703317136673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39089907794740468878091115 58634861692110703317136673)
            ·
              refine ⟨43976146269083027487852505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58634861692110703317136673 43976146269083027487852505)
              ·
                refine ⟨32982109701812270615889379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43976146269083027487852505 32982109701812270615889379)
                ·
                  refine ⟨49473164552718405923834069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32982109701812270615889379 49473164552718405923834069)
                  ·
                    refine ⟨1159527294204337638839861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49473164552718405923834069 1159527294204337638839861)
                    ·
                      rfl

theorem cell23_6774514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_6774514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774514 prefixEnd_6774514 := by exact prefixLift 6774514
  have htrace : WordTrace (prefixWord ++ tailWord_6774514) baseStart_6774514 baseEnd_6774514 := by
    simpa [prefixWord, tailWord_6774514, baseEnd_6774514] using wordTrace_append hprefix tailTrace_6774514
  have hstable : (prefixWord ++ tailWord_6774514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774514).length < 2 ^ (prefixWord ++ tailWord_6774514).sum := by decide
  have hdescent : baseEnd_6774514 < baseStart_6774514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774561 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 3, 4]
def baseStart_6774561 : Nat := 118140960795 + 6774561 * 2 ^ 59
def prefixEnd_6774561 : Nat := 4983230072969 + 3 ^ 40 * 6774561 * 2
def baseEnd_6774561 : Nat := 1159535338734591410877289

theorem tailTrace_6774561 : CollatzResearch.WordTrace tailWord_6774561 prefixEnd_6774561 1159535338734591410877289 := by
  unfold tailWord_6774561
  simp only [CollatzResearch.WordTrace]
  refine ⟨247088538809929974750203537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164725692539953316500135691 247088538809929974750203537)
  ·
    refine ⟨185316404107447481062652653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247088538809929974750203537 185316404107447481062652653)
    ·
      refine ⟨69493651540292805398494745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185316404107447481062652653 69493651540292805398494745)
      ·
        refine ⟨52120238655219604048871059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69493651540292805398494745 52120238655219604048871059)
        ·
          refine ⟨78180357982829406073306589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52120238655219604048871059 78180357982829406073306589)
          ·
            refine ⟨29317634243561027277489971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78180357982829406073306589 29317634243561027277489971)
            ·
              refine ⟨43976451365341540916234957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29317634243561027277489971 43976451365341540916234957)
              ·
                refine ⟨16491169262003077843588109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43976451365341540916234957 16491169262003077843588109)
                ·
                  refine ⟨6184188473251154191345541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16491169262003077843588109 6184188473251154191345541)
                  ·
                    refine ⟨1159535338734591410877289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184188473251154191345541 1159535338734591410877289)
                    ·
                      rfl

theorem cell23_6774561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_6774561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774561 prefixEnd_6774561 := by exact prefixLift 6774561
  have htrace : WordTrace (prefixWord ++ tailWord_6774561) baseStart_6774561 baseEnd_6774561 := by
    simpa [prefixWord, tailWord_6774561, baseEnd_6774561] using wordTrace_append hprefix tailTrace_6774561
  have hstable : (prefixWord ++ tailWord_6774561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774561).length < 2 ^ (prefixWord ++ tailWord_6774561).sum := by decide
  have hdescent : baseEnd_6774561 < baseStart_6774561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774568 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_6774568 : Nat := 118140960795 + 6774568 * 2 ^ 59
def prefixEnd_6774568 : Nat := 4983230072969 + 3 ^ 40 * 6774568 * 2
def baseEnd_6774568 : Nat := 3478609610568355705244335

theorem tailTrace_6774568 : CollatzResearch.WordTrace tailWord_6774568 prefixEnd_6774568 3478609610568355705244335 := by
  unfold tailWord_6774568
  simp only [CollatzResearch.WordTrace]
  refine ⟨123544397060452307472854179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164725862747269743297138905 123544397060452307472854179)
  ·
    refine ⟨185316595590678461209281269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123544397060452307472854179 185316595590678461209281269)
    ·
      refine ⟨17373430836626105738370119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185316595590678461209281269 17373430836626105738370119)
      ·
        refine ⟨26060146254939158607555179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17373430836626105738370119 26060146254939158607555179)
        ·
          refine ⟨39090219382408737911332769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26060146254939158607555179 39090219382408737911332769)
          ·
            refine ⟨29317664536806553433499577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39090219382408737911332769 29317664536806553433499577)
            ·
              refine ⟨21988248402604915075124683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29317664536806553433499577 21988248402604915075124683)
              ·
                refine ⟨32982372603907372612687025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21988248402604915075124683 32982372603907372612687025)
                ·
                  refine ⟨24736779452930529459515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32982372603907372612687025 24736779452930529459515269)
                  ·
                    refine ⟨4638146147424474273659113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24736779452930529459515269 4638146147424474273659113)
                    ·
                      refine ⟨3478609610568355705244335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638146147424474273659113 3478609610568355705244335)
                      ·
                        rfl

theorem cell23_6774568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_6774568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774568 prefixEnd_6774568 := by exact prefixLift 6774568
  have htrace : WordTrace (prefixWord ++ tailWord_6774568) baseStart_6774568 baseEnd_6774568 := by
    simpa [prefixWord, tailWord_6774568, baseEnd_6774568] using wordTrace_append hprefix tailTrace_6774568
  have hstable : (prefixWord ++ tailWord_6774568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774568).length < 2 ^ (prefixWord ++ tailWord_6774568).sum := by decide
  have hdescent : baseEnd_6774568 < baseStart_6774568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774595 : List Nat := [1, 1, 1, 3, 1, 7, 1, 3, 1, 4]
def baseStart_6774595 : Nat := 118140960795 + 6774595 * 2 ^ 59
def prefixEnd_6774595 : Nat := 4983230072969 + 3 ^ 40 * 6774595 * 2
def baseEnd_6774595 : Nat := 1159541158182009033202237

theorem tailTrace_6774595 : CollatzResearch.WordTrace tailWord_6774595 prefixEnd_6774595 1159541158182009033202237 := by
  unfold tailWord_6774595
  simp only [CollatzResearch.WordTrace]
  refine ⟨247089778891806798556941239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164726519261204532371294159 247089778891806798556941239)
  ·
    refine ⟨370634668337710197835411859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247089778891806798556941239 370634668337710197835411859)
    ·
      refine ⟨555952002506565296753117789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370634668337710197835411859 555952002506565296753117789)
      ·
        refine ⟨208482000939961986282419171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555952002506565296753117789 208482000939961986282419171)
        ·
          refine ⟨312723001409942979423628757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208482000939961986282419171 312723001409942979423628757)
          ·
            refine ⟨7329445345545538580241299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 312723001409942979423628757 7329445345545538580241299)
            ·
              refine ⟨10994168018318307870361949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7329445345545538580241299 10994168018318307870361949)
              ·
                refine ⟨4122813006869365451385731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10994168018318307870361949 4122813006869365451385731)
                ·
                  refine ⟨6184219510304048177078597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122813006869365451385731 6184219510304048177078597)
                  ·
                    refine ⟨1159541158182009033202237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184219510304048177078597 1159541158182009033202237)
                    ·
                      rfl

theorem cell23_6774595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 1, 4].length) (baseStart_6774595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774595 prefixEnd_6774595 := by exact prefixLift 6774595
  have htrace : WordTrace (prefixWord ++ tailWord_6774595) baseStart_6774595 baseEnd_6774595 := by
    simpa [prefixWord, tailWord_6774595, baseEnd_6774595] using wordTrace_append hprefix tailTrace_6774595
  have hstable : (prefixWord ++ tailWord_6774595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774595).length < 2 ^ (prefixWord ++ tailWord_6774595).sum := by decide
  have hdescent : baseEnd_6774595 < baseStart_6774595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774605 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_6774605 : Nat := 118140960795 + 6774605 * 2 ^ 59
def prefixEnd_6774605 : Nat := 4983230072969 + 3 ^ 40 * 6774605 * 2
def baseEnd_6774605 : Nat := 3478628609352572060481665

theorem tailTrace_6774605 : CollatzResearch.WordTrace tailWord_6774605 prefixEnd_6774605 3478628609352572060481665 := by
  unfold tailWord_6774605
  simp only [CollatzResearch.WordTrace]
  refine ⟨247090143621770570264805269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164726762414513713509870179 247090143621770570264805269)
  ·
    refine ⟨11582350482270495481162747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 247090143621770570264805269 11582350482270495481162747)
    ·
      refine ⟨17373525723405743221744121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11582350482270495481162747 17373525723405743221744121)
      ·
        refine ⟨13030144292554307416308091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17373525723405743221744121 13030144292554307416308091)
        ·
          refine ⟨19545216438831461124462137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13030144292554307416308091 19545216438831461124462137)
          ·
            refine ⟨14658912329123595843346603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19545216438831461124462137 14658912329123595843346603)
            ·
              refine ⟨21988368493685393765019905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14658912329123595843346603 21988368493685393765019905)
              ·
                refine ⟨16491276370264045323764929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21988368493685393765019905 16491276370264045323764929)
                ·
                  refine ⟨12368457277698033992823697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16491276370264045323764929 12368457277698033992823697)
                  ·
                    refine ⟨9276342958273525494617773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12368457277698033992823697 9276342958273525494617773)
                    ·
                      refine ⟨3478628609352572060481665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9276342958273525494617773 3478628609352572060481665)
                      ·
                        rfl

theorem cell23_6774605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_6774605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774605 prefixEnd_6774605 := by exact prefixLift 6774605
  have htrace : WordTrace (prefixWord ++ tailWord_6774605) baseStart_6774605 baseEnd_6774605 := by
    simpa [prefixWord, tailWord_6774605, baseEnd_6774605] using wordTrace_append hprefix tailTrace_6774605
  have hstable : (prefixWord ++ tailWord_6774605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774605).length < 2 ^ (prefixWord ++ tailWord_6774605).sum := by decide
  have hdescent : baseEnd_6774605 < baseStart_6774605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774612 : List Nat := [2, 4, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_6774612 : Nat := 118140960795 + 6774612 * 2 ^ 59
def prefixEnd_6774612 : Nat := 4983230072969 + 3 ^ 40 * 6774612 * 2
def baseEnd_6774612 : Nat := 1159544067905717844364711

theorem tailTrace_6774612 : CollatzResearch.WordTrace tailWord_6774612 prefixEnd_6774612 1159544067905717844364711 := by
  unfold tailWord_6774612
  simp only [CollatzResearch.WordTrace]
  refine ⟨123545199466372605230155045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164726932621830140306873393 123545199466372605230155045)
  ·
    refine ⟨23164724899944863480654071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123545199466372605230155045 23164724899944863480654071)
    ·
      refine ⟨34747087349917295220981107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23164724899944863480654071 34747087349917295220981107)
      ·
        refine ⟨52120631024875942831471661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34747087349917295220981107 52120631024875942831471661)
        ·
          refine ⟨19545236634328478561801873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52120631024875942831471661 19545236634328478561801873)
          ·
            refine ⟨14658927475746358921351405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19545236634328478561801873 14658927475746358921351405)
            ·
              refine ⟨5497097803404884595506777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14658927475746358921351405 5497097803404884595506777)
              ·
                refine ⟨4122823352553663446630083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5497097803404884595506777 4122823352553663446630083)
                ·
                  refine ⟨6184235028830495169945125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122823352553663446630083 6184235028830495169945125)
                  ·
                    refine ⟨1159544067905717844364711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184235028830495169945125 1159544067905717844364711)
                    ·
                      rfl

theorem cell23_6774612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_6774612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774612 prefixEnd_6774612 := by exact prefixLift 6774612
  have htrace : WordTrace (prefixWord ++ tailWord_6774612) baseStart_6774612 baseEnd_6774612 := by
    simpa [prefixWord, tailWord_6774612, baseEnd_6774612] using wordTrace_append hprefix tailTrace_6774612
  have hstable : (prefixWord ++ tailWord_6774612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774612).length < 2 ^ (prefixWord ++ tailWord_6774612).sum := by decide
  have hdescent : baseEnd_6774612 < baseStart_6774612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774638 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_6774638 : Nat := 118140960795 + 6774638 * 2 ^ 59
def prefixEnd_6774638 : Nat := 4983230072969 + 3 ^ 40 * 6774638 * 2
def baseEnd_6774638 : Nat := 1159548518071390143789671

theorem tailTrace_6774638 : CollatzResearch.WordTrace tailWord_6774638 prefixEnd_6774638 1159548518071390143789671 := by
  unfold tailWord_6774638
  simp only [CollatzResearch.WordTrace]
  refine ⟨30886418403831377112594571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164727564820434011267171045 30886418403831377112594571)
  ·
    refine ⟨46329627605747065668891857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30886418403831377112594571 46329627605747065668891857)
    ·
      refine ⟨34747220704310299251668893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46329627605747065668891857 34747220704310299251668893)
      ·
        refine ⟨13030207764116362219375835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34747220704310299251668893 13030207764116362219375835)
        ·
          refine ⟨19545311646174543329063753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13030207764116362219375835 19545311646174543329063753)
          ·
            refine ⟨14658983734630907496797815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19545311646174543329063753 14658983734630907496797815)
            ·
              refine ⟨21988475601946361245196723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14658983734630907496797815 21988475601946361245196723)
              ·
                refine ⟨32982713402919541867795085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21988475601946361245196723 32982713402919541867795085)
                ·
                  refine ⟨12368517526094828200423157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32982713402919541867795085 12368517526094828200423157)
                  ·
                    refine ⟨1159548518071390143789671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12368517526094828200423157 1159548518071390143789671)
                    ·
                      rfl

theorem cell23_6774638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_6774638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774638 prefixEnd_6774638 := by exact prefixLift 6774638
  have htrace : WordTrace (prefixWord ++ tailWord_6774638) baseStart_6774638 baseEnd_6774638 := by
    simpa [prefixWord, tailWord_6774638, baseEnd_6774638] using wordTrace_append hprefix tailTrace_6774638
  have hstable : (prefixWord ++ tailWord_6774638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774638).length < 2 ^ (prefixWord ++ tailWord_6774638).sum := by decide
  have hdescent : baseEnd_6774638 < baseStart_6774638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774641 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_6774641 : Nat := 118140960795 + 6774641 * 2 ^ 59
def prefixEnd_6774641 : Nat := 4983230072969 + 3 ^ 40 * 6774641 * 2
def baseEnd_6774641 : Nat := 3478647094656133919631499

theorem tailTrace_6774641 : CollatzResearch.WordTrace tailWord_6774641 prefixEnd_6774641 3478647094656133919631499 := by
  unfold tailWord_6774641
  simp only [CollatzResearch.WordTrace]
  refine ⟨247091456649640148413115777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164727637766426765608743851 247091456649640148413115777)
  ·
    refine ⟨185318592487230111309836833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247091456649640148413115777 185318592487230111309836833)
    ·
      refine ⟨138988944365422583482377625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185318592487230111309836833 138988944365422583482377625)
      ·
        refine ⟨104241708274066937611783219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138988944365422583482377625 104241708274066937611783219)
        ·
          refine ⟨156362562411100406417674829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104241708274066937611783219 156362562411100406417674829)
          ·
            refine ⟨58635960904162652406628061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156362562411100406417674829 58635960904162652406628061)
            ·
              refine ⟨21988485339060994652485523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58635960904162652406628061 21988485339060994652485523)
              ·
                refine ⟨32982728008591491978728285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21988485339060994652485523 32982728008591491978728285)
                ·
                  refine ⟨12368523003221809492023107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32982728008591491978728285 12368523003221809492023107)
                  ·
                    refine ⟨18552784504832714238034661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12368523003221809492023107 18552784504832714238034661)
                    ·
                      refine ⟨3478647094656133919631499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18552784504832714238034661 3478647094656133919631499)
                      ·
                        rfl

theorem cell23_6774641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_6774641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774641 prefixEnd_6774641 := by exact prefixLift 6774641
  have htrace : WordTrace (prefixWord ++ tailWord_6774641) baseStart_6774641 baseEnd_6774641 := by
    simpa [prefixWord, tailWord_6774641, baseEnd_6774641] using wordTrace_append hprefix tailTrace_6774641
  have hstable : (prefixWord ++ tailWord_6774641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774641).length < 2 ^ (prefixWord ++ tailWord_6774641).sum := by decide
  have hdescent : baseEnd_6774641 < baseStart_6774641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774645 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_6774645 : Nat := 118140960795 + 6774645 * 2 ^ 59
def prefixEnd_6774645 : Nat := 4983230072969 + 3 ^ 40 * 6774645 * 2
def baseEnd_6774645 : Nat := 3478649148578751903981481

theorem tailTrace_6774645 : CollatzResearch.WordTrace tailWord_6774645 prefixEnd_6774645 3478649148578751903981481 := by
  unfold tailWord_6774645
  simp only [CollatzResearch.WordTrace]
  refine ⟨247091602541625657096261389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164727735027750438064174259 247091602541625657096261389)
  ·
    refine ⟨92659350953109621411098021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247091602541625657096261389 92659350953109621411098021)
    ·
      refine ⟨17373628303708054014580879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92659350953109621411098021 17373628303708054014580879)
      ·
        refine ⟨26060442455562081021871319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17373628303708054014580879 26060442455562081021871319)
        ·
          refine ⟨39090663683343121532806979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26060442455562081021871319 39090663683343121532806979)
          ·
            refine ⟨58635995525014682299210469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39090663683343121532806979 58635995525014682299210469)
            ·
              refine ⟨10994249160940252931101963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58635995525014682299210469 10994249160940252931101963)
              ·
                refine ⟨16491373741410379396652945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10994249160940252931101963 16491373741410379396652945)
                ·
                  refine ⟨12368530306057784547489709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16491373741410379396652945 12368530306057784547489709)
                  ·
                    refine ⟨4638198864771669205308641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12368530306057784547489709 4638198864771669205308641)
                    ·
                      refine ⟨3478649148578751903981481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638198864771669205308641 3478649148578751903981481)
                      ·
                        rfl

theorem cell23_6774645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_6774645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774645 prefixEnd_6774645 := by exact prefixLift 6774645
  have htrace : WordTrace (prefixWord ++ tailWord_6774645) baseStart_6774645 baseEnd_6774645 := by
    simpa [prefixWord, tailWord_6774645, baseEnd_6774645] using wordTrace_append hprefix tailTrace_6774645
  have hstable : (prefixWord ++ tailWord_6774645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774645).length < 2 ^ (prefixWord ++ tailWord_6774645).sum := by decide
  have hdescent : baseEnd_6774645 < baseStart_6774645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774664 : List Nat := [2, 1, 3, 3, 14]
def baseStart_6774664 : Nat := 118140960795 + 6774664 * 2 ^ 59
def prefixEnd_6774664 : Nat := 4983230072969 + 3 ^ 40 * 6774664 * 2
def baseEnd_6774664 : Nat := 4771822914555812523517

theorem tailTrace_6774664 : CollatzResearch.WordTrace tailWord_6774664 prefixEnd_6774664 4771822914555812523517 := by
  unfold tailWord_6774664
  simp only [CollatzResearch.WordTrace]
  refine ⟨123546147764278411670601523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164728197019037882227468697 123546147764278411670601523)
  ·
    refine ⟨185319221646417617505902285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123546147764278411670601523 185319221646417617505902285)
    ·
      refine ⟨69494708117406606564713357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185319221646417617505902285 69494708117406606564713357)
      ·
        refine ⟨26060515544027477461767509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69494708117406606564713357 26060515544027477461767509)
        ·
          refine ⟨4771822914555812523517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 26060515544027477461767509 4771822914555812523517)
          ·
            rfl

theorem cell23_6774664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 14].length) (baseStart_6774664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774664 prefixEnd_6774664 := by exact prefixLift 6774664
  have htrace : WordTrace (prefixWord ++ tailWord_6774664) baseStart_6774664 baseEnd_6774664 := by
    simpa [prefixWord, tailWord_6774664, baseEnd_6774664] using wordTrace_append hprefix tailTrace_6774664
  have hstable : (prefixWord ++ tailWord_6774664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774664).length < 2 ^ (prefixWord ++ tailWord_6774664).sum := by decide
  have hdescent : baseEnd_6774664 < baseStart_6774664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774696 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6774696 : Nat := 118140960795 + 6774696 * 2 ^ 59
def prefixEnd_6774696 : Nat := 4983230072969 + 3 ^ 40 * 6774696 * 2
def baseEnd_6774696 : Nat := 3478675336092131204443747

theorem tailTrace_6774696 : CollatzResearch.WordTrace tailWord_6774696 prefixEnd_6774696 3478675336092131204443747 := by
  unfold tailWord_6774696
  simp only [CollatzResearch.WordTrace]
  refine ⟨123546731332220446403183971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164728975109627261870911961 123546731332220446403183971)
  ·
    refine ⟨185320096998330669604775957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123546731332220446403183971 185320096998330669604775957)
    ·
      refine ⟨8686879546796750137723873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185320096998330669604775957 8686879546796750137723873)
      ·
        refine ⟨6515159660097562603292905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8686879546796750137723873 6515159660097562603292905)
        ·
          refine ⟨4886369745073171952469679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6515159660097562603292905 4886369745073171952469679)
          ·
            refine ⟨7329554617609757928704519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4886369745073171952469679 7329554617609757928704519)
            ·
              refine ⟨10994331926414636893056779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7329554617609757928704519 10994331926414636893056779)
              ·
                refine ⟨16491497889621955339585169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10994331926414636893056779 16491497889621955339585169)
                ·
                  refine ⟨12368623417216466504688877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16491497889621955339585169 12368623417216466504688877)
                  ·
                    refine ⟨4638233781456174939258329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12368623417216466504688877 4638233781456174939258329)
                    ·
                      refine ⟨3478675336092131204443747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638233781456174939258329 3478675336092131204443747)
                      ·
                        rfl

theorem cell23_6774696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6774696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774696 prefixEnd_6774696 := by exact prefixLift 6774696
  have htrace : WordTrace (prefixWord ++ tailWord_6774696) baseStart_6774696 baseEnd_6774696 := by
    simpa [prefixWord, tailWord_6774696, baseEnd_6774696] using wordTrace_append hprefix tailTrace_6774696
  have hstable : (prefixWord ++ tailWord_6774696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774696).length < 2 ^ (prefixWord ++ tailWord_6774696).sum := by decide
  have hdescent : baseEnd_6774696 < baseStart_6774696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774709 : List Nat := [1, 3, 3, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_6774709 : Nat := 118140960795 + 6774709 * 2 ^ 59
def prefixEnd_6774709 : Nat := 4983230072969 + 3 ^ 40 * 6774709 * 2
def baseEnd_6774709 : Nat := 3478682011340639653581187

theorem tailTrace_6774709 : CollatzResearch.WordTrace tailWord_6774709 prefixEnd_6774709 3478682011340639653581187 := by
  unfold tailWord_6774709
  simp only [CollatzResearch.WordTrace]
  refine ⟨247093936813393796026591181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164729291208929197351060787 247093936813393796026591181)
  ·
    refine ⟨92660226305022673509971693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247093936813393796026591181 92660226305022673509971693)
    ·
      refine ⟨34747584864383502566239385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92660226305022673509971693 34747584864383502566239385)
      ·
        refine ⟨26060688648287626924679539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34747584864383502566239385 26060688648287626924679539)
        ·
          refine ⟨39091032972431440387019309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26060688648287626924679539 39091032972431440387019309)
          ·
            refine ⟨14659137364661790145132241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39091032972431440387019309 14659137364661790145132241)
            ·
              refine ⟨10994353023496342608849181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14659137364661790145132241 10994353023496342608849181)
              ·
                refine ⟨4122882383811128478318443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10994353023496342608849181 4122882383811128478318443)
                ·
                  refine ⟨6184323575716692717477665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122882383811128478318443 6184323575716692717477665)
                  ·
                    refine ⟨4638242681787519538108249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6184323575716692717477665 4638242681787519538108249)
                    ·
                      refine ⟨3478682011340639653581187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638242681787519538108249 3478682011340639653581187)
                      ·
                        rfl

theorem cell23_6774709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_6774709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774709 prefixEnd_6774709 := by exact prefixLift 6774709
  have htrace : WordTrace (prefixWord ++ tailWord_6774709) baseStart_6774709 baseEnd_6774709 := by
    simpa [prefixWord, tailWord_6774709, baseEnd_6774709] using wordTrace_append hprefix tailTrace_6774709
  have hstable : (prefixWord ++ tailWord_6774709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774709).length < 2 ^ (prefixWord ++ tailWord_6774709).sum := by decide
  have hdescent : baseEnd_6774709 < baseStart_6774709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774798 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_6774798 : Nat := 118140960795 + 6774798 * 2 ^ 59
def prefixEnd_6774798 : Nat := 4983230072969 + 3 ^ 40 * 6774798 * 2
def baseEnd_6774798 : Nat := 3478727711118889805368277

theorem tailTrace_6774798 : CollatzResearch.WordTrace tailWord_6774798 prefixEnd_6774798 3478727711118889805368277 := by
  unfold tailWord_6774798
  simp only [CollatzResearch.WordTrace]
  refine ⟨30887147863758920528322631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164731455273380909484387365 30887147863758920528322631)
  ·
    refine ⟨46330721795638380792483947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30887147863758920528322631 46330721795638380792483947)
    ·
      refine ⟨69496082693457571188725921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46330721795638380792483947 69496082693457571188725921)
      ·
        refine ⟨52122062020093178391544441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69496082693457571188725921 52122062020093178391544441)
        ·
          refine ⟨39091546515069883793658331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52122062020093178391544441 39091546515069883793658331)
          ·
            refine ⟨58637319772604825690487497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39091546515069883793658331 58637319772604825690487497)
            ·
              refine ⟨43977989829453619267865623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58637319772604825690487497 43977989829453619267865623)
              ·
                refine ⟨65966984744180428901798435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43977989829453619267865623 65966984744180428901798435)
                ·
                  refine ⟨98950477116270643352697653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65966984744180428901798435 98950477116270643352697653)
                  ·
                    refine ⟨9276607229650372814315405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98950477116270643352697653 9276607229650372814315405)
                    ·
                      refine ⟨3478727711118889805368277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9276607229650372814315405 3478727711118889805368277)
                      ·
                        rfl

theorem cell23_6774798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_6774798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774798 prefixEnd_6774798 := by exact prefixLift 6774798
  have htrace : WordTrace (prefixWord ++ tailWord_6774798) baseStart_6774798 baseEnd_6774798 := by
    simpa [prefixWord, tailWord_6774798, baseEnd_6774798] using wordTrace_append hprefix tailTrace_6774798
  have hstable : (prefixWord ++ tailWord_6774798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774798).length < 2 ^ (prefixWord ++ tailWord_6774798).sum := by decide
  have hdescent : baseEnd_6774798 < baseStart_6774798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774851 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 6]
def baseStart_6774851 : Nat := 118140960795 + 6774851 * 2 ^ 59
def prefixEnd_6774851 : Nat := 4983230072969 + 3 ^ 40 * 6774851 * 2
def baseEnd_6774851 : Nat := 3478754925593578098005533

theorem tailTrace_6774851 : CollatzResearch.WordTrace tailWord_6774851 prefixEnd_6774851 3478754925593578098005533 := by
  unfold tailWord_6774851
  simp only [CollatzResearch.WordTrace]
  refine ⟨247099115978879354278260407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164732743985919569518840271 247099115978879354278260407)
  ·
    refine ⟨370648673968319031417390611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247099115978879354278260407 370648673968319031417390611)
    ·
      refine ⟨555973010952478547126085917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370648673968319031417390611 555973010952478547126085917)
      ·
        refine ⟨208489879107179455172282219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555973010952478547126085917 208489879107179455172282219)
        ·
          refine ⟨312734818660769182758423329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208489879107179455172282219 312734818660769182758423329)
          ·
            refine ⟨234551113995576887068817497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312734818660769182758423329 234551113995576887068817497)
            ·
              refine ⟨175913335496682665301613123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234551113995576887068817497 175913335496682665301613123)
              ·
                refine ⟨263870003245023997952419685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175913335496682665301613123 263870003245023997952419685)
                ·
                  refine ⟨49475625608441999616078691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263870003245023997952419685 49475625608441999616078691)
                  ·
                    refine ⟨74213438412662999424118037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49475625608441999616078691 74213438412662999424118037)
                    ·
                      refine ⟨3478754925593578098005533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74213438412662999424118037 3478754925593578098005533)
                      ·
                        rfl

theorem cell23_6774851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_6774851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774851 prefixEnd_6774851 := by exact prefixLift 6774851
  have htrace : WordTrace (prefixWord ++ tailWord_6774851) baseStart_6774851 baseEnd_6774851 := by
    simpa [prefixWord, tailWord_6774851, baseEnd_6774851] using wordTrace_append hprefix tailTrace_6774851
  have hstable : (prefixWord ++ tailWord_6774851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774851).length < 2 ^ (prefixWord ++ tailWord_6774851).sum := by decide
  have hdescent : baseEnd_6774851 < baseStart_6774851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774855 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 2, 4, 2]
def baseStart_6774855 : Nat := 118140960795 + 6774855 * 2 ^ 59
def prefixEnd_6774855 : Nat := 4983230072969 + 3 ^ 40 * 6774855 * 2
def baseEnd_6774855 : Nat := 3478756979516196082355515

theorem tailTrace_6774855 : CollatzResearch.WordTrace tailWord_6774855 prefixEnd_6774855 3478756979516196082355515 := by
  unfold tailWord_6774855
  simp only [CollatzResearch.WordTrace]
  refine ⟨247099261870864862961406019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164732841247243241974270679 247099261870864862961406019)
  ·
    refine ⟨370648892806297294442109029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247099261870864862961406019 370648892806297294442109029)
    ·
      refine ⟨69496667401180742707895443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370648892806297294442109029 69496667401180742707895443)
      ·
        refine ⟨104245001101771114061843165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69496667401180742707895443 104245001101771114061843165)
        ·
          refine ⟨39091875413164167773191187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104245001101771114061843165 39091875413164167773191187)
          ·
            refine ⟨58637813119746251659786781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39091875413164167773191187 58637813119746251659786781)
            ·
              refine ⟨21989179919904844372420043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58637813119746251659786781 21989179919904844372420043)
              ·
                refine ⟨32983769879857266558630065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21989179919904844372420043 32983769879857266558630065)
                ·
                  refine ⟨24737827409892949918972549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32983769879857266558630065 24737827409892949918972549)
                  ·
                    refine ⟨4638342639354928109807353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24737827409892949918972549 4638342639354928109807353)
                    ·
                      refine ⟨3478756979516196082355515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638342639354928109807353 3478756979516196082355515)
                      ·
                        rfl

theorem cell23_6774855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_6774855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774855 prefixEnd_6774855 := by exact prefixLift 6774855
  have htrace : WordTrace (prefixWord ++ tailWord_6774855) baseStart_6774855 baseEnd_6774855 := by
    simpa [prefixWord, tailWord_6774855, baseEnd_6774855] using wordTrace_append hprefix tailTrace_6774855
  have hstable : (prefixWord ++ tailWord_6774855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774855).length < 2 ^ (prefixWord ++ tailWord_6774855).sum := by decide
  have hdescent : baseEnd_6774855 < baseStart_6774855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774858 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_6774858 : Nat := 118140960795 + 6774858 * 2 ^ 59
def prefixEnd_6774858 : Nat := 4983230072969 + 3 ^ 40 * 6774858 * 2
def baseEnd_6774858 : Nat := 3478758519958159570618001

theorem tailTrace_6774858 : CollatzResearch.WordTrace tailWord_6774858 prefixEnd_6774858 3478758519958159570618001 := by
  unfold tailWord_6774858
  simp only [CollatzResearch.WordTrace]
  refine ⟨61774842822463498618441307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164732914193235996315843485 61774842822463498618441307)
  ·
    refine ⟨92662264233695247927661961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61774842822463498618441307 92662264233695247927661961)
    ·
      refine ⟨69496698175271435945746471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92662264233695247927661961 69496698175271435945746471)
      ·
        refine ⟨104245047262907153918619707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69496698175271435945746471 104245047262907153918619707)
        ·
          refine ⟨156367570894360730877929561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104245047262907153918619707 156367570894360730877929561)
          ·
            refine ⟨117275678170770548158447171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156367570894360730877929561 117275678170770548158447171)
            ·
              refine ⟨175913517256155822237670757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117275678170770548158447171 175913517256155822237670757)
              ·
                refine ⟨32983784485529216669563267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175913517256155822237670757 32983784485529216669563267)
                ·
                  refine ⟨49475676728293825004344901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32983784485529216669563267 49475676728293825004344901)
                  ·
                    refine ⟨9276689386555092188314669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49475676728293825004344901 9276689386555092188314669)
                    ·
                      refine ⟨3478758519958159570618001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9276689386555092188314669 3478758519958159570618001)
                      ·
                        rfl

theorem cell23_6774858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_6774858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774858 prefixEnd_6774858 := by exact prefixLift 6774858
  have htrace : WordTrace (prefixWord ++ tailWord_6774858) baseStart_6774858 baseEnd_6774858 := by
    simpa [prefixWord, tailWord_6774858, baseEnd_6774858] using wordTrace_append hprefix tailTrace_6774858
  have hstable : (prefixWord ++ tailWord_6774858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774858).length < 2 ^ (prefixWord ++ tailWord_6774858).sum := by decide
  have hdescent : baseEnd_6774858 < baseStart_6774858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774895 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 6]
def baseStart_6774895 : Nat := 118140960795 + 6774895 * 2 ^ 59
def prefixEnd_6774895 : Nat := 4983230072969 + 3 ^ 40 * 6774895 * 2
def baseEnd_6774895 : Nat := 386530835415819547317259

theorem tailTrace_6774895 : CollatzResearch.WordTrace tailWord_6774895 prefixEnd_6774895 386530835415819547317259 := by
  unfold tailWord_6774895
  simp only [CollatzResearch.WordTrace]
  refine ⟨247100720790719949792862139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164733813860479966528574759 247100720790719949792862139)
  ·
    refine ⟨370651081186079924689293209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247100720790719949792862139 370651081186079924689293209)
    ·
      refine ⟨277988310889559943516969907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370651081186079924689293209 277988310889559943516969907)
      ·
        refine ⟨416982466334339915275454861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277988310889559943516969907 416982466334339915275454861)
        ·
          refine ⟨156368424875377468228295573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416982466334339915275454861 156368424875377468228295573)
          ·
            refine ⟨7329769916033318823201355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156368424875377468228295573 7329769916033318823201355)
            ·
              refine ⟨10994654874049978234802033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7329769916033318823201355 10994654874049978234802033)
              ·
                refine ⟨8245991155537483676101525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10994654874049978234802033 8245991155537483676101525)
                ·
                  refine ⟨386530835415819547317259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8245991155537483676101525 386530835415819547317259)
                  ·
                    rfl

theorem cell23_6774895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 6].length) (baseStart_6774895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774895 prefixEnd_6774895 := by exact prefixLift 6774895
  have htrace : WordTrace (prefixWord ++ tailWord_6774895) baseStart_6774895 baseEnd_6774895 := by
    simpa [prefixWord, tailWord_6774895, baseEnd_6774895] using wordTrace_append hprefix tailTrace_6774895
  have hstable : (prefixWord ++ tailWord_6774895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774895).length < 2 ^ (prefixWord ++ tailWord_6774895).sum := by decide
  have hdescent : baseEnd_6774895 < baseStart_6774895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774898 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_6774898 : Nat := 118140960795 + 6774898 * 2 ^ 59
def prefixEnd_6774898 : Nat := 4983230072969 + 3 ^ 40 * 6774898 * 2
def baseEnd_6774898 : Nat := 3478779059184339414117817

theorem tailTrace_6774898 : CollatzResearch.WordTrace tailWord_6774898 prefixEnd_6774898 3478779059184339414117817 := by
  unfold tailWord_6774898
  simp only [CollatzResearch.WordTrace]
  refine ⟨61775207552427270326305337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164733886806472720870147565 61775207552427270326305337)
  ·
    refine ⟨46331405664320452744729003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61775207552427270326305337 46331405664320452744729003)
    ·
      refine ⟨69497108496480679117093505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46331405664320452744729003 69497108496480679117093505)
      ·
        refine ⟨52122831372360509337820129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69497108496480679117093505 52122831372360509337820129)
        ·
          refine ⟨39092123529270382003365097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52122831372360509337820129 39092123529270382003365097)
          ·
            refine ⟨29319092646952786502523823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39092123529270382003365097 29319092646952786502523823)
            ·
              refine ⟨43978638970429179753785735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29319092646952786502523823 43978638970429179753785735)
              ·
                refine ⟨65967958455643769630678603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43978638970429179753785735 65967958455643769630678603)
                ·
                  refine ⟨98951937683465654446017905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65967958455643769630678603 98951937683465654446017905)
                  ·
                    refine ⟨74213953262599240834513429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98951937683465654446017905 74213953262599240834513429)
                    ·
                      refine ⟨3478779059184339414117817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74213953262599240834513429 3478779059184339414117817)
                      ·
                        rfl

theorem cell23_6774898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_6774898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774898 prefixEnd_6774898 := by exact prefixLift 6774898
  have htrace : WordTrace (prefixWord ++ tailWord_6774898) baseStart_6774898 baseEnd_6774898 := by
    simpa [prefixWord, tailWord_6774898, baseEnd_6774898] using wordTrace_append hprefix tailTrace_6774898
  have hstable : (prefixWord ++ tailWord_6774898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774898).length < 2 ^ (prefixWord ++ tailWord_6774898).sum := by decide
  have hdescent : baseEnd_6774898 < baseStart_6774898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774915 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 1, 5, 2]
def baseStart_6774915 : Nat := 118140960795 + 6774915 * 2 ^ 59
def prefixEnd_6774915 : Nat := 4983230072969 + 3 ^ 40 * 6774915 * 2
def baseEnd_6774915 : Nat := 3478787788355465847605239

theorem tailTrace_6774915 : CollatzResearch.WordTrace tailWord_6774915 prefixEnd_6774915 3478787788355465847605239 := by
  unfold tailWord_6774915
  simp only [CollatzResearch.WordTrace]
  refine ⟨247101450250647493208590199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164734300167098328805726799 247101450250647493208590199)
  ·
    refine ⟨370652175375971239812885299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247101450250647493208590199 370652175375971239812885299)
    ·
      refine ⟨555978263063956859719327949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370652175375971239812885299 555978263063956859719327949)
      ·
        refine ⟨208491848648983822394747981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555978263063956859719327949 208491848648983822394747981)
        ·
          refine ⟨78184443243368933398030493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208491848648983822394747981 78184443243368933398030493)
          ·
            refine ⟨29319166216263350024261435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78184443243368933398030493 29319166216263350024261435)
            ·
              refine ⟨43978749324395025036392153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29319166216263350024261435 43978749324395025036392153)
              ·
                refine ⟨32984061993296268777294115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43978749324395025036392153 32984061993296268777294115)
                ·
                  refine ⟨49476092989944403165941173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32984061993296268777294115 49476092989944403165941173)
                  ·
                    refine ⟨4638383717807287796806985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49476092989944403165941173 4638383717807287796806985)
                    ·
                      refine ⟨3478787788355465847605239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638383717807287796806985 3478787788355465847605239)
                      ·
                        rfl

theorem cell23_6774915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_6774915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774915 prefixEnd_6774915 := by exact prefixLift 6774915
  have htrace : WordTrace (prefixWord ++ tailWord_6774915) baseStart_6774915 baseEnd_6774915 := by
    simpa [prefixWord, tailWord_6774915, baseEnd_6774915] using wordTrace_append hprefix tailTrace_6774915
  have hstable : (prefixWord ++ tailWord_6774915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774915).length < 2 ^ (prefixWord ++ tailWord_6774915).sum := by decide
  have hdescent : baseEnd_6774915 < baseStart_6774915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774922 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_6774922 : Nat := 118140960795 + 6774922 * 2 ^ 59
def prefixEnd_6774922 : Nat := 4983230072969 + 3 ^ 40 * 6774922 * 2
def baseEnd_6774922 : Nat := 3478791382720047320217707

theorem tailTrace_6774922 : CollatzResearch.WordTrace tailWord_6774922 prefixEnd_6774922 3478791382720047320217707 := by
  unfold tailWord_6774922
  simp only [CollatzResearch.WordTrace]
  refine ⟨61775426390405533351023755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164734470374414755602730013 61775426390405533351023755)
  ·
    refine ⟨92663139585608300026535633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61775426390405533351023755 92663139585608300026535633)
    ·
      refine ⟨69497354689206225019901725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92663139585608300026535633 69497354689206225019901725)
      ·
        refine ⟨26061508008452334382463147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69497354689206225019901725 26061508008452334382463147)
        ·
          refine ⟨39092262012678501573694721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26061508008452334382463147 39092262012678501573694721)
          ·
            refine ⟨29319196509508876180271041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39092262012678501573694721 29319196509508876180271041)
            ·
              refine ⟨21989397382131657135203281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29319196509508876180271041 21989397382131657135203281)
              ·
                refine ⟨16492048036598742851402461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21989397382131657135203281 16492048036598742851402461)
                ·
                  refine ⟨6184518013724528569275923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16492048036598742851402461 6184518013724528569275923)
                  ·
                    refine ⟨9276777020586792853913885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6184518013724528569275923 9276777020586792853913885)
                    ·
                      refine ⟨3478791382720047320217707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9276777020586792853913885 3478791382720047320217707)
                      ·
                        rfl

theorem cell23_6774922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_6774922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774922 prefixEnd_6774922 := by exact prefixLift 6774922
  have htrace : WordTrace (prefixWord ++ tailWord_6774922) baseStart_6774922 baseEnd_6774922 := by
    simpa [prefixWord, tailWord_6774922, baseEnd_6774922] using wordTrace_append hprefix tailTrace_6774922
  have hstable : (prefixWord ++ tailWord_6774922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774922).length < 2 ^ (prefixWord ++ tailWord_6774922).sum := by decide
  have hdescent : baseEnd_6774922 < baseStart_6774922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6774968 : List Nat := [2, 1, 2, 1, 2, 1, 6, 8]
def baseStart_6774968 : Nat := 118140960795 + 6774968 * 2 ^ 59
def prefixEnd_6774968 : Nat := 4983230072969 + 3 ^ 40 * 6774968 * 2
def baseEnd_6774968 : Nat := 128845000104820523712685

theorem tailTrace_6774968 : CollatzResearch.WordTrace tailWord_6774968 prefixEnd_6774968 128845000104820523712685 := by
  unfold tailWord_6774968
  simp only [CollatzResearch.WordTrace]
  refine ⟨123551691659727741630134779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164735588879636988840179705 123551691659727741630134779)
  ·
    refine ⟨185327537489591612445202169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123551691659727741630134779 185327537489591612445202169)
    ·
      refine ⟨138995653117193709333901627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185327537489591612445202169 138995653117193709333901627)
      ·
        refine ⟨208493479675790564000852441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138995653117193709333901627 208493479675790564000852441)
        ·
          refine ⟨156370109756842923000639331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208493479675790564000852441 156370109756842923000639331)
          ·
            refine ⟨234555164635264384500958997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156370109756842923000639331 234555164635264384500958997)
            ·
              refine ⟨10994773342278018023482453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234555164635264384500958997 10994773342278018023482453)
              ·
                refine ⟨128845000104820523712685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10994773342278018023482453 128845000104820523712685)
                ·
                  rfl

theorem cell23_6774968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 8].length) (baseStart_6774968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6774968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6774968 prefixEnd_6774968 := by exact prefixLift 6774968
  have htrace : WordTrace (prefixWord ++ tailWord_6774968) baseStart_6774968 baseEnd_6774968 := by
    simpa [prefixWord, tailWord_6774968, baseEnd_6774968] using wordTrace_append hprefix tailTrace_6774968
  have hstable : (prefixWord ++ tailWord_6774968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6774968).length < 2 ^ (prefixWord ++ tailWord_6774968).sum := by decide
  have hdescent : baseEnd_6774968 < baseStart_6774968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6774968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775013 : List Nat := [1, 3, 1, 4, 2, 1, 4, 2, 1, 2, 2]
def baseStart_6775013 : Nat := 118140960795 + 6775013 * 2 ^ 59
def prefixEnd_6775013 : Nat := 4983230072969 + 3 ^ 40 * 6775013 * 2
def baseEnd_6775013 : Nat := 3478838109459606464179789

theorem tailTrace_6775013 : CollatzResearch.WordTrace tailWord_6775013 prefixEnd_6775013 3478838109459606464179789 := by
  unfold tailWord_6775013
  simp only [CollatzResearch.WordTrace]
  refine ⟨247105024604292455945657693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164736683069528303963771795 247105024604292455945657693)
  ·
    refine ⟨92664384226609670979621635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247105024604292455945657693 92664384226609670979621635)
    ·
      refine ⟨138996576339914506469432453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92664384226609670979621635 138996576339914506469432453)
      ·
        refine ⟨26061858063733969963018585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138996576339914506469432453 26061858063733969963018585)
        ·
          refine ⟨19546393547800477472263939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26061858063733969963018585 19546393547800477472263939)
          ·
            refine ⟨29319590321700716208395909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19546393547800477472263939 29319590321700716208395909)
            ·
              refine ⟨5497423185318884289074233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29319590321700716208395909 5497423185318884289074233)
              ·
                refine ⟨4123067388989163216805675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5497423185318884289074233 4123067388989163216805675)
                ·
                  refine ⟨6184601083483744825208513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123067388989163216805675 6184601083483744825208513)
                  ·
                    refine ⟨4638450812612808618906385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6184601083483744825208513 4638450812612808618906385)
                    ·
                      refine ⟨3478838109459606464179789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638450812612808618906385 3478838109459606464179789)
                      ·
                        rfl

theorem cell23_6775013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_6775013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775013 prefixEnd_6775013 := by exact prefixLift 6775013
  have htrace : WordTrace (prefixWord ++ tailWord_6775013) baseStart_6775013 baseEnd_6775013 := by
    simpa [prefixWord, tailWord_6775013, baseEnd_6775013] using wordTrace_append hprefix tailTrace_6775013
  have hstable : (prefixWord ++ tailWord_6775013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775013).length < 2 ^ (prefixWord ++ tailWord_6775013).sum := by decide
  have hdescent : baseEnd_6775013 < baseStart_6775013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775015 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 2, 7]
def baseStart_6775015 : Nat := 118140960795 + 6775015 * 2 ^ 59
def prefixEnd_6775015 : Nat := 4983230072969 + 3 ^ 40 * 6775015 * 2
def baseEnd_6775015 : Nat := 1159613045473638485451593

theorem tailTrace_6775015 : CollatzResearch.WordTrace tailWord_6775015 prefixEnd_6775015 1159613045473638485451593 := by
  unfold tailWord_6775015
  simp only [CollatzResearch.WordTrace]
  refine ⟨247105097550285210287230499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164736731700190140191486999 247105097550285210287230499)
  ·
    refine ⟨370657646325427815430845749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247105097550285210287230499 370657646325427815430845749)
    ·
      refine ⟨34749154343008857696641789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 370657646325427815430845749 34749154343008857696641789)
      ·
        refine ⟨13030932878628321636240671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34749154343008857696641789 13030932878628321636240671)
        ·
          refine ⟨19546399317942482454361007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13030932878628321636240671 19546399317942482454361007)
          ·
            refine ⟨29319598976913723681541511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19546399317942482454361007 29319598976913723681541511)
            ·
              refine ⟨43979398465370585522312267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29319598976913723681541511 43979398465370585522312267)
              ·
                refine ⟨65969097698055878283468401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43979398465370585522312267 65969097698055878283468401)
                ·
                  refine ⟨49476823273541908712601301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65969097698055878283468401 49476823273541908712601301)
                  ·
                    refine ⟨1159613045473638485451593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49476823273541908712601301 1159613045473638485451593)
                    ·
                      rfl

theorem cell23_6775015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_6775015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775015 prefixEnd_6775015 := by exact prefixLift 6775015
  have htrace : WordTrace (prefixWord ++ tailWord_6775015) baseStart_6775015 baseEnd_6775015 := by
    simpa [prefixWord, tailWord_6775015, baseEnd_6775015] using wordTrace_append hprefix tailTrace_6775015
  have hstable : (prefixWord ++ tailWord_6775015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775015).length < 2 ^ (prefixWord ++ tailWord_6775015).sum := by decide
  have hdescent : baseEnd_6775015 < baseStart_6775015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775052 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 1, 4, 2]
def baseStart_6775052 : Nat := 118140960795 + 6775052 * 2 ^ 59
def prefixEnd_6775052 : Nat := 4983230072969 + 3 ^ 40 * 6775052 * 2
def baseEnd_6775052 : Nat := 3478858135205131811592109

theorem tailTrace_6775052 : CollatzResearch.WordTrace tailWord_6775052 prefixEnd_6775052 3478858135205131811592109 := by
  unfold tailWord_6775052
  simp only [CollatzResearch.WordTrace]
  refine ⟨123553223525575582803163705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164737631367434110404218273 123553223525575582803163705)
  ·
    refine ⟨92664917644181687102372779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123553223525575582803163705 92664917644181687102372779)
    ·
      refine ⟨138997376466272530653559169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92664917644181687102372779 138997376466272530653559169)
      ·
        refine ⟨104248032349704397990169377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138997376466272530653559169 104248032349704397990169377)
        ·
          refine ⟨78186024262278298492627033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104248032349704397990169377 78186024262278298492627033)
          ·
            refine ⟨58639518196708723869470275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78186024262278298492627033 58639518196708723869470275)
            ·
              refine ⟨87959277295063085804205413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58639518196708723869470275 87959277295063085804205413)
              ·
                refine ⟨16492364492824328588288515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87959277295063085804205413 16492364492824328588288515)
                ·
                  refine ⟨24738546739236492882432773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16492364492824328588288515 24738546739236492882432773)
                  ·
                    refine ⟨4638477513606842415456145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24738546739236492882432773 4638477513606842415456145)
                    ·
                      refine ⟨3478858135205131811592109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638477513606842415456145 3478858135205131811592109)
                      ·
                        rfl

theorem cell23_6775052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_6775052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775052 prefixEnd_6775052 := by exact prefixLift 6775052
  have htrace : WordTrace (prefixWord ++ tailWord_6775052) baseStart_6775052 baseEnd_6775052 := by
    simpa [prefixWord, tailWord_6775052, baseEnd_6775052] using wordTrace_append hprefix tailTrace_6775052
  have hstable : (prefixWord ++ tailWord_6775052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775052).length < 2 ^ (prefixWord ++ tailWord_6775052).sum := by decide
  have hdescent : baseEnd_6775052 < baseStart_6775052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775075 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 7]
def baseStart_6775075 : Nat := 118140960795 + 6775075 * 2 ^ 59
def prefixEnd_6775075 : Nat := 4983230072969 + 3 ^ 40 * 6775075 * 2
def baseEnd_6775075 : Nat := 386541105028909469067167

theorem tailTrace_6775075 : CollatzResearch.WordTrace tailWord_6775075 prefixEnd_6775075 386541105028909469067167 := by
  unfold tailWord_6775075
  simp only [CollatzResearch.WordTrace]
  refine ⟨247107285930067840534414679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164738190620045227022943119 247107285930067840534414679)
  ·
    refine ⟨370660928895101760801622019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247107285930067840534414679 370660928895101760801622019)
    ·
      refine ⟨555991393342652641202433029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370660928895101760801622019 555991393342652641202433029)
      ·
        refine ⟨104248386251747370225456193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 555991393342652641202433029 104248386251747370225456193)
        ·
          refine ⟨78186289688810527669092145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104248386251747370225456193 78186289688810527669092145)
          ·
            refine ⟨58639717266607895751819109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78186289688810527669092145 58639717266607895751819109)
            ·
              refine ⟨10994946987488980453466083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58639717266607895751819109 10994946987488980453466083)
              ·
                refine ⟨16492420481233470680199125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10994946987488980453466083 16492420481233470680199125)
                ·
                  refine ⟨386541105028909469067167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16492420481233470680199125 386541105028909469067167)
                  ·
                    rfl

theorem cell23_6775075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 7].length) (baseStart_6775075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775075 prefixEnd_6775075 := by exact prefixLift 6775075
  have htrace : WordTrace (prefixWord ++ tailWord_6775075) baseStart_6775075 baseEnd_6775075 := by
    simpa [prefixWord, tailWord_6775075, baseEnd_6775075] using wordTrace_append hprefix tailTrace_6775075
  have hstable : (prefixWord ++ tailWord_6775075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775075).length < 2 ^ (prefixWord ++ tailWord_6775075).sum := by decide
  have hdescent : baseEnd_6775075 < baseStart_6775075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775092 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 7]
def baseStart_6775092 : Nat := 118140960795 + 6775092 * 2 ^ 59
def prefixEnd_6775092 : Nat := 4983230072969 + 3 ^ 40 * 6775092 * 2
def baseEnd_6775092 : Nat := 386542074936812406121325

theorem tailTrace_6775092 : CollatzResearch.WordTrace tailWord_6775092 prefixEnd_6775092 386542074936812406121325 := by
  unfold tailWord_6775092
  simp only [CollatzResearch.WordTrace]
  refine ⟨123553952985503126218891765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164738603980670834958522353 123553952985503126218891765)
  ·
    refine ⟨11583183092390918083021103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123553952985503126218891765 11583183092390918083021103)
    ·
      refine ⟨17374774638586377124531655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11583183092390918083021103 17374774638586377124531655)
      ·
        refine ⟨26062161957879565686797483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17374774638586377124531655 26062161957879565686797483)
        ·
          refine ⟨39093242936819348530196225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26062161957879565686797483 39093242936819348530196225)
          ·
            refine ⟨29319932202614511397647169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39093242936819348530196225 29319932202614511397647169)
            ·
              refine ⟨21989949151960883548235377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29319932202614511397647169 21989949151960883548235377)
              ·
                refine ⟨16492461863970662661176533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21989949151960883548235377 16492461863970662661176533)
                ·
                  refine ⟨386542074936812406121325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16492461863970662661176533 386542074936812406121325)
                  ·
                    rfl

theorem cell23_6775092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_6775092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775092 prefixEnd_6775092 := by exact prefixLift 6775092
  have htrace : WordTrace (prefixWord ++ tailWord_6775092) baseStart_6775092 baseEnd_6775092 := by
    simpa [prefixWord, tailWord_6775092, baseEnd_6775092] using wordTrace_append hprefix tailTrace_6775092
  have hstable : (prefixWord ++ tailWord_6775092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775092).length < 2 ^ (prefixWord ++ tailWord_6775092).sum := by decide
  have hdescent : baseEnd_6775092 < baseStart_6775092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775205 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_6775205 : Nat := 118140960795 + 6775205 * 2 ^ 59
def prefixEnd_6775205 : Nat := 4983230072969 + 3 ^ 40 * 6775205 * 2
def baseEnd_6775205 : Nat := 3478936697745269712978905

theorem tailTrace_6775205 : CollatzResearch.WordTrace tailWord_6775205 prefixEnd_6775205 3478936697745269712978905 := by
  unfold tailWord_6775205
  simp only [CollatzResearch.WordTrace]
  refine ⟨247112027419596872736647069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164741351613064581824431379 247112027419596872736647069)
  ·
    refine ⟨92667010282348827276242651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247112027419596872736647069 92667010282348827276242651)
    ·
      refine ⟨139000515423523240914363977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92667010282348827276242651 139000515423523240914363977)
      ·
        refine ⟨104250386567642430685772983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139000515423523240914363977 104250386567642430685772983)
        ·
          refine ⟨156375579851463646028659475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104250386567642430685772983 156375579851463646028659475)
          ·
            refine ⟨234563369777195469042989213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156375579851463646028659475 234563369777195469042989213)
            ·
              refine ⟨87961263666448300891120955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234563369777195469042989213 87961263666448300891120955)
              ·
                refine ⟨131941895499672451336681433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87961263666448300891120955 131941895499672451336681433)
                ·
                  refine ⟨98956421624754338502511075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131941895499672451336681433 98956421624754338502511075)
                  ·
                    refine ⟨148434632437131507753766613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98956421624754338502511075 148434632437131507753766613)
                    ·
                      refine ⟨3478936697745269712978905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148434632437131507753766613 3478936697745269712978905)
                      ·
                        rfl

theorem cell23_6775205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_6775205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775205 prefixEnd_6775205 := by exact prefixLift 6775205
  have htrace : WordTrace (prefixWord ++ tailWord_6775205) baseStart_6775205 baseEnd_6775205 := by
    simpa [prefixWord, tailWord_6775205, baseEnd_6775205] using wordTrace_append hprefix tailTrace_6775205
  have hstable : (prefixWord ++ tailWord_6775205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775205).length < 2 ^ (prefixWord ++ tailWord_6775205).sum := by decide
  have hdescent : baseEnd_6775205 < baseStart_6775205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775210 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_6775210 : Nat := 118140960795 + 6775210 * 2 ^ 59
def prefixEnd_6775210 : Nat := 4983230072969 + 3 ^ 40 * 6775210 * 2
def baseEnd_6775210 : Nat := 3478939265148542193416383

theorem tailTrace_6775210 : CollatzResearch.WordTrace tailWord_6775210 prefixEnd_6775210 3478939265148542193416383 := by
  unfold tailWord_6775210
  simp only [CollatzResearch.WordTrace]
  refine ⟨61778052446144689647644771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164741473189719172393719389 61778052446144689647644771)
  ·
    refine ⟨92667078669217034471467157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61778052446144689647644771 92667078669217034471467157)
    ·
      refine ⟨4343769312619548490850023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92667078669217034471467157 4343769312619548490850023)
      ·
        refine ⟨6515653968929322736275035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343769312619548490850023 6515653968929322736275035)
        ·
          refine ⟨9773480953393984104412553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515653968929322736275035 9773480953393984104412553)
          ·
            refine ⟨7330110715045488078309415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9773480953393984104412553 7330110715045488078309415)
            ·
              refine ⟨10995166072568232117464123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330110715045488078309415 10995166072568232117464123)
              ·
                refine ⟨16492749108852348176196185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10995166072568232117464123 16492749108852348176196185)
                ·
                  refine ⟨12369561831639261132147139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16492749108852348176196185 12369561831639261132147139)
                  ·
                    refine ⟨18554342747458891698220709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12369561831639261132147139 18554342747458891698220709)
                    ·
                      refine ⟨3478939265148542193416383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18554342747458891698220709 3478939265148542193416383)
                      ·
                        rfl

theorem cell23_6775210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_6775210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775210 prefixEnd_6775210 := by exact prefixLift 6775210
  have htrace : WordTrace (prefixWord ++ tailWord_6775210) baseStart_6775210 baseEnd_6775210 := by
    simpa [prefixWord, tailWord_6775210, baseEnd_6775210] using wordTrace_append hprefix tailTrace_6775210
  have hstable : (prefixWord ++ tailWord_6775210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775210).length < 2 ^ (prefixWord ++ tailWord_6775210).sum := by decide
  have hdescent : baseEnd_6775210 < baseStart_6775210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775212 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_6775212 : Nat := 118140960795 + 6775212 * 2 ^ 59
def prefixEnd_6775212 : Nat := 4983230072969 + 3 ^ 40 * 6775212 * 2
def baseEnd_6775212 : Nat := 1159646764036617061863791

theorem tailTrace_6775212 : CollatzResearch.WordTrace tailWord_6775212 prefixEnd_6775212 1159646764036617061863791 := by
  unfold tailWord_6775212
  simp only [CollatzResearch.WordTrace]
  refine ⟨123556141365285756466075945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164741521820381008621434593 123556141365285756466075945)
  ·
    refine ⟨92667106023964317349556959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123556141365285756466075945 92667106023964317349556959)
    ·
      refine ⟨139000659035946476024335439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92667106023964317349556959 139000659035946476024335439)
      ·
        refine ⟨208500988553919714036503159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139000659035946476024335439 208500988553919714036503159)
        ·
          refine ⟨312751482830879571054754739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208500988553919714036503159 312751482830879571054754739)
          ·
            refine ⟨469127224246319356582132109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312751482830879571054754739 469127224246319356582132109)
            ·
              refine ⟨175922709092369758718299541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469127224246319356582132109 175922709092369758718299541)
              ·
                refine ⟨8246376988704832439920291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 175922709092369758718299541 8246376988704832439920291)
                ·
                  refine ⟨12369565483057248659880437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8246376988704832439920291 12369565483057248659880437)
                  ·
                    refine ⟨1159646764036617061863791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12369565483057248659880437 1159646764036617061863791)
                    ·
                      rfl

theorem cell23_6775212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_6775212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775212 prefixEnd_6775212 := by exact prefixLift 6775212
  have htrace : WordTrace (prefixWord ++ tailWord_6775212) baseStart_6775212 baseEnd_6775212 := by
    simpa [prefixWord, tailWord_6775212, baseEnd_6775212] using wordTrace_append hprefix tailTrace_6775212
  have hstable : (prefixWord ++ tailWord_6775212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775212).length < 2 ^ (prefixWord ++ tailWord_6775212).sum := by decide
  have hdescent : baseEnd_6775212 < baseStart_6775212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775213 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_6775213 : Nat := 118140960795 + 6775213 * 2 ^ 59
def prefixEnd_6775213 : Nat := 4983230072969 + 3 ^ 40 * 6775213 * 2
def baseEnd_6775213 : Nat := 3478940805590505681678869

theorem tailTrace_6775213 : CollatzResearch.WordTrace tailWord_6775213 prefixEnd_6775213 3478940805590505681678869 := by
  unfold tailWord_6775213
  simp only [CollatzResearch.WordTrace]
  refine ⟨247112319203567890102938293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164741546135711926735292195 247112319203567890102938293)
  ·
    refine ⟨23166779925334489697150465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247112319203567890102938293 23166779925334489697150465)
    ·
      refine ⟨17375084944000867272862849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23166779925334489697150465 17375084944000867272862849)
      ·
        refine ⟨13031313708000650454647137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17375084944000867272862849 13031313708000650454647137)
        ·
          refine ⟨9773485281000487840985353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13031313708000650454647137 9773485281000487840985353)
          ·
            refine ⟨7330113960750365880739015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9773485281000487840985353 7330113960750365880739015)
            ·
              refine ⟨10995170941125548821108523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330113960750365880739015 10995170941125548821108523)
              ·
                refine ⟨16492756411688323231662785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10995170941125548821108523 16492756411688323231662785)
                ·
                  refine ⟨12369567308766242423747089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16492756411688323231662785 12369567308766242423747089)
                  ·
                    refine ⟨9277175481574681817810317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12369567308766242423747089 9277175481574681817810317)
                    ·
                      refine ⟨3478940805590505681678869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9277175481574681817810317 3478940805590505681678869)
                      ·
                        rfl

theorem cell23_6775213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_6775213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775213 prefixEnd_6775213 := by exact prefixLift 6775213
  have htrace : WordTrace (prefixWord ++ tailWord_6775213) baseStart_6775213 baseEnd_6775213 := by
    simpa [prefixWord, tailWord_6775213, baseEnd_6775213] using wordTrace_append hprefix tailTrace_6775213
  have hstable : (prefixWord ++ tailWord_6775213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775213).length < 2 ^ (prefixWord ++ tailWord_6775213).sum := by decide
  have hdescent : baseEnd_6775213 < baseStart_6775213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775229 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_6775229 : Nat := 118140960795 + 6775229 * 2 ^ 59
def prefixEnd_6775229 : Nat := 4983230072969 + 3 ^ 40 * 6775229 * 2
def baseEnd_6775229 : Nat := 1159649673760325873026265

theorem tailTrace_6775229 : CollatzResearch.WordTrace tailWord_6775229 prefixEnd_6775229 1159649673760325873026265 := by
  unfold tailWord_6775229
  simp only [CollatzResearch.WordTrace]
  refine ⟨247112902771509924835520741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164741935181006616557013827 247112902771509924835520741)
  ·
    refine ⟨46333669269658110906660139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247112902771509924835520741 46333669269658110906660139)
    ·
      refine ⟨69500503904487166359990209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46333669269658110906660139 69500503904487166359990209)
      ·
        refine ⟨52125377928365374769992657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69500503904487166359990209 52125377928365374769992657)
        ·
          refine ⟨39094033446274031077494493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52125377928365374769992657 39094033446274031077494493)
          ·
            refine ⟨14660262542352761654060435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39094033446274031077494493 14660262542352761654060435)
            ·
              refine ⟨21990393813529142481090653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14660262542352761654060435 21990393813529142481090653)
              ·
                refine ⟨8246397680073428430408995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21990393813529142481090653 8246397680073428430408995)
                ·
                  refine ⟨12369596520110142645613493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8246397680073428430408995 12369596520110142645613493)
                  ·
                    refine ⟨1159649673760325873026265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12369596520110142645613493 1159649673760325873026265)
                    ·
                      rfl

theorem cell23_6775229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_6775229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775229 prefixEnd_6775229 := by exact prefixLift 6775229
  have htrace : WordTrace (prefixWord ++ tailWord_6775229) baseStart_6775229 baseEnd_6775229 := by
    simpa [prefixWord, tailWord_6775229, baseEnd_6775229] using wordTrace_append hprefix tailTrace_6775229
  have hstable : (prefixWord ++ tailWord_6775229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775229).length < 2 ^ (prefixWord ++ tailWord_6775229).sum := by decide
  have hdescent : baseEnd_6775229 < baseStart_6775229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775272 : List Nat := [2, 1, 4, 1, 1, 4, 1, 9]
def baseStart_6775272 : Nat := 118140960795 + 6775272 * 2 ^ 59
def prefixEnd_6775272 : Nat := 4983230072969 + 3 ^ 40 * 6775272 * 2
def baseEnd_6775272 : Nat := 128850781516634109290411

theorem tailTrace_6775272 : CollatzResearch.WordTrace tailWord_6775272 prefixEnd_6775272 128850781516634109290411 := by
  unfold tailWord_6775272
  simp only [CollatzResearch.WordTrace]
  refine ⟨123557235555177071589668035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164742980740236095452890713 123557235555177071589668035)
  ·
    refine ⟨185335853332765607384502053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123557235555177071589668035 185335853332765607384502053)
    ·
      refine ⟨34750472499893551384594135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185335853332765607384502053 34750472499893551384594135)
      ·
        refine ⟨52125708749840327076891203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34750472499893551384594135 52125708749840327076891203)
        ·
          refine ⟨78188563124760490615336805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52125708749840327076891203 78188563124760490615336805)
          ·
            refine ⟨14660355585892591990375651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78188563124760490615336805 14660355585892591990375651)
            ·
              refine ⟨21990533378838887985563477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14660355585892591990375651 21990533378838887985563477)
              ·
                refine ⟨128850781516634109290411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21990533378838887985563477 128850781516634109290411)
                ·
                  rfl

theorem cell23_6775272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 9].length) (baseStart_6775272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775272 prefixEnd_6775272 := by exact prefixLift 6775272
  have htrace : WordTrace (prefixWord ++ tailWord_6775272) baseStart_6775272 baseEnd_6775272 := by
    simpa [prefixWord, tailWord_6775272, baseEnd_6775272] using wordTrace_append hprefix tailTrace_6775272
  have hstable : (prefixWord ++ tailWord_6775272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775272).length < 2 ^ (prefixWord ++ tailWord_6775272).sum := by decide
  have hdescent : baseEnd_6775272 < baseStart_6775272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775286 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_6775286 : Nat := 118140960795 + 6775286 * 2 ^ 59
def prefixEnd_6775286 : Nat := 4983230072969 + 3 ^ 40 * 6775286 * 2
def baseEnd_6775286 : Nat := 3478978289678283896066033

theorem tailTrace_6775286 : CollatzResearch.WordTrace tailWord_6775286 prefixEnd_6775286 3478978289678283896066033 := by
  unfold tailWord_6775286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15444686358268963973146607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164743321154868949046897141 15444686358268963973146607)
  ·
    refine ⟨23167029537403445959719911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15444686358268963973146607 23167029537403445959719911)
    ·
      refine ⟨34750544306105168939579867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23167029537403445959719911 34750544306105168939579867)
      ·
        refine ⟨52125816459157753409369801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34750544306105168939579867 52125816459157753409369801)
        ·
          refine ⟨39094362344368315057027351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52125816459157753409369801 39094362344368315057027351)
          ·
            refine ⟨58641543516552472585541027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39094362344368315057027351 58641543516552472585541027)
            ·
              refine ⟨87962315274828708878311541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58641543516552472585541027 87962315274828708878311541)
              ·
                refine ⟨8246467057015191457341707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87962315274828708878311541 8246467057015191457341707)
                ·
                  refine ⟨12369700585522787186012561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8246467057015191457341707 12369700585522787186012561)
                  ·
                    refine ⟨9277275439142090389509421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12369700585522787186012561 9277275439142090389509421)
                    ·
                      refine ⟨3478978289678283896066033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9277275439142090389509421 3478978289678283896066033)
                      ·
                        rfl

theorem cell23_6775286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_6775286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775286 prefixEnd_6775286 := by exact prefixLift 6775286
  have htrace : WordTrace (prefixWord ++ tailWord_6775286) baseStart_6775286 baseEnd_6775286 := by
    simpa [prefixWord, tailWord_6775286, baseEnd_6775286] using wordTrace_append hprefix tailTrace_6775286
  have hstable : (prefixWord ++ tailWord_6775286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775286).length < 2 ^ (prefixWord ++ tailWord_6775286).sum := by decide
  have hdescent : baseEnd_6775286 < baseStart_6775286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775299 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 4, 1, 3]
def baseStart_6775299 : Nat := 118140960795 + 6775299 * 2 ^ 59
def prefixEnd_6775299 : Nat := 4983230072969 + 3 ^ 40 * 6775299 * 2
def baseEnd_6775299 : Nat := 3478984964926792345203473

theorem tailTrace_6775299 : CollatzResearch.WordTrace tailWord_6775299 prefixEnd_6775299 3478984964926792345203473 := by
  unfold tailWord_6775299
  simp only [CollatzResearch.WordTrace]
  refine ⟨247115455881256326790568951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164743637254170884527045967 247115455881256326790568951)
  ·
    refine ⟨370673183821884490185853427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247115455881256326790568951 370673183821884490185853427)
    ·
      refine ⟨556009775732826735278780141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370673183821884490185853427 556009775732826735278780141)
      ·
        refine ⟨208503665899810025729542553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 556009775732826735278780141 208503665899810025729542553)
        ·
          refine ⟨156377749424857519297156915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208503665899810025729542553 156377749424857519297156915)
          ·
            refine ⟨234566624137286278945735373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156377749424857519297156915 234566624137286278945735373)
            ·
              refine ⟨87962484051482354604650765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234566624137286278945735373 87962484051482354604650765)
              ·
                refine ⟨32985931519305882976744037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87962484051482354604650765 32985931519305882976744037)
                ·
                  refine ⟨6184862159869853058139507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32985931519305882976744037 6184862159869853058139507)
                  ·
                    refine ⟨9277293239804779587209261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6184862159869853058139507 9277293239804779587209261)
                    ·
                      refine ⟨3478984964926792345203473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9277293239804779587209261 3478984964926792345203473)
                      ·
                        rfl

theorem cell23_6775299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_6775299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775299 prefixEnd_6775299 := by exact prefixLift 6775299
  have htrace : WordTrace (prefixWord ++ tailWord_6775299) baseStart_6775299 baseEnd_6775299 := by
    simpa [prefixWord, tailWord_6775299, baseEnd_6775299] using wordTrace_append hprefix tailTrace_6775299
  have hstable : (prefixWord ++ tailWord_6775299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775299).length < 2 ^ (prefixWord ++ tailWord_6775299).sum := by decide
  have hdescent : baseEnd_6775299 < baseStart_6775299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775300 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_6775300 : Nat := 118140960795 + 6775300 * 2 ^ 59
def prefixEnd_6775300 : Nat := 4983230072969 + 3 ^ 40 * 6775300 * 2
def baseEnd_6775300 : Nat := 3478985478407446841290969

theorem tailTrace_6775300 : CollatzResearch.WordTrace tailWord_6775300 prefixEnd_6775300 3478985478407446841290969 := by
  unfold tailWord_6775300
  simp only [CollatzResearch.WordTrace]
  refine ⟨123557746177126351980677677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164743661569501802640903569 123557746177126351980677677)
  ·
    refine ⟨46334154816422381992754129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123557746177126351980677677 46334154816422381992754129)
    ·
      refine ⟨34750616112316786494565597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46334154816422381992754129 34750616112316786494565597)
      ·
        refine ⟨13031481042118794935462099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34750616112316786494565597 13031481042118794935462099)
        ·
          refine ⟨19547221563178192403193149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13031481042118794935462099 19547221563178192403193149)
          ·
            refine ⟨7330208086191822151197431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19547221563178192403193149 7330208086191822151197431)
            ·
              refine ⟨10995312129287733226796147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330208086191822151197431 10995312129287733226796147)
              ·
                refine ⟨16492968193931599840194221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10995312129287733226796147 16492968193931599840194221)
                ·
                  refine ⟨6184863072724349940072833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16492968193931599840194221 6184863072724349940072833)
                  ·
                    refine ⟨4638647304543262455054625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6184863072724349940072833 4638647304543262455054625)
                    ·
                      refine ⟨3478985478407446841290969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638647304543262455054625 3478985478407446841290969)
                      ·
                        rfl

theorem cell23_6775300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_6775300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775300 prefixEnd_6775300 := by exact prefixLift 6775300
  have htrace : WordTrace (prefixWord ++ tailWord_6775300) baseStart_6775300 baseEnd_6775300 := by
    simpa [prefixWord, tailWord_6775300, baseEnd_6775300] using wordTrace_append hprefix tailTrace_6775300
  have hstable : (prefixWord ++ tailWord_6775300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775300).length < 2 ^ (prefixWord ++ tailWord_6775300).sum := by decide
  have hdescent : baseEnd_6775300 < baseStart_6775300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775350 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_6775350 : Nat := 118140960795 + 6775350 * 2 ^ 59
def prefixEnd_6775350 : Nat := 4983230072969 + 3 ^ 40 * 6775350 * 2
def baseEnd_6775350 : Nat := 3479011152440171645665739

theorem tailTrace_6775350 : CollatzResearch.WordTrace tailWord_6775350 prefixEnd_6775350 3479011152440171645665739 := by
  unfold tailWord_6775350
  simp only [CollatzResearch.WordTrace]
  refine ⟨15444832250254472656292219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164744877336047708333783669 15444832250254472656292219)
  ·
    refine ⟨23167248375381708984438329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15444832250254472656292219 23167248375381708984438329)
    ·
      refine ⟨17375436281536281738328747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23167248375381708984438329 17375436281536281738328747)
      ·
        refine ⟨26063154422304422607493121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17375436281536281738328747 26063154422304422607493121)
        ·
          refine ⟨19547365816728316955619841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26063154422304422607493121 19547365816728316955619841)
          ·
            refine ⟨14660524362546237716714881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19547365816728316955619841 14660524362546237716714881)
            ·
              refine ⟨10995393271909678287536161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14660524362546237716714881 10995393271909678287536161)
              ·
                refine ⟨8246544953932258715652121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10995393271909678287536161 8246544953932258715652121)
                ·
                  refine ⟨6184908715449194036739091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8246544953932258715652121 6184908715449194036739091)
                  ·
                    refine ⟨9277363073173791055108637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6184908715449194036739091 9277363073173791055108637)
                    ·
                      refine ⟨3479011152440171645665739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9277363073173791055108637 3479011152440171645665739)
                      ·
                        rfl

theorem cell23_6775350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_6775350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775350 prefixEnd_6775350 := by exact prefixLift 6775350
  have htrace : WordTrace (prefixWord ++ tailWord_6775350) baseStart_6775350 baseEnd_6775350 := by
    simpa [prefixWord, tailWord_6775350, baseEnd_6775350] using wordTrace_append hprefix tailTrace_6775350
  have hstable : (prefixWord ++ tailWord_6775350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775350).length < 2 ^ (prefixWord ++ tailWord_6775350).sum := by decide
  have hdescent : baseEnd_6775350 < baseStart_6775350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775366 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_6775366 : Nat := 118140960795 + 6775366 * 2 ^ 59
def prefixEnd_6775366 : Nat := 4983230072969 + 3 ^ 40 * 6775366 * 2
def baseEnd_6775366 : Nat := 1159673122710214527688555

theorem tailTrace_6775366 : CollatzResearch.WordTrace tailWord_6775366 prefixEnd_6775366 1159673122710214527688555 := by
  unfold tailWord_6775366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7722434361625424913539311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 164745266381342398155505301 7722434361625424913539311)
  ·
    refine ⟨11583651542438137370308967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7722434361625424913539311 11583651542438137370308967)
    ·
      refine ⟨17375477313657206055463451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11583651542438137370308967 17375477313657206055463451)
      ·
        refine ⟨26063215970485809083195177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17375477313657206055463451 26063215970485809083195177)
        ·
          refine ⟨19547411977864356812396383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26063215970485809083195177 19547411977864356812396383)
          ·
            refine ⟨29321117966796535218594575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19547411977864356812396383 29321117966796535218594575)
            ·
              refine ⟨43981676950194802827891863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29321117966796535218594575 43981676950194802827891863)
              ·
                refine ⟨65972515425292204241837795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43981676950194802827891863 65972515425292204241837795)
                ·
                  refine ⟨98958773137938306362756693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65972515425292204241837795 98958773137938306362756693)
                  ·
                    refine ⟨1159673122710214527688555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98958773137938306362756693 1159673122710214527688555)
                    ·
                      rfl

theorem cell23_6775366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_6775366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775366 prefixEnd_6775366 := by exact prefixLift 6775366
  have htrace : WordTrace (prefixWord ++ tailWord_6775366) baseStart_6775366 baseEnd_6775366 := by
    simpa [prefixWord, tailWord_6775366, baseEnd_6775366] using wordTrace_append hprefix tailTrace_6775366
  have hstable : (prefixWord ++ tailWord_6775366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775366).length < 2 ^ (prefixWord ++ tailWord_6775366).sum := by decide
  have hdescent : baseEnd_6775366 < baseStart_6775366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775373 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_6775373 : Nat := 118140960795 + 6775373 * 2 ^ 59
def prefixEnd_6775373 : Nat := 4983230072969 + 3 ^ 40 * 6775373 * 2
def baseEnd_6775373 : Nat := 3479022962495225055678133

theorem tailTrace_6775373 : CollatzResearch.WordTrace tailWord_6775373 prefixEnd_6775373 3479022962495225055678133 := by
  unfold tailWord_6775373
  simp only [CollatzResearch.WordTrace]
  refine ⟨247118154882988237428762773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164745436588658824952508515 247118154882988237428762773)
  ·
    refine ⟨11583663510140073629473255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 247118154882988237428762773 11583663510140073629473255)
    ·
      refine ⟨17375495265210110444209883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11583663510140073629473255 17375495265210110444209883)
      ·
        refine ⟨26063242897815165666314825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17375495265210110444209883 26063242897815165666314825)
        ·
          refine ⟨19547432173361374249736119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26063242897815165666314825 19547432173361374249736119)
          ·
            refine ⟨29321148260042061374604179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19547432173361374249736119 29321148260042061374604179)
            ·
              refine ⟨43981722390063092061906269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29321148260042061374604179 43981722390063092061906269)
              ·
                refine ⟨16493145896273659523214851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43981722390063092061906269 16493145896273659523214851)
                ·
                  refine ⟨24739718844410489284822277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16493145896273659523214851 24739718844410489284822277)
                  ·
                    refine ⟨4638697283326966740904177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24739718844410489284822277 4638697283326966740904177)
                    ·
                      refine ⟨3479022962495225055678133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638697283326966740904177 3479022962495225055678133)
                      ·
                        rfl

theorem cell23_6775373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_6775373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775373 prefixEnd_6775373 := by exact prefixLift 6775373
  have htrace : WordTrace (prefixWord ++ tailWord_6775373) baseStart_6775373 baseEnd_6775373 := by
    simpa [prefixWord, tailWord_6775373, baseEnd_6775373] using wordTrace_append hprefix tailTrace_6775373
  have hstable : (prefixWord ++ tailWord_6775373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775373).length < 2 ^ (prefixWord ++ tailWord_6775373).sum := by decide
  have hdescent : baseEnd_6775373 < baseStart_6775373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775394 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6775394 : Nat := 118140960795 + 6775394 * 2 ^ 59
def prefixEnd_6775394 : Nat := 4983230072969 + 3 ^ 40 * 6775394 * 2
def baseEnd_6775394 : Nat := 3479033745588969473515537

theorem tailTrace_6775394 : CollatzResearch.WordTrace tailWord_6775394 prefixEnd_6775394 3479033745588969473515537 := by
  unfold tailWord_6775394
  simp only [CollatzResearch.WordTrace]
  refine ⟨61779730203978039503819309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164745947210608105343518157 61779730203978039503819309)
  ·
    refine ⟨23167398826491764813932241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61779730203978039503819309 23167398826491764813932241)
    ·
      refine ⟨17375549119868823610449181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23167398826491764813932241 17375549119868823610449181)
      ·
        refine ⟨6515830919950808853918443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17375549119868823610449181 6515830919950808853918443)
        ·
          refine ⟨9773746379926213280877665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515830919950808853918443 9773746379926213280877665)
          ·
            refine ⟨7330309784944659960658249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9773746379926213280877665 7330309784944659960658249)
            ·
              refine ⟨5497732338708494970493687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7330309784944659960658249 5497732338708494970493687)
              ·
                refine ⟨8246598508062742455740531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5497732338708494970493687 8246598508062742455740531)
                ·
                  refine ⟨12369897762094113683610797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8246598508062742455740531 12369897762094113683610797)
                  ·
                    refine ⟨4638711660785292631354049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12369897762094113683610797 4638711660785292631354049)
                    ·
                      refine ⟨3479033745588969473515537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638711660785292631354049 3479033745588969473515537)
                      ·
                        rfl

theorem cell23_6775394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6775394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775394 prefixEnd_6775394 := by exact prefixLift 6775394
  have htrace : WordTrace (prefixWord ++ tailWord_6775394) baseStart_6775394 baseEnd_6775394 := by
    simpa [prefixWord, tailWord_6775394, baseEnd_6775394] using wordTrace_append hprefix tailTrace_6775394
  have hstable : (prefixWord ++ tailWord_6775394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775394).length < 2 ^ (prefixWord ++ tailWord_6775394).sum := by decide
  have hdescent : baseEnd_6775394 < baseStart_6775394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775396 : List Nat := [2, 3, 1, 1, 2, 2, 4, 3, 5]
def baseStart_6775396 : Nat := 118140960795 + 6775396 * 2 ^ 59
def prefixEnd_6775396 : Nat := 4983230072969 + 3 ^ 40 * 6775396 * 2
def baseEnd_6775396 : Nat := 386559419172253162854503

theorem tailTrace_6775396 : CollatzResearch.WordTrace tailWord_6775396 prefixEnd_6775396 386559419172253162854503 := by
  unfold tailWord_6775396
  simp only [CollatzResearch.WordTrace]
  refine ⟨123559496880952456178425021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164745995841269941571233361 123559496880952456178425021)
  ·
    refine ⟨46334811330357171066909383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123559496880952456178425021 46334811330357171066909383)
    ·
      refine ⟨69502216995535756600364075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46334811330357171066909383 69502216995535756600364075)
      ·
        refine ⟨104253325493303634900546113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69502216995535756600364075 104253325493303634900546113)
        ·
          refine ⟨78189994119977726175409585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104253325493303634900546113 78189994119977726175409585)
          ·
            refine ⟨58642495589983294631557189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78189994119977726175409585 58642495589983294631557189)
            ·
              refine ⟨10995467923121867743416973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58642495589983294631557189 10995467923121867743416973)
              ·
                refine ⟨4123300471170700403781365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10995467923121867743416973 4123300471170700403781365)
                ·
                  refine ⟨386559419172253162854503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4123300471170700403781365 386559419172253162854503)
                  ·
                    rfl

theorem cell23_6775396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_6775396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775396 prefixEnd_6775396 := by exact prefixLift 6775396
  have htrace : WordTrace (prefixWord ++ tailWord_6775396) baseStart_6775396 baseEnd_6775396 := by
    simpa [prefixWord, tailWord_6775396, baseEnd_6775396] using wordTrace_append hprefix tailTrace_6775396
  have hstable : (prefixWord ++ tailWord_6775396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775396).length < 2 ^ (prefixWord ++ tailWord_6775396).sum := by decide
  have hdescent : baseEnd_6775396 < baseStart_6775396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775406 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_6775406 : Nat := 118140960795 + 6775406 * 2 ^ 59
def prefixEnd_6775406 : Nat := 4983230072969 + 3 ^ 40 * 6775406 * 2
def baseEnd_6775406 : Nat := 3479039907356823426565481

theorem tailTrace_6775406 : CollatzResearch.WordTrace tailWord_6775406 prefixEnd_6775406 3479039907356823426565481 := by
  unfold tailWord_6775406
  simp only [CollatzResearch.WordTrace]
  refine ⟨30889919811483585508089259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164746238994579122709809381 30889919811483585508089259)
  ·
    refine ⟨46334879717225378262133889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30889919811483585508089259 46334879717225378262133889)
    ·
      refine ⟨34751159787919033696600417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46334879717225378262133889 34751159787919033696600417)
      ·
        refine ⟨26063369840939275272450313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34751159787919033696600417 26063369840939275272450313)
        ·
          refine ⟨19547527380704456454337735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26063369840939275272450313 19547527380704456454337735)
          ·
            refine ⟨29321291071056684681506603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19547527380704456454337735 29321291071056684681506603)
            ·
              refine ⟨43981936606585027022259905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29321291071056684681506603 43981936606585027022259905)
              ·
                refine ⟨32986452454938770266694929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43981936606585027022259905 32986452454938770266694929)
                ·
                  refine ⟨24739839341204077700021197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32986452454938770266694929 24739839341204077700021197)
                  ·
                    refine ⟨9277439752951529137507949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24739839341204077700021197 9277439752951529137507949)
                    ·
                      refine ⟨3479039907356823426565481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9277439752951529137507949 3479039907356823426565481)
                      ·
                        rfl

theorem cell23_6775406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_6775406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775406 prefixEnd_6775406 := by exact prefixLift 6775406
  have htrace : WordTrace (prefixWord ++ tailWord_6775406) baseStart_6775406 baseEnd_6775406 := by
    simpa [prefixWord, tailWord_6775406, baseEnd_6775406] using wordTrace_append hprefix tailTrace_6775406
  have hstable : (prefixWord ++ tailWord_6775406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775406).length < 2 ^ (prefixWord ++ tailWord_6775406).sum := by decide
  have hdescent : baseEnd_6775406 < baseStart_6775406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775429 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_6775429 : Nat := 118140960795 + 6775429 * 2 ^ 59
def prefixEnd_6775429 : Nat := 4983230072969 + 3 ^ 40 * 6775429 * 2
def baseEnd_6775429 : Nat := 3479051717411876836577875

theorem tailTrace_6775429 : CollatzResearch.WordTrace tailWord_6775429 prefixEnd_6775429 3479051717411876836577875 := by
  unfold tailWord_6775429
  simp only [CollatzResearch.WordTrace]
  refine ⟨247120197370785358992801341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164746798247190239328534227 247120197370785358992801341)
  ·
    refine ⟨92670074014044509622300503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247120197370785358992801341 92670074014044509622300503)
    ·
      refine ⟨139005111021066764433450755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92670074014044509622300503 139005111021066764433450755)
      ·
        refine ⟨208507666531600146650176133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139005111021066764433450755 208507666531600146650176133)
        ·
          refine ⟨39095187474675027496908025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208507666531600146650176133 39095187474675027496908025)
          ·
            refine ⟨29321390606006270622681019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39095187474675027496908025 29321390606006270622681019)
            ·
              refine ⟨43982085909009405934021529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29321390606006270622681019 43982085909009405934021529)
              ·
                refine ⟨32986564431757054450516147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43982085909009405934021529 32986564431757054450516147)
                ·
                  refine ⟨49479846647635581675774221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32986564431757054450516147 49479846647635581675774221)
                  ·
                    refine ⟨18554942492863343128415333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49479846647635581675774221 18554942492863343128415333)
                    ·
                      refine ⟨3479051717411876836577875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18554942492863343128415333 3479051717411876836577875)
                      ·
                        rfl

theorem cell23_6775429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_6775429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775429 prefixEnd_6775429 := by exact prefixLift 6775429
  have htrace : WordTrace (prefixWord ++ tailWord_6775429) baseStart_6775429 baseEnd_6775429 := by
    simpa [prefixWord, tailWord_6775429, baseEnd_6775429] using wordTrace_append hprefix tailTrace_6775429
  have hstable : (prefixWord ++ tailWord_6775429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775429).length < 2 ^ (prefixWord ++ tailWord_6775429).sum := by decide
  have hdescent : baseEnd_6775429 < baseStart_6775429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775449 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 1, 4, 3]
def baseStart_6775449 : Nat := 118140960795 + 6775449 * 2 ^ 59
def prefixEnd_6775449 : Nat := 4983230072969 + 3 ^ 40 * 6775449 * 2
def baseEnd_6775449 : Nat := 3479061987024966758327783

theorem tailTrace_6775449 : CollatzResearch.WordTrace tailWord_6775449 prefixEnd_6775449 3479061987024966758327783 := by
  unfold tailWord_6775449
  simp only [CollatzResearch.WordTrace]
  refine ⟨247120926830712902408529401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164747284553808601605686267 247120926830712902408529401)
  ·
    refine ⟨185340695123034676806397051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247120926830712902408529401 185340695123034676806397051)
    ·
      refine ⟨278011042684552015209595577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185340695123034676806397051 278011042684552015209595577)
      ·
        refine ⟨208508282013414011407196683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278011042684552015209595577 208508282013414011407196683)
        ·
          refine ⟨312762423020121017110795025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208508282013414011407196683 312762423020121017110795025)
          ·
            refine ⟨234571817265090762833096269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312762423020121017110795025 234571817265090762833096269)
            ·
              refine ⟨87964431474409036062411101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234571817265090762833096269 87964431474409036062411101)
              ·
                refine ⟨32986661802903388523404163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87964431474409036062411101 32986661802903388523404163)
                ·
                  refine ⟨49479992704355082785106245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32986661802903388523404163 49479992704355082785106245)
                  ·
                    refine ⟨9277498632066578022207421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49479992704355082785106245 9277498632066578022207421)
                    ·
                      refine ⟨3479061987024966758327783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9277498632066578022207421 3479061987024966758327783)
                      ·
                        rfl

theorem cell23_6775449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_6775449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775449 prefixEnd_6775449 := by exact prefixLift 6775449
  have htrace : WordTrace (prefixWord ++ tailWord_6775449) baseStart_6775449 baseEnd_6775449 := by
    simpa [prefixWord, tailWord_6775449, baseEnd_6775449] using wordTrace_append hprefix tailTrace_6775449
  have hstable : (prefixWord ++ tailWord_6775449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775449).length < 2 ^ (prefixWord ++ tailWord_6775449).sum := by decide
  have hdescent : baseEnd_6775449 < baseStart_6775449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775486 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_6775486 : Nat := 118140960795 + 6775486 * 2 ^ 59
def prefixEnd_6775486 : Nat := 4983230072969 + 3 ^ 40 * 6775486 * 2
def baseEnd_6775486 : Nat := 386564553978798123729457

theorem tailTrace_6775486 : CollatzResearch.WordTrace tailWord_6775486 prefixEnd_6775486 386564553978798123729457 := by
  unfold tailWord_6775486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30890284541447357215953289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164748184221052571818417541 30890284541447357215953289)
  ·
    refine ⟨23167713406085517911964967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30890284541447357215953289 23167713406085517911964967)
    ·
      refine ⟨34751570109128276867947451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23167713406085517911964967 34751570109128276867947451)
      ·
        refine ⟨52127355163692415301921177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34751570109128276867947451 52127355163692415301921177)
        ·
          refine ⟨39095516372769311476440883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52127355163692415301921177 39095516372769311476440883)
          ·
            refine ⟨58643274559153967214661325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39095516372769311476440883 58643274559153967214661325)
            ·
              refine ⟨21991227959682737705497997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58643274559153967214661325 21991227959682737705497997)
              ·
                refine ⟨8246710484881026639561749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21991227959682737705497997 8246710484881026639561749)
                ·
                  refine ⟨386564553978798123729457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8246710484881026639561749 386564553978798123729457)
                  ·
                    rfl

theorem cell23_6775486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_6775486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775486 prefixEnd_6775486 := by exact prefixLift 6775486
  have htrace : WordTrace (prefixWord ++ tailWord_6775486) baseStart_6775486 baseEnd_6775486 := by
    simpa [prefixWord, tailWord_6775486, baseEnd_6775486] using wordTrace_append hprefix tailTrace_6775486
  have hstable : (prefixWord ++ tailWord_6775486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775486).length < 2 ^ (prefixWord ++ tailWord_6775486).sum := by decide
  have hdescent : baseEnd_6775486 < baseStart_6775486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775539 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 5]
def baseStart_6775539 : Nat := 118140960795 + 6775539 * 2 ^ 59
def prefixEnd_6775539 : Nat := 4983230072969 + 3 ^ 40 * 6775539 * 2
def baseEnd_6775539 : Nat := 3479108200283871406202369

theorem tailTrace_6775539 : CollatzResearch.WordTrace tailWord_6775539 prefixEnd_6775539 3479108200283871406202369 := by
  unfold tailWord_6775539
  simp only [CollatzResearch.WordTrace]
  refine ⟨247124209400386847779305671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164749472933591231852870447 247124209400386847779305671)
  ·
    refine ⟨370686314100580271668958507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247124209400386847779305671 370686314100580271668958507)
    ·
      refine ⟨556029471150870407503437761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370686314100580271668958507 556029471150870407503437761)
      ·
        refine ⟨417022103363152805627578321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556029471150870407503437761 417022103363152805627578321)
        ·
          refine ⟨312766577522364604220683741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417022103363152805627578321 312766577522364604220683741)
          ·
            refine ⟨117287466570886726582756403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312766577522364604220683741 117287466570886726582756403)
            ·
              refine ⟨175931199856330089874134605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117287466570886726582756403 175931199856330089874134605)
              ·
                refine ⟨65974199946123783702800477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175931199856330089874134605 65974199946123783702800477)
                ·
                  refine ⟨24740324979796418888550179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65974199946123783702800477 24740324979796418888550179)
                  ·
                    refine ⟨37110487469694628332825269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24740324979796418888550179 37110487469694628332825269)
                    ·
                      refine ⟨3479108200283871406202369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37110487469694628332825269 3479108200283871406202369)
                      ·
                        rfl

theorem cell23_6775539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_6775539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775539 prefixEnd_6775539 := by exact prefixLift 6775539
  have htrace : WordTrace (prefixWord ++ tailWord_6775539) baseStart_6775539 baseEnd_6775539 := by
    simpa [prefixWord, tailWord_6775539, baseEnd_6775539] using wordTrace_append hprefix tailTrace_6775539
  have hstable : (prefixWord ++ tailWord_6775539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775539).length < 2 ^ (prefixWord ++ tailWord_6775539).sum := by decide
  have hdescent : baseEnd_6775539 < baseStart_6775539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775573 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_6775573 : Nat := 118140960795 + 6775573 * 2 ^ 59
def prefixEnd_6775573 : Nat := 4983230072969 + 3 ^ 40 * 6775573 * 2
def baseEnd_6775573 : Nat := 3479125658626124273177213

theorem tailTrace_6775573 : CollatzResearch.WordTrace tailWord_6775573 prefixEnd_6775573 3479125658626124273177213 := by
  unfold tailWord_6775573
  simp only [CollatzResearch.WordTrace]
  refine ⟨247125449482263671586043373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164750299654842447724028915 247125449482263671586043373)
  ·
    refine ⟨92672043555848876844766265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247125449482263671586043373 92672043555848876844766265)
    ·
      refine ⟨69504032666886657633574699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92672043555848876844766265 69504032666886657633574699)
      ·
        refine ⟨104256049000329986450362049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69504032666886657633574699 104256049000329986450362049)
        ·
          refine ⟨78192036750247489837771537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104256049000329986450362049 78192036750247489837771537)
          ·
            refine ⟨58644027562685617378328653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78192036750247489837771537 58644027562685617378328653)
            ·
              refine ⟨21991510336007106516873245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58644027562685617378328653 21991510336007106516873245)
              ·
                refine ⟨8246816376002664943827467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21991510336007106516873245 8246816376002664943827467)
                ·
                  refine ⟨12370224564003997415741201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8246816376002664943827467 12370224564003997415741201)
                  ·
                    refine ⟨9277668423002998061805901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12370224564003997415741201 9277668423002998061805901)
                    ·
                      refine ⟨3479125658626124273177213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9277668423002998061805901 3479125658626124273177213)
                      ·
                        rfl

theorem cell23_6775573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_6775573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775573 prefixEnd_6775573 := by exact prefixLift 6775573
  have htrace : WordTrace (prefixWord ++ tailWord_6775573) baseStart_6775573 baseEnd_6775573 := by
    simpa [prefixWord, tailWord_6775573, baseEnd_6775573] using wordTrace_append hprefix tailTrace_6775573
  have hstable : (prefixWord ++ tailWord_6775573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775573).length < 2 ^ (prefixWord ++ tailWord_6775573).sum := by decide
  have hdescent : baseEnd_6775573 < baseStart_6775573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775580 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_6775580 : Nat := 118140960795 + 6775580 * 2 ^ 59
def prefixEnd_6775580 : Nat := 4983230072969 + 3 ^ 40 * 6775580 * 2
def baseEnd_6775580 : Nat := 1159709750996901915263227

theorem tailTrace_6775580 : CollatzResearch.WordTrace tailWord_6775580 prefixEnd_6775580 1159709750996901915263227 := by
  unfold tailWord_6775580
  simp only [CollatzResearch.WordTrace]
  refine ⟨123562852396619155890774097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164750469862158874521032129 123562852396619155890774097)
  ·
    refine ⟨92672139297464366918080573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123562852396619155890774097 92672139297464366918080573)
    ·
      refine ⟨34752052236549137594280215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92672139297464366918080573 34752052236549137594280215)
      ·
        refine ⟨52128078354823706391420323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34752052236549137594280215 52128078354823706391420323)
        ·
          refine ⟨78192117532235559587130485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52128078354823706391420323 78192117532235559587130485)
          ·
            refine ⟨7330511018647083711293483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78192117532235559587130485 7330511018647083711293483)
            ·
              refine ⟨10995766527970625566940225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330511018647083711293483 10995766527970625566940225)
              ·
                refine ⟨8246824895977969175205169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10995766527970625566940225 8246824895977969175205169)
                ·
                  refine ⟨6185118671983476881403877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8246824895977969175205169 6185118671983476881403877)
                  ·
                    refine ⟨1159709750996901915263227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6185118671983476881403877 1159709750996901915263227)
                    ·
                      rfl

theorem cell23_6775580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_6775580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775580 prefixEnd_6775580 := by exact prefixLift 6775580
  have htrace : WordTrace (prefixWord ++ tailWord_6775580) baseStart_6775580 baseEnd_6775580 := by
    simpa [prefixWord, tailWord_6775580, baseEnd_6775580] using wordTrace_append hprefix tailTrace_6775580
  have hstable : (prefixWord ++ tailWord_6775580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775580).length < 2 ^ (prefixWord ++ tailWord_6775580).sum := by decide
  have hdescent : baseEnd_6775580 < baseStart_6775580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775597 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_6775597 : Nat := 118140960795 + 6775597 * 2 ^ 59
def prefixEnd_6775597 : Nat := 4983230072969 + 3 ^ 40 * 6775597 * 2
def baseEnd_6775597 : Nat := 1159712660720610726425701

theorem tailTrace_6775597 : CollatzResearch.WordTrace tailWord_6775597 prefixEnd_6775597 1159712660720610726425701 := by
  unfold tailWord_6775597
  simp only [CollatzResearch.WordTrace]
  refine ⟨247126324834176723684917045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164750883222784482456611363 247126324834176723684917045)
  ·
    refine ⟨23168092953204067845460973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247126324834176723684917045 23168092953204067845460973)
    ·
      refine ⟨8688034857451525442047865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23168092953204067845460973 8688034857451525442047865)
      ·
        refine ⟨6516026143088644081535899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8688034857451525442047865 6516026143088644081535899)
        ·
          refine ⟨9774039214632966122303849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6516026143088644081535899 9774039214632966122303849)
          ·
            refine ⟨7330529410974724591727887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9774039214632966122303849 7330529410974724591727887)
            ·
              refine ⟨10995794116462086887591831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330529410974724591727887 10995794116462086887591831)
              ·
                refine ⟨16493691174693130331387747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10995794116462086887591831 16493691174693130331387747)
                ·
                  refine ⟨24740536762039695497081621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16493691174693130331387747 24740536762039695497081621)
                  ·
                    refine ⟨1159712660720610726425701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24740536762039695497081621 1159712660720610726425701)
                    ·
                      rfl

theorem cell23_6775597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_6775597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775597 prefixEnd_6775597 := by exact prefixLift 6775597
  have htrace : WordTrace (prefixWord ++ tailWord_6775597) baseStart_6775597 baseEnd_6775597 := by
    simpa [prefixWord, tailWord_6775597, baseEnd_6775597] using wordTrace_append hprefix tailTrace_6775597
  have hstable : (prefixWord ++ tailWord_6775597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775597).length < 2 ^ (prefixWord ++ tailWord_6775597).sum := by decide
  have hdescent : baseEnd_6775597 < baseStart_6775597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775599 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_6775599 : Nat := 118140960795 + 6775599 * 2 ^ 59
def prefixEnd_6775599 : Nat := 4983230072969 + 3 ^ 40 * 6775599 * 2
def baseEnd_6775599 : Nat := 3479139009123141171452093

theorem tailTrace_6775599 : CollatzResearch.WordTrace tailWord_6775599 prefixEnd_6775599 3479139009123141171452093 := by
  unfold tailWord_6775599
  simp only [CollatzResearch.WordTrace]
  refine ⟨247126397780169478026489851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164750931853446318684326567 247126397780169478026489851)
  ·
    refine ⟨370689596670254217039734777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247126397780169478026489851 370689596670254217039734777)
    ·
      refine ⟨278017197502690662779801083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370689596670254217039734777 278017197502690662779801083)
      ·
        refine ⟨417025796254035994169701625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278017197502690662779801083 417025796254035994169701625)
        ·
          refine ⟨312769347190526995627276219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417025796254035994169701625 312769347190526995627276219)
          ·
            refine ⟨469154020785790493440914329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312769347190526995627276219 469154020785790493440914329)
            ·
              refine ⟨351865515589342870080685747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469154020785790493440914329 351865515589342870080685747)
              ·
                refine ⟨527798273384014305121028621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351865515589342870080685747 527798273384014305121028621)
                ·
                  refine ⟨197924352519005364420385733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527798273384014305121028621 197924352519005364420385733)
                  ·
                    refine ⟨37110816097313505828822325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197924352519005364420385733 37110816097313505828822325)
                    ·
                      refine ⟨3479139009123141171452093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37110816097313505828822325 3479139009123141171452093)
                      ·
                        rfl

theorem cell23_6775599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_6775599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775599 prefixEnd_6775599 := by exact prefixLift 6775599
  have htrace : WordTrace (prefixWord ++ tailWord_6775599) baseStart_6775599 baseEnd_6775599 := by
    simpa [prefixWord, tailWord_6775599, baseEnd_6775599] using wordTrace_append hprefix tailTrace_6775599
  have hstable : (prefixWord ++ tailWord_6775599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775599).length < 2 ^ (prefixWord ++ tailWord_6775599).sum := by decide
  have hdescent : baseEnd_6775599 < baseStart_6775599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775603 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 3]
def baseStart_6775603 : Nat := 118140960795 + 6775603 * 2 ^ 59
def prefixEnd_6775603 : Nat := 4983230072969 + 3 ^ 40 * 6775603 * 2
def baseEnd_6775603 : Nat := 3479141063045759155802075

theorem tailTrace_6775603 : CollatzResearch.WordTrace tailWord_6775603 prefixEnd_6775603 3479141063045759155802075 := by
  unfold tailWord_6775603
  simp only [CollatzResearch.WordTrace]
  refine ⟨247126543672154986709635463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164751029114769991139756975 247126543672154986709635463)
  ·
    refine ⟨370689815508232480064453195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247126543672154986709635463 370689815508232480064453195)
    ·
      refine ⟨556034723262348720096679793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370689815508232480064453195 556034723262348720096679793)
      ·
        refine ⟨417026042446761540072509845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556034723262348720096679793 417026042446761540072509845)
        ·
          refine ⟨19548095739691947190898899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 417026042446761540072509845 19548095739691947190898899)
          ·
            refine ⟨29322143609537920786348349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19548095739691947190898899 29322143609537920786348349)
            ·
              refine ⟨10995803853576720294880631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29322143609537920786348349 10995803853576720294880631)
              ·
                refine ⟨16493705780365080442320947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10995803853576720294880631 16493705780365080442320947)
                ·
                  refine ⟨24740558670547620663481421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16493705780365080442320947 24740558670547620663481421)
                  ·
                    refine ⟨9277709501455357748805533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24740558670547620663481421 9277709501455357748805533)
                    ·
                      refine ⟨3479141063045759155802075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9277709501455357748805533 3479141063045759155802075)
                      ·
                        rfl

theorem cell23_6775603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 3].length) (baseStart_6775603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775603 prefixEnd_6775603 := by exact prefixLift 6775603
  have htrace : WordTrace (prefixWord ++ tailWord_6775603) baseStart_6775603 baseEnd_6775603 := by
    simpa [prefixWord, tailWord_6775603, baseEnd_6775603] using wordTrace_append hprefix tailTrace_6775603
  have hstable : (prefixWord ++ tailWord_6775603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775603).length < 2 ^ (prefixWord ++ tailWord_6775603).sum := by decide
  have hdescent : baseEnd_6775603 < baseStart_6775603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775610 : List Nat := [3, 1, 1, 1, 7, 1, 2, 7]
def baseStart_6775610 : Nat := 118140960795 + 6775610 * 2 ^ 59
def prefixEnd_6775610 : Nat := 4983230072969 + 3 ^ 40 * 6775610 * 2
def baseEnd_6775610 : Nat := 128857209533716319570909

theorem tailTrace_6775610 : CollatzResearch.WordTrace tailWord_6775610 prefixEnd_6775610 128857209533716319570909 := by
  unfold tailWord_6775610
  simp only [CollatzResearch.WordTrace]
  refine ⟨61781699745782406726285071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164751199322086417936760189 61781699745782406726285071)
  ·
    refine ⟨92672549618673610089427607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61781699745782406726285071 92672549618673610089427607)
    ·
      refine ⟨139008824428010415134141411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92672549618673610089427607 139008824428010415134141411)
      ·
        refine ⟨208513236642015622701212117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139008824428010415134141411 208513236642015622701212117)
        ·
          refine ⟨4887028983797241157059659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 208513236642015622701212117 4887028983797241157059659)
          ·
            refine ⟨7330543475695861735589489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887028983797241157059659 7330543475695861735589489)
            ·
              refine ⟨5497907606771896301692117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7330543475695861735589489 5497907606771896301692117)
              ·
                refine ⟨128857209533716319570909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5497907606771896301692117 128857209533716319570909)
                ·
                  rfl

theorem cell23_6775610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 7].length) (baseStart_6775610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775610 prefixEnd_6775610 := by exact prefixLift 6775610
  have htrace : WordTrace (prefixWord ++ tailWord_6775610) baseStart_6775610 baseEnd_6775610 := by
    simpa [prefixWord, tailWord_6775610, baseEnd_6775610] using wordTrace_append hprefix tailTrace_6775610
  have hstable : (prefixWord ++ tailWord_6775610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775610).length < 2 ^ (prefixWord ++ tailWord_6775610).sum := by decide
  have hdescent : baseEnd_6775610 < baseStart_6775610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775666 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 7]
def baseStart_6775666 : Nat := 118140960795 + 6775666 * 2 ^ 59
def prefixEnd_6775666 : Nat := 4983230072969 + 3 ^ 40 * 6775666 * 2
def baseEnd_6775666 : Nat := 386574823591888045479365

theorem tailTrace_6775666 : CollatzResearch.WordTrace tailWord_6775666 prefixEnd_6775666 386574823591888045479365 := by
  unfold tailWord_6775666
  simp only [CollatzResearch.WordTrace]
  refine ⟨61782210367731687117294713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164752560980617832312785901 61782210367731687117294713)
  ·
    refine ⟨46336657775798765337971035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61782210367731687117294713 46336657775798765337971035)
    ·
      refine ⟨69504986663698148006956553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46336657775798765337971035 69504986663698148006956553)
      ·
        refine ⟨52128739997773611005217415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69504986663698148006956553 52128739997773611005217415)
        ·
          refine ⟨78193109996660416507826123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52128739997773611005217415 78193109996660416507826123)
          ·
            refine ⟨117289664994990624761739185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78193109996660416507826123 117289664994990624761739185)
            ·
              refine ⟨87967248746242968571304389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117289664994990624761739185 87967248746242968571304389)
              ·
                refine ⟨16493859139920556607119573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87967248746242968571304389 16493859139920556607119573)
                ·
                  refine ⟨386574823591888045479365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16493859139920556607119573 386574823591888045479365)
                  ·
                    rfl

theorem cell23_6775666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_6775666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775666 prefixEnd_6775666 := by exact prefixLift 6775666
  have htrace : WordTrace (prefixWord ++ tailWord_6775666) baseStart_6775666 baseEnd_6775666 := by
    simpa [prefixWord, tailWord_6775666, baseEnd_6775666] using wordTrace_append hprefix tailTrace_6775666
  have hstable : (prefixWord ++ tailWord_6775666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775666).length < 2 ^ (prefixWord ++ tailWord_6775666).sum := by decide
  have hdescent : baseEnd_6775666 < baseStart_6775666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775683 : List Nat := [1, 1, 1, 3, 4, 1, 2, 5, 5]
def baseStart_6775683 : Nat := 118140960795 + 6775683 * 2 ^ 59
def prefixEnd_6775683 : Nat := 4983230072969 + 3 ^ 40 * 6775683 * 2
def baseEnd_6775683 : Nat := 386575793499790982533523

theorem tailTrace_6775683 : CollatzResearch.WordTrace tailWord_6775683 prefixEnd_6775683 386575793499790982533523 := by
  unfold tailWord_6775683
  simp only [CollatzResearch.WordTrace]
  refine ⟨247129461511865160372547703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164752974341243440248365135 247129461511865160372547703)
  ·
    refine ⟨370694192267797740558821555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247129461511865160372547703 370694192267797740558821555)
    ·
      refine ⟨556041288401696610838232333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370694192267797740558821555 556041288401696610838232333)
      ·
        refine ⟨208515483150636229064337125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 556041288401696610838232333 208515483150636229064337125)
        ·
          refine ⟨39096653090744292949563211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208515483150636229064337125 39096653090744292949563211)
          ·
            refine ⟨58644979636116439424344817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39096653090744292949563211 58644979636116439424344817)
            ·
              refine ⟨43983734727087329568258613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58644979636116439424344817 43983734727087329568258613)
              ·
                refine ⟨4123475130664437147024245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43983734727087329568258613 4123475130664437147024245)
                ·
                  refine ⟨386575793499790982533523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4123475130664437147024245 386575793499790982533523)
                  ·
                    rfl

theorem cell23_6775683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 5].length) (baseStart_6775683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775683 prefixEnd_6775683 := by exact prefixLift 6775683
  have htrace : WordTrace (prefixWord ++ tailWord_6775683) baseStart_6775683 baseEnd_6775683 := by
    simpa [prefixWord, tailWord_6775683, baseEnd_6775683] using wordTrace_append hprefix tailTrace_6775683
  have hstable : (prefixWord ++ tailWord_6775683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775683).length < 2 ^ (prefixWord ++ tailWord_6775683).sum := by decide
  have hdescent : baseEnd_6775683 < baseStart_6775683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775700 : List Nat := [2, 4, 2, 1, 1, 1, 3, 4, 5]
def baseStart_6775700 : Nat := 118140960795 + 6775700 * 2 ^ 59
def prefixEnd_6775700 : Nat := 4983230072969 + 3 ^ 40 * 6775700 * 2
def baseEnd_6775700 : Nat := 386576763407693919587681

theorem tailTrace_6775700 : CollatzResearch.WordTrace tailWord_6775700 prefixEnd_6775700 386576763407693919587681 := by
  unfold tailWord_6775700
  simp only [CollatzResearch.WordTrace]
  refine ⟨123565040776401786137958277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164753387701869048183944369 123565040776401786137958277)
  ·
    refine ⟨23168445145575334900867177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123565040776401786137958277 23168445145575334900867177)
    ·
      refine ⟨17376333859181501175650383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23168445145575334900867177 17376333859181501175650383)
      ·
        refine ⟨26064500788772251763475575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17376333859181501175650383 26064500788772251763475575)
        ·
          refine ⟨39096751183158377645213363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26064500788772251763475575 39096751183158377645213363)
          ·
            refine ⟨58645126774737566467820045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39096751183158377645213363 58645126774737566467820045)
            ·
              refine ⟨21991922540526587425432517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58645126774737566467820045 21991922540526587425432517)
              ·
                refine ⟨4123485476348735142268597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21991922540526587425432517 4123485476348735142268597)
                ·
                  refine ⟨386576763407693919587681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4123485476348735142268597 386576763407693919587681)
                  ·
                    rfl

theorem cell23_6775700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_6775700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775700 prefixEnd_6775700 := by exact prefixLift 6775700
  have htrace : WordTrace (prefixWord ++ tailWord_6775700) baseStart_6775700 baseEnd_6775700 := by
    simpa [prefixWord, tailWord_6775700, baseEnd_6775700] using wordTrace_append hprefix tailTrace_6775700
  have hstable : (prefixWord ++ tailWord_6775700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775700).length < 2 ^ (prefixWord ++ tailWord_6775700).sum := by decide
  have hdescent : baseEnd_6775700 < baseStart_6775700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775703 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 1, 7, 2]
def baseStart_6775703 : Nat := 118140960795 + 6775703 * 2 ^ 59
def prefixEnd_6775703 : Nat := 4983230072969 + 3 ^ 40 * 6775703 * 2
def baseEnd_6775703 : Nat := 3479192411111208764551615

theorem tailTrace_6775703 : CollatzResearch.WordTrace tailWord_6775703 prefixEnd_6775703 3479192411111208764551615 := by
  unfold tailWord_6775703
  simp only [CollatzResearch.WordTrace]
  refine ⟨247130190971792703788275763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164753460647861802525517175 247130190971792703788275763)
  ·
    refine ⟨370695286457689055682413645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247130190971792703788275763 370695286457689055682413645)
    ·
      refine ⟨139010732421633395880905117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370695286457689055682413645 139010732421633395880905117)
      ·
        refine ⟨52129024658112523455339419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139010732421633395880905117 52129024658112523455339419)
        ·
          refine ⟨78193536987168785183009129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52129024658112523455339419 78193536987168785183009129)
          ·
            refine ⟨58645152740376588887256847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78193536987168785183009129 58645152740376588887256847)
            ·
              refine ⟨87967729110564883330885271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58645152740376588887256847 87967729110564883330885271)
              ·
                refine ⟨131951593665847324996327907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87967729110564883330885271 131951593665847324996327907)
                ·
                  refine ⟨197927390498770987494491861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131951593665847324996327907 197927390498770987494491861)
                  ·
                    refine ⟨4638923214814945019402153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 197927390498770987494491861 4638923214814945019402153)
                    ·
                      refine ⟨3479192411111208764551615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4638923214814945019402153 3479192411111208764551615)
                      ·
                        rfl

theorem cell23_6775703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_6775703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775703 prefixEnd_6775703 := by exact prefixLift 6775703
  have htrace : WordTrace (prefixWord ++ tailWord_6775703) baseStart_6775703 baseEnd_6775703 := by
    simpa [prefixWord, tailWord_6775703, baseEnd_6775703] using wordTrace_append hprefix tailTrace_6775703
  have hstable : (prefixWord ++ tailWord_6775703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775703).length < 2 ^ (prefixWord ++ tailWord_6775703).sum := by decide
  have hdescent : baseEnd_6775703 < baseStart_6775703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775733 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_6775733 : Nat := 118140960795 + 6775733 * 2 ^ 59
def prefixEnd_6775733 : Nat := 4983230072969 + 3 ^ 40 * 6775733 * 2
def baseEnd_6775733 : Nat := 3479207815530843647176477

theorem tailTrace_6775733 : CollatzResearch.WordTrace tailWord_6775733 prefixEnd_6775733 3479207815530843647176477 := by
  unfold tailWord_6775733
  simp only [CollatzResearch.WordTrace]
  refine ⟨247131285161684018911867853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164754190107789345941245235 247131285161684018911867853)
  ·
    refine ⟨92674231935631507091950445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247131285161684018911867853 92674231935631507091950445)
    ·
      refine ⟨34752836975861815159481417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92674231935631507091950445 34752836975861815159481417)
      ·
        refine ⟨26064627731896361369611063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34752836975861815159481417 26064627731896361369611063)
        ·
          refine ⟨39096941597844542054416595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26064627731896361369611063 39096941597844542054416595)
          ·
            refine ⟨58645412396766813081624893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39096941597844542054416595 58645412396766813081624893)
            ·
              refine ⟨21992029648787554905609335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58645412396766813081624893 21992029648787554905609335)
              ·
                refine ⟨32988044473181332358414003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21992029648787554905609335 32988044473181332358414003)
                ·
                  refine ⟨49482066709771998537621005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32988044473181332358414003 49482066709771998537621005)
                  ·
                    refine ⟨18555775016164499451607877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49482066709771998537621005 18555775016164499451607877)
                    ·
                      refine ⟨3479207815530843647176477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18555775016164499451607877 3479207815530843647176477)
                      ·
                        rfl

theorem cell23_6775733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_6775733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775733 prefixEnd_6775733 := by exact prefixLift 6775733
  have htrace : WordTrace (prefixWord ++ tailWord_6775733) baseStart_6775733 baseEnd_6775733 := by
    simpa [prefixWord, tailWord_6775733, baseEnd_6775733] using wordTrace_append hprefix tailTrace_6775733
  have hstable : (prefixWord ++ tailWord_6775733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775733).length < 2 ^ (prefixWord ++ tailWord_6775733).sum := by decide
  have hdescent : baseEnd_6775733 < baseStart_6775733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775817 : List Nat := [1, 2, 1, 1, 3, 1, 1, 8, 1, 1, 3]
def baseStart_6775817 : Nat := 118140960795 + 6775817 * 2 ^ 59
def prefixEnd_6775817 : Nat := 4983230072969 + 3 ^ 40 * 6775817 * 2
def baseEnd_6775817 : Nat := 3479250947905821318526091

theorem tailTrace_6775817 : CollatzResearch.WordTrace tailWord_6775817 prefixEnd_6775817 3479250947905821318526091 := by
  unfold tailWord_6775817
  simp only [CollatzResearch.WordTrace]
  refine ⟨247134348893379701257925705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164756232595586467505283803 247134348893379701257925705)
  ·
    refine ⟨185350761670034775943444279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247134348893379701257925705 185350761670034775943444279)
    ·
      refine ⟨278026142505052163915166419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185350761670034775943444279 278026142505052163915166419)
      ·
        refine ⟨417039213757578245872749629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278026142505052163915166419 417039213757578245872749629)
        ·
          refine ⟨156389705159091842202281111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417039213757578245872749629 156389705159091842202281111)
          ·
            refine ⟨234584557738637763303421667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156389705159091842202281111 234584557738637763303421667)
            ·
              refine ⟨351876836607956644955132501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234584557738637763303421667 351876836607956644955132501)
              ·
                refine ⟨4123556678999491933067959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 351876836607956644955132501 4123556678999491933067959)
                ·
                  refine ⟨6185335018499237899601939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123556678999491933067959 6185335018499237899601939)
                  ·
                    refine ⟨9278002527748856849402909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6185335018499237899601939 9278002527748856849402909)
                    ·
                      refine ⟨3479250947905821318526091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9278002527748856849402909 3479250947905821318526091)
                      ·
                        rfl

theorem cell23_6775817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 1, 1, 3].length) (baseStart_6775817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775817 prefixEnd_6775817 := by exact prefixLift 6775817
  have htrace : WordTrace (prefixWord ++ tailWord_6775817) baseStart_6775817 baseEnd_6775817 := by
    simpa [prefixWord, tailWord_6775817, baseEnd_6775817] using wordTrace_append hprefix tailTrace_6775817
  have hstable : (prefixWord ++ tailWord_6775817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775817).length < 2 ^ (prefixWord ++ tailWord_6775817).sum := by decide
  have hdescent : baseEnd_6775817 < baseStart_6775817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775844 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 2, 3, 2]
def baseStart_6775844 : Nat := 118140960795 + 6775844 * 2 ^ 59
def prefixEnd_6775844 : Nat := 4983230072969 + 3 ^ 40 * 6775844 * 2
def baseEnd_6775844 : Nat := 3479264811883492712888467

theorem tailTrace_6775844 : CollatzResearch.WordTrace tailWord_6775844 prefixEnd_6775844 3479264811883492712888467 := by
  unfold tailWord_6775844
  simp only [CollatzResearch.WordTrace]
  refine ⟨123567666832140942434579293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164756889109521256579439057 123567666832140942434579293)
  ·
    refine ⟨46337875062052853412967235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123567666832140942434579293 46337875062052853412967235)
    ·
      refine ⟨69506812593079280119450853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46337875062052853412967235 69506812593079280119450853)
      ·
        refine ⟨13032527361202365022397035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69506812593079280119450853 13032527361202365022397035)
        ·
          refine ⟨19548791041803547533595553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13032527361202365022397035 19548791041803547533595553)
          ·
            refine ⟨14661593281352660650196665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19548791041803547533595553 14661593281352660650196665)
            ·
              refine ⟨10996194961014495487647499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14661593281352660650196665 10996194961014495487647499)
              ·
                refine ⟨16494292441521743231471249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10996194961014495487647499 16494292441521743231471249)
                ·
                  refine ⟨12370719331141307423603437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16494292441521743231471249 12370719331141307423603437)
                  ·
                    refine ⟨4639019749177990283851289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12370719331141307423603437 4639019749177990283851289)
                    ·
                      refine ⟨3479264811883492712888467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639019749177990283851289 3479264811883492712888467)
                      ·
                        rfl

theorem cell23_6775844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_6775844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775844 prefixEnd_6775844 := by exact prefixLift 6775844
  have htrace : WordTrace (prefixWord ++ tailWord_6775844) baseStart_6775844 baseEnd_6775844 := by
    simpa [prefixWord, tailWord_6775844, baseEnd_6775844] using wordTrace_append hprefix tailTrace_6775844
  have hstable : (prefixWord ++ tailWord_6775844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775844).length < 2 ^ (prefixWord ++ tailWord_6775844).sum := by decide
  have hdescent : baseEnd_6775844 < baseStart_6775844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775857 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 1, 1, 4]
def baseStart_6775857 : Nat := 118140960795 + 6775857 * 2 ^ 59
def prefixEnd_6775857 : Nat := 4983230072969 + 3 ^ 40 * 6775857 * 2
def baseEnd_6775857 : Nat := 3479271487132001162025907

theorem tailTrace_6775857 : CollatzResearch.WordTrace tailWord_6775857 prefixEnd_6775857 3479271487132001162025907 := by
  unfold tailWord_6775857
  simp only [CollatzResearch.WordTrace]
  refine ⟨247135807813234788089381825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164757205208823192059587883 247135807813234788089381825)
  ·
    refine ⟨185351855859926091067036369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247135807813234788089381825 185351855859926091067036369)
    ·
      refine ⟨139013891894944568300277277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185351855859926091067036369 139013891894944568300277277)
      ·
        refine ⟨52130209460604213112603979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139013891894944568300277277 52130209460604213112603979)
        ·
          refine ⟨78195314190906319668905969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52130209460604213112603979 78195314190906319668905969)
          ·
            refine ⟨58646485643179739751679477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78195314190906319668905969 58646485643179739751679477)
            ·
              refine ⟨5498108029048100601719951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58646485643179739751679477 5498108029048100601719951)
              ·
                refine ⟨8247162043572150902579927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5498108029048100601719951 8247162043572150902579927)
                ·
                  refine ⟨12370743065358226353869891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8247162043572150902579927 12370743065358226353869891)
                  ·
                    refine ⟨18556114598037339530804837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12370743065358226353869891 18556114598037339530804837)
                    ·
                      refine ⟨3479271487132001162025907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18556114598037339530804837 3479271487132001162025907)
                      ·
                        rfl

theorem cell23_6775857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_6775857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775857 prefixEnd_6775857 := by exact prefixLift 6775857
  have htrace : WordTrace (prefixWord ++ tailWord_6775857) baseStart_6775857 baseEnd_6775857 := by
    simpa [prefixWord, tailWord_6775857, baseEnd_6775857] using wordTrace_append hprefix tailTrace_6775857
  have hstable : (prefixWord ++ tailWord_6775857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775857).length < 2 ^ (prefixWord ++ tailWord_6775857).sum := by decide
  have hdescent : baseEnd_6775857 < baseStart_6775857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775893 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_6775893 : Nat := 118140960795 + 6775893 * 2 ^ 59
def prefixEnd_6775893 : Nat := 4983230072969 + 3 ^ 40 * 6775893 * 2
def baseEnd_6775893 : Nat := 1159763324145187673725247

theorem tailTrace_6775893 : CollatzResearch.WordTrace tailWord_6775893 prefixEnd_6775893 1159763324145187673725247 := by
  unfold tailWord_6775893
  simp only [CollatzResearch.WordTrace]
  refine ⟨247137120841104366237692333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164758080560736244158461555 247137120841104366237692333)
  ·
    refine ⟨92676420315414137339134625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247137120841104366237692333 92676420315414137339134625)
    ·
      refine ⟨69507315236560603004350969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92676420315414137339134625 69507315236560603004350969)
      ·
        refine ⟨52130486427420452253263227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69507315236560603004350969 52130486427420452253263227)
        ·
          refine ⟨78195729641130678379894841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52130486427420452253263227 78195729641130678379894841)
          ·
            refine ⟨58646797230848008784921131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78195729641130678379894841 58646797230848008784921131)
            ·
              refine ⟨87970195846272013177381697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58646797230848008784921131 87970195846272013177381697)
              ·
                refine ⟨65977646884704009883036273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87970195846272013177381697 65977646884704009883036273)
                ·
                  refine ⟨49483235163528007412277205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65977646884704009883036273 49483235163528007412277205)
                  ·
                    refine ⟨1159763324145187673725247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49483235163528007412277205 1159763324145187673725247)
                    ·
                      rfl

theorem cell23_6775893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_6775893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775893 prefixEnd_6775893 := by exact prefixLift 6775893
  have htrace : WordTrace (prefixWord ++ tailWord_6775893) baseStart_6775893 baseEnd_6775893 := by
    simpa [prefixWord, tailWord_6775893, baseEnd_6775893] using wordTrace_append hprefix tailTrace_6775893
  have hstable : (prefixWord ++ tailWord_6775893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775893).length < 2 ^ (prefixWord ++ tailWord_6775893).sum := by decide
  have hdescent : baseEnd_6775893 < baseStart_6775893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775903 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_6775903 : Nat := 118140960795 + 6775903 * 2 ^ 59
def prefixEnd_6775903 : Nat := 4983230072969 + 3 ^ 40 * 6775903 * 2
def baseEnd_6775903 : Nat := 3479295107242107982050695

theorem tailTrace_6775903 : CollatzResearch.WordTrace tailWord_6775903 prefixEnd_6775903 3479295107242107982050695 := by
  unfold tailWord_6775903
  simp only [CollatzResearch.WordTrace]
  refine ⟨247137485571068137945556363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164758323714045425297037575 247137485571068137945556363)
  ·
    refine ⟨370706228356602206918334545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247137485571068137945556363 370706228356602206918334545)
    ·
      refine ⟨278029671267451655188750909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370706228356602206918334545 278029671267451655188750909)
      ·
        refine ⟨104261126725294370695781591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278029671267451655188750909 104261126725294370695781591)
        ·
          refine ⟨156391690087941556043672387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104261126725294370695781591 156391690087941556043672387)
          ·
            refine ⟨234587535131912334065508581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156391690087941556043672387 234587535131912334065508581)
            ·
              refine ⟨43985162837233562637282859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234587535131912334065508581 43985162837233562637282859)
              ·
                refine ⟨65977744255850343955924289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43985162837233562637282859 65977744255850343955924289)
                ·
                  refine ⟨49483308191887757966943217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65977744255850343955924289 49483308191887757966943217)
                  ·
                    refine ⟨37112481143915818475207413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49483308191887757966943217 37112481143915818475207413)
                    ·
                      refine ⟨3479295107242107982050695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37112481143915818475207413 3479295107242107982050695)
                      ·
                        rfl

theorem cell23_6775903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_6775903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775903 prefixEnd_6775903 := by exact prefixLift 6775903
  have htrace : WordTrace (prefixWord ++ tailWord_6775903) baseStart_6775903 baseEnd_6775903 := by
    simpa [prefixWord, tailWord_6775903, baseEnd_6775903] using wordTrace_append hprefix tailTrace_6775903
  have hstable : (prefixWord ++ tailWord_6775903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775903).length < 2 ^ (prefixWord ++ tailWord_6775903).sum := by decide
  have hdescent : baseEnd_6775903 < baseStart_6775903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775930 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2]
def baseStart_6775930 : Nat := 118140960795 + 6775930 * 2 ^ 59
def prefixEnd_6775930 : Nat := 4983230072969 + 3 ^ 40 * 6775930 * 2
def baseEnd_6775930 : Nat := 3479308971219779376413071

theorem tailTrace_6775930 : CollatzResearch.WordTrace tailWord_6775930 prefixEnd_6775930 3479308971219779376413071 := by
  unfold tailWord_6775930
  simp only [CollatzResearch.WordTrace]
  refine ⟨61784617585492580389197311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164758980227980214371192829 61784617585492580389197311)
  ·
    refine ⟨92676926378238870583795967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61784617585492580389197311 92676926378238870583795967)
    ·
      refine ⟨139015389567358305875693951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92676926378238870583795967 139015389567358305875693951)
      ·
        refine ⟨208523084351037458813540927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139015389567358305875693951 208523084351037458813540927)
        ·
          refine ⟨312784626526556188220311391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208523084351037458813540927 312784626526556188220311391)
          ·
            refine ⟨469176939789834282330467087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312784626526556188220311391 469176939789834282330467087)
            ·
              refine ⟨703765409684751423495700631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469176939789834282330467087 703765409684751423495700631)
              ·
                refine ⟨1055648114527127135243550947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703765409684751423495700631 1055648114527127135243550947)
                ·
                  refine ⟨1583472171790690702865326421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055648114527127135243550947 1583472171790690702865326421)
                  ·
                    refine ⟨4639078628293039168550761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1583472171790690702865326421 4639078628293039168550761)
                    ·
                      refine ⟨3479308971219779376413071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639078628293039168550761 3479308971219779376413071)
                      ·
                        rfl

theorem cell23_6775930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_6775930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775930 prefixEnd_6775930 := by exact prefixLift 6775930
  have htrace : WordTrace (prefixWord ++ tailWord_6775930) baseStart_6775930 baseEnd_6775930 := by
    simpa [prefixWord, tailWord_6775930, baseEnd_6775930] using wordTrace_append hprefix tailTrace_6775930
  have hstable : (prefixWord ++ tailWord_6775930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775930).length < 2 ^ (prefixWord ++ tailWord_6775930).sum := by decide
  have hdescent : baseEnd_6775930 < baseStart_6775930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775940 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_6775940 : Nat := 118140960795 + 6775940 * 2 ^ 59
def prefixEnd_6775940 : Nat := 4983230072969 + 3 ^ 40 * 6775940 * 2
def baseEnd_6775940 : Nat := 1159771368675441445762675

theorem tailTrace_6775940 : CollatzResearch.WordTrace tailWord_6775940 prefixEnd_6775940 1159771368675441445762675 := by
  unfold tailWord_6775940
  simp only [CollatzResearch.WordTrace]
  refine ⟨123569417535967046632326637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164759223381289395509768849 123569417535967046632326637)
  ·
    refine ⟨46338531575987642487122489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123569417535967046632326637 46338531575987642487122489)
    ·
      refine ⟨34753898681990731865341867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46338531575987642487122489 34753898681990731865341867)
      ·
        refine ⟨52130848022986097798012801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34753898681990731865341867 52130848022986097798012801)
        ·
          refine ⟨39098136017239573348509601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52130848022986097798012801 39098136017239573348509601)
          ·
            refine ⟨29323602012929680011382201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39098136017239573348509601 29323602012929680011382201)
            ·
              refine ⟨21992701509697260008536651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29323602012929680011382201 21992701509697260008536651)
              ·
                refine ⟨32989052264545890012804977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21992701509697260008536651 32989052264545890012804977)
                ·
                  refine ⟨24741789198409417509603733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32989052264545890012804977 24741789198409417509603733)
                  ·
                    refine ⟨1159771368675441445762675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24741789198409417509603733 1159771368675441445762675)
                    ·
                      rfl

theorem cell23_6775940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_6775940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775940 prefixEnd_6775940 := by exact prefixLift 6775940
  have htrace : WordTrace (prefixWord ++ tailWord_6775940) baseStart_6775940 baseEnd_6775940 := by
    simpa [prefixWord, tailWord_6775940, baseEnd_6775940] using wordTrace_append hprefix tailTrace_6775940
  have hstable : (prefixWord ++ tailWord_6775940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775940).length < 2 ^ (prefixWord ++ tailWord_6775940).sum := by decide
  have hdescent : baseEnd_6775940 < baseStart_6775940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775941 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 2, 1, 3]
def baseStart_6775941 : Nat := 118140960795 + 6775941 * 2 ^ 59
def prefixEnd_6775941 : Nat := 4983230072969 + 3 ^ 40 * 6775941 * 2
def baseEnd_6775941 : Nat := 3479314619506978833375521

theorem tailTrace_6775941 : CollatzResearch.WordTrace tailWord_6775941 prefixEnd_6775941 3479314619506978833375521 := by
  unfold tailWord_6775941
  simp only [CollatzResearch.WordTrace]
  refine ⟨247138871544930470435439677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164759247696620313623626451 247138871544930470435439677)
  ·
    refine ⟨92677076829348926413289879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247138871544930470435439677 92677076829348926413289879)
    ·
      refine ⟨139015615244023389619934819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92677076829348926413289879 139015615244023389619934819)
      ·
        refine ⟨208523422866035084429902229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139015615244023389619934819 208523422866035084429902229)
        ·
          refine ⟨9774535446845394582651667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 208523422866035084429902229 9774535446845394582651667)
          ·
            refine ⟨14661803170268091873977501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9774535446845394582651667 14661803170268091873977501)
            ·
              refine ⟨5498176188850534452741563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14661803170268091873977501 5498176188850534452741563)
              ·
                refine ⟨8247264283275801679112345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5498176188850534452741563 8247264283275801679112345)
                ·
                  refine ⟨6185448212456851259334259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8247264283275801679112345 6185448212456851259334259)
                  ·
                    refine ⟨9278172318685276889001389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6185448212456851259334259 9278172318685276889001389)
                    ·
                      refine ⟨3479314619506978833375521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9278172318685276889001389 3479314619506978833375521)
                      ·
                        rfl

theorem cell23_6775941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_6775941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775941 prefixEnd_6775941 := by exact prefixLift 6775941
  have htrace : WordTrace (prefixWord ++ tailWord_6775941) baseStart_6775941 baseEnd_6775941 := by
    simpa [prefixWord, tailWord_6775941, baseEnd_6775941] using wordTrace_append hprefix tailTrace_6775941
  have hstable : (prefixWord ++ tailWord_6775941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775941).length < 2 ^ (prefixWord ++ tailWord_6775941).sum := by decide
  have hdescent : baseEnd_6775941 < baseStart_6775941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775964 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_6775964 : Nat := 118140960795 + 6775964 * 2 ^ 59
def prefixEnd_6775964 : Nat := 4983230072969 + 3 ^ 40 * 6775964 * 2
def baseEnd_6775964 : Nat := 3479326429562032243387915

theorem tailTrace_6775964 : CollatzResearch.WordTrace tailWord_6775964 prefixEnd_6775964 3479326429562032243387915 := by
  unfold tailWord_6775964
  simp only [CollatzResearch.WordTrace]
  refine ⟨123569855211923572681763473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164759806949231430242351297 123569855211923572681763473)
  ·
    refine ⟨92677391408942679511322605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123569855211923572681763473 92677391408942679511322605)
    ·
      refine ⟨34754021778353504816745977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92677391408942679511322605 34754021778353504816745977)
      ·
        refine ⟨26065516333765128612559483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34754021778353504816745977 26065516333765128612559483)
        ·
          refine ⟨39098274500647692918839225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26065516333765128612559483 39098274500647692918839225)
          ·
            refine ⟨29323705875485769689129419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39098274500647692918839225 29323705875485769689129419)
            ·
              refine ⟨43985558813228654533694129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29323705875485769689129419 43985558813228654533694129)
              ·
                refine ⟨32989169109921490900270597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43985558813228654533694129 32989169109921490900270597)
                ·
                  refine ⟨6185469208110279543800737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32989169109921490900270597 6185469208110279543800737)
                  ·
                    refine ⟨4639101906082709657850553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6185469208110279543800737 4639101906082709657850553)
                    ·
                      refine ⟨3479326429562032243387915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639101906082709657850553 3479326429562032243387915)
                      ·
                        rfl

theorem cell23_6775964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_6775964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775964 prefixEnd_6775964 := by exact prefixLift 6775964
  have htrace : WordTrace (prefixWord ++ tailWord_6775964) baseStart_6775964 baseEnd_6775964 := by
    simpa [prefixWord, tailWord_6775964, baseEnd_6775964] using wordTrace_append hprefix tailTrace_6775964
  have hstable : (prefixWord ++ tailWord_6775964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775964).length < 2 ^ (prefixWord ++ tailWord_6775964).sum := by decide
  have hdescent : baseEnd_6775964 < baseStart_6775964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775967 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 5]
def baseStart_6775967 : Nat := 118140960795 + 6775967 * 2 ^ 59
def prefixEnd_6775967 : Nat := 4983230072969 + 3 ^ 40 * 6775967 * 2
def baseEnd_6775967 : Nat := 3479327970003995731650401

theorem tailTrace_6775967 : CollatzResearch.WordTrace tailWord_6775967 prefixEnd_6775967 3479327970003995731650401 := by
  unfold tailWord_6775967
  simp only [CollatzResearch.WordTrace]
  refine ⟨247139819842836276875886155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164759879895224184583924103 247139819842836276875886155)
  ·
    refine ⟨370709729764254415313829233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247139819842836276875886155 370709729764254415313829233)
    ·
      refine ⟨278032297323190811485371925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370709729764254415313829233 278032297323190811485371925)
      ·
        refine ⟨13032763937024569288376809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 278032297323190811485371925 13032763937024569288376809)
        ·
          refine ⟨9774572952768426966282607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13032763937024569288376809 9774572952768426966282607)
          ·
            refine ⟨14661859429152640449423911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9774572952768426966282607 14661859429152640449423911)
            ·
              refine ⟨21992789143728960674135867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14661859429152640449423911 21992789143728960674135867)
              ·
                refine ⟨32989183715593441011203801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21992789143728960674135867 32989183715593441011203801)
                ·
                  refine ⟨24741887786695080758402851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32989183715593441011203801 24741887786695080758402851)
                  ·
                    refine ⟨37112831680042621137604277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24741887786695080758402851 37112831680042621137604277)
                    ·
                      refine ⟨3479327970003995731650401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37112831680042621137604277 3479327970003995731650401)
                      ·
                        rfl

theorem cell23_6775967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_6775967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775967 prefixEnd_6775967 := by exact prefixLift 6775967
  have htrace : WordTrace (prefixWord ++ tailWord_6775967) baseStart_6775967 baseEnd_6775967 := by
    simpa [prefixWord, tailWord_6775967, baseEnd_6775967] using wordTrace_append hprefix tailTrace_6775967
  have hstable : (prefixWord ++ tailWord_6775967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775967).length < 2 ^ (prefixWord ++ tailWord_6775967).sum := by decide
  have hdescent : baseEnd_6775967 < baseStart_6775967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775980 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 3]
def baseStart_6775980 : Nat := 118140960795 + 6775980 * 2 ^ 59
def prefixEnd_6775980 : Nat := 4983230072969 + 3 ^ 40 * 6775980 * 2
def baseEnd_6775980 : Nat := 3479334645252504180787841

theorem tailTrace_6775980 : CollatzResearch.WordTrace tailWord_6775980 prefixEnd_6775980 3479334645252504180787841 := by
  unfold tailWord_6775980
  simp only [CollatzResearch.WordTrace]
  refine ⟨123570146995894590048054697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164760195994526120064072929 123570146995894590048054697)
  ·
    refine ⟨92677610246920942536041023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123570146995894590048054697 92677610246920942536041023)
    ·
      refine ⟨139016415370381413804061535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92677610246920942536041023 139016415370381413804061535)
      ·
        refine ⟨208524623055572120706092303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139016415370381413804061535 208524623055572120706092303)
        ·
          refine ⟨312786934583358181059138455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208524623055572120706092303 312786934583358181059138455)
          ·
            refine ⟨469180401875037271588707683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312786934583358181059138455 469180401875037271588707683)
            ·
              refine ⟨703770602812555907383061525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469180401875037271588707683 703770602812555907383061525)
              ·
                refine ⟨32989247006838558158581009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 703770602812555907383061525 32989247006838558158581009)
                ·
                  refine ⟨24741935255128918618935757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32989247006838558158581009 24741935255128918618935757)
                  ·
                    refine ⟨9278225720673344482100909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24741935255128918618935757 9278225720673344482100909)
                    ·
                      refine ⟨3479334645252504180787841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9278225720673344482100909 3479334645252504180787841)
                      ·
                        rfl

theorem cell23_6775980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_6775980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775980 prefixEnd_6775980 := by exact prefixLift 6775980
  have htrace : WordTrace (prefixWord ++ tailWord_6775980) baseStart_6775980 baseEnd_6775980 := by
    simpa [prefixWord, tailWord_6775980, baseEnd_6775980] using wordTrace_append hprefix tailTrace_6775980
  have hstable : (prefixWord ++ tailWord_6775980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775980).length < 2 ^ (prefixWord ++ tailWord_6775980).sum := by decide
  have hdescent : baseEnd_6775980 < baseStart_6775980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6775998 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_6775998 : Nat := 118140960795 + 6775998 * 2 ^ 59
def prefixEnd_6775998 : Nat := 4983230072969 + 3 ^ 40 * 6775998 * 2
def baseEnd_6775998 : Nat := 3479343887904285110362759

theorem tailTrace_6775998 : CollatzResearch.WordTrace tailWord_6775998 prefixEnd_6775998 3479343887904285110362759 := by
  unfold tailWord_6775998
  simp only [CollatzResearch.WordTrace]
  refine ⟨30892618813215496146283081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164760633670482646113509765 30892618813215496146283081)
  ·
    refine ⟨23169464109911622109712311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30892618813215496146283081 23169464109911622109712311)
    ·
      refine ⟨34754196164867433164568467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23169464109911622109712311 34754196164867433164568467)
      ·
        refine ⟨52131294247301149746852701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34754196164867433164568467 52131294247301149746852701)
        ·
          refine ⟨19549235342737931155069763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52131294247301149746852701 19549235342737931155069763)
          ·
            refine ⟨29323853014106896732604645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19549235342737931155069763 29323853014106896732604645)
            ·
              refine ⟨5498222440145043137363371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29323853014106896732604645 5498222440145043137363371)
              ·
                refine ⟨8247333660217564706045057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5498222440145043137363371 8247333660217564706045057)
                ·
                  refine ⟨6185500245163173529533793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8247333660217564706045057 6185500245163173529533793)
                  ·
                    refine ⟨4639125183872380147150345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6185500245163173529533793 4639125183872380147150345)
                    ·
                      refine ⟨3479343887904285110362759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639125183872380147150345 3479343887904285110362759)
                      ·
                        rfl

theorem cell23_6775998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_6775998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6775998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6775998 prefixEnd_6775998 := by exact prefixLift 6775998
  have htrace : WordTrace (prefixWord ++ tailWord_6775998) baseStart_6775998 baseEnd_6775998 := by
    simpa [prefixWord, tailWord_6775998, baseEnd_6775998] using wordTrace_append hprefix tailTrace_6775998
  have hstable : (prefixWord ++ tailWord_6775998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6775998).length < 2 ^ (prefixWord ++ tailWord_6775998).sum := by decide
  have hdescent : baseEnd_6775998 < baseStart_6775998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6775998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776002 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_6776002 : Nat := 118140960795 + 6776002 * 2 ^ 59
def prefixEnd_6776002 : Nat := 4983230072969 + 3 ^ 40 * 6776002 * 2
def baseEnd_6776002 : Nat := 3479345941826903094712741

theorem tailTrace_6776002 : CollatzResearch.WordTrace tailWord_6776002 prefixEnd_6776002 3479345941826903094712741 := by
  unfold tailWord_6776002
  simp only [CollatzResearch.WordTrace]
  refine ⟨61785274099427369463352565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164760730931806318568940173 61785274099427369463352565)
  ·
    refine ⟨5792369446821315887189303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61785274099427369463352565 5792369446821315887189303)
    ·
      refine ⟨8688554170231973830783955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5792369446821315887189303 8688554170231973830783955)
      ·
        refine ⟨13032831255347960746175933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8688554170231973830783955 13032831255347960746175933)
        ·
          refine ⟨4887311720755485279815975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13032831255347960746175933 4887311720755485279815975)
          ·
            refine ⟨7330967581133227919723963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887311720755485279815975 7330967581133227919723963)
            ·
              refine ⟨10996451371699841879585945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330967581133227919723963 10996451371699841879585945)
              ·
                refine ⟨8247338528774881409689459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10996451371699841879585945 8247338528774881409689459)
                ·
                  refine ⟨12371007793162322114534189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8247338528774881409689459 12371007793162322114534189)
                  ·
                    refine ⟨4639127922435870792950321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12371007793162322114534189 4639127922435870792950321)
                    ·
                      refine ⟨3479345941826903094712741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639127922435870792950321 3479345941826903094712741)
                      ·
                        rfl

theorem cell23_6776002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_6776002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776002 prefixEnd_6776002 := by exact prefixLift 6776002
  have htrace : WordTrace (prefixWord ++ tailWord_6776002) baseStart_6776002 baseEnd_6776002 := by
    simpa [prefixWord, tailWord_6776002, baseEnd_6776002] using wordTrace_append hprefix tailTrace_6776002
  have hstable : (prefixWord ++ tailWord_6776002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776002).length < 2 ^ (prefixWord ++ tailWord_6776002).sum := by decide
  have hdescent : baseEnd_6776002 < baseStart_6776002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776040 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6776040 : Nat := 118140960795 + 6776040 * 2 ^ 59
def prefixEnd_6776040 : Nat := 4983230072969 + 3 ^ 40 * 6776040 * 2
def baseEnd_6776040 : Nat := 3479365454091773946037565

theorem tailTrace_6776040 : CollatzResearch.WordTrace tailWord_6776040 prefixEnd_6776040 3479365454091773946037565 := by
  unfold tailWord_6776040
  simp only [CollatzResearch.WordTrace]
  refine ⟨123571241185785905171646787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164761654914381206895529049 123571241185785905171646787)
  ·
    refine ⟨185356861778678857757470181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123571241185785905171646787 185356861778678857757470181)
    ·
      refine ⟨34754411583502285829525659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185356861778678857757470181 34754411583502285829525659)
      ·
        refine ⟨52131617375253428744288489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34754411583502285829525659 52131617375253428744288489)
        ·
          refine ⟨39098713031440071558216367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52131617375253428744288489 39098713031440071558216367)
          ·
            refine ⟨58648069547160107337324551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39098713031440071558216367 58648069547160107337324551)
            ·
              refine ⟨87972104320740161005986827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58648069547160107337324551 87972104320740161005986827)
              ·
                refine ⟨131958156481110241508980241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87972104320740161005986827 131958156481110241508980241)
                ·
                  refine ⟨98968617360832681131735181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131958156481110241508980241 98968617360832681131735181)
                  ·
                    refine ⟨37113231510312255424400693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98968617360832681131735181 37113231510312255424400693)
                    ·
                      refine ⟨3479365454091773946037565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37113231510312255424400693 3479365454091773946037565)
                      ·
                        rfl

theorem cell23_6776040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6776040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776040 prefixEnd_6776040 := by exact prefixLift 6776040
  have htrace : WordTrace (prefixWord ++ tailWord_6776040) baseStart_6776040 baseEnd_6776040 := by
    simpa [prefixWord, tailWord_6776040, baseEnd_6776040] using wordTrace_append hprefix tailTrace_6776040
  have hstable : (prefixWord ++ tailWord_6776040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776040).length < 2 ^ (prefixWord ++ tailWord_6776040).sum := by decide
  have hdescent : baseEnd_6776040 < baseStart_6776040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776114 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2]
def baseStart_6776114 : Nat := 118140960795 + 6776114 * 2 ^ 59
def prefixEnd_6776114 : Nat := 4983230072969 + 3 ^ 40 * 6776114 * 2
def baseEnd_6776114 : Nat := 3479403451660206656512225

theorem tailTrace_6776114 : CollatzResearch.WordTrace tailWord_6776114 prefixEnd_6776114 3479403451660206656512225 := by
  unfold tailWord_6776114
  simp only [CollatzResearch.WordTrace]
  refine ⟨61786295343325930245371849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164763454248869147320991597 61786295343325930245371849)
  ·
    refine ⟨46339721507494447684028887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61786295343325930245371849 46339721507494447684028887)
    ·
      refine ⟨69509582261241671526043331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46339721507494447684028887 69509582261241671526043331)
      ·
        refine ⟨104264373391862507289064997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69509582261241671526043331 104264373391862507289064997)
        ·
          refine ⟨19549570010974220116699687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104264373391862507289064997 19549570010974220116699687)
          ·
            refine ⟨29324355016461330175049531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19549570010974220116699687 29324355016461330175049531)
            ·
              refine ⟨43986532524691995262574297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29324355016461330175049531 43986532524691995262574297)
              ·
                refine ⟨32989899393518996446930723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43986532524691995262574297 32989899393518996446930723)
                ·
                  refine ⟨49484849090278494670396085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32989899393518996446930723 49484849090278494670396085)
                  ·
                    refine ⟨4639204602213608875349633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49484849090278494670396085 4639204602213608875349633)
                    ·
                      refine ⟨3479403451660206656512225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639204602213608875349633 3479403451660206656512225)
                      ·
                        rfl

theorem cell23_6776114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_6776114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776114 prefixEnd_6776114 := by exact prefixLift 6776114
  have htrace : WordTrace (prefixWord ++ tailWord_6776114) baseStart_6776114 baseEnd_6776114 := by
    simpa [prefixWord, tailWord_6776114, baseEnd_6776114] using wordTrace_append hprefix tailTrace_6776114
  have hstable : (prefixWord ++ tailWord_6776114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776114).length < 2 ^ (prefixWord ++ tailWord_6776114).sum := by decide
  have hdescent : baseEnd_6776114 < baseStart_6776114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776124 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_6776124 : Nat := 118140960795 + 6776124 * 2 ^ 59
def prefixEnd_6776124 : Nat := 4983230072969 + 3 ^ 40 * 6776124 * 2
def baseEnd_6776124 : Nat := 1159802862155583872462393

theorem tailTrace_6776124 : CollatzResearch.WordTrace tailWord_6776124 prefixEnd_6776124 1159802862155583872462393 := by
  unfold tailWord_6776124
  simp only [CollatzResearch.WordTrace]
  refine ⟨123572773051633746344675713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164763697402178328459567617 123572773051633746344675713)
  ·
    refine ⟨92679579788725309758506785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123572773051633746344675713 92679579788725309758506785)
    ·
      refine ⟨69509684841543982318880089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92679579788725309758506785 69509684841543982318880089)
      ·
        refine ⟨52132263631157986739160067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69509684841543982318880089 52132263631157986739160067)
        ·
          refine ⟨78198395446736980108740101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52132263631157986739160067 78198395446736980108740101)
          ·
            refine ⟨14662199146263183770388769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78198395446736980108740101 14662199146263183770388769)
            ·
              refine ⟨10996649359697387827791577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14662199146263183770388769 10996649359697387827791577)
              ·
                refine ⟨8247487019773040870843683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10996649359697387827791577 8247487019773040870843683)
                ·
                  refine ⟨12371230529659561306265525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8247487019773040870843683 12371230529659561306265525)
                  ·
                    refine ⟨1159802862155583872462393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12371230529659561306265525 1159802862155583872462393)
                    ·
                      rfl

theorem cell23_6776124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_6776124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776124 prefixEnd_6776124 := by exact prefixLift 6776124
  have htrace : WordTrace (prefixWord ++ tailWord_6776124) baseStart_6776124 baseEnd_6776124 := by
    simpa [prefixWord, tailWord_6776124, baseEnd_6776124] using wordTrace_append hprefix tailTrace_6776124
  have hstable : (prefixWord ++ tailWord_6776124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776124).length < 2 ^ (prefixWord ++ tailWord_6776124).sum := by decide
  have hdescent : baseEnd_6776124 < baseStart_6776124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776137 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 4, 4]
def baseStart_6776137 : Nat := 118140960795 + 6776137 * 2 ^ 59
def prefixEnd_6776137 : Nat := 4983230072969 + 3 ^ 40 * 6776137 * 2
def baseEnd_6776137 : Nat := 1159805087238420022174873

theorem tailTrace_6776137 : CollatzResearch.WordTrace tailWord_6776137 prefixEnd_6776137 1159805087238420022174873 := by
  unfold tailWord_6776137
  simp only [CollatzResearch.WordTrace]
  refine ⟨247146020252220395909574665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164764013501480263939716443 247146020252220395909574665)
  ·
    refine ⟨185359515189165296932180999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247146020252220395909574665 185359515189165296932180999)
    ·
      refine ⟨278039272783747945398271499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185359515189165296932180999 278039272783747945398271499)
      ·
        refine ⟨417058909175621918097407249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278039272783747945398271499 417058909175621918097407249)
        ·
          refine ⟨312794181881716438573055437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417058909175621918097407249 312794181881716438573055437)
          ·
            refine ⟨117297818205643664464895789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312794181881716438573055437 117297818205643664464895789)
            ·
              refine ⟨43986681827116374174335921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117297818205643664464895789 43986681827116374174335921)
              ·
                refine ⟨32990011370337280630751941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43986681827116374174335921 32990011370337280630751941)
                ·
                  refine ⟨6185627131938240118265989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32990011370337280630751941 6185627131938240118265989)
                  ·
                    refine ⟨1159805087238420022174873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6185627131938240118265989 1159805087238420022174873)
                    ·
                      rfl

theorem cell23_6776137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 4].length) (baseStart_6776137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776137 prefixEnd_6776137 := by exact prefixLift 6776137
  have htrace : WordTrace (prefixWord ++ tailWord_6776137) baseStart_6776137 baseEnd_6776137 := by
    simpa [prefixWord, tailWord_6776137, baseEnd_6776137] using wordTrace_append hprefix tailTrace_6776137
  have hstable : (prefixWord ++ tailWord_6776137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776137).length < 2 ^ (prefixWord ++ tailWord_6776137).sum := by decide
  have hdescent : baseEnd_6776137 < baseStart_6776137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776147 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 5]
def baseStart_6776147 : Nat := 118140960795 + 6776147 * 2 ^ 59
def prefixEnd_6776147 : Nat := 4983230072969 + 3 ^ 40 * 6776147 * 2
def baseEnd_6776147 : Nat := 3479420396521805027399573

theorem tailTrace_6776147 : CollatzResearch.WordTrace tailWord_6776147 prefixEnd_6776147 3479420396521805027399573 := by
  unfold tailWord_6776147
  simp only [CollatzResearch.WordTrace]
  refine ⟨247146384982184167617438695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164764256654789445078292463 247146384982184167617438695)
  ·
    refine ⟨370719577473276251426158043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247146384982184167617438695 370719577473276251426158043)
    ·
      refine ⟨556079366209914377139237065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370719577473276251426158043 556079366209914377139237065)
      ·
        refine ⟨417059524657435782854427799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556079366209914377139237065 417059524657435782854427799)
        ·
          refine ⟨625589286986153674281641699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417059524657435782854427799 625589286986153674281641699)
          ·
            refine ⟨938383930479230511422462549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625589286986153674281641699 938383930479230511422462549)
            ·
              refine ⟨10996686685303482555731983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 938383930479230511422462549 10996686685303482555731983)
              ·
                refine ⟨16495030027955223833597975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10996686685303482555731983 16495030027955223833597975)
                ·
                  refine ⟨24742545041932835750396963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16495030027955223833597975 24742545041932835750396963)
                  ·
                    refine ⟨37113817562899253625595445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24742545041932835750396963 37113817562899253625595445)
                    ·
                      refine ⟨3479420396521805027399573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37113817562899253625595445 3479420396521805027399573)
                      ·
                        rfl

theorem cell23_6776147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 5].length) (baseStart_6776147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776147 prefixEnd_6776147 := by exact prefixLift 6776147
  have htrace : WordTrace (prefixWord ++ tailWord_6776147) baseStart_6776147 baseEnd_6776147 := by
    simpa [prefixWord, tailWord_6776147, baseEnd_6776147] using wordTrace_append hprefix tailTrace_6776147
  have hstable : (prefixWord ++ tailWord_6776147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776147).length < 2 ^ (prefixWord ++ tailWord_6776147).sum := by decide
  have hdescent : baseEnd_6776147 < baseStart_6776147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776181 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_6776181 : Nat := 118140960795 + 6776181 * 2 ^ 59
def prefixEnd_6776181 : Nat := 4983230072969 + 3 ^ 40 * 6776181 * 2
def baseEnd_6776181 : Nat := 3479437854864057894374417

theorem tailTrace_6776181 : CollatzResearch.WordTrace tailWord_6776181 prefixEnd_6776181 3479437854864057894374417 := by
  unfold tailWord_6776181
  simp only [CollatzResearch.WordTrace]
  refine ⟨247147625064060991424176397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164765083376040660949450931 247147625064060991424176397)
  ·
    refine ⟨92680359399022871784066149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247147625064060991424176397 92680359399022871784066149)
    ·
      refine ⟨17377567387316788459512403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92680359399022871784066149 17377567387316788459512403)
      ·
        refine ⟨26066351080975182689268605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17377567387316788459512403 26066351080975182689268605)
        ·
          refine ⟨9774881655365693508475727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26066351080975182689268605 9774881655365693508475727)
          ·
            refine ⟨14662322483048540262713591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9774881655365693508475727 14662322483048540262713591)
            ·
              refine ⟨21993483724572810394070387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14662322483048540262713591 21993483724572810394070387)
              ·
                refine ⟨32990225586859215591105581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21993483724572810394070387 32990225586859215591105581)
                ·
                  refine ⟨12371334595072205846664593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32990225586859215591105581 12371334595072205846664593)
                  ·
                    refine ⟨9278500946304154384998445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12371334595072205846664593 9278500946304154384998445)
                    ·
                      refine ⟨3479437854864057894374417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9278500946304154384998445 3479437854864057894374417)
                      ·
                        rfl

theorem cell23_6776181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_6776181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776181 prefixEnd_6776181 := by exact prefixLift 6776181
  have htrace : WordTrace (prefixWord ++ tailWord_6776181) baseStart_6776181 baseEnd_6776181 := by
    simpa [prefixWord, tailWord_6776181, baseEnd_6776181] using wordTrace_append hprefix tailTrace_6776181
  have hstable : (prefixWord ++ tailWord_6776181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776181).length < 2 ^ (prefixWord ++ tailWord_6776181).sum := by decide
  have hdescent : baseEnd_6776181 < baseStart_6776181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776212 : List Nat := [2, 4, 2, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_6776212 : Nat := 118140960795 + 6776212 * 2 ^ 59
def prefixEnd_6776212 : Nat := 4983230072969 + 3 ^ 40 * 6776212 * 2
def baseEnd_6776212 : Nat := 3479453772764347273086775

theorem tailTrace_6776212 : CollatzResearch.WordTrace tailWord_6776212 prefixEnd_6776212 3479453772764347273086775 := by
  unfold tailWord_6776212
  simp only [CollatzResearch.WordTrace]
  refine ⟨123574377863474341859277445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164765837151299122479036593 123574377863474341859277445)
  ·
    refine ⟨23170195849401439098614521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123574377863474341859277445 23170195849401439098614521)
    ·
      refine ⟨17377646887051079323960891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23170195849401439098614521 17377646887051079323960891)
      ·
        refine ⟨26066470330576618985941337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17377646887051079323960891 26066470330576618985941337)
        ·
          refine ⟨19549852747932464239456003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26066470330576618985941337 19549852747932464239456003)
          ·
            refine ⟨29324779121898696359184005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19549852747932464239456003 29324779121898696359184005)
            ·
              refine ⟨5498396085356005567347001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29324779121898696359184005 5498396085356005567347001)
              ·
                refine ⟨4123797064017004175510251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498396085356005567347001 4123797064017004175510251)
                ·
                  refine ⟨6185695596025506263265377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123797064017004175510251 6185695596025506263265377)
                  ·
                    refine ⟨4639271697019129697449033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6185695596025506263265377 4639271697019129697449033)
                    ·
                      refine ⟨3479453772764347273086775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639271697019129697449033 3479453772764347273086775)
                      ·
                        rfl

theorem cell23_6776212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_6776212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776212 prefixEnd_6776212 := by exact prefixLift 6776212
  have htrace : WordTrace (prefixWord ++ tailWord_6776212) baseStart_6776212 baseEnd_6776212 := by
    simpa [prefixWord, tailWord_6776212, baseEnd_6776212] using wordTrace_append hprefix tailTrace_6776212
  have hstable : (prefixWord ++ tailWord_6776212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776212).length < 2 ^ (prefixWord ++ tailWord_6776212).sum := by decide
  have hdescent : baseEnd_6776212 < baseStart_6776212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776217 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_6776217 : Nat := 118140960795 + 6776217 * 2 ^ 59
def prefixEnd_6776217 : Nat := 4983230072969 + 3 ^ 40 * 6776217 * 2
def baseEnd_6776217 : Nat := 3479456340167619753524251

theorem tailTrace_6776217 : CollatzResearch.WordTrace tailWord_6776217 prefixEnd_6776217 3479456340167619753524251 := by
  unfold tailWord_6776217
  simp only [CollatzResearch.WordTrace]
  refine ⟨247148938091930569572486905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164765958727953713048324603 247148938091930569572486905)
  ·
    refine ⟨185361703568947927179365179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247148938091930569572486905 185361703568947927179365179)
    ·
      refine ⟨278042555353421890769047769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185361703568947927179365179 278042555353421890769047769)
      ·
        refine ⟨208531916515066418076785827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278042555353421890769047769 208531916515066418076785827)
        ·
          refine ⟨312797874772599627115178741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208531916515066418076785827 312797874772599627115178741)
          ·
            refine ⟨29324800759931215042048007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 312797874772599627115178741 29324800759931215042048007)
            ·
              refine ⟨43987201139896822563072011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29324800759931215042048007 43987201139896822563072011)
              ·
                refine ⟨65980801709845233844608017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43987201139896822563072011 65980801709845233844608017)
                ·
                  refine ⟨49485601282383925383456013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65980801709845233844608017 49485601282383925383456013)
                  ·
                    refine ⟨18557100480893972018796005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49485601282383925383456013 18557100480893972018796005)
                    ·
                      refine ⟨3479456340167619753524251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18557100480893972018796005 3479456340167619753524251)
                      ·
                        rfl

theorem cell23_6776217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_6776217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776217 prefixEnd_6776217 := by exact prefixLift 6776217
  have htrace : WordTrace (prefixWord ++ tailWord_6776217) baseStart_6776217 baseEnd_6776217 := by
    simpa [prefixWord, tailWord_6776217, baseEnd_6776217] using wordTrace_append hprefix tailTrace_6776217
  have hstable : (prefixWord ++ tailWord_6776217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776217).length < 2 ^ (prefixWord ++ tailWord_6776217).sum := by decide
  have hdescent : baseEnd_6776217 < baseStart_6776217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776221 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_6776221 : Nat := 118140960795 + 6776221 * 2 ^ 59
def prefixEnd_6776221 : Nat := 4983230072969 + 3 ^ 40 * 6776221 * 2
def baseEnd_6776221 : Nat := 3479458394090237737874233

theorem tailTrace_6776221 : CollatzResearch.WordTrace tailWord_6776221 prefixEnd_6776221 3479458394090237737874233 := by
  unfold tailWord_6776221
  simp only [CollatzResearch.WordTrace]
  refine ⟨247149083983916078255632517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164766055989277385503755011 247149083983916078255632517)
  ·
    refine ⟨46340453246984264672931097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247149083983916078255632517 46340453246984264672931097)
    ·
      refine ⟨34755339935238198504698323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46340453246984264672931097 34755339935238198504698323)
      ·
        refine ⟨52133009902857297757047485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34755339935238198504698323 52133009902857297757047485)
        ·
          refine ⟨19549878713571486658892807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52133009902857297757047485 19549878713571486658892807)
          ·
            refine ⟨29324818070357229988339211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19549878713571486658892807 29324818070357229988339211)
            ·
              refine ⟨43987227105535844982508817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29324818070357229988339211 43987227105535844982508817)
              ·
                refine ⟨32990420329151883736881613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43987227105535844982508817 32990420329151883736881613)
                ·
                  refine ⟨12371407623431956401330605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32990420329151883736881613 12371407623431956401330605)
                  ·
                    refine ⟨4639277858786983650498977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12371407623431956401330605 4639277858786983650498977)
                    ·
                      refine ⟨3479458394090237737874233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639277858786983650498977 3479458394090237737874233)
                      ·
                        rfl

theorem cell23_6776221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_6776221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776221 prefixEnd_6776221 := by exact prefixLift 6776221
  have htrace : WordTrace (prefixWord ++ tailWord_6776221) baseStart_6776221 baseEnd_6776221 := by
    simpa [prefixWord, tailWord_6776221, baseEnd_6776221] using wordTrace_append hprefix tailTrace_6776221
  have hstable : (prefixWord ++ tailWord_6776221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776221).length < 2 ^ (prefixWord ++ tailWord_6776221).sum := by decide
  have hdescent : baseEnd_6776221 < baseStart_6776221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776227 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 2, 6]
def baseStart_6776227 : Nat := 118140960795 + 6776227 * 2 ^ 59
def prefixEnd_6776227 : Nat := 4983230072969 + 3 ^ 40 * 6776227 * 2
def baseEnd_6776227 : Nat := 1159820491658054904799735

theorem tailTrace_6776227 : CollatzResearch.WordTrace tailWord_6776227 prefixEnd_6776227 1159820491658054904799735 := by
  unfold tailWord_6776227
  simp only [CollatzResearch.WordTrace]
  refine ⟨247149302821894341280350935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164766201881262894186900623 247149302821894341280350935)
  ·
    refine ⟨370723954232841511920526403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247149302821894341280350935 370723954232841511920526403)
    ·
      refine ⟨556085931349262267880789605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370723954232841511920526403 556085931349262267880789605)
      ·
        refine ⟨104266112127986675227648051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 556085931349262267880789605 104266112127986675227648051)
        ·
          refine ⟨156399168191980012841472077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104266112127986675227648051 156399168191980012841472077)
          ·
            refine ⟨58649688071992504815552029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156399168191980012841472077 58649688071992504815552029)
            ·
              refine ⟨21993633026997189305832011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58649688071992504815552029 21993633026997189305832011)
              ·
                refine ⟨32990449540495783958748017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21993633026997189305832011 32990449540495783958748017)
                ·
                  refine ⟨24742837155371837969061013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32990449540495783958748017 24742837155371837969061013)
                  ·
                    refine ⟨1159820491658054904799735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24742837155371837969061013 1159820491658054904799735)
                    ·
                      rfl

theorem cell23_6776227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 6].length) (baseStart_6776227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776227 prefixEnd_6776227 := by exact prefixLift 6776227
  have htrace : WordTrace (prefixWord ++ tailWord_6776227) baseStart_6776227 baseEnd_6776227 := by
    simpa [prefixWord, tailWord_6776227, baseEnd_6776227] using wordTrace_append hprefix tailTrace_6776227
  have hstable : (prefixWord ++ tailWord_6776227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776227).length < 2 ^ (prefixWord ++ tailWord_6776227).sum := by decide
  have hdescent : baseEnd_6776227 < baseStart_6776227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776247 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_6776247 : Nat := 118140960795 + 6776247 * 2 ^ 59
def prefixEnd_6776247 : Nat := 4983230072969 + 3 ^ 40 * 6776247 * 2
def baseEnd_6776247 : Nat := 3479471744587254636149113

theorem tailTrace_6776247 : CollatzResearch.WordTrace tailWord_6776247 prefixEnd_6776247 3479471744587254636149113 := by
  unfold tailWord_6776247
  simp only [CollatzResearch.WordTrace]
  refine ⟨247150032281821884696078995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164766688187881256464052663 247150032281821884696078995)
  ·
    refine ⟨370725048422732827044118493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247150032281821884696078995 370725048422732827044118493)
    ·
      refine ⟨139021893158524810141544435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370725048422732827044118493 139021893158524810141544435)
      ·
        refine ⟨208532839737787215212316653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139021893158524810141544435 208532839737787215212316653)
        ·
          refine ⟨78199814901670205704618745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208532839737787215212316653 78199814901670205704618745)
          ·
            refine ⟨58649861176252654278464059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78199814901670205704618745 58649861176252654278464059)
            ·
              refine ⟨87974791764378981417696089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58649861176252654278464059 87974791764378981417696089)
              ·
                refine ⟨65981093823284236063272067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87974791764378981417696089 65981093823284236063272067)
                ·
                  refine ⟨98971640734926354094908101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65981093823284236063272067 98971640734926354094908101)
                  ·
                    refine ⟨18557182637798691392795269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98971640734926354094908101 18557182637798691392795269)
                    ·
                      refine ⟨3479471744587254636149113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18557182637798691392795269 3479471744587254636149113)
                      ·
                        rfl

theorem cell23_6776247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_6776247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776247 prefixEnd_6776247 := by exact prefixLift 6776247
  have htrace : WordTrace (prefixWord ++ tailWord_6776247) baseStart_6776247 baseEnd_6776247 := by
    simpa [prefixWord, tailWord_6776247, baseEnd_6776247] using wordTrace_append hprefix tailTrace_6776247
  have hstable : (prefixWord ++ tailWord_6776247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776247).length < 2 ^ (prefixWord ++ tailWord_6776247).sum := by decide
  have hdescent : baseEnd_6776247 < baseStart_6776247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776268 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 4, 2, 2]
def baseStart_6776268 : Nat := 118140960795 + 6776268 * 2 ^ 59
def prefixEnd_6776268 : Nat := 4983230072969 + 3 ^ 40 * 6776268 * 2
def baseEnd_6776268 : Nat := 3479482527680999053986517

theorem tailTrace_6776268 : CollatzResearch.WordTrace tailWord_6776268 prefixEnd_6776268 3479482527680999053986517 := by
  unfold tailWord_6776268
  simp only [CollatzResearch.WordTrace]
  refine ⟨123575399107372902641296729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164767198809830536855062305 123575399107372902641296729)
  ·
    refine ⟨92681549330529676980972547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123575399107372902641296729 92681549330529676980972547)
    ·
      refine ⟨139022323995794515471458821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92681549330529676980972547 139022323995794515471458821)
      ·
        refine ⟨26066685749211471650898529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139022323995794515471458821 26066685749211471650898529)
        ·
          refine ⟨19550014311908603738173897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26066685749211471650898529 19550014311908603738173897)
          ·
            refine ⟨14662510733931452803630423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19550014311908603738173897 14662510733931452803630423)
            ·
              refine ⟨21993766100897179205445635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14662510733931452803630423 21993766100897179205445635)
              ·
                refine ⟨32990649151345768808168453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21993766100897179205445635 32990649151345768808168453)
                ·
                  refine ⟨6185746715877331651531585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32990649151345768808168453 6185746715877331651531585)
                  ·
                    refine ⟨4639310036907998738648689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6185746715877331651531585 4639310036907998738648689)
                    ·
                      refine ⟨3479482527680999053986517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639310036907998738648689 3479482527680999053986517)
                      ·
                        rfl

theorem cell23_6776268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_6776268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776268 prefixEnd_6776268 := by exact prefixLift 6776268
  have htrace : WordTrace (prefixWord ++ tailWord_6776268) baseStart_6776268 baseEnd_6776268 := by
    simpa [prefixWord, tailWord_6776268, baseEnd_6776268] using wordTrace_append hprefix tailTrace_6776268
  have hstable : (prefixWord ++ tailWord_6776268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776268).length < 2 ^ (prefixWord ++ tailWord_6776268).sum := by decide
  have hdescent : baseEnd_6776268 < baseStart_6776268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776287 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 3, 7]
def baseStart_6776287 : Nat := 118140960795 + 6776287 * 2 ^ 59
def prefixEnd_6776287 : Nat := 4983230072969 + 3 ^ 40 * 6776287 * 2
def baseEnd_6776287 : Nat := 1159830761271144826549643

theorem tailTrace_6776287 : CollatzResearch.WordTrace tailWord_6776287 prefixEnd_6776287 1159830761271144826549643 := by
  unfold tailWord_6776287
  simp only [CollatzResearch.WordTrace]
  refine ⟨247151491201676971527535115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164767660801117981018356743 247151491201676971527535115)
  ·
    refine ⟨370727236802515457291302673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247151491201676971527535115 370727236802515457291302673)
    ·
      refine ⟨278045427601886592968477005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370727236802515457291302673 278045427601886592968477005)
      ·
        refine ⟨104267035350707472363178877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278045427601886592968477005 104267035350707472363178877)
        ·
          refine ⟨39100138256515302136192079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104267035350707472363178877 39100138256515302136192079)
          ·
            refine ⟨58650207384772953204288119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39100138256515302136192079 58650207384772953204288119)
            ·
              refine ⟨87975311077159429806432179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58650207384772953204288119 87975311077159429806432179)
              ·
                refine ⟨131962966615739144709648269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87975311077159429806432179 131962966615739144709648269)
                ·
                  refine ⟨49486112480902179266118101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131962966615739144709648269 49486112480902179266118101)
                  ·
                    refine ⟨1159830761271144826549643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49486112480902179266118101 1159830761271144826549643)
                    ·
                      rfl

theorem cell23_6776287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_6776287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776287 prefixEnd_6776287 := by exact prefixLift 6776287
  have htrace : WordTrace (prefixWord ++ tailWord_6776287) baseStart_6776287 baseEnd_6776287 := by
    simpa [prefixWord, tailWord_6776287, baseEnd_6776287] using wordTrace_append hprefix tailTrace_6776287
  have hstable : (prefixWord ++ tailWord_6776287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776287).length < 2 ^ (prefixWord ++ tailWord_6776287).sum := by decide
  have hdescent : baseEnd_6776287 < baseStart_6776287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776321 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 2, 5]
def baseStart_6776321 : Nat := 118140960795 + 6776321 * 2 ^ 59
def prefixEnd_6776321 : Nat := 4983230072969 + 3 ^ 40 * 6776321 * 2
def baseEnd_6776321 : Nat := 1159836580718562448874591

theorem tailTrace_6776321 : CollatzResearch.WordTrace tailWord_6776321 prefixEnd_6776321 1159836580718562448874591 := by
  unfold tailWord_6776321
  simp only [CollatzResearch.WordTrace]
  refine ⟨247152731283553795334272817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164768487522369196889515211 247152731283553795334272817)
  ·
    refine ⟨185364548462665346500704613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247152731283553795334272817 185364548462665346500704613)
    ·
      refine ⟨34755852836749752468882115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185364548462665346500704613 34755852836749752468882115)
      ·
        refine ⟨52133779255124628703323173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34755852836749752468882115 52133779255124628703323173)
        ·
          refine ⟨9775083610335867881873095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52133779255124628703323173 9775083610335867881873095)
          ·
            refine ⟨14662625415503801822809643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9775083610335867881873095 14662625415503801822809643)
            ·
              refine ⟨21993938123255702734214465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14662625415503801822809643 21993938123255702734214465)
              ·
                refine ⟨16495453592441777050660849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21993938123255702734214465 16495453592441777050660849)
                ·
                  refine ⟨12371590194331332787995637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16495453592441777050660849 12371590194331332787995637)
                  ·
                    refine ⟨1159836580718562448874591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12371590194331332787995637 1159836580718562448874591)
                    ·
                      rfl

theorem cell23_6776321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_6776321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776321 prefixEnd_6776321 := by exact prefixLift 6776321
  have htrace : WordTrace (prefixWord ++ tailWord_6776321) baseStart_6776321 baseEnd_6776321 := by
    simpa [prefixWord, tailWord_6776321, baseEnd_6776321] using wordTrace_append hprefix tailTrace_6776321
  have hstable : (prefixWord ++ tailWord_6776321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776321).length < 2 ^ (prefixWord ++ tailWord_6776321).sum := by decide
  have hdescent : baseEnd_6776321 < baseStart_6776321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776354 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_6776354 : Nat := 118140960795 + 6776354 * 2 ^ 59
def prefixEnd_6776354 : Nat := 4983230072969 + 3 ^ 40 * 6776354 * 2
def baseEnd_6776354 : Nat := 3479526687017285717511121

theorem tailTrace_6776354 : CollatzResearch.WordTrace tailWord_6776354 prefixEnd_6776354 3479526687017285717511121 := by
  unfold tailWord_6776354
  simp only [CollatzResearch.WordTrace]
  refine ⟨61788483723108560492556029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164769289928289494646816077 61788483723108560492556029)
  ·
    refine ⟨23170681396165710184708511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61788483723108560492556029 23170681396165710184708511)
    ·
      refine ⟨34756022094248565277062767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23170681396165710184708511 34756022094248565277062767)
      ·
        refine ⟨52134033141372847915594151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34756022094248565277062767 52134033141372847915594151)
        ·
          refine ⟨78201049712059271873391227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52134033141372847915594151 78201049712059271873391227)
          ·
            refine ⟨117301574568088907810086841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78201049712059271873391227 117301574568088907810086841)
            ·
              refine ⟨87976180926066680857565131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117301574568088907810086841 87976180926066680857565131)
              ·
                refine ⟨131964271389100021286347697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87976180926066680857565131 131964271389100021286347697)
                ·
                  refine ⟨98973203541825015964760773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131964271389100021286347697 98973203541825015964760773)
                  ·
                    refine ⟨18557475664092190493392645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98973203541825015964760773 18557475664092190493392645)
                    ·
                      refine ⟨3479526687017285717511121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18557475664092190493392645 3479526687017285717511121)
                      ·
                        rfl

theorem cell23_6776354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_6776354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776354 prefixEnd_6776354 := by exact prefixLift 6776354
  have htrace : WordTrace (prefixWord ++ tailWord_6776354) baseStart_6776354 baseEnd_6776354 := by
    simpa [prefixWord, tailWord_6776354, baseEnd_6776354] using wordTrace_append hprefix tailTrace_6776354
  have hstable : (prefixWord ++ tailWord_6776354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776354).length < 2 ^ (prefixWord ++ tailWord_6776354).sum := by decide
  have hdescent : baseEnd_6776354 < baseStart_6776354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776394 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_6776394 : Nat := 118140960795 + 6776394 * 2 ^ 59
def prefixEnd_6776394 : Nat := 4983230072969 + 3 ^ 40 * 6776394 * 2
def baseEnd_6776394 : Nat := 1159849075414488520336979

theorem tailTrace_6776394 : CollatzResearch.WordTrace tailWord_6776394 prefixEnd_6776394 1159849075414488520336979 := by
  unfold tailWord_6776394
  simp only [CollatzResearch.WordTrace]
  refine ⟨61788848453072332200420059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164770262541526219201120157 61788848453072332200420059)
  ·
    refine ⟨92683272679608498300630089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61788848453072332200420059 92683272679608498300630089)
    ·
      refine ⟨69512454509706373725472567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92683272679608498300630089 69512454509706373725472567)
      ·
        refine ⟨104268681764559560588208851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69512454509706373725472567 104268681764559560588208851)
        ·
          refine ⟨156403022646839340882313277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104268681764559560588208851 156403022646839340882313277)
          ·
            refine ⟨58651133492564752830867479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156403022646839340882313277 58651133492564752830867479)
            ·
              refine ⟨87976700238847129246301219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58651133492564752830867479 87976700238847129246301219)
              ·
                refine ⟨131965050358270693869451829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87976700238847129246301219 131965050358270693869451829)
                ·
                  refine ⟨12371723471087877550261109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131965050358270693869451829 12371723471087877550261109)
                  ·
                    refine ⟨1159849075414488520336979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12371723471087877550261109 1159849075414488520336979)
                    ·
                      rfl

theorem cell23_6776394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_6776394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776394 prefixEnd_6776394 := by exact prefixLift 6776394
  have htrace : WordTrace (prefixWord ++ tailWord_6776394) baseStart_6776394 baseEnd_6776394 := by
    simpa [prefixWord, tailWord_6776394, baseEnd_6776394] using wordTrace_append hprefix tailTrace_6776394
  have hstable : (prefixWord ++ tailWord_6776394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776394).length < 2 ^ (prefixWord ++ tailWord_6776394).sum := by decide
  have hdescent : baseEnd_6776394 < baseStart_6776394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776401 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 1, 5, 2]
def baseStart_6776401 : Nat := 118140960795 + 6776401 * 2 ^ 59
def prefixEnd_6776401 : Nat := 4983230072969 + 3 ^ 40 * 6776401 * 2
def baseEnd_6776401 : Nat := 3479550820608047033623405

theorem tailTrace_6776401 : CollatzResearch.WordTrace tailWord_6776401 prefixEnd_6776401 3479550820608047033623405 := by
  unfold tailWord_6776401
  simp only [CollatzResearch.WordTrace]
  refine ⟨247155649123263968997185057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164770432748842645998123371 247155649123263968997185057)
  ·
    refine ⟨185366736842447976747888793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247155649123263968997185057 185366736842447976747888793)
    ·
      refine ⟨139025052631835982560916595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185366736842447976747888793 139025052631835982560916595)
      ·
        refine ⟨208537578947753973841374893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139025052631835982560916595 208537578947753973841374893)
        ·
          refine ⟨78201592105407740190515585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208537578947753973841374893 78201592105407740190515585)
          ·
            refine ⟨58651194079055805142886689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78201592105407740190515585 58651194079055805142886689)
            ·
              refine ⟨43988395559291853857165017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58651194079055805142886689 43988395559291853857165017)
              ·
                refine ⟨32991296669468890392873763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43988395559291853857165017 32991296669468890392873763)
                ·
                  refine ⟨49486945004203335589310645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32991296669468890392873763 49486945004203335589310645)
                  ·
                    refine ⟨4639401094144062711497873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49486945004203335589310645 4639401094144062711497873)
                    ·
                      refine ⟨3479550820608047033623405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4639401094144062711497873 3479550820608047033623405)
                      ·
                        rfl

theorem cell23_6776401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_6776401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776401 prefixEnd_6776401 := by exact prefixLift 6776401
  have htrace : WordTrace (prefixWord ++ tailWord_6776401) baseStart_6776401 baseEnd_6776401 := by
    simpa [prefixWord, tailWord_6776401, baseEnd_6776401] using wordTrace_append hprefix tailTrace_6776401
  have hstable : (prefixWord ++ tailWord_6776401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776401).length < 2 ^ (prefixWord ++ tailWord_6776401).sum := by decide
  have hdescent : baseEnd_6776401 < baseStart_6776401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6776404 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_6776404 : Nat := 118140960795 + 6776404 * 2 ^ 59
def prefixEnd_6776404 : Nat := 4983230072969 + 3 ^ 40 * 6776404 * 2
def baseEnd_6776404 : Nat := 3479552361050010521885891

theorem tailTrace_6776404 : CollatzResearch.WordTrace tailWord_6776404 prefixEnd_6776404 3479552361050010521885891 := by
  unfold tailWord_6776404
  simp only [CollatzResearch.WordTrace]
  refine ⟨123577879271126550254772133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164770505694835400339696177 123577879271126550254772133)
  ·
    refine ⟨23170852363336228172769775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123577879271126550254772133 23170852363336228172769775)
    ·
      refine ⟨34756278545004342259154663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23170852363336228172769775 34756278545004342259154663)
      ·
        refine ⟨52134417817506513388731995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34756278545004342259154663 52134417817506513388731995)
        ·
          refine ⟨78201626726259770083097993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52134417817506513388731995 78201626726259770083097993)
          ·
            refine ⟨58651220044694827562323495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78201626726259770083097993 58651220044694827562323495)
            ·
              refine ⟨87976830067042241343485243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58651220044694827562323495 87976830067042241343485243)
              ·
                refine ⟨131965245100563362015227865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87976830067042241343485243 131965245100563362015227865)
                ·
                  refine ⟨98973933825422521511420899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131965245100563362015227865 98973933825422521511420899)
                  ·
                    refine ⟨148460900738133782267131349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98973933825422521511420899 148460900738133782267131349)
                    ·
                      refine ⟨3479552361050010521885891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148460900738133782267131349 3479552361050010521885891)
                      ·
                        rfl

theorem cell23_6776404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_6776404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6776404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6776404 prefixEnd_6776404 := by exact prefixLift 6776404
  have htrace : WordTrace (prefixWord ++ tailWord_6776404) baseStart_6776404 baseEnd_6776404 := by
    simpa [prefixWord, tailWord_6776404, baseEnd_6776404] using wordTrace_append hprefix tailTrace_6776404
  have hstable : (prefixWord ++ tailWord_6776404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6776404).length < 2 ^ (prefixWord ++ tailWord_6776404).sum := by decide
  have hdescent : baseEnd_6776404 < baseStart_6776404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6776404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
