import V185TrunkScan23Chunk0527

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3121838 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_3121838 : Nat := 118140960795 + 3121838 * 2 ^ 59
def prefixEnd_3121838 : Nat := 4983230072969 + 3 ^ 40 * 3121838 * 2
def baseEnd_3121838 : Nat := 1603003419470862028167935

theorem tailTrace_3121838 : CollatzResearch.WordTrace tailWord_3121838 prefixEnd_3121838 1603003419470862028167935 := by
  unfold tailWord_3121838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14232848258015196040984771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75908524042747712218585445 14232848258015196040984771)
  ·
    refine ⟨21349272387022794061477157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14232848258015196040984771 21349272387022794061477157)
    ·
      refine ⟨4002988572566773886526967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21349272387022794061477157 4002988572566773886526967)
      ·
        refine ⟨6004482858850160829790451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4002988572566773886526967 6004482858850160829790451)
        ·
          refine ⟨9006724288275241244685677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6004482858850160829790451 9006724288275241244685677)
          ·
            refine ⟨3377521608103215466757129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9006724288275241244685677 3377521608103215466757129)
            ·
              refine ⟨2533141206077411600067847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3377521608103215466757129 2533141206077411600067847)
              ·
                refine ⟨3799711809116117400101771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533141206077411600067847 3799711809116117400101771)
                ·
                  refine ⟨5699567713674176100152657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3799711809116117400101771 5699567713674176100152657)
                  ·
                    refine ⟨4274675785255632075114493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5699567713674176100152657 4274675785255632075114493)
                    ·
                      refine ⟨1603003419470862028167935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4274675785255632075114493 1603003419470862028167935)
                      ·
                        rfl

theorem cell23_3121838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_3121838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121838 prefixEnd_3121838 := by exact prefixLift 3121838
  have htrace : WordTrace (prefixWord ++ tailWord_3121838) baseStart_3121838 baseEnd_3121838 := by
    simpa [prefixWord, tailWord_3121838, baseEnd_3121838] using wordTrace_append hprefix tailTrace_3121838
  have hstable : (prefixWord ++ tailWord_3121838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121838).length < 2 ^ (prefixWord ++ tailWord_3121838).sum := by decide
  have hdescent : baseEnd_3121838 < baseStart_3121838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121880 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 7]
def baseStart_3121880 : Nat := 118140960795 + 3121880 * 2 ^ 59
def prefixEnd_3121880 : Nat := 4983230072969 + 3 ^ 40 * 3121880 * 2
def baseEnd_3121880 : Nat := 178113887295372318204749

theorem tailTrace_3121880 : CollatzResearch.WordTrace tailWord_3121880 prefixEnd_3121880 178113887295372318204749 := by
  unfold tailWord_3121880
  simp only [CollatzResearch.WordTrace]
  refine ⟨56932158964984704750453547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75909545286646273000604729 56932158964984704750453547)
  ·
    refine ⟨85398238447477057125680321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56932158964984704750453547 85398238447477057125680321)
    ·
      refine ⟨64048678835607792844260241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85398238447477057125680321 64048678835607792844260241)
      ·
        refine ⟨48036509126705844633195181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64048678835607792844260241 48036509126705844633195181)
        ·
          refine ⟨18013690922514691737448193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48036509126705844633195181 18013690922514691737448193)
          ·
            refine ⟨13510268191886018803086145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18013690922514691737448193 13510268191886018803086145)
            ·
              refine ⟨10132701143914514102314609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13510268191886018803086145 10132701143914514102314609)
              ·
                refine ⟨7599525857935885576735957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10132701143914514102314609 7599525857935885576735957)
                ·
                  refine ⟨178113887295372318204749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7599525857935885576735957 178113887295372318204749)
                  ·
                    rfl

theorem cell23_3121880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 7].length) (baseStart_3121880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121880 prefixEnd_3121880 := by exact prefixLift 3121880
  have htrace : WordTrace (prefixWord ++ tailWord_3121880) baseStart_3121880 baseEnd_3121880 := by
    simpa [prefixWord, tailWord_3121880, baseEnd_3121880] using wordTrace_append hprefix tailTrace_3121880
  have hstable : (prefixWord ++ tailWord_3121880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121880).length < 2 ^ (prefixWord ++ tailWord_3121880).sum := by decide
  have hdescent : baseEnd_3121880 < baseStart_3121880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121883 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8]
def baseStart_3121883 : Nat := 118140960795 + 3121883 * 2 ^ 59
def prefixEnd_3121883 : Nat := 4983230072969 + 3 ^ 40 * 3121883 * 2
def baseEnd_3121883 : Nat := 1603026526100314352105227

theorem tailTrace_3121883 : CollatzResearch.WordTrace tailWord_3121883 prefixEnd_3121883 1603026526100314352105227 := by
  unfold tailWord_3121883
  simp only [CollatzResearch.WordTrace]
  refine ⟨113864427348958541013266303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75909618232639027342177535 113864427348958541013266303)
  ·
    refine ⟨170796641023437811519899455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113864427348958541013266303 170796641023437811519899455)
    ·
      refine ⟨256194961535156717279849183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170796641023437811519899455 256194961535156717279849183)
      ·
        refine ⟨384292442302735075919773775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256194961535156717279849183 384292442302735075919773775)
        ·
          refine ⟨576438663454102613879660663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384292442302735075919773775 576438663454102613879660663)
          ·
            refine ⟨864657995181153920819490995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576438663454102613879660663 864657995181153920819490995)
            ·
              refine ⟨1296986992771730881229236493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864657995181153920819490995 1296986992771730881229236493)
              ·
                refine ⟨486370122289399080460963685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1296986992771730881229236493 486370122289399080460963685)
                ·
                  refine ⟨91194397929262327586430691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 486370122289399080460963685 91194397929262327586430691)
                  ·
                    refine ⟨136791596893893491379646037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91194397929262327586430691 136791596893893491379646037)
                    ·
                      refine ⟨1603026526100314352105227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 136791596893893491379646037 1603026526100314352105227)
                      ·
                        rfl

theorem cell23_3121883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_3121883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121883 prefixEnd_3121883 := by exact prefixLift 3121883
  have htrace : WordTrace (prefixWord ++ tailWord_3121883) baseStart_3121883 baseEnd_3121883 := by
    simpa [prefixWord, tailWord_3121883, baseEnd_3121883] using wordTrace_append hprefix tailTrace_3121883
  have hstable : (prefixWord ++ tailWord_3121883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121883).length < 2 ^ (prefixWord ++ tailWord_3121883).sum := by decide
  have hdescent : baseEnd_3121883 < baseStart_3121883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121897 : List Nat := [1, 2, 1, 1, 1, 2, 7, 3, 5]
def baseStart_3121897 : Nat := 118140960795 + 3121897 * 2 ^ 59
def prefixEnd_3121897 : Nat := 4983230072969 + 3 ^ 40 * 3121897 * 2
def baseEnd_3121897 : Nat := 178114857203275255258907

theorem tailTrace_3121897 : CollatzResearch.WordTrace tailWord_3121897 prefixEnd_3121897 178114857203275255258907 := by
  unfold tailWord_3121897
  simp only [CollatzResearch.WordTrace]
  refine ⟨113864937970907821404275945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75909958647271880936183963 113864937970907821404275945)
  ·
    refine ⟨85398703478180866053206959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113864937970907821404275945 85398703478180866053206959)
    ·
      refine ⟨128098055217271299079810439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85398703478180866053206959 128098055217271299079810439)
      ·
        refine ⟨192147082825906948619715659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128098055217271299079810439 192147082825906948619715659)
        ·
          refine ⟨288220624238860422929573489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192147082825906948619715659 288220624238860422929573489)
          ·
            refine ⟨216165468179145317197180117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288220624238860422929573489 216165468179145317197180117)
            ·
              refine ⟨5066378160448718371808909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 216165468179145317197180117 5066378160448718371808909)
              ·
                refine ⟨1899891810168269389428341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5066378160448718371808909 1899891810168269389428341)
                ·
                  refine ⟨178114857203275255258907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1899891810168269389428341 178114857203275255258907)
                  ·
                    rfl

theorem cell23_3121897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 5].length) (baseStart_3121897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121897 prefixEnd_3121897 := by exact prefixLift 3121897
  have htrace : WordTrace (prefixWord ++ tailWord_3121897) baseStart_3121897 baseEnd_3121897 := by
    simpa [prefixWord, tailWord_3121897, baseEnd_3121897] using wordTrace_append hprefix tailTrace_3121897
  have hstable : (prefixWord ++ tailWord_3121897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121897).length < 2 ^ (prefixWord ++ tailWord_3121897).sum := by decide
  have hdescent : baseEnd_3121897 < baseStart_3121897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121917 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 2, 5, 2]
def baseStart_3121917 : Nat := 118140960795 + 3121917 * 2 ^ 59
def prefixEnd_3121917 : Nat := 4983230072969 + 3 ^ 40 * 3121917 * 2
def baseEnd_3121917 : Nat := 1603043984442567219080071

theorem tailTrace_3121917 : CollatzResearch.WordTrace tailWord_3121917 prefixEnd_3121917 1603043984442567219080071 := by
  unfold tailWord_3121917
  simp only [CollatzResearch.WordTrace]
  refine ⟨113865667430835364820004005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75910444953890243213336003 113865667430835364820004005)
  ·
    refine ⟨21349812643281630903750751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113865667430835364820004005 21349812643281630903750751)
    ·
      refine ⟨32024718964922446355626127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21349812643281630903750751 32024718964922446355626127)
      ·
        refine ⟨48037078447383669533439191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32024718964922446355626127 48037078447383669533439191)
        ·
          refine ⟨72055617671075504300158787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48037078447383669533439191 72055617671075504300158787)
          ·
            refine ⟨108083426506613256450238181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72055617671075504300158787 108083426506613256450238181)
            ·
              refine ⟨20265642469989985584419659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108083426506613256450238181 20265642469989985584419659)
              ·
                refine ⟨30398463704984978376629489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20265642469989985584419659 30398463704984978376629489)
                ·
                  refine ⟨22798847778738733782472117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30398463704984978376629489 22798847778738733782472117)
                  ·
                    refine ⟨2137391979256756292106761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22798847778738733782472117 2137391979256756292106761)
                    ·
                      refine ⟨1603043984442567219080071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137391979256756292106761 1603043984442567219080071)
                      ·
                        rfl

theorem cell23_3121917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_3121917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121917 prefixEnd_3121917 := by exact prefixLift 3121917
  have htrace : WordTrace (prefixWord ++ tailWord_3121917) baseStart_3121917 baseEnd_3121917 := by
    simpa [prefixWord, tailWord_3121917, baseEnd_3121917] using wordTrace_append hprefix tailTrace_3121917
  have hstable : (prefixWord ++ tailWord_3121917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121917).length < 2 ^ (prefixWord ++ tailWord_3121917).sum := by decide
  have hdescent : baseEnd_3121917 < baseStart_3121917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121965 : List Nat := [1, 5, 3, 2, 1, 2, 2, 2, 5]
def baseStart_3121965 : Nat := 118140960795 + 3121965 * 2 ^ 59
def prefixEnd_3121965 : Nat := 4983230072969 + 3 ^ 40 * 3121965 * 2
def baseEnd_3121965 : Nat := 178118736834887003475539

theorem tailTrace_3121965 : CollatzResearch.WordTrace tailWord_3121965 prefixEnd_3121965 178118736834887003475539 := by
  unfold tailWord_3121965
  simp only [CollatzResearch.WordTrace]
  refine ⟨113867418134661469017751349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75911612089774312678500899 113867418134661469017751349)
  ·
    refine ⟨10675070450124512720414189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113867418134661469017751349 10675070450124512720414189)
    ·
      refine ⟨4003151418796692270155321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10675070450124512720414189 4003151418796692270155321)
      ·
        refine ⟨3002363564097519202616491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4003151418796692270155321 3002363564097519202616491)
        ·
          refine ⟨4503545346146278803924737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002363564097519202616491 4503545346146278803924737)
          ·
            refine ⟨3377659009609709102943553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4503545346146278803924737 3377659009609709102943553)
            ·
              refine ⟨2533244257207281827207665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3377659009609709102943553 2533244257207281827207665)
              ·
                refine ⟨1899933192905461370405749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2533244257207281827207665 1899933192905461370405749)
                ·
                  refine ⟨178118736834887003475539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1899933192905461370405749 178118736834887003475539)
                  ·
                    rfl

theorem cell23_3121965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_3121965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121965 prefixEnd_3121965 := by exact prefixLift 3121965
  have htrace : WordTrace (prefixWord ++ tailWord_3121965) baseStart_3121965 baseEnd_3121965 := by
    simpa [prefixWord, tailWord_3121965, baseEnd_3121965] using wordTrace_append hprefix tailTrace_3121965
  have hstable : (prefixWord ++ tailWord_3121965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121965).length < 2 ^ (prefixWord ++ tailWord_3121965).sum := by decide
  have hdescent : baseEnd_3121965 < baseStart_3121965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121981 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 2, 4, 2]
def baseStart_3121981 : Nat := 118140960795 + 3121981 * 2 ^ 59
def prefixEnd_3121981 : Nat := 4983230072969 + 3 ^ 40 * 3121981 * 2
def baseEnd_3121981 : Nat := 1603076847204454968679777

theorem tailTrace_3121981 : CollatzResearch.WordTrace tailWord_3121981 prefixEnd_3121981 1603076847204454968679777 := by
  unfold tailWord_3121981
  simp only [CollatzResearch.WordTrace]
  refine ⟨113868001702603503750333797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75912001135069002500222531 113868001702603503750333797)
  ·
    refine ⟨21350250319238156953187587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113868001702603503750333797 21350250319238156953187587)
    ·
      refine ⟨32025375478857235429781381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21350250319238156953187587 32025375478857235429781381)
      ·
        refine ⟨6004757902285731643084009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32025375478857235429781381 6004757902285731643084009)
        ·
          refine ⟨4503568426714298732313007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6004757902285731643084009 4503568426714298732313007)
          ·
            refine ⟨6755352640071448098469511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503568426714298732313007 6755352640071448098469511)
            ·
              refine ⟨10133028960107172147704267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6755352640071448098469511 10133028960107172147704267)
              ·
                refine ⟨15199543440160758221556401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10133028960107172147704267 15199543440160758221556401)
                ·
                  refine ⟨11399657580120568666167301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15199543440160758221556401 11399657580120568666167301)
                  ·
                    refine ⟨2137435796272606624906369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11399657580120568666167301 2137435796272606624906369)
                    ·
                      refine ⟨1603076847204454968679777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137435796272606624906369 1603076847204454968679777)
                      ·
                        rfl

theorem cell23_3121981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_3121981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3121981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3121981 prefixEnd_3121981 := by exact prefixLift 3121981
  have htrace : WordTrace (prefixWord ++ tailWord_3121981) baseStart_3121981 baseEnd_3121981 := by
    simpa [prefixWord, tailWord_3121981, baseEnd_3121981] using wordTrace_append hprefix tailTrace_3121981
  have hstable : (prefixWord ++ tailWord_3121981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121981).length < 2 ^ (prefixWord ++ tailWord_3121981).sum := by decide
  have hdescent : baseEnd_3121981 < baseStart_3121981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122001 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 2, 2, 3]
def baseStart_3122001 : Nat := 118140960795 + 3122001 * 2 ^ 59
def prefixEnd_3122001 : Nat := 4983230072969 + 3 ^ 40 * 3122001 * 2
def baseEnd_3122001 : Nat := 1603087116817544890429685

theorem tailTrace_3122001 : CollatzResearch.WordTrace tailWord_3122001 prefixEnd_3122001 1603087116817544890429685 := by
  unfold tailWord_3122001
  simp only [CollatzResearch.WordTrace]
  refine ⟨113868731162531047166061857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75912487441687364777374571 113868731162531047166061857)
  ·
    refine ⟨85401548371898285374546393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113868731162531047166061857 85401548371898285374546393)
    ·
      refine ⟨64051161278923714030909795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85401548371898285374546393 64051161278923714030909795)
      ·
        refine ⟨96076741918385571046364693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64051161278923714030909795 96076741918385571046364693)
        ·
          refine ⟨4503597277424323642798345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96076741918385571046364693 4503597277424323642798345)
          ·
            refine ⟨3377697958068242732098759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4503597277424323642798345 3377697958068242732098759)
            ·
              refine ⟨5066546937102364098148139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3377697958068242732098759 5066546937102364098148139)
              ·
                refine ⟨7599820405653546147222209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5066546937102364098148139 7599820405653546147222209)
                ·
                  refine ⟨5699865304240159610416657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7599820405653546147222209 5699865304240159610416657)
                  ·
                    refine ⟨4274898978180119707812493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5699865304240159610416657 4274898978180119707812493)
                    ·
                      refine ⟨1603087116817544890429685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4274898978180119707812493 1603087116817544890429685)
                      ·
                        rfl

theorem cell23_3122001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_3122001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122001 prefixEnd_3122001 := by exact prefixLift 3122001
  have htrace : WordTrace (prefixWord ++ tailWord_3122001) baseStart_3122001 baseEnd_3122001 := by
    simpa [prefixWord, tailWord_3122001, baseEnd_3122001] using wordTrace_append hprefix tailTrace_3122001
  have hstable : (prefixWord ++ tailWord_3122001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122001).length < 2 ^ (prefixWord ++ tailWord_3122001).sum := by decide
  have hdescent : baseEnd_3122001 < baseStart_3122001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122047 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 1, 6]
def baseStart_3122047 : Nat := 118140960795 + 3122047 * 2 ^ 59
def prefixEnd_3122047 : Nat := 4983230072969 + 3 ^ 40 * 3122047 * 2
def baseEnd_3122047 : Nat := 534370245642550570151491

theorem tailTrace_3122047 : CollatzResearch.WordTrace tailWord_3122047 prefixEnd_3122047 534370245642550570151491 := by
  unfold tailWord_3122047
  simp only [CollatzResearch.WordTrace]
  refine ⟨113870408920364397022236395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75913605946909598014824263 113870408920364397022236395)
  ·
    refine ⟨170805613380546595533354593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113870408920364397022236395 170805613380546595533354593)
    ·
      refine ⟨128104210035409946650015945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170805613380546595533354593 128104210035409946650015945)
      ·
        refine ⟨96078157526557459987511959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128104210035409946650015945 96078157526557459987511959)
        ·
          refine ⟨144117236289836189981267939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96078157526557459987511959 144117236289836189981267939)
          ·
            refine ⟨216175854434754284971901909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144117236289836189981267939 216175854434754284971901909)
            ·
              refine ⟨5066621588314553554028951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 216175854434754284971901909 5066621588314553554028951)
              ·
                refine ⟨7599932382471830331043427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5066621588314553554028951 7599932382471830331043427)
                ·
                  refine ⟨11399898573707745496565141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7599932382471830331043427 11399898573707745496565141)
                  ·
                    refine ⟨534370245642550570151491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11399898573707745496565141 534370245642550570151491)
                    ·
                      rfl

theorem cell23_3122047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 6].length) (baseStart_3122047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122047 prefixEnd_3122047 := by exact prefixLift 3122047
  have htrace : WordTrace (prefixWord ++ tailWord_3122047) baseStart_3122047 baseEnd_3122047 := by
    simpa [prefixWord, tailWord_3122047, baseEnd_3122047] using wordTrace_append hprefix tailTrace_3122047
  have hstable : (prefixWord ++ tailWord_3122047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122047).length < 2 ^ (prefixWord ++ tailWord_3122047).sum := by decide
  have hdescent : baseEnd_3122047 < baseStart_3122047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122102 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3122102 : Nat := 118140960795 + 3122102 * 2 ^ 59
def prefixEnd_3122102 : Nat := 4983230072969 + 3 ^ 40 * 3122102 * 2
def baseEnd_3122102 : Nat := 534379659454549665088907

theorem tailTrace_3122102 : CollatzResearch.WordTrace tailWord_3122102 prefixEnd_3122102 534379659454549665088907 := by
  unfold tailWord_3122102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7117025933447821338468035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75914943290110094276992373 7117025933447821338468035)
  ·
    refine ⟨10675538900171732007702053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7117025933447821338468035 10675538900171732007702053)
    ·
      refine ⟨2001663543782199751444135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10675538900171732007702053 2001663543782199751444135)
      ·
        refine ⟨3002495315673299627166203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001663543782199751444135 3002495315673299627166203)
        ·
          refine ⟨4503742973509949440749305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002495315673299627166203 4503742973509949440749305)
          ·
            refine ⟨3377807230132462080561979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4503742973509949440749305 3377807230132462080561979)
            ·
              refine ⟨5066710845198693120842969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3377807230132462080561979 5066710845198693120842969)
              ·
                refine ⟨3800033133899019840632227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5066710845198693120842969 3800033133899019840632227)
                ·
                  refine ⟨5700049700848529760948341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800033133899019840632227 5700049700848529760948341)
                  ·
                    refine ⟨534379659454549665088907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5700049700848529760948341 534379659454549665088907)
                    ·
                      rfl

theorem cell23_3122102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3122102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122102 prefixEnd_3122102 := by exact prefixLift 3122102
  have htrace : WordTrace (prefixWord ++ tailWord_3122102) baseStart_3122102 baseEnd_3122102 := by
    simpa [prefixWord, tailWord_3122102, baseEnd_3122102] using wordTrace_append hprefix tailTrace_3122102
  have hstable : (prefixWord ++ tailWord_3122102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122102).length < 2 ^ (prefixWord ++ tailWord_3122102).sum := by decide
  have hdescent : baseEnd_3122102 < baseStart_3122102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122138 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3]
def baseStart_3122138 : Nat := 118140960795 + 3122138 * 2 ^ 59
def prefixEnd_3122138 : Nat := 4983230072969 + 3 ^ 40 * 3122138 * 2
def baseEnd_3122138 : Nat := 1603157463667210854416555

theorem tailTrace_3122138 : CollatzResearch.WordTrace tailWord_3122138 prefixEnd_3122138 1603157463667210854416555 := by
  unfold tailWord_3122138
  simp only [CollatzResearch.WordTrace]
  refine ⟨28468431990758679890949767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75915818642023146375866045 28468431990758679890949767)
  ·
    refine ⟨42702647986138019836424651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28468431990758679890949767 42702647986138019836424651)
    ·
      refine ⟨64053971979207029754636977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42702647986138019836424651 64053971979207029754636977)
      ·
        refine ⟨48040478984405272315977733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64053971979207029754636977 48040478984405272315977733)
        ·
          refine ⟨9007589809575988559245825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48040478984405272315977733 9007589809575988559245825)
          ·
            refine ⟨6755692357181991419434369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9007589809575988559245825 6755692357181991419434369)
            ·
              refine ⟨5066769267886493564575777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6755692357181991419434369 5066769267886493564575777)
              ·
                refine ⟨3800076950914870173431833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5066769267886493564575777 3800076950914870173431833)
                ·
                  refine ⟨2850057713186152630073875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800076950914870173431833 2850057713186152630073875)
                  ·
                    refine ⟨4275086569779228945110813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2850057713186152630073875 4275086569779228945110813)
                    ·
                      refine ⟨1603157463667210854416555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4275086569779228945110813 1603157463667210854416555)
                      ·
                        rfl

theorem cell23_3122138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_3122138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122138 prefixEnd_3122138 := by exact prefixLift 3122138
  have htrace : WordTrace (prefixWord ++ tailWord_3122138) baseStart_3122138 baseEnd_3122138 := by
    simpa [prefixWord, tailWord_3122138, baseEnd_3122138] using wordTrace_append hprefix tailTrace_3122138
  have hstable : (prefixWord ++ tailWord_3122138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122138).length < 2 ^ (prefixWord ++ tailWord_3122138).sum := by decide
  have hdescent : baseEnd_3122138 < baseStart_3122138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122154 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_3122154 : Nat := 118140960795 + 3122154 * 2 ^ 59
def prefixEnd_3122154 : Nat := 4983230072969 + 3 ^ 40 * 3122154 * 2
def baseEnd_3122154 : Nat := 534388559785894263938827

theorem tailTrace_3122154 : CollatzResearch.WordTrace tailWord_3122154 prefixEnd_3122154 534388559785894263938827 := by
  unfold tailWord_3122154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28468577882744188574095379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75916207687317836197587677 28468577882744188574095379)
  ·
    refine ⟨42702866824116282861143069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28468577882744188574095379 42702866824116282861143069)
    ·
      refine ⟨16013575059043606072928651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42702866824116282861143069 16013575059043606072928651)
      ·
        refine ⟨24020362588565409109392977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16013575059043606072928651 24020362588565409109392977)
        ·
          refine ⟨18015271941424056832044733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24020362588565409109392977 18015271941424056832044733)
          ·
            refine ⟨6755726978034021312016775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18015271941424056832044733 6755726978034021312016775)
            ·
              refine ⟨10133590467051031968025163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6755726978034021312016775 10133590467051031968025163)
              ·
                refine ⟨15200385700576547952037745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10133590467051031968025163 15200385700576547952037745)
                ·
                  refine ⟨11400289275432410964028309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15200385700576547952037745 11400289275432410964028309)
                  ·
                    refine ⟨534388559785894263938827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11400289275432410964028309 534388559785894263938827)
                    ·
                      rfl

theorem cell23_3122154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_3122154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122154 prefixEnd_3122154 := by exact prefixLift 3122154
  have htrace : WordTrace (prefixWord ++ tailWord_3122154) baseStart_3122154 baseEnd_3122154 := by
    simpa [prefixWord, tailWord_3122154, baseEnd_3122154] using wordTrace_append hprefix tailTrace_3122154
  have hstable : (prefixWord ++ tailWord_3122154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122154).length < 2 ^ (prefixWord ++ tailWord_3122154).sum := by decide
  have hdescent : baseEnd_3122154 < baseStart_3122154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122161 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 1, 4, 2]
def baseStart_3122161 : Nat := 118140960795 + 3122161 * 2 ^ 59
def prefixEnd_3122161 : Nat := 4983230072969 + 3 ^ 40 * 3122161 * 2
def baseEnd_3122161 : Nat := 1603169273722264264428949

theorem tailTrace_3122161 : CollatzResearch.WordTrace tailWord_3122161 prefixEnd_3122161 1603169273722264264428949 := by
  unfold tailWord_3122161
  simp only [CollatzResearch.WordTrace]
  refine ⟨113874566841951394491886337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75916377894634262994590891 113874566841951394491886337)
  ·
    refine ⟨85405925131463545868914753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113874566841951394491886337 85405925131463545868914753)
    ·
      refine ⟨64054443848597659401686065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85405925131463545868914753 64054443848597659401686065)
      ·
        refine ⟨48040832886448244551264549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64054443848597659401686065 48040832886448244551264549)
        ·
          refine ⟨9007656166209045853362103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48040832886448244551264549 9007656166209045853362103)
          ·
            refine ⟨13511484249313568780043155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9007656166209045853362103 13511484249313568780043155)
            ·
              refine ⟨20267226373970353170064733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13511484249313568780043155 20267226373970353170064733)
              ·
                refine ⟨7600209890238882438774275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20267226373970353170064733 7600209890238882438774275)
                ·
                  refine ⟨11400314835358323658161413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7600209890238882438774275 11400314835358323658161413)
                  ·
                    refine ⟨2137559031629685685905265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11400314835358323658161413 2137559031629685685905265)
                    ·
                      refine ⟨1603169273722264264428949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137559031629685685905265 1603169273722264264428949)
                      ·
                        rfl

theorem cell23_3122161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_3122161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122161 prefixEnd_3122161 := by exact prefixLift 3122161
  have htrace : WordTrace (prefixWord ++ tailWord_3122161) baseStart_3122161 baseEnd_3122161 := by
    simpa [prefixWord, tailWord_3122161, baseEnd_3122161] using wordTrace_append hprefix tailTrace_3122161
  have hstable : (prefixWord ++ tailWord_3122161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122161).length < 2 ^ (prefixWord ++ tailWord_3122161).sum := by decide
  have hdescent : baseEnd_3122161 < baseStart_3122161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122212 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 2, 2, 2]
def baseStart_3122212 : Nat := 118140960795 + 3122212 * 2 ^ 59
def prefixEnd_3122212 : Nat := 4983230072969 + 3 ^ 40 * 3122212 * 2
def baseEnd_3122212 : Nat := 1603195461235643564891215

theorem tailTrace_3122212 : CollatzResearch.WordTrace tailWord_3122212 prefixEnd_3122212 1603195461235643564891215 := by
  unfold tailWord_3122212
  simp only [CollatzResearch.WordTrace]
  refine ⟨56938213482383315100996445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75917617976511086801328593 56938213482383315100996445)
  ·
    refine ⟨21351830055893743162873667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56938213482383315100996445 21351830055893743162873667)
    ·
      refine ⟨32027745083840614744310501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21351830055893743162873667 32027745083840614744310501)
      ·
        refine ⟨6005202203220115264558219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32027745083840614744310501 6005202203220115264558219)
        ·
          refine ⟨9007803304830172896837329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6005202203220115264558219 9007803304830172896837329)
          ·
            refine ⟨6755852478622629672627997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9007803304830172896837329 6755852478622629672627997)
            ·
              refine ⟨2533444679483486127235499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6755852478622629672627997 2533444679483486127235499)
              ·
                refine ⟨3800167019225229190853249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533444679483486127235499 3800167019225229190853249)
                ·
                  refine ⟨2850125264418921893139937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800167019225229190853249 2850125264418921893139937)
                  ·
                    refine ⟨2137593948314191419854953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2850125264418921893139937 2137593948314191419854953)
                    ·
                      refine ⟨1603195461235643564891215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137593948314191419854953 1603195461235643564891215)
                      ·
                        rfl

theorem cell23_3122212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_3122212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122212 prefixEnd_3122212 := by exact prefixLift 3122212
  have htrace : WordTrace (prefixWord ++ tailWord_3122212) baseStart_3122212 baseEnd_3122212 := by
    simpa [prefixWord, tailWord_3122212, baseEnd_3122212] using wordTrace_append hprefix tailTrace_3122212
  have hstable : (prefixWord ++ tailWord_3122212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122212).length < 2 ^ (prefixWord ++ tailWord_3122212).sum := by decide
  have hdescent : baseEnd_3122212 < baseStart_3122212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122227 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 1, 10]
def baseStart_3122227 : Nat := 118140960795 + 3122227 * 2 ^ 59
def prefixEnd_3122227 : Nat := 4983230072969 + 3 ^ 40 * 3122227 * 2
def baseEnd_3122227 : Nat := 534401054481820335401215

theorem tailTrace_3122227 : CollatzResearch.WordTrace tailWord_3122227 prefixEnd_3122227 534401054481820335401215 := by
  unfold tailWord_3122227
  simp only [CollatzResearch.WordTrace]
  refine ⟨113876974059712287763788935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75917982706474858509192623 113876974059712287763788935)
  ·
    refine ⟨170815461089568431645683403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113876974059712287763788935 170815461089568431645683403)
    ·
      refine ⟨256223191634352647468525105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170815461089568431645683403 256223191634352647468525105)
      ·
        refine ⟨192167393725764485601393829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256223191634352647468525105 192167393725764485601393829)
        ·
          refine ⟨36031386323580841050261343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192167393725764485601393829 36031386323580841050261343)
          ·
            refine ⟨54047079485371261575392015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36031386323580841050261343 54047079485371261575392015)
            ·
              refine ⟨81070619228056892363088023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54047079485371261575392015 81070619228056892363088023)
              ·
                refine ⟨121605928842085338544632035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81070619228056892363088023 121605928842085338544632035)
                ·
                  refine ⟨182408893263128007816948053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121605928842085338544632035 182408893263128007816948053)
                  ·
                    refine ⟨534401054481820335401215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 182408893263128007816948053 534401054481820335401215)
                    ·
                      rfl

theorem cell23_3122227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 10].length) (baseStart_3122227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122227 prefixEnd_3122227 := by exact prefixLift 3122227
  have htrace : WordTrace (prefixWord ++ tailWord_3122227) baseStart_3122227 baseEnd_3122227 := by
    simpa [prefixWord, tailWord_3122227, baseEnd_3122227] using wordTrace_append hprefix tailTrace_3122227
  have hstable : (prefixWord ++ tailWord_3122227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122227).length < 2 ^ (prefixWord ++ tailWord_3122227).sum := by decide
  have hdescent : baseEnd_3122227 < baseStart_3122227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122234 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_3122234 : Nat := 118140960795 + 3122234 * 2 ^ 59
def prefixEnd_3122234 : Nat := 4983230072969 + 3 ^ 40 * 3122234 * 2
def baseEnd_3122234 : Nat := 1603206757810042478816113

theorem tailTrace_3122234 : CollatzResearch.WordTrace tailWord_3122234 prefixEnd_3122234 1603206757810042478816113 := by
  unfold tailWord_3122234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28469307342671731989823439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75918152913791285306195837 28469307342671731989823439)
  ·
    refine ⟨42703961014007597984735159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28469307342671731989823439 42703961014007597984735159)
    ·
      refine ⟨64055941521011396977102739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42703961014007597984735159 64055941521011396977102739)
      ·
        refine ⟨96083912281517095465654109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64055941521011396977102739 96083912281517095465654109)
        ·
          refine ⟨36031467105568910799620291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96083912281517095465654109 36031467105568910799620291)
          ·
            refine ⟨54047200658353366199430437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36031467105568910799620291 54047200658353366199430437)
            ·
              refine ⟨10133850123441256162393207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54047200658353366199430437 10133850123441256162393207)
              ·
                refine ⟨15200775185161884243589811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10133850123441256162393207 15200775185161884243589811)
                ·
                  refine ⟨22801162777742826365384717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15200775185161884243589811 22801162777742826365384717)
                  ·
                    refine ⟨8550436041653559887019269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22801162777742826365384717 8550436041653559887019269)
                    ·
                      refine ⟨1603206757810042478816113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8550436041653559887019269 1603206757810042478816113)
                      ·
                        rfl

theorem cell23_3122234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_3122234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122234 prefixEnd_3122234 := by exact prefixLift 3122234
  have htrace : WordTrace (prefixWord ++ tailWord_3122234) baseStart_3122234 baseEnd_3122234 := by
    simpa [prefixWord, tailWord_3122234, baseEnd_3122234] using wordTrace_append hprefix tailTrace_3122234
  have hstable : (prefixWord ++ tailWord_3122234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122234).length < 2 ^ (prefixWord ++ tailWord_3122234).sum := by decide
  have hdescent : baseEnd_3122234 < baseStart_3122234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122311 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 3, 5, 2]
def baseStart_3122311 : Nat := 118140960795 + 3122311 * 2 ^ 59
def prefixEnd_3122311 : Nat := 4983230072969 + 3 ^ 40 * 3122311 * 2
def baseEnd_3122311 : Nat := 1603246295820438677553259

theorem tailTrace_3122311 : CollatzResearch.WordTrace tailWord_3122311 prefixEnd_3122311 1603246295820438677553259 := by
  unfold tailWord_3122311
  simp only [CollatzResearch.WordTrace]
  refine ⟨113880037791407970109846787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75920025194271980073231191 113880037791407970109846787)
  ·
    refine ⟨170820056687111955164770181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113880037791407970109846787 170820056687111955164770181)
    ·
      refine ⟨32028760628833491593394409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170820056687111955164770181 32028760628833491593394409)
      ·
        refine ⟨24021570471625118695045807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32028760628833491593394409 24021570471625118695045807)
        ·
          refine ⟨36032355707437678042568711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24021570471625118695045807 36032355707437678042568711)
          ·
            refine ⟨54048533561156517063853067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36032355707437678042568711 54048533561156517063853067)
            ·
              refine ⟨81072800341734775595779601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54048533561156517063853067 81072800341734775595779601)
              ·
                refine ⟨60804600256301081696834701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81072800341734775595779601 60804600256301081696834701)
                ·
                  refine ⟨22801725096112905636313013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60804600256301081696834701 22801725096112905636313013)
                  ·
                    refine ⟨2137661727760584903404345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22801725096112905636313013 2137661727760584903404345)
                    ·
                      refine ⟨1603246295820438677553259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137661727760584903404345 1603246295820438677553259)
                      ·
                        rfl

theorem cell23_3122311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_3122311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122311 prefixEnd_3122311 := by exact prefixLift 3122311
  have htrace : WordTrace (prefixWord ++ tailWord_3122311) baseStart_3122311 baseEnd_3122311 := by
    simpa [prefixWord, tailWord_3122311, baseEnd_3122311] using wordTrace_append hprefix tailTrace_3122311
  have hstable : (prefixWord ++ tailWord_3122311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122311).length < 2 ^ (prefixWord ++ tailWord_3122311).sum := by decide
  have hdescent : baseEnd_3122311 < baseStart_3122311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122335 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3122335 : Nat := 118140960795 + 3122335 * 2 ^ 59
def prefixEnd_3122335 : Nat := 4983230072969 + 3 ^ 40 * 3122335 * 2
def baseEnd_3122335 : Nat := 1603258619356146583653149

theorem tailTrace_3122335 : CollatzResearch.WordTrace tailWord_3122335 prefixEnd_3122335 1603258619356146583653149 := by
  unfold tailWord_3122335
  simp only [CollatzResearch.WordTrace]
  refine ⟨113880913143321022208720459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75920608762214014805813639 113880913143321022208720459)
  ·
    refine ⟨170821369714981533313080689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113880913143321022208720459 170821369714981533313080689)
    ·
      refine ⟨128116027286236149984810517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170821369714981533313080689 128116027286236149984810517)
      ·
        refine ⟨6005438779042319530537993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128116027286236149984810517 6005438779042319530537993)
        ·
          refine ⟨4504079084281739647903495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6005438779042319530537993 4504079084281739647903495)
          ·
            refine ⟨6756118626422609471855243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504079084281739647903495 6756118626422609471855243)
            ·
              refine ⟨10134177939633914207782865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6756118626422609471855243 10134177939633914207782865)
              ·
                refine ⟨7600633454725435655837149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10134177939633914207782865 7600633454725435655837149)
                ·
                  refine ⟨2850237545522038370938931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7600633454725435655837149 2850237545522038370938931)
                  ·
                    refine ⟨4275356318283057556408397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2850237545522038370938931 4275356318283057556408397)
                    ·
                      refine ⟨1603258619356146583653149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4275356318283057556408397 1603258619356146583653149)
                      ·
                        rfl

theorem cell23_3122335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3122335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122335 prefixEnd_3122335 := by exact prefixLift 3122335
  have htrace : WordTrace (prefixWord ++ tailWord_3122335) baseStart_3122335 baseEnd_3122335 := by
    simpa [prefixWord, tailWord_3122335, baseEnd_3122335] using wordTrace_append hprefix tailTrace_3122335
  have hstable : (prefixWord ++ tailWord_3122335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122335).length < 2 ^ (prefixWord ++ tailWord_3122335).sum := by decide
  have hdescent : baseEnd_3122335 < baseStart_3122335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122341 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_3122341 : Nat := 118140960795 + 3122341 * 2 ^ 59
def prefixEnd_3122341 : Nat := 4983230072969 + 3 ^ 40 * 3122341 * 2
def baseEnd_3122341 : Nat := 1603261700240073560178121

theorem tailTrace_3122341 : CollatzResearch.WordTrace tailWord_3122341 prefixEnd_3122341 1603261700240073560178121 := by
  unfold tailWord_3122341
  simp only [CollatzResearch.WordTrace]
  refine ⟨113881131981299285233438877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75920754654199523488959251 113881131981299285233438877)
  ·
    refine ⟨42705424492987231962539579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113881131981299285233438877 42705424492987231962539579)
    ·
      refine ⟨64058136739480847943809369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42705424492987231962539579 64058136739480847943809369)
      ·
        refine ⟨48043602554610635957857027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64058136739480847943809369 48043602554610635957857027)
        ·
          refine ⟨72065403831915953936785541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48043602554610635957857027 72065403831915953936785541)
          ·
            refine ⟨13512263218484241363147289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72065403831915953936785541 13512263218484241363147289)
            ·
              refine ⟨10134197413863181022360467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13512263218484241363147289 10134197413863181022360467)
              ·
                refine ⟨15201296120794771533540701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10134197413863181022360467 15201296120794771533540701)
                ·
                  refine ⟨5700486045298039325077763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15201296120794771533540701 5700486045298039325077763)
                  ·
                    refine ⟨8550729067947058987616645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5700486045298039325077763 8550729067947058987616645)
                    ·
                      refine ⟨1603261700240073560178121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8550729067947058987616645 1603261700240073560178121)
                      ·
                        rfl

theorem cell23_3122341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_3122341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122341 prefixEnd_3122341 := by exact prefixLift 3122341
  have htrace : WordTrace (prefixWord ++ tailWord_3122341) baseStart_3122341 baseEnd_3122341 := by
    simpa [prefixWord, tailWord_3122341, baseEnd_3122341] using wordTrace_append hprefix tailTrace_3122341
  have hstable : (prefixWord ++ tailWord_3122341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122341).length < 2 ^ (prefixWord ++ tailWord_3122341).sum := by decide
  have hdescent : baseEnd_3122341 < baseStart_3122341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122368 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 4, 4]
def baseStart_3122368 : Nat := 118140960795 + 3122368 * 2 ^ 59
def prefixEnd_3122368 : Nat := 4983230072969 + 3 ^ 40 * 3122368 * 2
def baseEnd_3122368 : Nat := 534425188072581651513499

theorem tailTrace_3122368 : CollatzResearch.WordTrace tailWord_3122368 prefixEnd_3122368 534425188072581651513499 := by
  unfold tailWord_3122368
  simp only [CollatzResearch.WordTrace]
  refine ⟨56941058376100734422335879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75921411168134312563114505 56941058376100734422335879)
  ·
    refine ⟨85411587564151101633503819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56941058376100734422335879 85411587564151101633503819)
    ·
      refine ⟨128117381346226652450255729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85411587564151101633503819 128117381346226652450255729)
      ·
        refine ⟨96088036009669989337691797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128117381346226652450255729 96088036009669989337691797)
        ·
          refine ⟨4504126687953280750204303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96088036009669989337691797 4504126687953280750204303)
          ·
            refine ⟨6756190031929921125306455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504126687953280750204303 6756190031929921125306455)
            ·
              refine ⟨10134285047894881687959683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6756190031929921125306455 10134285047894881687959683)
              ·
                refine ⟨15201427571842322531939525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10134285047894881687959683 15201427571842322531939525)
                ·
                  refine ⟨2850267669720435474738661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15201427571842322531939525 2850267669720435474738661)
                  ·
                    refine ⟨534425188072581651513499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2850267669720435474738661 534425188072581651513499)
                    ·
                      rfl

theorem cell23_3122368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4, 4].length) (baseStart_3122368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122368 prefixEnd_3122368 := by exact prefixLift 3122368
  have htrace : WordTrace (prefixWord ++ tailWord_3122368) baseStart_3122368 baseEnd_3122368 := by
    simpa [prefixWord, tailWord_3122368, baseEnd_3122368] using wordTrace_append hprefix tailTrace_3122368
  have hstable : (prefixWord ++ tailWord_3122368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122368).length < 2 ^ (prefixWord ++ tailWord_3122368).sum := by decide
  have hdescent : baseEnd_3122368 < baseStart_3122368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122408 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_3122408 : Nat := 118140960795 + 3122408 * 2 ^ 59
def prefixEnd_3122408 : Nat := 4983230072969 + 3 ^ 40 * 3122408 * 2
def baseEnd_3122408 : Nat := 1603296103443924798040313

theorem tailTrace_3122408 : CollatzResearch.WordTrace tailWord_3122408 prefixEnd_3122408 1603296103443924798040313 := by
  unfold tailWord_3122408
  simp only [CollatzResearch.WordTrace]
  refine ⟨56941787836028277838063939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75922383781371037117418585 56941787836028277838063939)
  ·
    refine ⟨85412681754042416757095909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56941787836028277838063939 85412681754042416757095909)
    ·
      refine ⟨16014877828882953141955483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85412681754042416757095909 16014877828882953141955483)
      ·
        refine ⟨24022316743324429712933225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16014877828882953141955483 24022316743324429712933225)
        ·
          refine ⟨18016737557493322284699919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24022316743324429712933225 18016737557493322284699919)
          ·
            refine ⟨27025106336239983427049879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18016737557493322284699919 27025106336239983427049879)
            ·
              refine ⟨40537659504359975140574819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27025106336239983427049879 40537659504359975140574819)
              ·
                refine ⟨60806489256539962710862229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40537659504359975140574819 60806489256539962710862229)
                ·
                  refine ⟨2850304183900310752071667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60806489256539962710862229 2850304183900310752071667)
                  ·
                    refine ⟨4275456275850466128107501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2850304183900310752071667 4275456275850466128107501)
                    ·
                      refine ⟨1603296103443924798040313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4275456275850466128107501 1603296103443924798040313)
                      ·
                        rfl

theorem cell23_3122408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_3122408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122408 prefixEnd_3122408 := by exact prefixLift 3122408
  have htrace : WordTrace (prefixWord ++ tailWord_3122408) baseStart_3122408 baseEnd_3122408 := by
    simpa [prefixWord, tailWord_3122408, baseEnd_3122408] using wordTrace_append hprefix tailTrace_3122408
  have hstable : (prefixWord ++ tailWord_3122408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122408).length < 2 ^ (prefixWord ++ tailWord_3122408).sum := by decide
  have hdescent : baseEnd_3122408 < baseStart_3122408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122482 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2]
def baseStart_3122482 : Nat := 118140960795 + 3122482 * 2 ^ 59
def prefixEnd_3122482 : Nat := 4983230072969 + 3 ^ 40 * 3122482 * 2
def baseEnd_3122482 : Nat := 1603334101012357508514973

theorem tailTrace_3122482 : CollatzResearch.WordTrace tailWord_3122482 prefixEnd_3122482 1603334101012357508514973 := by
  unfold tailWord_3122482
  simp only [CollatzResearch.WordTrace]
  refine ⟨28471568668447116578580425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75924183115858977542881133 28471568668447116578580425)
  ·
    refine ⟨21353676501335337433935319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28471568668447116578580425 21353676501335337433935319)
    ·
      refine ⟨32030514752003006150902979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21353676501335337433935319 32030514752003006150902979)
      ·
        refine ⟨48045772128004509226354469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32030514752003006150902979 48045772128004509226354469)
        ·
          refine ⟨9008582274000845479941463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48045772128004509226354469 9008582274000845479941463)
          ·
            refine ⟨13512873411001268219912195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9008582274000845479941463 13512873411001268219912195)
            ·
              refine ⟨20269310116501902329868293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13512873411001268219912195 20269310116501902329868293)
              ·
                refine ⟨3800495646844106686850305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20269310116501902329868293 3800495646844106686850305)
                ·
                  refine ⟨2850371735133080015137729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800495646844106686850305 2850371735133080015137729)
                  ·
                    refine ⟨2137778801349810011353297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2850371735133080015137729 2137778801349810011353297)
                    ·
                      refine ⟨1603334101012357508514973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137778801349810011353297 1603334101012357508514973)
                      ·
                        rfl

theorem cell23_3122482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_3122482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122482 prefixEnd_3122482 := by exact prefixLift 3122482
  have htrace : WordTrace (prefixWord ++ tailWord_3122482) baseStart_3122482 baseEnd_3122482 := by
    simpa [prefixWord, tailWord_3122482, baseEnd_3122482] using wordTrace_append hprefix tailTrace_3122482
  have hstable : (prefixWord ++ tailWord_3122482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122482).length < 2 ^ (prefixWord ++ tailWord_3122482).sum := by decide
  have hdescent : baseEnd_3122482 < baseStart_3122482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122501 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_3122501 : Nat := 118140960795 + 3122501 * 2 ^ 59
def prefixEnd_3122501 : Nat := 4983230072969 + 3 ^ 40 * 3122501 * 2
def baseEnd_3122501 : Nat := 534447952381597644725795

theorem tailTrace_3122501 : CollatzResearch.WordTrace tailWord_3122501 prefixEnd_3122501 534447952381597644725795 := by
  unfold tailWord_3122501
  simp only [CollatzResearch.WordTrace]
  refine ⟨113886967660719632559263357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75924645107146421706175571 113886967660719632559263357)
  ·
    refine ⟨42707612872769862209723759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113886967660719632559263357 42707612872769862209723759)
    ·
      refine ⟨64061419309154793314585639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42707612872769862209723759 64061419309154793314585639)
      ·
        refine ⟨96092128963732189971878459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64061419309154793314585639 96092128963732189971878459)
        ·
          refine ⟨144138193445598284957817689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96092128963732189971878459 144138193445598284957817689)
          ·
            refine ⟨108103645084198713718363267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144138193445598284957817689 108103645084198713718363267)
            ·
              refine ⟨162155467626298070577544901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108103645084198713718363267 162155467626298070577544901)
              ·
                refine ⟨30404150179930888233289669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162155467626298070577544901 30404150179930888233289669)
                ·
                  refine ⟨5700778158737041543741813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30404150179930888233289669 5700778158737041543741813)
                  ·
                    refine ⟨534447952381597644725795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5700778158737041543741813 534447952381597644725795)
                    ·
                      rfl

theorem cell23_3122501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_3122501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122501 prefixEnd_3122501 := by exact prefixLift 3122501
  have htrace : WordTrace (prefixWord ++ tailWord_3122501) baseStart_3122501 baseEnd_3122501 := by
    simpa [prefixWord, tailWord_3122501, baseEnd_3122501] using wordTrace_append hprefix tailTrace_3122501
  have hstable : (prefixWord ++ tailWord_3122501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122501).length < 2 ^ (prefixWord ++ tailWord_3122501).sum := by decide
  have hdescent : baseEnd_3122501 < baseStart_3122501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122551 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_3122551 : Nat := 118140960795 + 3122551 * 2 ^ 59
def prefixEnd_3122551 : Nat := 4983230072969 + 3 ^ 40 * 3122551 * 2
def baseEnd_3122551 : Nat := 1603369531177517738552155

theorem tailTrace_3122551 : CollatzResearch.WordTrace tailWord_3122551 prefixEnd_3122551 1603369531177517738552155 := by
  unfold tailWord_3122551
  simp only [CollatzResearch.WordTrace]
  refine ⟨113888791310538491098583507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75925860873692327399055671 113888791310538491098583507)
  ·
    refine ⟨170833186965807736647875261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113888791310538491098583507 170833186965807736647875261)
    ·
      refine ⟨64062445112177901242953223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170833186965807736647875261 64062445112177901242953223)
      ·
        refine ⟨96093667668266851864429835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64062445112177901242953223 96093667668266851864429835)
        ·
          refine ⟨144140501502400277796644753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96093667668266851864429835 144140501502400277796644753)
          ·
            refine ⟨108105376126800208347483565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144140501502400277796644753 108105376126800208347483565)
            ·
              refine ⟨40539516047550078130306337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108105376126800208347483565 40539516047550078130306337)
              ·
                refine ⟨30404637035662558597729753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40539516047550078130306337 30404637035662558597729753)
                ·
                  refine ⟨22803477776746918948297315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30404637035662558597729753 22803477776746918948297315)
                  ·
                    refine ⟨34205216665120378422445973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22803477776746918948297315 34205216665120378422445973)
                    ·
                      refine ⟨1603369531177517738552155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34205216665120378422445973 1603369531177517738552155)
                      ·
                        rfl

theorem cell23_3122551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_3122551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122551 prefixEnd_3122551 := by exact prefixLift 3122551
  have htrace : WordTrace (prefixWord ++ tailWord_3122551) baseStart_3122551 baseEnd_3122551 := by
    simpa [prefixWord, tailWord_3122551, baseEnd_3122551] using wordTrace_append hprefix tailTrace_3122551
  have hstable : (prefixWord ++ tailWord_3122551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122551).length < 2 ^ (prefixWord ++ tailWord_3122551).sum := by decide
  have hdescent : baseEnd_3122551 < baseStart_3122551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122599 : List Nat := [1, 1, 6, 1, 1, 1, 5, 2, 1, 4]
def baseStart_3122599 : Nat := 118140960795 + 3122599 * 2 ^ 59
def prefixEnd_3122599 : Nat := 4983230072969 + 3 ^ 40 * 3122599 * 2
def baseEnd_3122599 : Nat := 534464726082977850250645

theorem tailTrace_3122599 : CollatzResearch.WordTrace tailWord_3122599 prefixEnd_3122599 534464726082977850250645 := by
  unfold tailWord_3122599
  simp only [CollatzResearch.WordTrace]
  refine ⟨113890542014364595296330851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75927028009576396864220567 113890542014364595296330851)
  ·
    refine ⟨170835813021546892944496277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113890542014364595296330851 170835813021546892944496277)
    ·
      refine ⟨8007928735385010606773263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170835813021546892944496277 8007928735385010606773263)
      ·
        refine ⟨12011893103077515910159895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8007928735385010606773263 12011893103077515910159895)
        ·
          refine ⟨18017839654616273865239843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12011893103077515910159895 18017839654616273865239843)
          ·
            refine ⟨27026759481924410797859765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18017839654616273865239843 27026759481924410797859765)
            ·
              refine ⟨2533758701430413512299353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27026759481924410797859765 2533758701430413512299353)
              ·
                refine ⟨1900319026072810134224515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2533758701430413512299353 1900319026072810134224515)
                ·
                  refine ⟨2850478539109215201336773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900319026072810134224515 2850478539109215201336773)
                  ·
                    refine ⟨534464726082977850250645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2850478539109215201336773 534464726082977850250645)
                    ·
                      rfl

theorem cell23_3122599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_3122599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122599 prefixEnd_3122599 := by exact prefixLift 3122599
  have htrace : WordTrace (prefixWord ++ tailWord_3122599) baseStart_3122599 baseEnd_3122599 := by
    simpa [prefixWord, tailWord_3122599, baseEnd_3122599] using wordTrace_append hprefix tailTrace_3122599
  have hstable : (prefixWord ++ tailWord_3122599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122599).length < 2 ^ (prefixWord ++ tailWord_3122599).sum := by decide
  have hdescent : baseEnd_3122599 < baseStart_3122599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122601 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_3122601 : Nat := 118140960795 + 3122601 * 2 ^ 59
def prefixEnd_3122601 : Nat := 4983230072969 + 3 ^ 40 * 3122601 * 2
def baseEnd_3122601 : Nat := 1603395205210242542926925

theorem tailTrace_3122601 : CollatzResearch.WordTrace tailWord_3122601 prefixEnd_3122601 1603395205210242542926925 := by
  unfold tailWord_3122601
  simp only [CollatzResearch.WordTrace]
  refine ⟨113890614960357349637903657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75927076640238233091935771 113890614960357349637903657)
  ·
    refine ⟨85417961220268012228427743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113890614960357349637903657 85417961220268012228427743)
    ·
      refine ⟨128126941830402018342641615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85417961220268012228427743 128126941830402018342641615)
      ·
        refine ⟨192190412745603027513962423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128126941830402018342641615 192190412745603027513962423)
        ·
          refine ⟨288285619118404541270943635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192190412745603027513962423 288285619118404541270943635)
          ·
            refine ⟨432428428677606811906415453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288285619118404541270943635 432428428677606811906415453)
            ·
              refine ⟨162160660754102554464905795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432428428677606811906415453 162160660754102554464905795)
              ·
                refine ⟨243240991131153831697358693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162160660754102554464905795 243240991131153831697358693)
                ·
                  refine ⟨45607685837091343443254755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243240991131153831697358693 45607685837091343443254755)
                  ·
                    refine ⟨68411528755637015164882133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45607685837091343443254755 68411528755637015164882133)
                    ·
                      refine ⟨1603395205210242542926925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68411528755637015164882133 1603395205210242542926925)
                      ·
                        rfl

theorem cell23_3122601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_3122601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122601 prefixEnd_3122601 := by exact prefixLift 3122601
  have htrace : WordTrace (prefixWord ++ tailWord_3122601) baseStart_3122601 baseEnd_3122601 := by
    simpa [prefixWord, tailWord_3122601, baseEnd_3122601] using wordTrace_append hprefix tailTrace_3122601
  have hstable : (prefixWord ++ tailWord_3122601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122601).length < 2 ^ (prefixWord ++ tailWord_3122601).sum := by decide
  have hdescent : baseEnd_3122601 < baseStart_3122601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122615 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 4, 3, 2]
def baseStart_3122615 : Nat := 118140960795 + 3122615 * 2 ^ 59
def prefixEnd_3122615 : Nat := 4983230072969 + 3 ^ 40 * 3122615 * 2
def baseEnd_3122615 : Nat := 1603402393939405488151861

theorem tailTrace_3122615 : CollatzResearch.WordTrace tailWord_3122615 prefixEnd_3122615 1603402393939405488151861 := by
  unfold tailWord_3122615
  simp only [CollatzResearch.WordTrace]
  refine ⟨113891125582306630028913299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75927417054871086685942199 113891125582306630028913299)
  ·
    refine ⟨170836688373459945043369949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113891125582306630028913299 170836688373459945043369949)
    ·
      refine ⟨64063758140047479391263731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170836688373459945043369949 64063758140047479391263731)
      ·
        refine ⟨96095637210071219086895597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64063758140047479391263731 96095637210071219086895597)
        ·
          refine ⟨36035863953776707157585849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96095637210071219086895597 36035863953776707157585849)
          ·
            refine ⟨27026897965332530368189387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36035863953776707157585849 27026897965332530368189387)
            ·
              refine ⟨40540346947998795552284081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27026897965332530368189387 40540346947998795552284081)
              ·
                refine ⟨30405260210999096664213061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40540346947998795552284081 30405260210999096664213061)
                ·
                  refine ⟨5700986289562330624539949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30405260210999096664213061 5700986289562330624539949)
                  ·
                    refine ⟨2137869858585873984202481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5700986289562330624539949 2137869858585873984202481)
                    ·
                      refine ⟨1603402393939405488151861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137869858585873984202481 1603402393939405488151861)
                      ·
                        rfl

theorem cell23_3122615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_3122615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122615 prefixEnd_3122615 := by exact prefixLift 3122615
  have htrace : WordTrace (prefixWord ++ tailWord_3122615) baseStart_3122615 baseEnd_3122615 := by
    simpa [prefixWord, tailWord_3122615, baseEnd_3122615] using wordTrace_append hprefix tailTrace_3122615
  have hstable : (prefixWord ++ tailWord_3122615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122615).length < 2 ^ (prefixWord ++ tailWord_3122615).sum := by decide
  have hdescent : baseEnd_3122615 < baseStart_3122615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122632 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 2, 3, 2]
def baseStart_3122632 : Nat := 118140960795 + 3122632 * 2 ^ 59
def prefixEnd_3122632 : Nat := 4983230072969 + 3 ^ 40 * 3122632 * 2
def baseEnd_3122632 : Nat := 1603411123110531921639283

theorem tailTrace_3122632 : CollatzResearch.WordTrace tailWord_3122632 prefixEnd_3122632 1603411123110531921639283 := by
  unfold tailWord_3122632
  simp only [CollatzResearch.WordTrace]
  refine ⟨56945872811622520966141075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75927830415496694621521433 56945872811622520966141075)
  ·
    refine ⟨85418809217433781449211613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56945872811622520966141075 85418809217433781449211613)
    ·
      refine ⟨32032053456537668043454355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85418809217433781449211613 32032053456537668043454355)
      ·
        refine ⟨48048080184806502065181533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32032053456537668043454355 48048080184806502065181533)
        ·
          refine ⟨18018030069302438274443075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48048080184806502065181533 18018030069302438274443075)
          ·
            refine ⟨27027045103953657411664613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18018030069302438274443075 27027045103953657411664613)
            ·
              refine ⟨5067570956991310764687115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27027045103953657411664613 5067570956991310764687115)
              ·
                refine ⟨7601356435486966147030673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5067570956991310764687115 7601356435486966147030673)
                ·
                  refine ⟨5701017326615224610273005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7601356435486966147030673 5701017326615224610273005)
                  ·
                    refine ⟨2137881497480709228852377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5701017326615224610273005 2137881497480709228852377)
                    ·
                      refine ⟨1603411123110531921639283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137881497480709228852377 1603411123110531921639283)
                      ·
                        rfl

theorem cell23_3122632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_3122632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122632 prefixEnd_3122632 := by exact prefixLift 3122632
  have htrace : WordTrace (prefixWord ++ tailWord_3122632) baseStart_3122632 baseEnd_3122632 := by
    simpa [prefixWord, tailWord_3122632, baseEnd_3122632] using wordTrace_append hprefix tailTrace_3122632
  have hstable : (prefixWord ++ tailWord_3122632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122632).length < 2 ^ (prefixWord ++ tailWord_3122632).sum := by decide
  have hdescent : baseEnd_3122632 < baseStart_3122632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122638 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_3122638 : Nat := 118140960795 + 3122638 * 2 ^ 59
def prefixEnd_3122638 : Nat := 4983230072969 + 3 ^ 40 * 3122638 * 2
def baseEnd_3122638 : Nat := 534471401331486299388085

theorem tailTrace_3122638 : CollatzResearch.WordTrace tailWord_3122638 prefixEnd_3122638 534471401331486299388085 := by
  unfold tailWord_3122638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14236495557652913119625071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75927976307482203304667045 14236495557652913119625071)
  ·
    refine ⟨21354743336479369679437607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14236495557652913119625071 21354743336479369679437607)
    ·
      refine ⟨32032115004719054519156411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21354743336479369679437607 32032115004719054519156411)
      ·
        refine ⟨48048172507078581778734617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32032115004719054519156411 48048172507078581778734617)
        ·
          refine ⟨36036129380308936334050963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48048172507078581778734617 36036129380308936334050963)
          ·
            refine ⟨54054194070463404501076445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36036129380308936334050963 54054194070463404501076445)
            ·
              refine ⟨20270322776423776687903667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54054194070463404501076445 20270322776423776687903667)
              ·
                refine ⟨30405484164635665031855501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20270322776423776687903667 30405484164635665031855501)
                ·
                  refine ⟨11402056561738374386945813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30405484164635665031855501 11402056561738374386945813)
                  ·
                    refine ⟨534471401331486299388085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11402056561738374386945813 534471401331486299388085)
                    ·
                      rfl

theorem cell23_3122638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_3122638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122638 prefixEnd_3122638 := by exact prefixLift 3122638
  have htrace : WordTrace (prefixWord ++ tailWord_3122638) baseStart_3122638 baseEnd_3122638 := by
    simpa [prefixWord, tailWord_3122638, baseEnd_3122638] using wordTrace_append hprefix tailTrace_3122638
  have hstable : (prefixWord ++ tailWord_3122638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122638).length < 2 ^ (prefixWord ++ tailWord_3122638).sum := by decide
  have hdescent : baseEnd_3122638 < baseStart_3122638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122685 : List Nat := [1, 4, 1, 1, 1, 5, 3, 7]
def baseStart_3122685 : Nat := 118140960795 + 3122685 * 2 ^ 59
def prefixEnd_3122685 : Nat := 4983230072969 + 3 ^ 40 * 3122685 * 2
def baseEnd_3122685 : Nat := 59386605095748896825057

theorem tailTrace_3122685 : CollatzResearch.WordTrace tailWord_3122685 prefixEnd_3122685 59386605095748896825057 := by
  unfold tailWord_3122685
  simp only [CollatzResearch.WordTrace]
  refine ⟨113893678692053031983961509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75929119128035354655974339 113893678692053031983961509)
  ·
    refine ⟨21355064754759943496992783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113893678692053031983961509 21355064754759943496992783)
    ·
      refine ⟨32032597132139915245489175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21355064754759943496992783 32032597132139915245489175)
      ·
        refine ⟨48048895698209872868233763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32032597132139915245489175 48048895698209872868233763)
        ·
          refine ⟨72073343547314809302350645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48048895698209872868233763 72073343547314809302350645)
          ·
            refine ⟨6756875957560763372095373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72073343547314809302350645 6756875957560763372095373)
            ·
              refine ⟨2533828484085286264535765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6756875957560763372095373 2533828484085286264535765)
              ·
                refine ⟨59386605095748896825057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2533828484085286264535765 59386605095748896825057)
                ·
                  rfl

theorem cell23_3122685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 7].length) (baseStart_3122685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122685 prefixEnd_3122685 := by exact prefixLift 3122685
  have htrace : WordTrace (prefixWord ++ tailWord_3122685) baseStart_3122685 baseEnd_3122685 := by
    simpa [prefixWord, tailWord_3122685, baseEnd_3122685] using wordTrace_append hprefix tailTrace_3122685
  have hstable : (prefixWord ++ tailWord_3122685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122685).length < 2 ^ (prefixWord ++ tailWord_3122685).sum := by decide
  have hdescent : baseEnd_3122685 < baseStart_3122685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122722 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_3122722 : Nat := 118140960795 + 3122722 * 2 ^ 59
def prefixEnd_3122722 : Nat := 4983230072969 + 3 ^ 40 * 3122722 * 2
def baseEnd_3122722 : Nat := 1603457336369436569513869

theorem tailTrace_3122722 : CollatzResearch.WordTrace tailWord_3122722 prefixEnd_3122722 1603457336369436569513869 := by
  unfold tailWord_3122722
  simp only [CollatzResearch.WordTrace]
  refine ⟨28473757048229746825764605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75930018795279324868705613 28473757048229746825764605)
  ·
    refine ⟨10677658893086155059661727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28473757048229746825764605 10677658893086155059661727)
    ·
      refine ⟨16016488339629232589492591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10677658893086155059661727 16016488339629232589492591)
      ·
        refine ⟨24024732509443848884238887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16016488339629232589492591 24024732509443848884238887)
        ·
          refine ⟨36037098764165773326358331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24024732509443848884238887 36037098764165773326358331)
          ·
            refine ⟨54055648146248659989537497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36037098764165773326358331 54055648146248659989537497)
            ·
              refine ⟨40541736109686494992153123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54055648146248659989537497 40541736109686494992153123)
              ·
                refine ⟨60812604164529742488229685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40541736109686494992153123 60812604164529742488229685)
                ·
                  refine ⟨5701181640424663358271533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60812604164529742488229685 5701181640424663358271533)
                  ·
                    refine ⟨2137943115159248759351825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5701181640424663358271533 2137943115159248759351825)
                    ·
                      refine ⟨1603457336369436569513869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137943115159248759351825 1603457336369436569513869)
                      ·
                        rfl

theorem cell23_3122722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_3122722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122722 prefixEnd_3122722 := by exact prefixLift 3122722
  have htrace : WordTrace (prefixWord ++ tailWord_3122722) baseStart_3122722 baseEnd_3122722 := by
    simpa [prefixWord, tailWord_3122722, baseEnd_3122722] using wordTrace_append hprefix tailTrace_3122722
  have hstable : (prefixWord ++ tailWord_3122722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122722).length < 2 ^ (prefixWord ++ tailWord_3122722).sum := by decide
  have hdescent : baseEnd_3122722 < baseStart_3122722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122739 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 1, 3, 2]
def baseStart_3122739 : Nat := 118140960795 + 3122739 * 2 ^ 59
def prefixEnd_3122739 : Nat := 4983230072969 + 3 ^ 40 * 3122739 * 2
def baseEnd_3122739 : Nat := 1603466065540563003001291

theorem tailTrace_3122739 : CollatzResearch.WordTrace tailWord_3122739 prefixEnd_3122739 1603466065540563003001291 := by
  unfold tailWord_3122739
  simp only [CollatzResearch.WordTrace]
  refine ⟨113895648233857399206427271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75930432155904932804284847 113895648233857399206427271)
  ·
    refine ⟨170843472350786098809640907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113895648233857399206427271 170843472350786098809640907)
    ·
      refine ⟨256265208526179148214461361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170843472350786098809640907 256265208526179148214461361)
      ·
        refine ⟨192198906394634361160846021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256265208526179148214461361 192198906394634361160846021)
        ·
          refine ⟨36037294948993942717658629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192198906394634361160846021 36037294948993942717658629)
          ·
            refine ⟨6756992802936364259560993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36037294948993942717658629 6756992802936364259560993)
            ·
              refine ⟨5067744602202273194670745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6756992802936364259560993 5067744602202273194670745)
              ·
                refine ⟨3800808451651704896003059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5067744602202273194670745 3800808451651704896003059)
                ·
                  refine ⟨5701212677477557344004589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800808451651704896003059 5701212677477557344004589)
                  ·
                    refine ⟨2137954754054084004001721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5701212677477557344004589 2137954754054084004001721)
                    ·
                      refine ⟨1603466065540563003001291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137954754054084004001721 1603466065540563003001291)
                      ·
                        rfl

theorem cell23_3122739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 3, 2].length) (baseStart_3122739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122739 prefixEnd_3122739 := by exact prefixLift 3122739
  have htrace : WordTrace (prefixWord ++ tailWord_3122739) baseStart_3122739 baseEnd_3122739 := by
    simpa [prefixWord, tailWord_3122739, baseEnd_3122739] using wordTrace_append hprefix tailTrace_3122739
  have hstable : (prefixWord ++ tailWord_3122739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122739).length < 2 ^ (prefixWord ++ tailWord_3122739).sum := by decide
  have hdescent : baseEnd_3122739 < baseStart_3122739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122768 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_3122768 : Nat := 118140960795 + 3122768 * 2 ^ 59
def prefixEnd_3122768 : Nat := 4983230072969 + 3 ^ 40 * 3122768 * 2
def baseEnd_3122768 : Nat := 1603480956479543389538657

theorem tailTrace_3122768 : CollatzResearch.WordTrace tailWord_3122768 prefixEnd_3122768 1603480956479543389538657 := by
  unfold tailWord_3122768
  simp only [CollatzResearch.WordTrace]
  refine ⟨56948352975376168579616479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75931137300501558106155305 56948352975376168579616479)
  ·
    refine ⟨85422529463064252869424719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56948352975376168579616479 85422529463064252869424719)
    ·
      refine ⟨128133794194596379304137079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85422529463064252869424719 128133794194596379304137079)
      ·
        refine ⟨192200691291894568956205619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128133794194596379304137079 192200691291894568956205619)
        ·
          refine ⟨288301036937841853434308429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192200691291894568956205619 288301036937841853434308429)
          ·
            refine ⟨108112888851690695037865661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288301036937841853434308429 108112888851690695037865661)
            ·
              refine ⟨40542333319384010639199623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108112888851690695037865661 40542333319384010639199623)
              ·
                refine ⟨60813499979076015958799435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40542333319384010639199623 60813499979076015958799435)
                ·
                  refine ⟨91220249968614023938199153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60813499979076015958799435 91220249968614023938199153)
                  ·
                    refine ⟨68415187476460517953649365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91220249968614023938199153 68415187476460517953649365)
                    ·
                      refine ⟨1603480956479543389538657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68415187476460517953649365 1603480956479543389538657)
                      ·
                        rfl

theorem cell23_3122768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_3122768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122768 prefixEnd_3122768 := by exact prefixLift 3122768
  have htrace : WordTrace (prefixWord ++ tailWord_3122768) baseStart_3122768 baseEnd_3122768 := by
    simpa [prefixWord, tailWord_3122768, baseEnd_3122768] using wordTrace_append hprefix tailTrace_3122768
  have hstable : (prefixWord ++ tailWord_3122768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122768).length < 2 ^ (prefixWord ++ tailWord_3122768).sum := by decide
  have hdescent : baseEnd_3122768 < baseStart_3122768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122769 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 2, 2, 2]
def baseStart_3122769 : Nat := 118140960795 + 3122769 * 2 ^ 59
def prefixEnd_3122769 : Nat := 4983230072969 + 3 ^ 40 * 3122769 * 2
def baseEnd_3122769 : Nat := 1603481469960197885626153

theorem tailTrace_3122769 : CollatzResearch.WordTrace tailWord_3122769 prefixEnd_3122769 1603481469960197885626153 := by
  unfold tailWord_3122769
  simp only [CollatzResearch.WordTrace]
  refine ⟨113896742423748714330019361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75931161615832476220012907 113896742423748714330019361)
  ·
    refine ⟨85422556817811535747514521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113896742423748714330019361 85422556817811535747514521)
    ·
      refine ⟨64066917613358651810635891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85422556817811535747514521 64066917613358651810635891)
      ·
        refine ⟨96100376420037977715953837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64066917613358651810635891 96100376420037977715953837)
        ·
          refine ⟨36037641157514241643482689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96100376420037977715953837 36037641157514241643482689)
          ·
            refine ⟨27028230868135681232612017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36037641157514241643482689 27028230868135681232612017)
            ·
              refine ⟨20271173151101760924459013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27028230868135681232612017 20271173151101760924459013)
              ·
                refine ⟨3800844965831580173336065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20271173151101760924459013 3800844965831580173336065)
                ·
                  refine ⟨2850633724373685130002049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800844965831580173336065 2850633724373685130002049)
                  ·
                    refine ⟨2137975293280263847501537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2850633724373685130002049 2137975293280263847501537)
                    ·
                      refine ⟨1603481469960197885626153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2137975293280263847501537 1603481469960197885626153)
                      ·
                        rfl

theorem cell23_3122769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_3122769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122769 prefixEnd_3122769 := by exact prefixLift 3122769
  have htrace : WordTrace (prefixWord ++ tailWord_3122769) baseStart_3122769 baseEnd_3122769 := by
    simpa [prefixWord, tailWord_3122769, baseEnd_3122769] using wordTrace_append hprefix tailTrace_3122769
  have hstable : (prefixWord ++ tailWord_3122769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122769).length < 2 ^ (prefixWord ++ tailWord_3122769).sum := by decide
  have hdescent : baseEnd_3122769 < baseStart_3122769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122775 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 7]
def baseStart_3122775 : Nat := 118140960795 + 3122775 * 2 ^ 59
def prefixEnd_3122775 : Nat := 4983230072969 + 3 ^ 40 * 3122775 * 2
def baseEnd_3122775 : Nat := 178164950093791651350125

theorem tailTrace_3122775 : CollatzResearch.WordTrace tailWord_3122775 prefixEnd_3122775 178164950093791651350125 := by
  unfold tailWord_3122775
  simp only [CollatzResearch.WordTrace]
  refine ⟨113896961261726977354737779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75931307507817984903158519 113896961261726977354737779)
  ·
    refine ⟨170845441892590466032106669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113896961261726977354737779 170845441892590466032106669)
    ·
      refine ⟨64067040709721424762040001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170845441892590466032106669 64067040709721424762040001)
      ·
        refine ⟨48050280532291068571530001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64067040709721424762040001 48050280532291068571530001)
        ·
          refine ⟨36037710399218301428647501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48050280532291068571530001 36037710399218301428647501)
          ·
            refine ⟨13514141399706863035742813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36037710399218301428647501 13514141399706863035742813)
            ·
              refine ⟨5067803024890073638403555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13514141399706863035742813 5067803024890073638403555)
              ·
                refine ⟨7601704537335110457605333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5067803024890073638403555 7601704537335110457605333)
                ·
                  refine ⟨178164950093791651350125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7601704537335110457605333 178164950093791651350125)
                  ·
                    rfl

theorem cell23_3122775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 7].length) (baseStart_3122775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122775 prefixEnd_3122775 := by exact prefixLift 3122775
  have htrace : WordTrace (prefixWord ++ tailWord_3122775) baseStart_3122775 baseEnd_3122775 := by
    simpa [prefixWord, tailWord_3122775, baseEnd_3122775] using wordTrace_append hprefix tailTrace_3122775
  have hstable : (prefixWord ++ tailWord_3122775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122775).length < 2 ^ (prefixWord ++ tailWord_3122775).sum := by decide
  have hdescent : baseEnd_3122775 < baseStart_3122775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122785 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_3122785 : Nat := 118140960795 + 3122785 * 2 ^ 59
def prefixEnd_3122785 : Nat := 4983230072969 + 3 ^ 40 * 3122785 * 2
def baseEnd_3122785 : Nat := 1603489685650669823026079

theorem tailTrace_3122785 : CollatzResearch.WordTrace tailWord_3122785 prefixEnd_3122785 1603489685650669823026079 := by
  unfold tailWord_3122785
  simp only [CollatzResearch.WordTrace]
  refine ⟨113897325991690749062601809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75931550661127166041734539 113897325991690749062601809)
  ·
    refine ⟨85422994493768061796951357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113897325991690749062601809 85422994493768061796951357)
    ·
      refine ⟨32033622935163023173856759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85422994493768061796951357 32033622935163023173856759)
      ·
        refine ⟨48050434402744534760785139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32033622935163023173856759 48050434402744534760785139)
        ·
          refine ⟨72075651604116802141177709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48050434402744534760785139 72075651604116802141177709)
          ·
            refine ⟨27028369351543800802941641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72075651604116802141177709 27028369351543800802941641)
            ·
              refine ⟨20271277013657850602206231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27028369351543800802941641 20271277013657850602206231)
              ·
                refine ⟨30406915520486775903309347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20271277013657850602206231 30406915520486775903309347)
                ·
                  refine ⟨45610373280730163854964021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30406915520486775903309347 45610373280730163854964021)
                  ·
                    refine ⟨4275972495068452861402877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45610373280730163854964021 4275972495068452861402877)
                    ·
                      refine ⟨1603489685650669823026079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4275972495068452861402877 1603489685650669823026079)
                      ·
                        rfl

theorem cell23_3122785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_3122785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122785 prefixEnd_3122785 := by exact prefixLift 3122785
  have htrace : WordTrace (prefixWord ++ tailWord_3122785) baseStart_3122785 baseEnd_3122785 := by
    simpa [prefixWord, tailWord_3122785, baseEnd_3122785] using wordTrace_append hprefix tailTrace_3122785
  have hstable : (prefixWord ++ tailWord_3122785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122785).length < 2 ^ (prefixWord ++ tailWord_3122785).sum := by decide
  have hdescent : baseEnd_3122785 < baseStart_3122785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122826 : List Nat := [3, 1, 2, 3, 2, 3, 2, 2, 5]
def baseStart_3122826 : Nat := 118140960795 + 3122826 * 2 ^ 59
def prefixEnd_3122826 : Nat := 4983230072969 + 3 ^ 40 * 3122826 * 2
def baseEnd_3122826 : Nat := 178167859817500462512599

theorem tailTrace_3122826 : CollatzResearch.WordTrace tailWord_3122826 prefixEnd_3122826 178167859817500462512599 := by
  unfold tailWord_3122826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28474705346135553266211083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75932547589694808709896221 28474705346135553266211083)
  ·
    refine ⟨42712058019203329899316625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28474705346135553266211083 42712058019203329899316625)
    ·
      refine ⟨32034043514402497424487469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42712058019203329899316625 32034043514402497424487469)
      ·
        refine ⟨12012766317900936534182801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32034043514402497424487469 12012766317900936534182801)
        ·
          refine ⟨9009574738425702400637101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12012766317900936534182801 9009574738425702400637101)
          ·
            refine ⟨3378590526909638400238913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9009574738425702400637101 3378590526909638400238913)
            ·
              refine ⟨2533942895182228800179185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378590526909638400238913 2533942895182228800179185)
              ·
                refine ⟨1900457171386671600134389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2533942895182228800179185 1900457171386671600134389)
                ·
                  refine ⟨178167859817500462512599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1900457171386671600134389 178167859817500462512599)
                  ·
                    rfl

theorem cell23_3122826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_3122826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122826 prefixEnd_3122826 := by exact prefixLift 3122826
  have htrace : WordTrace (prefixWord ++ tailWord_3122826) baseStart_3122826 baseEnd_3122826 := by
    simpa [prefixWord, tailWord_3122826, baseEnd_3122826] using wordTrace_append hprefix tailTrace_3122826
  have hstable : (prefixWord ++ tailWord_3122826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122826).length < 2 ^ (prefixWord ++ tailWord_3122826).sum := by decide
  have hdescent : baseEnd_3122826 < baseStart_3122826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122852 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_3122852 : Nat := 118140960795 + 3122852 * 2 ^ 59
def prefixEnd_3122852 : Nat := 4983230072969 + 3 ^ 40 * 3122852 * 2
def baseEnd_3122852 : Nat := 534508029618173686962757

theorem tailTrace_3122852 : CollatzResearch.WordTrace tailWord_3122852 prefixEnd_3122852 534508029618173686962757 := by
  unfold tailWord_3122852
  simp only [CollatzResearch.WordTrace]
  refine ⟨56949884841224009752645405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75933179788298679670193873 56949884841224009752645405)
  ·
    refine ⟨21356206815459003657242027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56949884841224009752645405 21356206815459003657242027)
    ·
      refine ⟨32034310223188505485863041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21356206815459003657242027 32034310223188505485863041)
      ·
        refine ⟨24025732667391379114397281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32034310223188505485863041 24025732667391379114397281)
        ·
          refine ⟨18019299500543534335797961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24025732667391379114397281 18019299500543534335797961)
          ·
            refine ⟨13514474625407650751848471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18019299500543534335797961 13514474625407650751848471)
            ·
              refine ⟨20271711938111476127772707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13514474625407650751848471 20271711938111476127772707)
              ·
                refine ⟨30407567907167214191659061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20271711938111476127772707 30407567907167214191659061)
                ·
                  refine ⟨2850709491296926330468037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30407567907167214191659061 2850709491296926330468037)
                  ·
                    refine ⟨534508029618173686962757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2850709491296926330468037 534508029618173686962757)
                    ·
                      rfl

theorem cell23_3122852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_3122852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122852 prefixEnd_3122852 := by exact prefixLift 3122852
  have htrace : WordTrace (prefixWord ++ tailWord_3122852) baseStart_3122852 baseEnd_3122852 := by
    simpa [prefixWord, tailWord_3122852, baseEnd_3122852] using wordTrace_append hprefix tailTrace_3122852
  have hstable : (prefixWord ++ tailWord_3122852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122852).length < 2 ^ (prefixWord ++ tailWord_3122852).sum := by decide
  have hdescent : baseEnd_3122852 < baseStart_3122852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122856 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3122856 : Nat := 118140960795 + 3122856 * 2 ^ 59
def prefixEnd_3122856 : Nat := 4983230072969 + 3 ^ 40 * 3122856 * 2
def baseEnd_3122856 : Nat := 534508714259046348412751

theorem tailTrace_3122856 : CollatzResearch.WordTrace tailWord_3122856 prefixEnd_3122856 534508714259046348412751 := by
  unfold tailWord_3122856
  simp only [CollatzResearch.WordTrace]
  refine ⟨56949957787216764094218211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75933277049622352125624281 56949957787216764094218211)
  ·
    refine ⟨85424936680825146141327317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56949957787216764094218211 85424936680825146141327317)
    ·
      refine ⟨2002146953456839362687359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 85424936680825146141327317 2002146953456839362687359)
      ·
        refine ⟨3003220430185259044031039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2002146953456839362687359 3003220430185259044031039)
        ·
          refine ⟨4504830645277888566046559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003220430185259044031039 4504830645277888566046559)
          ·
            refine ⟨6757245967916832849069839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504830645277888566046559 6757245967916832849069839)
            ·
              refine ⟨10135868951875249273604759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6757245967916832849069839 10135868951875249273604759)
              ·
                refine ⟨15203803427812873910407139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10135868951875249273604759 15203803427812873910407139)
                ·
                  refine ⟨22805705141719310865610709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15203803427812873910407139 22805705141719310865610709)
                  ·
                    refine ⟨534508714259046348412751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22805705141719310865610709 534508714259046348412751)
                    ·
                      rfl

theorem cell23_3122856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3122856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122856 prefixEnd_3122856 := by exact prefixLift 3122856
  have htrace : WordTrace (prefixWord ++ tailWord_3122856) baseStart_3122856 baseEnd_3122856 := by
    simpa [prefixWord, tailWord_3122856, baseEnd_3122856] using wordTrace_append hprefix tailTrace_3122856
  have hstable : (prefixWord ++ tailWord_3122856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122856).length < 2 ^ (prefixWord ++ tailWord_3122856).sum := by decide
  have hdescent : baseEnd_3122856 < baseStart_3122856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122875 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 3]
def baseStart_3122875 : Nat := 118140960795 + 3122875 * 2 ^ 59
def prefixEnd_3122875 : Nat := 4983230072969 + 3 ^ 40 * 3122875 * 2
def baseEnd_3122875 : Nat := 1603535898909574470900665

theorem tailTrace_3122875 : CollatzResearch.WordTrace tailWord_3122875 prefixEnd_3122875 1603535898909574470900665 := by
  unfold tailWord_3122875
  simp only [CollatzResearch.WordTrace]
  refine ⟨113900608561364694433378079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75933739040909796288918719 113900608561364694433378079)
  ·
    refine ⟨170850912842047041650067119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113900608561364694433378079 170850912842047041650067119)
    ·
      refine ⟨256276369263070562475100679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170850912842047041650067119 256276369263070562475100679)
      ·
        refine ⟨384414553894605843712651019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256276369263070562475100679 384414553894605843712651019)
        ·
          refine ⟨576621830841908765568976529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384414553894605843712651019 576621830841908765568976529)
          ·
            refine ⟨432466373131431574176732397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576621830841908765568976529 432466373131431574176732397)
            ·
              refine ⟨162174889924286840316274649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432466373131431574176732397 162174889924286840316274649)
              ·
                refine ⟨121631167443215130237205987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162174889924286840316274649 121631167443215130237205987)
                ·
                  refine ⟨182446751164822695355808981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121631167443215130237205987 182446751164822695355808981)
                  ·
                    refine ⟨4276095730425531922401773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 182446751164822695355808981 4276095730425531922401773)
                    ·
                      refine ⟨1603535898909574470900665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4276095730425531922401773 1603535898909574470900665)
                      ·
                        rfl

theorem cell23_3122875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 3].length) (baseStart_3122875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122875 prefixEnd_3122875 := by exact prefixLift 3122875
  have htrace : WordTrace (prefixWord ++ tailWord_3122875) baseStart_3122875 baseEnd_3122875 := by
    simpa [prefixWord, tailWord_3122875, baseEnd_3122875] using wordTrace_append hprefix tailTrace_3122875
  have hstable : (prefixWord ++ tailWord_3122875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122875).length < 2 ^ (prefixWord ++ tailWord_3122875).sum := by decide
  have hdescent : baseEnd_3122875 < baseStart_3122875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122895 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 5, 5]
def baseStart_3122895 : Nat := 118140960795 + 3122895 * 2 ^ 59
def prefixEnd_3122895 : Nat := 4983230072969 + 3 ^ 40 * 3122895 * 2
def baseEnd_3122895 : Nat := 534515389507554797550191

theorem tailTrace_3122895 : CollatzResearch.WordTrace tailWord_3122895 prefixEnd_3122895 534515389507554797550191 := by
  unfold tailWord_3122895
  simp only [CollatzResearch.WordTrace]
  refine ⟨113901338021292237849106139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75934225347528158566070759 113901338021292237849106139)
  ·
    refine ⟨170852007031938356773659209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113901338021292237849106139 170852007031938356773659209)
    ·
      refine ⟨128139005273953767580244407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170852007031938356773659209 128139005273953767580244407)
      ·
        refine ⟨192208507910930651370366611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128139005273953767580244407 192208507910930651370366611)
        ·
          refine ⟨288312761866395977055549917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192208507910930651370366611 288312761866395977055549917)
          ·
            refine ⟨108117285699898491395831219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288312761866395977055549917 108117285699898491395831219)
            ·
              refine ⟨162175928549847737093746829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108117285699898491395831219 162175928549847737093746829)
              ·
                refine ⟨60815973206192901410155061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162175928549847737093746829 60815973206192901410155061)
                ·
                  refine ⟨5701497488080584507202037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60815973206192901410155061 5701497488080584507202037)
                  ·
                    refine ⟨534515389507554797550191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5701497488080584507202037 534515389507554797550191)
                    ·
                      rfl

theorem cell23_3122895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_3122895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122895 prefixEnd_3122895 := by exact prefixLift 3122895
  have htrace : WordTrace (prefixWord ++ tailWord_3122895) baseStart_3122895 baseEnd_3122895 := by
    simpa [prefixWord, tailWord_3122895, baseEnd_3122895] using wordTrace_append hprefix tailTrace_3122895
  have hstable : (prefixWord ++ tailWord_3122895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122895).length < 2 ^ (prefixWord ++ tailWord_3122895).sum := by decide
  have hdescent : baseEnd_3122895 < baseStart_3122895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122912 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 1, 5]
def baseStart_3122912 : Nat := 118140960795 + 3122912 * 2 ^ 59
def prefixEnd_3122912 : Nat := 4983230072969 + 3 ^ 40 * 3122912 * 2
def baseEnd_3122912 : Nat := 534518299231263608712665

theorem tailTrace_3122912 : CollatzResearch.WordTrace tailWord_3122912 prefixEnd_3122912 534518299231263608712665 := by
  unfold tailWord_3122912
  simp only [CollatzResearch.WordTrace]
  refine ⟨56950979031115324876237495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75934638708153766501649993 56950979031115324876237495)
  ·
    refine ⟨85426468546672987314356243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56950979031115324876237495 85426468546672987314356243)
    ·
      refine ⟨128139702820009480971534365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85426468546672987314356243 128139702820009480971534365)
      ·
        refine ⟨48052388557503555364325387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128139702820009480971534365 48052388557503555364325387)
        ·
          refine ⟨72078582836255333046488081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48052388557503555364325387 72078582836255333046488081)
          ·
            refine ⟨54058937127191499784866061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72078582836255333046488081 54058937127191499784866061)
            ·
              refine ⟨20272101422696812419324773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54058937127191499784866061 20272101422696812419324773)
              ·
                refine ⟨3801019016755652328623395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20272101422696812419324773 3801019016755652328623395)
                ·
                  refine ⟨5701528525133478492935093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801019016755652328623395 5701528525133478492935093)
                  ·
                    refine ⟨534518299231263608712665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5701528525133478492935093 534518299231263608712665)
                    ·
                      rfl

theorem cell23_3122912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 5].length) (baseStart_3122912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122912 prefixEnd_3122912 := by exact prefixLift 3122912
  have htrace : WordTrace (prefixWord ++ tailWord_3122912) baseStart_3122912 baseEnd_3122912 := by
    simpa [prefixWord, tailWord_3122912, baseEnd_3122912] using wordTrace_append hprefix tailTrace_3122912
  have hstable : (prefixWord ++ tailWord_3122912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122912).length < 2 ^ (prefixWord ++ tailWord_3122912).sum := by decide
  have hdescent : baseEnd_3122912 < baseStart_3122912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122952 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3122952 : Nat := 118140960795 + 3122952 * 2 ^ 59
def prefixEnd_3122952 : Nat := 4983230072969 + 3 ^ 40 * 3122952 * 2
def baseEnd_3122952 : Nat := 1603575436919970669637811

theorem tailTrace_3122952 : CollatzResearch.WordTrace tailWord_3122952 prefixEnd_3122952 1603575436919970669637811 := by
  unfold tailWord_3122952
  simp only [CollatzResearch.WordTrace]
  refine ⟨56951708491042868291965555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75935611321390491055954073 56951708491042868291965555)
  ·
    refine ⟨85427562736564302437948333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56951708491042868291965555 85427562736564302437948333)
    ·
      refine ⟨32035336026211613414230625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85427562736564302437948333 32035336026211613414230625)
      ·
        refine ⟨24026502019658710060672969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32035336026211613414230625 24026502019658710060672969)
        ·
          refine ⟨18019876514744032545504727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24026502019658710060672969 18019876514744032545504727)
          ·
            refine ⟨27029814772116048818257091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18019876514744032545504727 27029814772116048818257091)
            ·
              refine ⟨40544722158174073227385637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27029814772116048818257091 40544722158174073227385637)
              ·
                refine ⟨7602135404657638730134807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40544722158174073227385637 7602135404657638730134807)
                ·
                  refine ⟨11403203106986458095202211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7602135404657638730134807 11403203106986458095202211)
                  ·
                    refine ⟨17104804660479687142803317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11403203106986458095202211 17104804660479687142803317)
                    ·
                      refine ⟨1603575436919970669637811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17104804660479687142803317 1603575436919970669637811)
                      ·
                        rfl

theorem cell23_3122952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3122952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122952 prefixEnd_3122952 := by exact prefixLift 3122952
  have htrace : WordTrace (prefixWord ++ tailWord_3122952) baseStart_3122952 baseEnd_3122952 := by
    simpa [prefixWord, tailWord_3122952, baseEnd_3122952] using wordTrace_append hprefix tailTrace_3122952
  have hstable : (prefixWord ++ tailWord_3122952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122952).length < 2 ^ (prefixWord ++ tailWord_3122952).sum := by decide
  have hdescent : baseEnd_3122952 < baseStart_3122952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122955 : List Nat := [1, 1, 1, 1, 5, 1, 3, 10]
def baseStart_3122955 : Nat := 118140960795 + 3122955 * 2 ^ 59
def prefixEnd_3122955 : Nat := 4983230072969 + 3 ^ 40 * 3122955 * 2
def baseEnd_3122955 : Nat := 59391739902293857700011

theorem tailTrace_3122955 : CollatzResearch.WordTrace tailWord_3122955 prefixEnd_3122955 59391739902293857700011 := by
  unfold tailWord_3122955
  simp only [CollatzResearch.WordTrace]
  refine ⟨113903526401074868096290319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75935684267383245397526879 113903526401074868096290319)
  ·
    refine ⟨170855289601612302144435479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113903526401074868096290319 170855289601612302144435479)
    ·
      refine ⟨256282934402418453216653219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170855289601612302144435479 256282934402418453216653219)
      ·
        refine ⟨384424401603627679824979829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256282934402418453216653219 384424401603627679824979829)
        ·
          refine ⟨36039787650340094983591859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 384424401603627679824979829 36039787650340094983591859)
          ·
            refine ⟨54059681475510142475387789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36039787650340094983591859 54059681475510142475387789)
            ·
              refine ⟨20272380553316303428270421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54059681475510142475387789 20272380553316303428270421)
              ·
                refine ⟨59391739902293857700011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20272380553316303428270421 59391739902293857700011)
                ·
                  rfl

theorem cell23_3122955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 10].length) (baseStart_3122955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122955 prefixEnd_3122955 := by exact prefixLift 3122955
  have htrace : WordTrace (prefixWord ++ tailWord_3122955) baseStart_3122955 baseEnd_3122955 := by
    simpa [prefixWord, tailWord_3122955, baseEnd_3122955] using wordTrace_append hprefix tailTrace_3122955
  have hstable : (prefixWord ++ tailWord_3122955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122955).length < 2 ^ (prefixWord ++ tailWord_3122955).sum := by decide
  have hdescent : baseEnd_3122955 < baseStart_3122955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3122985 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 3, 9]
def baseStart_3122985 : Nat := 118140960795 + 3122985 * 2 ^ 59
def prefixEnd_3122985 : Nat := 4983230072969 + 3 ^ 40 * 3122985 * 2
def baseEnd_3122985 : Nat := 534530793927189680175053

theorem tailTrace_3122985 : CollatzResearch.WordTrace tailWord_3122985 prefixEnd_3122985 534530793927189680175053 := by
  unfold tailWord_3122985
  simp only [CollatzResearch.WordTrace]
  refine ⟨113904620590966183219882409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75936413727310788813254939 113904620590966183219882409)
  ·
    refine ⟨85428465443224637414911807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113904620590966183219882409 85428465443224637414911807)
    ·
      refine ⟨128142698164836956122367711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85428465443224637414911807 128142698164836956122367711)
      ·
        refine ⟨192214047247255434183551567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128142698164836956122367711 192214047247255434183551567)
        ·
          refine ⟨288321070870883151275327351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192214047247255434183551567 288321070870883151275327351)
          ·
            refine ⟨432481606306324726912991027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288321070870883151275327351 432481606306324726912991027)
            ·
              refine ⟨648722409459487090369486541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432481606306324726912991027 648722409459487090369486541)
              ·
                refine ⟨243270903547307658888557453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 648722409459487090369486541 243270903547307658888557453)
                ·
                  refine ⟨91226588830240372083209045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243270903547307658888557453 91226588830240372083209045)
                  ·
                    refine ⟨534530793927189680175053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 91226588830240372083209045 534530793927189680175053)
                    ·
                      rfl

theorem cell23_3122985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_3122985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3122985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3122985 prefixEnd_3122985 := by exact prefixLift 3122985
  have htrace : WordTrace (prefixWord ++ tailWord_3122985) baseStart_3122985 baseEnd_3122985 := by
    simpa [prefixWord, tailWord_3122985, baseEnd_3122985] using wordTrace_append hprefix tailTrace_3122985
  have hstable : (prefixWord ++ tailWord_3122985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3122985).length < 2 ^ (prefixWord ++ tailWord_3122985).sum := by decide
  have hdescent : baseEnd_3122985 < baseStart_3122985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3122985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123000 : List Nat := [2, 1, 2, 1, 3, 3, 4, 2, 1, 2, 2]
def baseStart_3123000 : Nat := 118140960795 + 3123000 * 2 ^ 59
def prefixEnd_3123000 : Nat := 4983230072969 + 3 ^ 40 * 3123000 * 2
def baseEnd_3123000 : Nat := 1603600083991386481837591

theorem tailTrace_3123000 : CollatzResearch.WordTrace tailWord_3123000 prefixEnd_3123000 1603600083991386481837591 := by
  unfold tailWord_3123000
  simp only [CollatzResearch.WordTrace]
  refine ⟨56952583842955920390839227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75936778457274560521118969 56952583842955920390839227)
  ·
    refine ⟨85428875764433880586258841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56952583842955920390839227 85428875764433880586258841)
    ·
      refine ⟨64071656823325410439694131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85428875764433880586258841 64071656823325410439694131)
      ·
        refine ⟨96107485234988115659541197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64071656823325410439694131 96107485234988115659541197)
        ·
          refine ⟨36040306963120543372327949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96107485234988115659541197 36040306963120543372327949)
          ·
            refine ⟨13515115111170203764622981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36040306963120543372327949 13515115111170203764622981)
            ·
              refine ⟨2534084083344413205866809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13515115111170203764622981 2534084083344413205866809)
              ·
                refine ⟨1900563062508309904400107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534084083344413205866809 1900563062508309904400107)
                ·
                  refine ⟨2850844593762464856600161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900563062508309904400107 2850844593762464856600161)
                  ·
                    refine ⟨2138133445321848642450121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2850844593762464856600161 2138133445321848642450121)
                    ·
                      refine ⟨1603600083991386481837591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138133445321848642450121 1603600083991386481837591)
                      ·
                        rfl

theorem cell23_3123000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 1, 2, 2].length) (baseStart_3123000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123000 prefixEnd_3123000 := by exact prefixLift 3123000
  have htrace : WordTrace (prefixWord ++ tailWord_3123000) baseStart_3123000 baseEnd_3123000 := by
    simpa [prefixWord, tailWord_3123000, baseEnd_3123000] using wordTrace_append hprefix tailTrace_3123000
  have hstable : (prefixWord ++ tailWord_3123000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123000).length < 2 ^ (prefixWord ++ tailWord_3123000).sum := by decide
  have hdescent : baseEnd_3123000 < baseStart_3123000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123002 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_3123002 : Nat := 118140960795 + 3123002 * 2 ^ 59
def prefixEnd_3123002 : Nat := 4983230072969 + 3 ^ 40 * 3123002 * 2
def baseEnd_3123002 : Nat := 534533703650898491337527

theorem tailTrace_3123002 : CollatzResearch.WordTrace tailWord_3123002 prefixEnd_3123002 534533703650898491337527 := by
  unfold tailWord_3123002
  simp only [CollatzResearch.WordTrace]
  refine ⟨28476310157976148780812815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75936827087936396748834173 28476310157976148780812815)
  ·
    refine ⟨42714465236964223171219223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28476310157976148780812815 42714465236964223171219223)
    ·
      refine ⟨64071697855446334756828835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42714465236964223171219223 64071697855446334756828835)
      ·
        refine ⟨96107546783169502135243253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64071697855446334756828835 96107546783169502135243253)
        ·
          refine ⟨9010082510922140825179055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96107546783169502135243253 9010082510922140825179055)
          ·
            refine ⟨13515123766383211237768583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9010082510922140825179055 13515123766383211237768583)
            ·
              refine ⟨20272685649574816856652875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13515123766383211237768583 20272685649574816856652875)
              ·
                refine ⟨30409028474362225284979313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20272685649574816856652875 30409028474362225284979313)
                ·
                  refine ⟨22806771355771668963734485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30409028474362225284979313 22806771355771668963734485)
                  ·
                    refine ⟨534533703650898491337527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22806771355771668963734485 534533703650898491337527)
                    ·
                      rfl

theorem cell23_3123002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_3123002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123002 prefixEnd_3123002 := by exact prefixLift 3123002
  have htrace : WordTrace (prefixWord ++ tailWord_3123002) baseStart_3123002 baseEnd_3123002 := by
    simpa [prefixWord, tailWord_3123002, baseEnd_3123002] using wordTrace_append hprefix tailTrace_3123002
  have hstable : (prefixWord ++ tailWord_3123002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123002).length < 2 ^ (prefixWord ++ tailWord_3123002).sum := by decide
  have hdescent : baseEnd_3123002 < baseStart_3123002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123016 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_3123016 : Nat := 118140960795 + 3123016 * 2 ^ 59
def prefixEnd_3123016 : Nat := 4983230072969 + 3 ^ 40 * 3123016 * 2
def baseEnd_3123016 : Nat := 1603608299681858419237517

theorem tailTrace_3123016 : CollatzResearch.WordTrace tailWord_3123016 prefixEnd_3123016 1603608299681858419237517 := by
  unfold tailWord_3123016
  simp only [CollatzResearch.WordTrace]
  refine ⟨56952875626926937757130451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75937167502569250342840601 56952875626926937757130451)
  ·
    refine ⟨85429313440390406635695677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56952875626926937757130451 85429313440390406635695677)
    ·
      refine ⟨32035992540146402488385879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85429313440390406635695677 32035992540146402488385879)
      ·
        refine ⟨48053988810219603732578819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32035992540146402488385879 48053988810219603732578819)
        ·
          refine ⟨72080983215329405598868229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48053988810219603732578819 72080983215329405598868229)
          ·
            refine ⟨13515184352874263549787793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72080983215329405598868229 13515184352874263549787793)
            ·
              refine ⟨10136388264655697662340845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13515184352874263549787793 10136388264655697662340845)
              ·
                refine ⟨3801145599245886623377817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10136388264655697662340845 3801145599245886623377817)
                ·
                  refine ⟨2850859199434414967533363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3801145599245886623377817 2850859199434414967533363)
                  ·
                    refine ⟨4276288799151622451300045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2850859199434414967533363 4276288799151622451300045)
                    ·
                      refine ⟨1603608299681858419237517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4276288799151622451300045 1603608299681858419237517)
                      ·
                        rfl

theorem cell23_3123016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_3123016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123016 prefixEnd_3123016 := by exact prefixLift 3123016
  have htrace : WordTrace (prefixWord ++ tailWord_3123016) baseStart_3123016 baseEnd_3123016 := by
    simpa [prefixWord, tailWord_3123016, baseEnd_3123016] using wordTrace_append hprefix tailTrace_3123016
  have hstable : (prefixWord ++ tailWord_3123016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123016).length < 2 ^ (prefixWord ++ tailWord_3123016).sum := by decide
  have hdescent : baseEnd_3123016 < baseStart_3123016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123026 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_3123026 : Nat := 118140960795 + 3123026 * 2 ^ 59
def prefixEnd_3123026 : Nat := 4983230072969 + 3 ^ 40 * 3123026 * 2
def baseEnd_3123026 : Nat := 1603613434488403380112471

theorem tailTrace_3123026 : CollatzResearch.WordTrace tailWord_3123026 prefixEnd_3123026 1603613434488403380112471 := by
  unfold tailWord_3123026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28476528995954411805531233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75937410655878431481416621 28476528995954411805531233)
  ·
    refine ⟨21357396746965808854148425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28476528995954411805531233 21357396746965808854148425)
    ·
      refine ⟨16018047560224356640611319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21357396746965808854148425 16018047560224356640611319)
      ·
        refine ⟨24027071340336534960916979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16018047560224356640611319 24027071340336534960916979)
        ·
          refine ⟨36040607010504802441375469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24027071340336534960916979 36040607010504802441375469)
          ·
            refine ⟨13515227628939300915515801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36040607010504802441375469 13515227628939300915515801)
            ·
              refine ⟨10136420721704475686636851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13515227628939300915515801 10136420721704475686636851)
              ·
                refine ⟨15204631082556713529955277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10136420721704475686636851 15204631082556713529955277)
                ·
                  refine ⟨5701736655958767573733229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15204631082556713529955277 5701736655958767573733229)
                  ·
                    refine ⟨2138151245984537840149961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5701736655958767573733229 2138151245984537840149961)
                    ·
                      refine ⟨1603613434488403380112471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138151245984537840149961 1603613434488403380112471)
                      ·
                        rfl

theorem cell23_3123026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_3123026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123026 prefixEnd_3123026 := by exact prefixLift 3123026
  have htrace : WordTrace (prefixWord ++ tailWord_3123026) baseStart_3123026 baseEnd_3123026 := by
    simpa [prefixWord, tailWord_3123026, baseEnd_3123026] using wordTrace_append hprefix tailTrace_3123026
  have hstable : (prefixWord ++ tailWord_3123026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123026).length < 2 ^ (prefixWord ++ tailWord_3123026).sum := by decide
  have hdescent : baseEnd_3123026 < baseStart_3123026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123043 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 1, 3, 2]
def baseStart_3123043 : Nat := 118140960795 + 3123043 * 2 ^ 59
def prefixEnd_3123043 : Nat := 4983230072969 + 3 ^ 40 * 3123043 * 2
def baseEnd_3123043 : Nat := 1603622163659529813599893

theorem tailTrace_3123043 : CollatzResearch.WordTrace tailWord_3123043 prefixEnd_3123043 1603622163659529813599893 := by
  unfold tailWord_3123043
  simp only [CollatzResearch.WordTrace]
  refine ⟨113906736024756059125493783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75937824016504039416995855 113906736024756059125493783)
  ·
    refine ⟨170860104037134088688240675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113906736024756059125493783 170860104037134088688240675)
    ·
      refine ⟨256290156055701133032361013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170860104037134088688240675 256290156055701133032361013)
      ·
        refine ⟨24027202130221981221783845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256290156055701133032361013 24027202130221981221783845)
        ·
          refine ⟨4505100399416621479084471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24027202130221981221783845 4505100399416621479084471)
          ·
            refine ⟨6757650599124932218626707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4505100399416621479084471 6757650599124932218626707)
            ·
              refine ⟨10136475898687398327940061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6757650599124932218626707 10136475898687398327940061)
              ·
                refine ⟨3801178462007774372977523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10136475898687398327940061 3801178462007774372977523)
                ·
                  refine ⟨5701767693011661559466285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801178462007774372977523 5701767693011661559466285)
                  ·
                    refine ⟨2138162884879373084799857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5701767693011661559466285 2138162884879373084799857)
                    ·
                      refine ⟨1603622163659529813599893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138162884879373084799857 1603622163659529813599893)
                      ·
                        rfl

theorem cell23_3123043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_3123043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123043 prefixEnd_3123043 := by exact prefixLift 3123043
  have htrace : WordTrace (prefixWord ++ tailWord_3123043) baseStart_3123043 baseEnd_3123043 := by
    simpa [prefixWord, tailWord_3123043, baseEnd_3123043] using wordTrace_append hprefix tailTrace_3123043
  have hstable : (prefixWord ++ tailWord_3123043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123043).length < 2 ^ (prefixWord ++ tailWord_3123043).sum := by decide
  have hdescent : baseEnd_3123043 < baseStart_3123043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123129 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3123129 : Nat := 118140960795 + 3123129 * 2 ^ 59
def prefixEnd_3123129 : Nat := 4983230072969 + 3 ^ 40 * 3123129 * 2
def baseEnd_3123129 : Nat := 1603666322995816477124497

theorem tailTrace_3123129 : CollatzResearch.WordTrace tailWord_3123129 prefixEnd_3123129 1603666322995816477124497 := by
  unfold tailWord_3123129
  simp only [CollatzResearch.WordTrace]
  refine ⟨113909872702444495813124441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75939915134962997208749627 113909872702444495813124441)
  ·
    refine ⟨85432404526833371859843331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113909872702444495813124441 85432404526833371859843331)
    ·
      refine ⟨128148606790250057789764997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85432404526833371859843331 128148606790250057789764997)
      ·
        refine ⟨24027863773171885835580937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128148606790250057789764997 24027863773171885835580937)
        ·
          refine ⟨18020897829878914376685703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24027863773171885835580937 18020897829878914376685703)
          ·
            refine ⟨27031346744818371565028555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18020897829878914376685703 27031346744818371565028555)
            ·
              refine ⟨40547020117227557347542833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27031346744818371565028555 40547020117227557347542833)
              ·
                refine ⟨30410265087920668010657125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40547020117227557347542833 30410265087920668010657125)
                ·
                  refine ⟨5701924703985125251998211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30410265087920668010657125 5701924703985125251998211)
                  ·
                    refine ⟨8552887055977687877997317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5701924703985125251998211 8552887055977687877997317)
                    ·
                      refine ⟨1603666322995816477124497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8552887055977687877997317 1603666322995816477124497)
                      ·
                        rfl

theorem cell23_3123129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3123129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123129 prefixEnd_3123129 := by exact prefixLift 3123129
  have htrace : WordTrace (prefixWord ++ tailWord_3123129) baseStart_3123129 baseEnd_3123129 := by
    simpa [prefixWord, tailWord_3123129, baseEnd_3123129] using wordTrace_append hprefix tailTrace_3123129
  have hstable : (prefixWord ++ tailWord_3123129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123129).length < 2 ^ (prefixWord ++ tailWord_3123129).sum := by decide
  have hdescent : baseEnd_3123129 < baseStart_3123129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123152 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 10]
def baseStart_3123152 : Nat := 118140960795 + 3123152 * 2 ^ 59
def prefixEnd_3123152 : Nat := 4983230072969 + 3 ^ 40 * 3123152 * 2
def baseEnd_3123152 : Nat := 178186459227874431904099

theorem tailTrace_3123152 : CollatzResearch.WordTrace tailWord_3123152 prefixEnd_3123152 178186459227874431904099 := by
  unfold tailWord_3123152
  simp only [CollatzResearch.WordTrace]
  refine ⟨56955355790680585370605855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75940474387574113827474473 56955355790680585370605855)
  ·
    refine ⟨85433033686020878055908783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56955355790680585370605855 85433033686020878055908783)
    ·
      refine ⟨128149550529031317083863175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85433033686020878055908783 128149550529031317083863175)
      ·
        refine ⟨192224325793546975625794763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128149550529031317083863175 192224325793546975625794763)
        ·
          refine ⟨288336488690320463438692145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192224325793546975625794763 288336488690320463438692145)
          ·
            refine ⟨216252366517740347579019109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288336488690320463438692145 216252366517740347579019109)
            ·
              refine ⟨40547318722076315171066083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216252366517740347579019109 40547318722076315171066083)
              ·
                refine ⟨60820978083114472756599125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40547318722076315171066083 60820978083114472756599125)
                ·
                  refine ⟨178186459227874431904099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 60820978083114472756599125 178186459227874431904099)
                  ·
                    rfl

theorem cell23_3123152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 10].length) (baseStart_3123152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123152 prefixEnd_3123152 := by exact prefixLift 3123152
  have htrace : WordTrace (prefixWord ++ tailWord_3123152) baseStart_3123152 baseEnd_3123152 := by
    simpa [prefixWord, tailWord_3123152, baseEnd_3123152] using wordTrace_append hprefix tailTrace_3123152
  have hstable : (prefixWord ++ tailWord_3123152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123152).length < 2 ^ (prefixWord ++ tailWord_3123152).sum := by decide
  have hdescent : baseEnd_3123152 < baseStart_3123152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123164 : List Nat := [2, 2, 6, 1, 1, 2, 2, 2, 5]
def baseStart_3123164 : Nat := 118140960795 + 3123164 * 2 ^ 59
def prefixEnd_3123164 : Nat := 4983230072969 + 3 ^ 40 * 3123164 * 2
def baseEnd_3123164 : Nat := 178187143868747093354093

theorem tailTrace_3123164 : CollatzResearch.WordTrace tailWord_3123164 prefixEnd_3123164 178187143868747093354093 := by
  unfold tailWord_3123164
  simp only [CollatzResearch.WordTrace]
  refine ⟨56955574628658848395324273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75940766171545131193765697 56955574628658848395324273)
  ·
    refine ⟨42716680971494136296493205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56955574628658848395324273 42716680971494136296493205)
    ·
      refine ⟨2002344420538787638898119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42716680971494136296493205 2002344420538787638898119)
      ·
        refine ⟨3003516630808181458347179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2002344420538787638898119 3003516630808181458347179)
        ·
          refine ⟨4505274946212272187520769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003516630808181458347179 4505274946212272187520769)
          ·
            refine ⟨3378956209659204140640577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4505274946212272187520769 3378956209659204140640577)
            ·
              refine ⟨2534217157244403105480433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378956209659204140640577 2534217157244403105480433)
              ·
                refine ⟨1900662867933302329110325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534217157244403105480433 1900662867933302329110325)
                ·
                  refine ⟨178187143868747093354093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1900662867933302329110325 178187143868747093354093)
                  ·
                    rfl

theorem cell23_3123164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_3123164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123164 prefixEnd_3123164 := by exact prefixLift 3123164
  have htrace : WordTrace (prefixWord ++ tailWord_3123164) baseStart_3123164 baseEnd_3123164 := by
    simpa [prefixWord, tailWord_3123164, baseEnd_3123164] using wordTrace_append hprefix tailTrace_3123164
  have hstable : (prefixWord ++ tailWord_3123164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123164).length < 2 ^ (prefixWord ++ tailWord_3123164).sum := by decide
  have hdescent : baseEnd_3123164 < baseStart_3123164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123169 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 6]
def baseStart_3123169 : Nat := 118140960795 + 3123169 * 2 ^ 59
def prefixEnd_3123169 : Nat := 4983230072969 + 3 ^ 40 * 3123169 * 2
def baseEnd_3123169 : Nat := 178187429135777368958257

theorem tailTrace_3123169 : CollatzResearch.WordTrace tailWord_3123169 prefixEnd_3123169 178187429135777368958257 := by
  unfold tailWord_3123169
  simp only [CollatzResearch.WordTrace]
  refine ⟨113911331622299582644580561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75940887748199721763053707 113911331622299582644580561)
  ·
    refine ⟨85433498716724686983435421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113911331622299582644580561 85433498716724686983435421)
    ·
      refine ⟨32037562018771757618788283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85433498716724686983435421 32037562018771757618788283)
      ·
        refine ⟨48056343028157636428182425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32037562018771757618788283 48056343028157636428182425)
        ·
          refine ⟨36042257271118227321136819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48056343028157636428182425 36042257271118227321136819)
          ·
            refine ⟨54063385906677340981705229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36042257271118227321136819 54063385906677340981705229)
            ·
              refine ⟨20273769715004002868139461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54063385906677340981705229 20273769715004002868139461)
              ·
                refine ⟨3801331821563250537776149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20273769715004002868139461 3801331821563250537776149)
                ·
                  refine ⟨178187429135777368958257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3801331821563250537776149 178187429135777368958257)
                  ·
                    rfl

theorem cell23_3123169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 6].length) (baseStart_3123169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123169 prefixEnd_3123169 := by exact prefixLift 3123169
  have htrace : WordTrace (prefixWord ++ tailWord_3123169) baseStart_3123169 baseEnd_3123169 := by
    simpa [prefixWord, tailWord_3123169, baseEnd_3123169] using wordTrace_append hprefix tailTrace_3123169
  have hstable : (prefixWord ++ tailWord_3123169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123169).length < 2 ^ (prefixWord ++ tailWord_3123169).sum := by decide
  have hdescent : baseEnd_3123169 < baseStart_3123169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123270 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3123270 : Nat := 118140960795 + 3123270 * 2 ^ 59
def prefixEnd_3123270 : Nat := 4983230072969 + 3 ^ 40 * 3123270 * 2
def baseEnd_3123270 : Nat := 1603738723768100425461349

theorem tailTrace_3123270 : CollatzResearch.WordTrace tailWord_3123270 prefixEnd_3123270 1603738723768100425461349 := by
  unfold tailWord_3123270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3559844231091677402937727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75943343596622451262671509 3559844231091677402937727)
  ·
    refine ⟨5339766346637516104406591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3559844231091677402937727 5339766346637516104406591)
    ·
      refine ⟨8009649519956274156609887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5339766346637516104406591 8009649519956274156609887)
      ·
        refine ⟨12014474279934411234914831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8009649519956274156609887 12014474279934411234914831)
        ·
          refine ⟨18021711419901616852372247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12014474279934411234914831 18021711419901616852372247)
          ·
            refine ⟨27032567129852425278558371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18021711419901616852372247 27032567129852425278558371)
            ·
              refine ⟨40548850694778637917837557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27032567129852425278558371 40548850694778637917837557)
              ·
                refine ⟨3801454752635497304797271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40548850694778637917837557 3801454752635497304797271)
                ·
                  refine ⟨5702182128953245957195907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801454752635497304797271 5702182128953245957195907)
                  ·
                    refine ⟨8553273193429868935793861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5702182128953245957195907 8553273193429868935793861)
                    ·
                      refine ⟨1603738723768100425461349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8553273193429868935793861 1603738723768100425461349)
                      ·
                        rfl

theorem cell23_3123270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3123270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123270 prefixEnd_3123270 := by exact prefixLift 3123270
  have htrace : WordTrace (prefixWord ++ tailWord_3123270) baseStart_3123270 baseEnd_3123270 := by
    simpa [prefixWord, tailWord_3123270, baseEnd_3123270] using wordTrace_append hprefix tailTrace_3123270
  have hstable : (prefixWord ++ tailWord_3123270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123270).length < 2 ^ (prefixWord ++ tailWord_3123270).sum := by decide
  have hdescent : baseEnd_3123270 < baseStart_3123270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123289 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 2, 7]
def baseStart_3123289 : Nat := 118140960795 + 3123289 * 2 ^ 59
def prefixEnd_3123289 : Nat := 4983230072969 + 3 ^ 40 * 3123289 * 2
def baseEnd_3123289 : Nat := 534582826633511950374587

theorem tailTrace_3123289 : CollatzResearch.WordTrace tailWord_3123289 prefixEnd_3123289 534582826633511950374587 := by
  unfold tailWord_3123289
  simp only [CollatzResearch.WordTrace]
  refine ⟨113915708381864843138948921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75943805587909895425965947 113915708381864843138948921)
  ·
    refine ⟨85436781286398632354211691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113915708381864843138948921 85436781286398632354211691)
    ·
      refine ⟨128155171929597948531317537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85436781286398632354211691 128155171929597948531317537)
      ·
        refine ⟨96116378947198461398488153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128155171929597948531317537 96116378947198461398488153)
        ·
          refine ⟨72087284210398846048866115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96116378947198461398488153 72087284210398846048866115)
          ·
            refine ⟨108130926315598269073299173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72087284210398846048866115 108130926315598269073299173)
            ·
              refine ⟨20274548684174675451243595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108130926315598269073299173 20274548684174675451243595)
              ·
                refine ⟨30411823026262013176865393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20274548684174675451243595 30411823026262013176865393)
                ·
                  refine ⟨22808867269696509882649045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30411823026262013176865393 22808867269696509882649045)
                  ·
                    refine ⟨534582826633511950374587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22808867269696509882649045 534582826633511950374587)
                    ·
                      rfl

theorem cell23_3123289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_3123289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123289 prefixEnd_3123289 := by exact prefixLift 3123289
  have htrace : WordTrace (prefixWord ++ tailWord_3123289) baseStart_3123289 baseEnd_3123289 := by
    simpa [prefixWord, tailWord_3123289, baseEnd_3123289] using wordTrace_append hprefix tailTrace_3123289
  have hstable : (prefixWord ++ tailWord_3123289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123289).length < 2 ^ (prefixWord ++ tailWord_3123289).sum := by decide
  have hdescent : baseEnd_3123289 < baseStart_3123289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123293 : List Nat := [1, 4, 4, 1, 1, 2, 2, 8]
def baseStart_3123293 : Nat := 118140960795 + 3123293 * 2 ^ 59
def prefixEnd_3123293 : Nat := 4983230072969 + 3 ^ 40 * 3123293 * 2
def baseEnd_3123293 : Nat := 59398167919376067980509

theorem tailTrace_3123293 : CollatzResearch.WordTrace tailWord_3123293 prefixEnd_3123293 59398167919376067980509 := by
  unfold tailWord_3123293
  simp only [CollatzResearch.WordTrace]
  refine ⟨113915854273850351822094533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75943902849233567881396355 113915854273850351822094533)
  ·
    refine ⟨21359222676346940966642725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113915854273850351822094533 21359222676346940966642725)
    ·
      refine ⟨4004854251815051431245511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21359222676346940966642725 4004854251815051431245511)
      ·
        refine ⟨6007281377722577146868267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4004854251815051431245511 6007281377722577146868267)
        ·
          refine ⟨9010922066583865720302401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6007281377722577146868267 9010922066583865720302401)
          ·
            refine ⟨6758191549937899290226801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9010922066583865720302401 6758191549937899290226801)
            ·
              refine ⟨5068643662453424467670101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6758191549937899290226801 5068643662453424467670101)
              ·
                refine ⟨59398167919376067980509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5068643662453424467670101 59398167919376067980509)
                ·
                  rfl

theorem cell23_3123293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 8].length) (baseStart_3123293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123293 prefixEnd_3123293 := by exact prefixLift 3123293
  have htrace : WordTrace (prefixWord ++ tailWord_3123293) baseStart_3123293 baseEnd_3123293 := by
    simpa [prefixWord, tailWord_3123293, baseEnd_3123293] using wordTrace_append hprefix tailTrace_3123293
  have hstable : (prefixWord ++ tailWord_3123293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123293).length < 2 ^ (prefixWord ++ tailWord_3123293).sum := by decide
  have hdescent : baseEnd_3123293 < baseStart_3123293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123313 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 3, 3, 2]
def baseStart_3123313 : Nat := 118140960795 + 3123313 * 2 ^ 59
def prefixEnd_3123313 : Nat := 4983230072969 + 3 ^ 40 * 3123313 * 2
def baseEnd_3123313 : Nat := 1603760803436243757223651

theorem tailTrace_3123313 : CollatzResearch.WordTrace tailWord_3123313 prefixEnd_3123313 1603760803436243757223651 := by
  unfold tailWord_3123313
  simp only [CollatzResearch.WordTrace]
  refine ⟨113916583733777895237822593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75944389155851930158548395 113916583733777895237822593)
  ·
    refine ⟨85437437800333421428366945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113916583733777895237822593 85437437800333421428366945)
    ·
      refine ⟨64078078350250066071275209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85437437800333421428366945 64078078350250066071275209)
      ·
        refine ⟨48058558762687549553456407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64078078350250066071275209 48058558762687549553456407)
        ·
          refine ⟨72087838144031324330184611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48058558762687549553456407 72087838144031324330184611)
          ·
            refine ⟨108131757216046986495276917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72087838144031324330184611 108131757216046986495276917)
            ·
              refine ⟨10137352239004404983932211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108131757216046986495276917 10137352239004404983932211)
              ·
                refine ⟨15206028358506607475898317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10137352239004404983932211 15206028358506607475898317)
                ·
                  refine ⟨5702260634439977803461869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15206028358506607475898317 5702260634439977803461869)
                  ·
                    refine ⟨2138347737914991676298201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5702260634439977803461869 2138347737914991676298201)
                    ·
                      refine ⟨1603760803436243757223651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138347737914991676298201 1603760803436243757223651)
                      ·
                        rfl

theorem cell23_3123313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_3123313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123313 prefixEnd_3123313 := by exact prefixLift 3123313
  have htrace : WordTrace (prefixWord ++ tailWord_3123313) baseStart_3123313 baseEnd_3123313 := by
    simpa [prefixWord, tailWord_3123313, baseEnd_3123313] using wordTrace_append hprefix tailTrace_3123313
  have hstable : (prefixWord ++ tailWord_3123313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123313).length < 2 ^ (prefixWord ++ tailWord_3123313).sum := by decide
  have hdescent : baseEnd_3123313 < baseStart_3123313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123339 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 6]
def baseStart_3123339 : Nat := 118140960795 + 3123339 * 2 ^ 59
def prefixEnd_3123339 : Nat := 4983230072969 + 3 ^ 40 * 3123339 * 2
def baseEnd_3123339 : Nat := 1603774153933260655498531

theorem tailTrace_3123339 : CollatzResearch.WordTrace tailWord_3123339 prefixEnd_3123339 1603774153933260655498531 := by
  unfold tailWord_3123339
  simp only [CollatzResearch.WordTrace]
  refine ⟨113917532031683701678269071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75945021354455801118846047 113917532031683701678269071)
  ·
    refine ⟨170876298047525552517403607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113917532031683701678269071 170876298047525552517403607)
    ·
      refine ⟨256314447071288328776105411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170876298047525552517403607 256314447071288328776105411)
      ·
        refine ⟨384471670606932493164158117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256314447071288328776105411 384471670606932493164158117)
        ·
          refine ⟨72088438238799842468279647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384471670606932493164158117 72088438238799842468279647)
          ·
            refine ⟨108132657358199763702419471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72088438238799842468279647 108132657358199763702419471)
            ·
              refine ⟨162198986037299645553629207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108132657358199763702419471 162198986037299645553629207)
              ·
                refine ⟨243298479055949468330443811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162198986037299645553629207 243298479055949468330443811)
                ·
                  refine ⟨364947718583924202495665717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243298479055949468330443811 364947718583924202495665717)
                  ·
                    refine ⟨34213848617242893983968661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 364947718583924202495665717 34213848617242893983968661)
                    ·
                      refine ⟨1603774153933260655498531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34213848617242893983968661 1603774153933260655498531)
                      ·
                        rfl

theorem cell23_3123339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_3123339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123339 prefixEnd_3123339 := by exact prefixLift 3123339
  have htrace : WordTrace (prefixWord ++ tailWord_3123339) baseStart_3123339 baseEnd_3123339 := by
    simpa [prefixWord, tailWord_3123339, baseEnd_3123339] using wordTrace_append hprefix tailTrace_3123339
  have hstable : (prefixWord ++ tailWord_3123339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123339).length < 2 ^ (prefixWord ++ tailWord_3123339).sum := by decide
  have hdescent : baseEnd_3123339 < baseStart_3123339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123360 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 1, 4, 2]
def baseStart_3123360 : Nat := 118140960795 + 3123360 * 2 ^ 59
def prefixEnd_3123360 : Nat := 4983230072969 + 3 ^ 40 * 3123360 * 2
def baseEnd_3123360 : Nat := 1603784937027005073335935

theorem tailTrace_3123360 : CollatzResearch.WordTrace tailWord_3123360 prefixEnd_3123360 1603784937027005073335935 := by
  unfold tailWord_3123360
  simp only [CollatzResearch.WordTrace]
  refine ⟨56959148982303811132391767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75945531976405081509855689 56959148982303811132391767)
  ·
    refine ⟨85438723473455716698587651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56959148982303811132391767 85438723473455716698587651)
    ·
      refine ⟨128158085210183575047881477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85438723473455716698587651 128158085210183575047881477)
      ·
        refine ⟨24029640976909420321477777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128158085210183575047881477 24029640976909420321477777)
        ·
          refine ⟨18022230732682065241108333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24029640976909420321477777 18022230732682065241108333)
          ·
            refine ⟨6758336524755774465415625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18022230732682065241108333 6758336524755774465415625)
            ·
              refine ⟨5068752393566830849061719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6758336524755774465415625 5068752393566830849061719)
              ·
                refine ⟨7603128590350246273592579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5068752393566830849061719 7603128590350246273592579)
                ·
                  refine ⟨11404692885525369410388869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7603128590350246273592579 11404692885525369410388869)
                  ·
                    refine ⟨2138379916036006764447913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11404692885525369410388869 2138379916036006764447913)
                    ·
                      refine ⟨1603784937027005073335935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138379916036006764447913 1603784937027005073335935)
                      ·
                        rfl

theorem cell23_3123360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_3123360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123360 prefixEnd_3123360 := by exact prefixLift 3123360
  have htrace : WordTrace (prefixWord ++ tailWord_3123360) baseStart_3123360 baseEnd_3123360 := by
    simpa [prefixWord, tailWord_3123360, baseEnd_3123360] using wordTrace_append hprefix tailTrace_3123360
  have hstable : (prefixWord ++ tailWord_3123360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123360).length < 2 ^ (prefixWord ++ tailWord_3123360).sum := by decide
  have hdescent : baseEnd_3123360 < baseStart_3123360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123376 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 3]
def baseStart_3123376 : Nat := 118140960795 + 3123376 * 2 ^ 59
def prefixEnd_3123376 : Nat := 4983230072969 + 3 ^ 40 * 3123376 * 2
def baseEnd_3123376 : Nat := 1603793152717477010735861

theorem tailTrace_3123376 : CollatzResearch.WordTrace tailWord_3123376 prefixEnd_3123376 1603793152717477010735861 := by
  unfold tailWord_3123376
  simp only [CollatzResearch.WordTrace]
  refine ⟨56959440766274828498682991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75945921021699771331577321 56959440766274828498682991)
  ·
    refine ⟨85439161149412242748024487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56959440766274828498682991 85439161149412242748024487)
    ·
      refine ⟨128158741724118364122036731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85439161149412242748024487 128158741724118364122036731)
      ·
        refine ⟨192238112586177546183055097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128158741724118364122036731 192238112586177546183055097)
        ·
          refine ⟨144178584439633159637291323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192238112586177546183055097 144178584439633159637291323)
          ·
            refine ⟨216267876659449739455936985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144178584439633159637291323 216267876659449739455936985)
            ·
              refine ⟨162200907494587304591952739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216267876659449739455936985 162200907494587304591952739)
              ·
                refine ⟨243301361241880956887929109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162200907494587304591952739 243301361241880956887929109)
                ·
                  refine ⟨11404751308213169854121677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 243301361241880956887929109 11404751308213169854121677)
                  ·
                    refine ⟨4276781740579938695295629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11404751308213169854121677 4276781740579938695295629)
                    ·
                      refine ⟨1603793152717477010735861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4276781740579938695295629 1603793152717477010735861)
                      ·
                        rfl

theorem cell23_3123376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 3].length) (baseStart_3123376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123376 prefixEnd_3123376 := by exact prefixLift 3123376
  have htrace : WordTrace (prefixWord ++ tailWord_3123376) baseStart_3123376 baseEnd_3123376 := by
    simpa [prefixWord, tailWord_3123376, baseEnd_3123376] using wordTrace_append hprefix tailTrace_3123376
  have hstable : (prefixWord ++ tailWord_3123376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123376).length < 2 ^ (prefixWord ++ tailWord_3123376).sum := by decide
  have hdescent : baseEnd_3123376 < baseStart_3123376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123381 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_3123381 : Nat := 118140960795 + 3123381 * 2 ^ 59
def prefixEnd_3123381 : Nat := 4983230072969 + 3 ^ 40 * 3123381 * 2
def baseEnd_3123381 : Nat := 1603795720120749491173339

theorem tailTrace_3123381 : CollatzResearch.WordTrace tailWord_3123381 prefixEnd_3123381 1603795720120749491173339 := by
  unfold tailWord_3123381
  simp only [CollatzResearch.WordTrace]
  refine ⟨113919063897531542851297997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75946042598354361900865331 113919063897531542851297997)
  ·
    refine ⟨42719648961574328569236749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113919063897531542851297997 42719648961574328569236749)
    ·
      refine ⟨16019868360590373213463781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42719648961574328569236749 16019868360590373213463781)
      ·
        refine ⟨3003725317610694977524459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16019868360590373213463781 3003725317610694977524459)
        ·
          refine ⟨4505587976416042466286689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003725317610694977524459 4505587976416042466286689)
          ·
            refine ⟨3379190982312031849715017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4505587976416042466286689 3379190982312031849715017)
            ·
              refine ⟨2534393236734023887286263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3379190982312031849715017 2534393236734023887286263)
              ·
                refine ⟨3801589855101035830929395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2534393236734023887286263 3801589855101035830929395)
                ·
                  refine ⟨5702384782651553746394093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801589855101035830929395 5702384782651553746394093)
                  ·
                    refine ⟨2138394293494332654897785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5702384782651553746394093 2138394293494332654897785)
                    ·
                      refine ⟨1603795720120749491173339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138394293494332654897785 1603795720120749491173339)
                      ·
                        rfl

theorem cell23_3123381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_3123381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123381 prefixEnd_3123381 := by exact prefixLift 3123381
  have htrace : WordTrace (prefixWord ++ tailWord_3123381) baseStart_3123381 baseEnd_3123381 := by
    simpa [prefixWord, tailWord_3123381, baseEnd_3123381] using wordTrace_append hprefix tailTrace_3123381
  have hstable : (prefixWord ++ tailWord_3123381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123381).length < 2 ^ (prefixWord ++ tailWord_3123381).sum := by decide
  have hdescent : baseEnd_3123381 < baseStart_3123381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123383 : List Nat := [1, 1, 3, 1, 4, 2, 1, 5, 5]
def baseStart_3123383 : Nat := 118140960795 + 3123383 * 2 ^ 59
def prefixEnd_3123383 : Nat := 4983230072969 + 3 ^ 40 * 3123383 * 2
def baseEnd_3123383 : Nat := 178199638564673164816481

theorem tailTrace_3123383 : CollatzResearch.WordTrace tailWord_3123383 prefixEnd_3123383 178199638564673164816481 := by
  unfold tailWord_3123383
  simp only [CollatzResearch.WordTrace]
  refine ⟨113919136843524297192870803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75946091229016198128580535 113919136843524297192870803)
  ·
    refine ⟨170878705265286445789306205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113919136843524297192870803 170878705265286445789306205)
    ·
      refine ⟨64079514474482417170989827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170878705265286445789306205 64079514474482417170989827)
      ·
        refine ⟨96119271711723625756484741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64079514474482417170989827 96119271711723625756484741)
        ·
          refine ⟨18022363445948179829340889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96119271711723625756484741 18022363445948179829340889)
          ·
            refine ⟨13516772584461134872005667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18022363445948179829340889 13516772584461134872005667)
            ·
              refine ⟨20275158876691702308008501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13516772584461134872005667 20275158876691702308008501)
              ·
                refine ⟨1900796144689847091375797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20275158876691702308008501 1900796144689847091375797)
                ·
                  refine ⟨178199638564673164816481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1900796144689847091375797 178199638564673164816481)
                  ·
                    rfl

theorem cell23_3123383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 5].length) (baseStart_3123383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123383 prefixEnd_3123383 := by exact prefixLift 3123383
  have htrace : WordTrace (prefixWord ++ tailWord_3123383) baseStart_3123383 baseEnd_3123383 := by
    simpa [prefixWord, tailWord_3123383, baseEnd_3123383] using wordTrace_append hprefix tailTrace_3123383
  have hstable : (prefixWord ++ tailWord_3123383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123383).length < 2 ^ (prefixWord ++ tailWord_3123383).sum := by decide
  have hdescent : baseEnd_3123383 < baseStart_3123383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123456 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 8]
def baseStart_3123456 : Nat := 118140960795 + 3123456 * 2 ^ 59
def prefixEnd_3123456 : Nat := 4983230072969 + 3 ^ 40 * 3123456 * 2
def baseEnd_3123456 : Nat := 178203803463315188637277

theorem tailTrace_3123456 : CollatzResearch.WordTrace tailWord_3123456 prefixEnd_3123456 178203803463315188637277 := by
  unfold tailWord_3123456
  simp only [CollatzResearch.WordTrace]
  refine ⟨56960899686129915330139111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75947866248173220440185481 56960899686129915330139111)
  ·
    refine ⟨85441349529194872995208667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56960899686129915330139111 85441349529194872995208667)
    ·
      refine ⟨128162024293792309492813001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85441349529194872995208667 128162024293792309492813001)
      ·
        refine ⟨96121518220344232119609751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128162024293792309492813001 96121518220344232119609751)
        ·
          refine ⟨144182277330516348179414627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96121518220344232119609751 144182277330516348179414627)
          ·
            refine ⟨216273415995774522269121941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144182277330516348179414627 216273415995774522269121941)
            ·
              refine ⟨10137816374801930731365091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 216273415995774522269121941 10137816374801930731365091)
              ·
                refine ⟨15206724562202896097047637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10137816374801930731365091 15206724562202896097047637)
                ·
                  refine ⟨178203803463315188637277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15206724562202896097047637 178203803463315188637277)
                  ·
                    rfl

theorem cell23_3123456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 8].length) (baseStart_3123456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123456 prefixEnd_3123456 := by exact prefixLift 3123456
  have htrace : WordTrace (prefixWord ++ tailWord_3123456) baseStart_3123456 baseEnd_3123456 := by
    simpa [prefixWord, tailWord_3123456, baseEnd_3123456] using wordTrace_append hprefix tailTrace_3123456
  have hstable : (prefixWord ++ tailWord_3123456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123456).length < 2 ^ (prefixWord ++ tailWord_3123456).sum := by decide
  have hdescent : baseEnd_3123456 < baseStart_3123456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123473 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 6]
def baseStart_3123473 : Nat := 118140960795 + 3123473 * 2 ^ 59
def prefixEnd_3123473 : Nat := 4983230072969 + 3 ^ 40 * 3123473 * 2
def baseEnd_3123473 : Nat := 178204773371218125691435

theorem tailTrace_3123473 : CollatzResearch.WordTrace tailWord_3123473 prefixEnd_3123473 178204773371218125691435 := by
  unfold tailWord_3123473
  simp only [CollatzResearch.WordTrace]
  refine ⟨113922419413198242563647073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75948279608798828375764715 113922419413198242563647073)
  ·
    refine ⟨85441814559898681922735305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113922419413198242563647073 85441814559898681922735305)
    ·
      refine ⟨64081360919924011442051479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85441814559898681922735305 64081360919924011442051479)
      ·
        refine ⟨96122041379886017163077219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64081360919924011442051479 96122041379886017163077219)
        ·
          refine ⟨144183062069829025744615829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96122041379886017163077219 144183062069829025744615829)
          ·
            refine ⟨6758581034523235581778867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144183062069829025744615829 6758581034523235581778867)
            ·
              refine ⟨10137871551784853372668301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6758581034523235581778867 10137871551784853372668301)
              ·
                refine ⟨3801701831919320014750613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10137871551784853372668301 3801701831919320014750613)
                ·
                  refine ⟨178204773371218125691435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3801701831919320014750613 178204773371218125691435)
                  ·
                    rfl

theorem cell23_3123473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 6].length) (baseStart_3123473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123473 prefixEnd_3123473 := by exact prefixLift 3123473
  have htrace : WordTrace (prefixWord ++ tailWord_3123473) baseStart_3123473 baseEnd_3123473 := by
    simpa [prefixWord, tailWord_3123473, baseEnd_3123473] using wordTrace_append hprefix tailTrace_3123473
  have hstable : (prefixWord ++ tailWord_3123473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123473).length < 2 ^ (prefixWord ++ tailWord_3123473).sum := by decide
  have hdescent : baseEnd_3123473 < baseStart_3123473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123503 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 1, 5]
def baseStart_3123503 : Nat := 118140960795 + 3123503 * 2 ^ 59
def prefixEnd_3123503 : Nat := 4983230072969 + 3 ^ 40 * 3123503 * 2
def baseEnd_3123503 : Nat := 534619454920199337949259

theorem tailTrace_3123503 : CollatzResearch.WordTrace tailWord_3123503 prefixEnd_3123503 534619454920199337949259 := by
  unfold tailWord_3123503
  simp only [CollatzResearch.WordTrace]
  refine ⟨113923513603089557687239163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75949009068726371791492775 113923513603089557687239163)
  ·
    refine ⟨170885270404634336530858745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113923513603089557687239163 170885270404634336530858745)
    ·
      refine ⟨128163952803475752398144059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170885270404634336530858745 128163952803475752398144059)
      ·
        refine ⟨192245929205213628597216089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128163952803475752398144059 192245929205213628597216089)
        ·
          refine ⟨144184446903910221447912067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192245929205213628597216089 144184446903910221447912067)
          ·
            refine ⟨216276670355865332171868101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144184446903910221447912067 216276670355865332171868101)
            ·
              refine ⟨40551875691724749782225269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216276670355865332171868101 40551875691724749782225269)
              ·
                refine ⟨3801738346099195292083619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40551875691724749782225269 3801738346099195292083619)
                ·
                  refine ⟨5702607519148792938125429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801738346099195292083619 5702607519148792938125429)
                  ·
                    refine ⟨534619454920199337949259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5702607519148792938125429 534619454920199337949259)
                    ·
                      rfl

theorem cell23_3123503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 5].length) (baseStart_3123503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123503 prefixEnd_3123503 := by exact prefixLift 3123503
  have htrace : WordTrace (prefixWord ++ tailWord_3123503) baseStart_3123503 baseEnd_3123503 := by
    simpa [prefixWord, tailWord_3123503, baseEnd_3123503] using wordTrace_append hprefix tailTrace_3123503
  have hstable : (prefixWord ++ tailWord_3123503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123503).length < 2 ^ (prefixWord ++ tailWord_3123503).sum := by decide
  have hdescent : baseEnd_3123503 < baseStart_3123503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123523 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 4]
def baseStart_3123523 : Nat := 118140960795 + 3123523 * 2 ^ 59
def prefixEnd_3123523 : Nat := 4983230072969 + 3 ^ 40 * 3123523 * 2
def baseEnd_3123523 : Nat := 1603868634373687935597685

theorem tailTrace_3123523 : CollatzResearch.WordTrace tailWord_3123523 prefixEnd_3123523 1603868634373687935597685 := by
  unfold tailWord_3123523
  simp only [CollatzResearch.WordTrace]
  refine ⟨113924243063017101102967223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75949495375344734068644815 113924243063017101102967223)
  ·
    refine ⟨170886364594525651654450835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113924243063017101102967223 170886364594525651654450835)
    ·
      refine ⟨256329546891788477481676253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170886364594525651654450835 256329546891788477481676253)
      ·
        refine ⟨96123580084420679055628595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256329546891788477481676253 96123580084420679055628595)
        ·
          refine ⟨144185370126631018583442893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96123580084420679055628595 144185370126631018583442893)
          ·
            refine ⟨54069513797486631968791085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144185370126631018583442893 54069513797486631968791085)
            ·
              refine ⟨20276067674057486988296657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54069513797486631968791085 20276067674057486988296657)
              ·
                refine ⟨15207050755543115241222493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20276067674057486988296657 15207050755543115241222493)
                ·
                  refine ⟨5702644033328668215458435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15207050755543115241222493 5702644033328668215458435)
                  ·
                    refine ⟨8553966049993002323187653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5702644033328668215458435 8553966049993002323187653)
                    ·
                      refine ⟨1603868634373687935597685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8553966049993002323187653 1603868634373687935597685)
                      ·
                        rfl

theorem cell23_3123523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_3123523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123523 prefixEnd_3123523 := by exact prefixLift 3123523
  have htrace : WordTrace (prefixWord ++ tailWord_3123523) baseStart_3123523 baseEnd_3123523 := by
    simpa [prefixWord, tailWord_3123523, baseEnd_3123523] using wordTrace_append hprefix tailTrace_3123523
  have hstable : (prefixWord ++ tailWord_3123523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123523).length < 2 ^ (prefixWord ++ tailWord_3123523).sum := by decide
  have hdescent : baseEnd_3123523 < baseStart_3123523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123540 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_3123540 : Nat := 118140960795 + 3123540 * 2 ^ 59
def prefixEnd_3123540 : Nat := 4983230072969 + 3 ^ 40 * 3123540 * 2
def baseEnd_3123540 : Nat := 1603877363544814369085107

theorem tailTrace_3123540 : CollatzResearch.WordTrace tailWord_3123540 prefixEnd_3123540 1603877363544814369085107 := by
  unfold tailWord_3123540
  simp only [CollatzResearch.WordTrace]
  refine ⟨56962431551977756503168037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75949908735970342004224049 56962431551977756503168037)
  ·
    refine ⟨10680455915995829344344007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56962431551977756503168037 10680455915995829344344007)
    ·
      refine ⟨16020683873993744016516011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10680455915995829344344007 16020683873993744016516011)
      ·
        refine ⟨24031025810990616024774017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16020683873993744016516011 24031025810990616024774017)
        ·
          refine ⟨18023269358242962018580513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24031025810990616024774017 18023269358242962018580513)
          ·
            refine ⟨13517452018682221513935385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18023269358242962018580513 13517452018682221513935385)
            ·
              refine ⟨10138089014011666135451539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13517452018682221513935385 10138089014011666135451539)
              ·
                refine ⟨15207133521017499203177309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10138089014011666135451539 15207133521017499203177309)
                ·
                  refine ⟨5702675070381562201191491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15207133521017499203177309 5702675070381562201191491)
                  ·
                    refine ⟨8554012605572343301787237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5702675070381562201191491 8554012605572343301787237)
                    ·
                      refine ⟨1603877363544814369085107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8554012605572343301787237 1603877363544814369085107)
                      ·
                        rfl

theorem cell23_3123540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_3123540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123540 prefixEnd_3123540 := by exact prefixLift 3123540
  have htrace : WordTrace (prefixWord ++ tailWord_3123540) baseStart_3123540 baseEnd_3123540 := by
    simpa [prefixWord, tailWord_3123540, baseEnd_3123540] using wordTrace_append hprefix tailTrace_3123540
  have hstable : (prefixWord ++ tailWord_3123540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123540).length < 2 ^ (prefixWord ++ tailWord_3123540).sum := by decide
  have hdescent : baseEnd_3123540 < baseStart_3123540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123554 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3123554 : Nat := 118140960795 + 3123554 * 2 ^ 59
def prefixEnd_3123554 : Nat := 4983230072969 + 3 ^ 40 * 3123554 * 2
def baseEnd_3123554 : Nat := 534628184091325771436681

theorem tailTrace_3123554 : CollatzResearch.WordTrace tailWord_3123554 prefixEnd_3123554 534628184091325771436681 := by
  unfold tailWord_3123554
  simp only [CollatzResearch.WordTrace]
  refine ⟨28481343431476198349336429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75950249150603195598230477 28481343431476198349336429)
  ·
    refine ⟨10680503786803574381001161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28481343431476198349336429 10680503786803574381001161)
    ·
      refine ⟨8010377840102680785750871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10680503786803574381001161 8010377840102680785750871)
      ·
        refine ⟨12015566760154021178626307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8010377840102680785750871 12015566760154021178626307)
        ·
          refine ⟨18023350140231031767939461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12015566760154021178626307 18023350140231031767939461)
          ·
            refine ⟨3379378151293318456488649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18023350140231031767939461 3379378151293318456488649)
            ·
              refine ⟨2534533613469988842366487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3379378151293318456488649 2534533613469988842366487)
              ·
                refine ⟨3801800420204983263549731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2534533613469988842366487 3801800420204983263549731)
                ·
                  refine ⟨5702700630307474895324597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801800420204983263549731 5702700630307474895324597)
                  ·
                    refine ⟨534628184091325771436681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5702700630307474895324597 534628184091325771436681)
                    ·
                      rfl

theorem cell23_3123554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3123554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123554 prefixEnd_3123554 := by exact prefixLift 3123554
  have htrace : WordTrace (prefixWord ++ tailWord_3123554) baseStart_3123554 baseEnd_3123554 := by
    simpa [prefixWord, tailWord_3123554, baseEnd_3123554] using wordTrace_append hprefix tailTrace_3123554
  have hstable : (prefixWord ++ tailWord_3123554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123554).length < 2 ^ (prefixWord ++ tailWord_3123554).sum := by decide
  have hdescent : baseEnd_3123554 < baseStart_3123554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123557 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 1, 1, 4]
def baseStart_3123557 : Nat := 118140960795 + 3123557 * 2 ^ 59
def prefixEnd_3123557 : Nat := 4983230072969 + 3 ^ 40 * 3123557 * 2
def baseEnd_3123557 : Nat := 1603886092715940802572529

theorem tailTrace_3123557 : CollatzResearch.WordTrace tailWord_3123557 prefixEnd_3123557 1603886092715940802572529 := by
  unfold tailWord_3123557
  simp only [CollatzResearch.WordTrace]
  refine ⟨113925483144893924909704925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75950322096595949939803283 113925483144893924909704925)
  ·
    refine ⟨42722056179335221841139347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113925483144893924909704925 42722056179335221841139347)
    ·
      refine ⟨64083084269002832761709021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42722056179335221841139347 64083084269002832761709021)
      ·
        refine ⟨24031156600876062285640883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64083084269002832761709021 24031156600876062285640883)
        ·
          refine ⟨36046734901314093428461325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24031156600876062285640883 36046734901314093428461325)
          ·
            refine ⟨13517525587992785035672997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36046734901314093428461325 13517525587992785035672997)
            ·
              refine ⟨2534536047748647194188687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13517525587992785035672997 2534536047748647194188687)
              ·
                refine ⟨3801804071622970791283031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2534536047748647194188687 3801804071622970791283031)
                ·
                  refine ⟨5702706107434456186924547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801804071622970791283031 5702706107434456186924547)
                  ·
                    refine ⟨8554059161151684280386821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5702706107434456186924547 8554059161151684280386821)
                    ·
                      refine ⟨1603886092715940802572529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8554059161151684280386821 1603886092715940802572529)
                      ·
                        rfl

theorem cell23_3123557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_3123557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123557 prefixEnd_3123557 := by exact prefixLift 3123557
  have htrace : WordTrace (prefixWord ++ tailWord_3123557) baseStart_3123557 baseEnd_3123557 := by
    simpa [prefixWord, tailWord_3123557, baseEnd_3123557] using wordTrace_append hprefix tailTrace_3123557
  have hstable : (prefixWord ++ tailWord_3123557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123557).length < 2 ^ (prefixWord ++ tailWord_3123557).sum := by decide
  have hdescent : baseEnd_3123557 < baseStart_3123557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123587 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 4]
def baseStart_3123587 : Nat := 118140960795 + 3123587 * 2 ^ 59
def prefixEnd_3123587 : Nat := 4983230072969 + 3 ^ 40 * 3123587 * 2
def baseEnd_3123587 : Nat := 1603901497135575685197391

theorem tailTrace_3123587 : CollatzResearch.WordTrace tailWord_3123587 prefixEnd_3123587 1603901497135575685197391 := by
  unfold tailWord_3123587
  simp only [CollatzResearch.WordTrace]
  refine ⟨113926577334785240033297015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75951051556523493355531343 113926577334785240033297015)
  ·
    refine ⟨170889866002177860049945523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113926577334785240033297015 170889866002177860049945523)
    ·
      refine ⟨256334799003266790074918285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170889866002177860049945523 256334799003266790074918285)
      ·
        refine ⟨96125549626225046278094357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256334799003266790074918285 96125549626225046278094357)
        ·
          refine ⟨4505885138729299044285673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96125549626225046278094357 4505885138729299044285673)
          ·
            refine ⟨3379413854046974283214255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4505885138729299044285673 3379413854046974283214255)
            ·
              refine ⟨5069120781070461424821383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379413854046974283214255 5069120781070461424821383)
              ·
                refine ⟨7603681171605692137232075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5069120781070461424821383 7603681171605692137232075)
                ·
                  refine ⟨11405521757408538205848113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7603681171605692137232075 11405521757408538205848113)
                  ·
                    refine ⟨8554141318056403654386085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11405521757408538205848113 8554141318056403654386085)
                    ·
                      refine ⟨1603901497135575685197391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8554141318056403654386085 1603901497135575685197391)
                      ·
                        rfl

theorem cell23_3123587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_3123587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123587 prefixEnd_3123587 := by exact prefixLift 3123587
  have htrace : WordTrace (prefixWord ++ tailWord_3123587) baseStart_3123587 baseEnd_3123587 := by
    simpa [prefixWord, tailWord_3123587, baseEnd_3123587] using wordTrace_append hprefix tailTrace_3123587
  have hstable : (prefixWord ++ tailWord_3123587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123587).length < 2 ^ (prefixWord ++ tailWord_3123587).sum := by decide
  have hdescent : baseEnd_3123587 < baseStart_3123587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123608 : List Nat := [2, 1, 2, 5, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3123608 : Nat := 118140960795 + 3123608 * 2 ^ 59
def prefixEnd_3123608 : Nat := 4983230072969 + 3 ^ 40 * 3123608 * 2
def baseEnd_3123608 : Nat := 1603912280229320103034795

theorem tailTrace_3123608 : CollatzResearch.WordTrace tailWord_3123608 prefixEnd_3123608 1603912280229320103034795 := by
  unfold tailWord_3123608
  simp only [CollatzResearch.WordTrace]
  refine ⟨56963671633854580309905739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75951562178472773746540985 56963671633854580309905739)
  ·
    refine ⟨85445507450781870464858609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56963671633854580309905739 85445507450781870464858609)
    ·
      refine ⟨64084130588086402848643957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85445507450781870464858609 64084130588086402848643957)
      ·
        refine ⟨6007887242633100267060371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64084130588086402848643957 6007887242633100267060371)
        ·
          refine ⟨9011830863949650400590557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6007887242633100267060371 9011830863949650400590557)
          ·
            refine ⟨3379436573981118900221459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9011830863949650400590557 3379436573981118900221459)
            ·
              refine ⟨5069154860971678350332189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379436573981118900221459 5069154860971678350332189)
              ·
                refine ⟨1900933072864379381374571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5069154860971678350332189 1900933072864379381374571)
                ·
                  refine ⟨2851399609296569072061857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900933072864379381374571 2851399609296569072061857)
                  ·
                    refine ⟨2138549706972426804046393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2851399609296569072061857 2138549706972426804046393)
                    ·
                      refine ⟨1603912280229320103034795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138549706972426804046393 1603912280229320103034795)
                      ·
                        rfl

theorem cell23_3123608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3123608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123608 prefixEnd_3123608 := by exact prefixLift 3123608
  have htrace : WordTrace (prefixWord ++ tailWord_3123608) baseStart_3123608 baseEnd_3123608 := by
    simpa [prefixWord, tailWord_3123608, baseEnd_3123608] using wordTrace_append hprefix tailTrace_3123608
  have hstable : (prefixWord ++ tailWord_3123608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123608).length < 2 ^ (prefixWord ++ tailWord_3123608).sum := by decide
  have hdescent : baseEnd_3123608 < baseStart_3123608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123624 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3123624 : Nat := 118140960795 + 3123624 * 2 ^ 59
def prefixEnd_3123624 : Nat := 4983230072969 + 3 ^ 40 * 3123624 * 2
def baseEnd_3123624 : Nat := 1603920495919792040434721

theorem tailTrace_3123624 : CollatzResearch.WordTrace tailWord_3123624 prefixEnd_3123624 1603920495919792040434721 := by
  unfold tailWord_3123624
  simp only [CollatzResearch.WordTrace]
  refine ⟨56963963417825597676196963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75951951223767463568262617 56963963417825597676196963)
  ·
    refine ⟨85445945126738396514295445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56963963417825597676196963 85445945126738396514295445)
    ·
      refine ⟨4005278677815862336607599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85445945126738396514295445 4005278677815862336607599)
      ·
        refine ⟨6007918016723793504911399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005278677815862336607599 6007918016723793504911399)
        ·
          refine ⟨9011877025085690257367099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6007918016723793504911399 9011877025085690257367099)
          ·
            refine ⟨13517815537628535386050649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9011877025085690257367099 13517815537628535386050649)
            ·
              refine ⟨10138361653221401539537987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13517815537628535386050649 10138361653221401539537987)
              ·
                refine ⟨15207542479832102309306981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10138361653221401539537987 15207542479832102309306981)
                ·
                  refine ⟨2851414214968519182995059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15207542479832102309306981 2851414214968519182995059)
                  ·
                    refine ⟨4277121322452778774492589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2851414214968519182995059 4277121322452778774492589)
                    ·
                      refine ⟨1603920495919792040434721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4277121322452778774492589 1603920495919792040434721)
                      ·
                        rfl

theorem cell23_3123624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3123624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123624 prefixEnd_3123624 := by exact prefixLift 3123624
  have htrace : WordTrace (prefixWord ++ tailWord_3123624) baseStart_3123624 baseEnd_3123624 := by
    simpa [prefixWord, tailWord_3123624, baseEnd_3123624] using wordTrace_append hprefix tailTrace_3123624
  have hstable : (prefixWord ++ tailWord_3123624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123624).length < 2 ^ (prefixWord ++ tailWord_3123624).sum := by decide
  have hdescent : baseEnd_3123624 < baseStart_3123624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123641 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 2, 1, 3]
def baseStart_3123641 : Nat := 118140960795 + 3123641 * 2 ^ 59
def prefixEnd_3123641 : Nat := 4983230072969 + 3 ^ 40 * 3123641 * 2
def baseEnd_3123641 : Nat := 1603929225090918473922143

theorem tailTrace_3123641 : CollatzResearch.WordTrace tailWord_3123641 prefixEnd_3123641 1603929225090918473922143 := by
  unfold tailWord_3123641
  simp only [CollatzResearch.WordTrace]
  refine ⟨113928546876589607255762777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75952364584393071503841851 113928546876589607255762777)
  ·
    refine ⟨85446410157442205441822083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113928546876589607255762777 85446410157442205441822083)
    ·
      refine ⟨128169615236163308162733125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85446410157442205441822083 128169615236163308162733125)
      ·
        refine ⟨24031802856780620280512461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128169615236163308162733125 24031802856780620280512461)
        ·
          refine ⟨9011926071292732605192173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24031802856780620280512461 9011926071292732605192173)
          ·
            refine ⟨3379472276734774726947065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9011926071292732605192173 3379472276734774726947065)
            ·
              refine ⟨2534604207551081045210299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3379472276734774726947065 2534604207551081045210299)
              ·
                refine ⟨3801906311326621567815449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2534604207551081045210299 3801906311326621567815449)
                ·
                  refine ⟨2851429733494966175861587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3801906311326621567815449 2851429733494966175861587)
                  ·
                    refine ⟨4277144600242449263792381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2851429733494966175861587 4277144600242449263792381)
                    ·
                      refine ⟨1603929225090918473922143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4277144600242449263792381 1603929225090918473922143)
                      ·
                        rfl

theorem cell23_3123641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_3123641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123641 prefixEnd_3123641 := by exact prefixLift 3123641
  have htrace : WordTrace (prefixWord ++ tailWord_3123641) baseStart_3123641 baseEnd_3123641 := by
    simpa [prefixWord, tailWord_3123641, baseEnd_3123641] using wordTrace_append hprefix tailTrace_3123641
  have hstable : (prefixWord ++ tailWord_3123641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123641).length < 2 ^ (prefixWord ++ tailWord_3123641).sum := by decide
  have hdescent : baseEnd_3123641 < baseStart_3123641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123680 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 3]
def baseStart_3123680 : Nat := 118140960795 + 3123680 * 2 ^ 59
def prefixEnd_3123680 : Nat := 4983230072969 + 3 ^ 40 * 3123680 * 2
def baseEnd_3123680 : Nat := 1603949250836443821334463

theorem tailTrace_3123680 : CollatzResearch.WordTrace tailWord_3123680 prefixEnd_3123680 1603949250836443821334463 := by
  unfold tailWord_3123680
  simp only [CollatzResearch.WordTrace]
  refine ⟨56964984661724158458216247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75953312882298877944288329 56964984661724158458216247)
  ·
    refine ⟨85447476992586237687324371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56964984661724158458216247 85447476992586237687324371)
    ·
      refine ⟨128171215488879356530986557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85447476992586237687324371 128171215488879356530986557)
      ·
        refine ⟨48064205808329758699119959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128171215488879356530986557 48064205808329758699119959)
        ·
          refine ⟨72096308712494638048679939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48064205808329758699119959 72096308712494638048679939)
          ·
            refine ⟨108144463068741957073019909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72096308712494638048679939 108144463068741957073019909)
            ·
              refine ⟨20277086825389116951191233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108144463068741957073019909 20277086825389116951191233)
              ·
                refine ⟨15207815119041837713393425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20277086825389116951191233 15207815119041837713393425)
                ·
                  refine ⟨11405861339281378285045069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15207815119041837713393425 11405861339281378285045069)
                  ·
                    refine ⟨4277198002230516856891901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11405861339281378285045069 4277198002230516856891901)
                    ·
                      refine ⟨1603949250836443821334463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4277198002230516856891901 1603949250836443821334463)
                      ·
                        rfl

theorem cell23_3123680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_3123680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123680 prefixEnd_3123680 := by exact prefixLift 3123680
  have htrace : WordTrace (prefixWord ++ tailWord_3123680) baseStart_3123680 baseEnd_3123680 := by
    simpa [prefixWord, tailWord_3123680, baseEnd_3123680] using wordTrace_append hprefix tailTrace_3123680
  have hstable : (prefixWord ++ tailWord_3123680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123680).length < 2 ^ (prefixWord ++ tailWord_3123680).sum := by decide
  have hdescent : baseEnd_3123680 < baseStart_3123680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123687 : List Nat := [1, 1, 5, 2, 1, 1, 3, 4, 5]
def baseStart_3123687 : Nat := 118140960795 + 3123687 * 2 ^ 59
def prefixEnd_3123687 : Nat := 4983230072969 + 3 ^ 40 * 3123687 * 2
def baseEnd_3123687 : Nat := 178216982800113921549659

theorem tailTrace_3123687 : CollatzResearch.WordTrace tailWord_3123687 prefixEnd_3123687 178216982800113921549659 := by
  unfold tailWord_3123687
  simp only [CollatzResearch.WordTrace]
  refine ⟨113930224634422957111937315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75953483089615304741291543 113930224634422957111937315)
  ·
    refine ⟨170895336951634435667905973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113930224634422957111937315 170895336951634435667905973)
    ·
      refine ⟨16021437839215728343866185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170895336951634435667905973 16021437839215728343866185)
      ·
        refine ⟨12016078379411796257899639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16021437839215728343866185 12016078379411796257899639)
        ·
          refine ⟨18024117569117694386849459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12016078379411796257899639 18024117569117694386849459)
          ·
            refine ⟨27036176353676541580274189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18024117569117694386849459 27036176353676541580274189)
            ·
              refine ⟨10138566132628703092602821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27036176353676541580274189 10138566132628703092602821)
              ·
                refine ⟨1900981149867881829863029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10138566132628703092602821 1900981149867881829863029)
                ·
                  refine ⟨178216982800113921549659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1900981149867881829863029 178216982800113921549659)
                  ·
                    rfl

theorem cell23_3123687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 5].length) (baseStart_3123687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123687 prefixEnd_3123687 := by exact prefixLift 3123687
  have htrace : WordTrace (prefixWord ++ tailWord_3123687) baseStart_3123687 baseEnd_3123687 := by
    simpa [prefixWord, tailWord_3123687, baseEnd_3123687] using wordTrace_append hprefix tailTrace_3123687
  have hstable : (prefixWord ++ tailWord_3123687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123687).length < 2 ^ (prefixWord ++ tailWord_3123687).sum := by decide
  have hdescent : baseEnd_3123687 < baseStart_3123687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123747 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 3, 4]
def baseStart_3123747 : Nat := 118140960795 + 3123747 * 2 ^ 59
def prefixEnd_3123747 : Nat := 4983230072969 + 3 ^ 40 * 3123747 * 2
def baseEnd_3123747 : Nat := 534661218013431686398885

theorem tailTrace_3123747 : CollatzResearch.WordTrace tailWord_3123747 prefixEnd_3123747 534661218013431686398885 := by
  unfold tailWord_3123747
  simp only [CollatzResearch.WordTrace]
  refine ⟨113932413014205587359121495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75954942009470391572747663 113932413014205587359121495)
  ·
    refine ⟨170898619521308381038682243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113932413014205587359121495 170898619521308381038682243)
    ·
      refine ⟨256347929281962571558023365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170898619521308381038682243 256347929281962571558023365)
      ·
        refine ⟨48065236740367982167129381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256347929281962571558023365 48065236740367982167129381)
        ·
          refine ⟨9012231888818996656336759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48065236740367982167129381 9012231888818996656336759)
          ·
            refine ⟨13518347833228494984505139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9012231888818996656336759 13518347833228494984505139)
            ·
              refine ⟨20277521749842742476757709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13518347833228494984505139 20277521749842742476757709)
              ·
                refine ⟨7604070656191028428784141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20277521749842742476757709 7604070656191028428784141)
                ·
                  refine ⟨2851526496071635660794053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7604070656191028428784141 2851526496071635660794053)
                  ·
                    refine ⟨534661218013431686398885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2851526496071635660794053 534661218013431686398885)
                    ·
                      rfl

theorem cell23_3123747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 4].length) (baseStart_3123747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123747 prefixEnd_3123747 := by exact prefixLift 3123747
  have htrace : WordTrace (prefixWord ++ tailWord_3123747) baseStart_3123747 baseEnd_3123747 := by
    simpa [prefixWord, tailWord_3123747, baseEnd_3123747] using wordTrace_append hprefix tailTrace_3123747
  have hstable : (prefixWord ++ tailWord_3123747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123747).length < 2 ^ (prefixWord ++ tailWord_3123747).sum := by decide
  have hdescent : baseEnd_3123747 < baseStart_3123747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123754 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_3123754 : Nat := 118140960795 + 3123754 * 2 ^ 59
def prefixEnd_3123754 : Nat := 4983230072969 + 3 ^ 40 * 3123754 * 2
def baseEnd_3123754 : Nat := 1603987248404876531809123

theorem tailTrace_3123754 : CollatzResearch.WordTrace tailWord_3123754 prefixEnd_3123754 1603987248404876531809123 := by
  unfold tailWord_3123754
  simp only [CollatzResearch.WordTrace]
  refine ⟨28483167081295056888656579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75955112216786818369750877 28483167081295056888656579)
  ·
    refine ⟨42724750621942585332984869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28483167081295056888656579 42724750621942585332984869)
    ·
      refine ⟨8010890741614234749934663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42724750621942585332984869 8010890741614234749934663)
      ·
        refine ⟨12016336112421352124901995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8010890741614234749934663 12016336112421352124901995)
        ·
          refine ⟨18024504168632028187352993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12016336112421352124901995 18024504168632028187352993)
          ·
            refine ⟨13518378126474021140514745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18024504168632028187352993 13518378126474021140514745)
            ·
              refine ⟨10138783594855515855386059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13518378126474021140514745 10138783594855515855386059)
              ·
                refine ⟨15208175392283273783079089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10138783594855515855386059 15208175392283273783079089)
                ·
                  refine ⟨11406131544212455337309317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15208175392283273783079089 11406131544212455337309317)
                  ·
                    refine ⟨2138649664539835375745497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11406131544212455337309317 2138649664539835375745497)
                    ·
                      refine ⟨1603987248404876531809123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138649664539835375745497 1603987248404876531809123)
                      ·
                        rfl

theorem cell23_3123754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_3123754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123754 prefixEnd_3123754 := by exact prefixLift 3123754
  have htrace : WordTrace (prefixWord ++ tailWord_3123754) baseStart_3123754 baseEnd_3123754 := by
    simpa [prefixWord, tailWord_3123754, baseEnd_3123754] using wordTrace_append hprefix tailTrace_3123754
  have hstable : (prefixWord ++ tailWord_3123754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123754).length < 2 ^ (prefixWord ++ tailWord_3123754).sum := by decide
  have hdescent : baseEnd_3123754 < baseStart_3123754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123760 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 6]
def baseStart_3123760 : Nat := 118140960795 + 3123760 * 2 ^ 59
def prefixEnd_3123760 : Nat := 4983230072969 + 3 ^ 40 * 3123760 * 2
def baseEnd_3123760 : Nat := 178221147698755945370455

theorem tailTrace_3123760 : CollatzResearch.WordTrace tailWord_3123760 prefixEnd_3123760 178221147698755945370455 := by
  unfold tailWord_3123760
  simp only [CollatzResearch.WordTrace]
  refine ⟨56966443581579245289672367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75955258108772327052896489 56966443581579245289672367)
  ·
    refine ⟨85449665372368867934508551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56966443581579245289672367 85449665372368867934508551)
    ·
      refine ⟨128174498058553301901762827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85449665372368867934508551 128174498058553301901762827)
      ·
        refine ⟨192261747087829952852644241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128174498058553301901762827 192261747087829952852644241)
        ·
          refine ⟨144196310315872464639483181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192261747087829952852644241 144196310315872464639483181)
          ·
            refine ⟨54073616368452174239806193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144196310315872464639483181 54073616368452174239806193)
            ·
              refine ⟨40555212276339130679854645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54073616368452174239806193 40555212276339130679854645)
              ·
                refine ⟨3802051150906793501236373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40555212276339130679854645 3802051150906793501236373)
                ·
                  refine ⟨178221147698755945370455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3802051150906793501236373 178221147698755945370455)
                  ·
                    rfl

theorem cell23_3123760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 6].length) (baseStart_3123760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123760 prefixEnd_3123760 := by exact prefixLift 3123760
  have htrace : WordTrace (prefixWord ++ tailWord_3123760) baseStart_3123760 baseEnd_3123760 := by
    simpa [prefixWord, tailWord_3123760, baseEnd_3123760] using wordTrace_append hprefix tailTrace_3123760
  have hstable : (prefixWord ++ tailWord_3123760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123760).length < 2 ^ (prefixWord ++ tailWord_3123760).sum := by decide
  have hdescent : baseEnd_3123760 < baseStart_3123760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123781 : List Nat := [1, 3, 1, 1, 1, 7, 1, 3, 1, 4]
def baseStart_3123781 : Nat := 118140960795 + 3123781 * 2 ^ 59
def prefixEnd_3123781 : Nat := 4983230072969 + 3 ^ 40 * 3123781 * 2
def baseEnd_3123781 : Nat := 534667037460849308723833

theorem tailTrace_3123781 : CollatzResearch.WordTrace tailWord_3123781 prefixEnd_3123781 534667037460849308723833 := by
  unfold tailWord_3123781
  simp only [CollatzResearch.WordTrace]
  refine ⟨113933653096082411165859197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75955768730721607443906131 113933653096082411165859197)
  ·
    refine ⟨42725119911030904187197199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113933653096082411165859197 42725119911030904187197199)
    ·
      refine ⟨64087679866546356280795799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42725119911030904187197199 64087679866546356280795799)
      ·
        refine ⟨96131519799819534421193699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64087679866546356280795799 96131519799819534421193699)
        ·
          refine ⟨144197279699729301631790549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96131519799819534421193699 144197279699729301631790549)
          ·
            refine ⟨3379623742962405506995091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 144197279699729301631790549 3379623742962405506995091)
            ·
              refine ⟨5069435614443608260492637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379623742962405506995091 5069435614443608260492637)
              ·
                refine ⟨1901038355416353097684739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5069435614443608260492637 1901038355416353097684739)
                ·
                  refine ⟨2851557533124529646527109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901038355416353097684739 2851557533124529646527109)
                  ·
                    refine ⟨534667037460849308723833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2851557533124529646527109 534667037460849308723833)
                    ·
                      rfl

theorem cell23_3123781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_3123781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123781 prefixEnd_3123781 := by exact prefixLift 3123781
  have htrace : WordTrace (prefixWord ++ tailWord_3123781) baseStart_3123781 baseEnd_3123781 := by
    simpa [prefixWord, tailWord_3123781, baseEnd_3123781] using wordTrace_append hprefix tailTrace_3123781
  have hstable : (prefixWord ++ tailWord_3123781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123781).length < 2 ^ (prefixWord ++ tailWord_3123781).sum := by decide
  have hdescent : baseEnd_3123781 < baseStart_3123781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123787 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 5, 1, 3]
def baseStart_3123787 : Nat := 118140960795 + 3123787 * 2 ^ 59
def prefixEnd_3123787 : Nat := 4983230072969 + 3 ^ 40 * 3123787 * 2
def baseEnd_3123787 : Nat := 1604004193266474902696471

theorem tailTrace_3123787 : CollatzResearch.WordTrace tailWord_3123787 prefixEnd_3123787 1604004193266474902696471 := by
  unfold tailWord_3123787
  simp only [CollatzResearch.WordTrace]
  refine ⟨113933871934060674190577615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75955914622707116127051743 113933871934060674190577615)
  ·
    refine ⟨170900807901091011285866423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113933871934060674190577615 170900807901091011285866423)
    ·
      refine ⟨256351211851636516928799635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170900807901091011285866423 256351211851636516928799635)
      ·
        refine ⟨384526817777454775393199453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256351211851636516928799635 384526817777454775393199453)
        ·
          refine ⟨144197556666545540772449795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384526817777454775393199453 144197556666545540772449795)
          ·
            refine ⟨216296334999818311158674693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144197556666545540772449795 216296334999818311158674693)
            ·
              refine ⟨40555562812465933342251505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216296334999818311158674693 40555562812465933342251505)
              ·
                refine ⟨30416672109349450006688629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40555562812465933342251505 30416672109349450006688629)
                ·
                  refine ⟨2851563010251510938127059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30416672109349450006688629 2851563010251510938127059)
                  ·
                    refine ⟨4277344515377266407190589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2851563010251510938127059 4277344515377266407190589)
                    ·
                      refine ⟨1604004193266474902696471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4277344515377266407190589 1604004193266474902696471)
                      ·
                        rfl

theorem cell23_3123787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 1, 3].length) (baseStart_3123787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123787 prefixEnd_3123787 := by exact prefixLift 3123787
  have htrace : WordTrace (prefixWord ++ tailWord_3123787) baseStart_3123787 baseEnd_3123787 := by
    simpa [prefixWord, tailWord_3123787, baseEnd_3123787] using wordTrace_append hprefix tailTrace_3123787
  have hstable : (prefixWord ++ tailWord_3123787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123787).length < 2 ^ (prefixWord ++ tailWord_3123787).sum := by decide
  have hdescent : baseEnd_3123787 < baseStart_3123787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123827 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 4]
def baseStart_3123827 : Nat := 118140960795 + 3123827 * 2 ^ 59
def prefixEnd_3123827 : Nat := 4983230072969 + 3 ^ 40 * 3123827 * 2
def baseEnd_3123827 : Nat := 1604024732492654746196287

theorem tailTrace_3123827 : CollatzResearch.WordTrace tailWord_3123827 prefixEnd_3123827 1604024732492654746196287 := by
  unfold tailWord_3123827
  simp only [CollatzResearch.WordTrace]
  refine ⟨113935330853915761022033735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75956887235943840681355823 113935330853915761022033735)
  ·
    refine ⟨170902996280873641533050603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113935330853915761022033735 170902996280873641533050603)
    ·
      refine ⟨256354494421310462299575905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170902996280873641533050603 256354494421310462299575905)
      ·
        refine ⟨192265870815982846724681929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256354494421310462299575905 192265870815982846724681929)
        ·
          refine ⟨144199403111987135043511447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192265870815982846724681929 144199403111987135043511447)
          ·
            refine ⟨216299104667980702565267171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144199403111987135043511447 216299104667980702565267171)
            ·
              refine ⟨324448657001971053847900757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216299104667980702565267171 324448657001971053847900757)
              ·
                refine ⟨3802132699241848287280087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 324448657001971053847900757 3802132699241848287280087)
                ·
                  refine ⟨5703199048862772430920131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802132699241848287280087 5703199048862772430920131)
                  ·
                    refine ⟨8554798573294158646380197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5703199048862772430920131 8554798573294158646380197)
                    ·
                      refine ⟨1604024732492654746196287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8554798573294158646380197 1604024732492654746196287)
                      ·
                        rfl

theorem cell23_3123827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 4].length) (baseStart_3123827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123827 prefixEnd_3123827 := by exact prefixLift 3123827
  have htrace : WordTrace (prefixWord ++ tailWord_3123827) baseStart_3123827 baseEnd_3123827 := by
    simpa [prefixWord, tailWord_3123827, baseEnd_3123827] using wordTrace_append hprefix tailTrace_3123827
  have hstable : (prefixWord ++ tailWord_3123827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123827).length < 2 ^ (prefixWord ++ tailWord_3123827).sum := by decide
  have hdescent : baseEnd_3123827 < baseStart_3123827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123850 : List Nat := [3, 1, 2, 3, 14]
def baseStart_3123850 : Nat := 118140960795 + 3123850 * 2 ^ 59
def prefixEnd_3123850 : Nat := 4983230072969 + 3 ^ 40 * 3123850 * 2
def baseEnd_3123850 : Nat := 2200324475374085262289

theorem tailTrace_3123850 : CollatzResearch.WordTrace tailWord_3123850 prefixEnd_3123850 2200324475374085262289 := by
  unfold tailWord_3123850
  simp only [CollatzResearch.WordTrace]
  refine ⟨28484042433208108987530251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75957446488554957300080669 28484042433208108987530251)
  ·
    refine ⟨42726063649812163481295377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28484042433208108987530251 42726063649812163481295377)
    ·
      refine ⟨32044547737359122610971533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42726063649812163481295377 32044547737359122610971533)
      ·
        refine ⟨12016705401509670979114325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32044547737359122610971533 12016705401509670979114325)
        ·
          refine ⟨2200324475374085262289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 12016705401509670979114325 2200324475374085262289)
          ·
            rfl

theorem cell23_3123850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 14].length) (baseStart_3123850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123850 prefixEnd_3123850 := by exact prefixLift 3123850
  have htrace : WordTrace (prefixWord ++ tailWord_3123850) baseStart_3123850 baseEnd_3123850 := by
    simpa [prefixWord, tailWord_3123850, baseEnd_3123850] using wordTrace_append hprefix tailTrace_3123850
  have hstable : (prefixWord ++ tailWord_3123850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123850).length < 2 ^ (prefixWord ++ tailWord_3123850).sum := by decide
  have hdescent : baseEnd_3123850 < baseStart_3123850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123882 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3123882 : Nat := 118140960795 + 3123882 * 2 ^ 59
def prefixEnd_3123882 : Nat := 4983230072969 + 3 ^ 40 * 3123882 * 2
def baseEnd_3123882 : Nat := 1604052973928652031008535

theorem tailTrace_3123882 : CollatzResearch.WordTrace tailWord_3123882 prefixEnd_3123882 1604052973928652031008535 := by
  unfold tailWord_3123882
  simp only [CollatzResearch.WordTrace]
  refine ⟨28484334217179126353821475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75958224579144336943523933 28484334217179126353821475)
  ·
    refine ⟨42726501325768689530732213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28484334217179126353821475 42726501325768689530732213)
    ·
      refine ⟨4005609499290814643506145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42726501325768689530732213 4005609499290814643506145)
      ·
        refine ⟨3004207124468110982629609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4005609499290814643506145 3004207124468110982629609)
        ·
          refine ⟨2253155343351083236972207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3004207124468110982629609 2253155343351083236972207)
          ·
            refine ⟨3379733015026624855458311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253155343351083236972207 3379733015026624855458311)
            ·
              refine ⟨5069599522539937283187467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379733015026624855458311 5069599522539937283187467)
              ·
                refine ⟨7604399283809905924781201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5069599522539937283187467 7604399283809905924781201)
                ·
                  refine ⟨5703299462857429443585901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7604399283809905924781201 5703299462857429443585901)
                  ·
                    refine ⟨2138737298571536041344713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5703299462857429443585901 2138737298571536041344713)
                    ·
                      refine ⟨1604052973928652031008535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138737298571536041344713 1604052973928652031008535)
                      ·
                        rfl

theorem cell23_3123882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3123882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123882 prefixEnd_3123882 := by exact prefixLift 3123882
  have htrace : WordTrace (prefixWord ++ tailWord_3123882) baseStart_3123882 baseEnd_3123882 := by
    simpa [prefixWord, tailWord_3123882, baseEnd_3123882] using wordTrace_append hprefix tailTrace_3123882
  have hstable : (prefixWord ++ tailWord_3123882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123882).length < 2 ^ (prefixWord ++ tailWord_3123882).sum := by decide
  have hdescent : baseEnd_3123882 < baseStart_3123882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123895 : List Nat := [1, 1, 3, 1, 6, 1, 2, 3, 1, 2, 2]
def baseStart_3123895 : Nat := 118140960795 + 3123895 * 2 ^ 59
def prefixEnd_3123895 : Nat := 4983230072969 + 3 ^ 40 * 3123895 * 2
def baseEnd_3123895 : Nat := 1604059649177160480145975

theorem tailTrace_3123895 : CollatzResearch.WordTrace tailWord_3123895 prefixEnd_3123895 1604059649177160480145975 := by
  unfold tailWord_3123895
  simp only [CollatzResearch.WordTrace]
  refine ⟨113937811017669408635509139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75958540678446272423672759 113937811017669408635509139)
  ·
    refine ⟨170906716526504112953263709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113937811017669408635509139 170906716526504112953263709)
    ·
      refine ⟨64090018697439042357473891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170906716526504112953263709 64090018697439042357473891)
      ·
        refine ⟨96135028046158563536210837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64090018697439042357473891 96135028046158563536210837)
        ·
          refine ⟨4506329439663682665759883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96135028046158563536210837 4506329439663682665759883)
          ·
            refine ⟨6759494159495523998639825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506329439663682665759883 6759494159495523998639825)
            ·
              refine ⟨5069620619621642998979869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6759494159495523998639825 5069620619621642998979869)
              ·
                refine ⟨1901107732358116124617451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5069620619621642998979869 1901107732358116124617451)
                ·
                  refine ⟨2851661598537174186926177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901107732358116124617451 2851661598537174186926177)
                  ·
                    refine ⟨2138746198902880640194633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2851661598537174186926177 2138746198902880640194633)
                    ·
                      refine ⟨1604059649177160480145975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138746198902880640194633 1604059649177160480145975)
                      ·
                        rfl

theorem cell23_3123895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 1, 2, 2].length) (baseStart_3123895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123895 prefixEnd_3123895 := by exact prefixLift 3123895
  have htrace : WordTrace (prefixWord ++ tailWord_3123895) baseStart_3123895 baseEnd_3123895 := by
    simpa [prefixWord, tailWord_3123895, baseEnd_3123895] using wordTrace_append hprefix tailTrace_3123895
  have hstable : (prefixWord ++ tailWord_3123895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123895).length < 2 ^ (prefixWord ++ tailWord_3123895).sum := by decide
  have hdescent : baseEnd_3123895 < baseStart_3123895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123905 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3123905 : Nat := 118140960795 + 3123905 * 2 ^ 59
def prefixEnd_3123905 : Nat := 4983230072969 + 3 ^ 40 * 3123905 * 2
def baseEnd_3123905 : Nat := 534688261327901813673643

theorem tailTrace_3123905 : CollatzResearch.WordTrace tailWord_3123905 prefixEnd_3123905 534688261327901813673643 := by
  unfold tailWord_3123905
  simp only [CollatzResearch.WordTrace]
  refine ⟨113938175747633180343373169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75958783831755453562248779 113938175747633180343373169)
  ·
    refine ⟨85453631810724885257529877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113938175747633180343373169 85453631810724885257529877)
    ·
      refine ⟨4005638991127728996446713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85453631810724885257529877 4005638991127728996446713)
      ·
        refine ⟨3004229243345796747335035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4005638991127728996446713 3004229243345796747335035)
        ·
          refine ⟨4506343865018695121002553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004229243345796747335035 4506343865018695121002553)
          ·
            refine ⟨3379757898764021340751915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4506343865018695121002553 3379757898764021340751915)
            ·
              refine ⟨5069636848146032011127873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379757898764021340751915 5069636848146032011127873)
              ·
                refine ⟨3802227636109524008345905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5069636848146032011127873 3802227636109524008345905)
                ·
                  refine ⟨2851670727082143006259429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3802227636109524008345905 2851670727082143006259429)
                  ·
                    refine ⟨534688261327901813673643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2851670727082143006259429 534688261327901813673643)
                    ·
                      rfl

theorem cell23_3123905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3123905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123905 prefixEnd_3123905 := by exact prefixLift 3123905
  have htrace : WordTrace (prefixWord ++ tailWord_3123905) baseStart_3123905 baseEnd_3123905 := by
    simpa [prefixWord, tailWord_3123905, baseEnd_3123905] using wordTrace_append hprefix tailTrace_3123905
  have hstable : (prefixWord ++ tailWord_3123905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123905).length < 2 ^ (prefixWord ++ tailWord_3123905).sum := by decide
  have hdescent : baseEnd_3123905 < baseStart_3123905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123927 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 2, 6]
def baseStart_3123927 : Nat := 118140960795 + 3123927 * 2 ^ 59
def prefixEnd_3123927 : Nat := 4983230072969 + 3 ^ 40 * 3123927 * 2
def baseEnd_3123927 : Nat := 534692026852701451648609

theorem tailTrace_3123927 : CollatzResearch.WordTrace tailWord_3123927 prefixEnd_3123927 534692026852701451648609 := by
  unfold tailWord_3123927
  simp only [CollatzResearch.WordTrace]
  refine ⟨113938978153553478100674035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75959318769035652067116023 113938978153553478100674035)
  ·
    refine ⟨170908467230330217151011053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113938978153553478100674035 170908467230330217151011053)
    ·
      refine ⟨64090675211373831431629145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170908467230330217151011053 64090675211373831431629145)
      ·
        refine ⟨48068006408530373573721859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64090675211373831431629145 48068006408530373573721859)
        ·
          refine ⟨72102009612795560360582789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48068006408530373573721859 72102009612795560360582789)
          ·
            refine ⟨13519126802399167567609273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72102009612795560360582789 13519126802399167567609273)
            ·
              refine ⟨10139345101799375675706955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13519126802399167567609273 10139345101799375675706955)
              ·
                refine ⟨15209017652699063513560433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10139345101799375675706955 15209017652699063513560433)
                ·
                  refine ⟨11406763239524297635170325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15209017652699063513560433 11406763239524297635170325)
                  ·
                    refine ⟨534692026852701451648609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11406763239524297635170325 534692026852701451648609)
                    ·
                      rfl

theorem cell23_3123927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_3123927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123927 prefixEnd_3123927 := by exact prefixLift 3123927
  have htrace : WordTrace (prefixWord ++ tailWord_3123927) baseStart_3123927 baseEnd_3123927 := by
    simpa [prefixWord, tailWord_3123927, baseEnd_3123927] using wordTrace_append hprefix tailTrace_3123927
  have hstable : (prefixWord ++ tailWord_3123927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123927).length < 2 ^ (prefixWord ++ tailWord_3123927).sum := by decide
  have hdescent : baseEnd_3123927 < baseStart_3123927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123928 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 2, 1, 3]
def baseStart_3123928 : Nat := 118140960795 + 3123928 * 2 ^ 59
def prefixEnd_3123928 : Nat := 4983230072969 + 3 ^ 40 * 3123928 * 2
def baseEnd_3123928 : Nat := 1604076594038758851033323

theorem tailTrace_3123928 : CollatzResearch.WordTrace tailWord_3123928 prefixEnd_3123928 1604076594038758851033323 := by
  unfold tailWord_3123928
  simp only [CollatzResearch.WordTrace]
  refine ⟨56969507313274927635730219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75959343084366570180973625 56969507313274927635730219)
  ·
    refine ⟨85454260969912391453595329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56969507313274927635730219 85454260969912391453595329)
    ·
      refine ⟨64090695727434293590196497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85454260969912391453595329 64090695727434293590196497)
      ·
        refine ⟨48068021795575720192647373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64090695727434293590196497 48068021795575720192647373)
        ·
          refine ⟨18025508173340895072242765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48068021795575720192647373 18025508173340895072242765)
          ·
            refine ⟨6759565565002835652091037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18025508173340895072242765 6759565565002835652091037)
            ·
              refine ⟨2534837086876063369534139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6759565565002835652091037 2534837086876063369534139)
              ·
                refine ⟨3802255630314095054301209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2534837086876063369534139 3802255630314095054301209)
                ·
                  refine ⟨2851691722735571290725907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3802255630314095054301209 2851691722735571290725907)
                  ·
                    refine ⟨4277537584103356936088861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2851691722735571290725907 4277537584103356936088861)
                    ·
                      refine ⟨1604076594038758851033323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4277537584103356936088861 1604076594038758851033323)
                      ·
                        rfl

theorem cell23_3123928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_3123928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123928 prefixEnd_3123928 := by exact prefixLift 3123928
  have htrace : WordTrace (prefixWord ++ tailWord_3123928) baseStart_3123928 baseEnd_3123928 := by
    simpa [prefixWord, tailWord_3123928, baseEnd_3123928] using wordTrace_append hprefix tailTrace_3123928
  have hstable : (prefixWord ++ tailWord_3123928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123928).length < 2 ^ (prefixWord ++ tailWord_3123928).sum := by decide
  have hdescent : baseEnd_3123928 < baseStart_3123928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123951 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 4, 2, 2]
def baseStart_3123951 : Nat := 118140960795 + 3123951 * 2 ^ 59
def prefixEnd_3123951 : Nat := 4983230072969 + 3 ^ 40 * 3123951 * 2
def baseEnd_3123951 : Nat := 1604088404093812261045717

theorem tailTrace_3123951 : CollatzResearch.WordTrace tailWord_3123951 prefixEnd_3123951 1604088404093812261045717 := by
  unfold tailWord_3123951
  simp only [CollatzResearch.WordTrace]
  refine ⟨113939853505466530199547707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75959902336977686799698471 113939853505466530199547707)
  ·
    refine ⟨170909780258199795299321561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113939853505466530199547707 170909780258199795299321561)
    ·
      refine ⟨128182335193649846474491171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170909780258199795299321561 128182335193649846474491171)
      ·
        refine ⟨192273502790474769711736757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128182335193649846474491171 192273502790474769711736757)
        ·
          refine ⟨18025640886607009660475321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192273502790474769711736757 18025640886607009660475321)
          ·
            refine ⟨13519230664955257245356491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18025640886607009660475321 13519230664955257245356491)
            ·
              refine ⟨20278845997432885868034737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13519230664955257245356491 20278845997432885868034737)
              ·
                refine ⟨15209134498074664401026053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20278845997432885868034737 15209134498074664401026053)
                ·
                  refine ⟨2851712718388999575192385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15209134498074664401026053 2851712718388999575192385)
                  ·
                    refine ⟨2138784538791749681394289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2851712718388999575192385 2138784538791749681394289)
                    ·
                      refine ⟨1604088404093812261045717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138784538791749681394289 1604088404093812261045717)
                      ·
                        rfl

theorem cell23_3123951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 2, 2].length) (baseStart_3123951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123951 prefixEnd_3123951 := by exact prefixLift 3123951
  have htrace : WordTrace (prefixWord ++ tailWord_3123951) baseStart_3123951 baseEnd_3123951 := by
    simpa [prefixWord, tailWord_3123951, baseEnd_3123951] using wordTrace_append hprefix tailTrace_3123951
  have hstable : (prefixWord ++ tailWord_3123951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123951).length < 2 ^ (prefixWord ++ tailWord_3123951).sum := by decide
  have hdescent : baseEnd_3123951 < baseStart_3123951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123954 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3123954 : Nat := 118140960795 + 3123954 * 2 ^ 59
def prefixEnd_3123954 : Nat := 4983230072969 + 3 ^ 40 * 3123954 * 2
def baseEnd_3123954 : Nat := 1604089944535775749308203

theorem tailTrace_3123954 : CollatzResearch.WordTrace tailWord_3123954 prefixEnd_3123954 1604089944535775749308203 := by
  unfold tailWord_3123954
  simp only [CollatzResearch.WordTrace]
  refine ⟨28484990731113915427976729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75959975282970441141271277 28484990731113915427976729)
  ·
    refine ⟨21363743048335436570982547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28484990731113915427976729 21363743048335436570982547)
    ·
      refine ⟨32045614572503154856473821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21363743048335436570982547 32045614572503154856473821)
      ·
        refine ⟨12017105464688683071177683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32045614572503154856473821 12017105464688683071177683)
        ·
          refine ⟨18025658197033024606766525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12017105464688683071177683 18025658197033024606766525)
          ·
            refine ⟨6759621823887384227537447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18025658197033024606766525 6759621823887384227537447)
            ·
              refine ⟨10139432735831076341306171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6759621823887384227537447 10139432735831076341306171)
              ·
                refine ⟨15209149103746614511959257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10139432735831076341306171 15209149103746614511959257)
                ·
                  refine ⟨11406861827809960883969443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15209149103746614511959257 11406861827809960883969443)
                  ·
                    refine ⟨17110292741714941325954165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11406861827809960883969443 17110292741714941325954165)
                    ·
                      refine ⟨1604089944535775749308203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17110292741714941325954165 1604089944535775749308203)
                      ·
                        rfl

theorem cell23_3123954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3123954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123954 prefixEnd_3123954 := by exact prefixLift 3123954
  have htrace : WordTrace (prefixWord ++ tailWord_3123954) baseStart_3123954 baseEnd_3123954 := by
    simpa [prefixWord, tailWord_3123954, baseEnd_3123954] using wordTrace_append hprefix tailTrace_3123954
  have hstable : (prefixWord ++ tailWord_3123954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123954).length < 2 ^ (prefixWord ++ tailWord_3123954).sum := by decide
  have hdescent : baseEnd_3123954 < baseStart_3123954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3123987 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 4, 5]
def baseStart_3123987 : Nat := 118140960795 + 3123987 * 2 ^ 59
def prefixEnd_3123987 : Nat := 4983230072969 + 3 ^ 40 * 3123987 * 2
def baseEnd_3123987 : Nat := 534702296465791373398517

theorem tailTrace_3123987 : CollatzResearch.WordTrace tailWord_3123987 prefixEnd_3123987 534702296465791373398517 := by
  unfold tailWord_3123987
  simp only [CollatzResearch.WordTrace]
  refine ⟨113941166533336108347858215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75960777688890738898572143 113941166533336108347858215)
  ·
    refine ⟨170911749800004162521787323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113941166533336108347858215 170911749800004162521787323)
    ·
      refine ⟨256367624700006243782680985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170911749800004162521787323 256367624700006243782680985)
      ·
        refine ⟨192275718525004682837010739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256367624700006243782680985 192275718525004682837010739)
        ·
          refine ⟨288413577787507024255516109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192275718525004682837010739 288413577787507024255516109)
          ·
            refine ⟨108155091670315134095818541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288413577787507024255516109 108155091670315134095818541)
            ·
              refine ⟨40558159376368175285931953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108155091670315134095818541 40558159376368175285931953)
              ·
                refine ⟨30418619532276131464448965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40558159376368175285931953 30418619532276131464448965)
                ·
                  refine ⟨5703491162301774649584181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30418619532276131464448965 5703491162301774649584181)
                  ·
                    refine ⟨534702296465791373398517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5703491162301774649584181 534702296465791373398517)
                    ·
                      rfl

theorem cell23_3123987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 5].length) (baseStart_3123987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3123987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3123987 prefixEnd_3123987 := by exact prefixLift 3123987
  have htrace : WordTrace (prefixWord ++ tailWord_3123987) baseStart_3123987 baseEnd_3123987 := by
    simpa [prefixWord, tailWord_3123987, baseEnd_3123987] using wordTrace_append hprefix tailTrace_3123987
  have hstable : (prefixWord ++ tailWord_3123987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3123987).length < 2 ^ (prefixWord ++ tailWord_3123987).sum := by decide
  have hdescent : baseEnd_3123987 < baseStart_3123987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3123987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124024 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_3124024 : Nat := 118140960795 + 3124024 * 2 ^ 59
def prefixEnd_3124024 : Nat := 4983230072969 + 3 ^ 40 * 3124024 * 2
def baseEnd_3124024 : Nat := 1604125888181590475432881

theorem tailTrace_3124024 : CollatzResearch.WordTrace tailWord_3124024 prefixEnd_3124024 1604125888181590475432881 := by
  unfold tailWord_3124024
  simp only [CollatzResearch.WordTrace]
  refine ⟨56971258017101031833477563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75961677356134709111303417 56971258017101031833477563)
  ·
    refine ⟨85456887025651547750216345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56971258017101031833477563 85456887025651547750216345)
    ·
      refine ⟨64092665269238660812662259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85456887025651547750216345 64092665269238660812662259)
      ·
        refine ⟨96138997903857991218993389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64092665269238660812662259 96138997903857991218993389)
        ·
          refine ⟨36052124213946746707122521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96138997903857991218993389 36052124213946746707122521)
          ·
            refine ⟨27039093160460060030341891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36052124213946746707122521 27039093160460060030341891)
            ·
              refine ⟨40558639740690090045512837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27039093160460060030341891 40558639740690090045512837)
              ·
                refine ⟨7604744951379391883533657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40558639740690090045512837 7604744951379391883533657)
                ·
                  refine ⟨5703558713534543912650243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7604744951379391883533657 5703558713534543912650243)
                  ·
                    refine ⟨8555338070301815868975365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5703558713534543912650243 8555338070301815868975365)
                    ·
                      refine ⟨1604125888181590475432881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8555338070301815868975365 1604125888181590475432881)
                      ·
                        rfl

theorem cell23_3124024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_3124024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124024 prefixEnd_3124024 := by exact prefixLift 3124024
  have htrace : WordTrace (prefixWord ++ tailWord_3124024) baseStart_3124024 baseEnd_3124024 := by
    simpa [prefixWord, tailWord_3124024, baseEnd_3124024] using wordTrace_append hprefix tailTrace_3124024
  have hstable : (prefixWord ++ tailWord_3124024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124024).length < 2 ^ (prefixWord ++ tailWord_3124024).sum := by decide
  have hdescent : baseEnd_3124024 < baseStart_3124024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124037 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_3124037 : Nat := 118140960795 + 3124037 * 2 ^ 59
def prefixEnd_3124037 : Nat := 4983230072969 + 3 ^ 40 * 3124037 * 2
def baseEnd_3124037 : Nat := 1604132563430098924570321

theorem tailTrace_3124037 : CollatzResearch.WordTrace tailWord_3124037 prefixEnd_3124037 1604132563430098924570321 := by
  unfold tailWord_3124037
  simp only [CollatzResearch.WordTrace]
  refine ⟨113942990183154966887178365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75961993455436644591452243 113942990183154966887178365)
  ·
    refine ⟨42728621318683112582691887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113942990183154966887178365 42728621318683112582691887)
    ·
      refine ⟨64092931978024668874037831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42728621318683112582691887 64092931978024668874037831)
      ·
        refine ⟨96139397967037003311056747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64092931978024668874037831 96139397967037003311056747)
        ·
          refine ⟨144209096950555504966585121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96139397967037003311056747 144209096950555504966585121)
          ·
            refine ⟨108156822712916628724938841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144209096950555504966585121 108156822712916628724938841)
            ·
              refine ⟨81117617034687471543704131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108156822712916628724938841 81117617034687471543704131)
              ·
                refine ⟨121676425552031207315556197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81117617034687471543704131 121676425552031207315556197)
                ·
                  refine ⟨22814329791005851371666787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121676425552031207315556197 22814329791005851371666787)
                  ·
                    refine ⟨34221494686508777057500181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22814329791005851371666787 34221494686508777057500181)
                    ·
                      refine ⟨1604132563430098924570321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34221494686508777057500181 1604132563430098924570321)
                      ·
                        rfl

theorem cell23_3124037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_3124037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124037 prefixEnd_3124037 := by exact prefixLift 3124037
  have htrace : WordTrace (prefixWord ++ tailWord_3124037) baseStart_3124037 baseEnd_3124037 := by
    simpa [prefixWord, tailWord_3124037, baseEnd_3124037] using wordTrace_append hprefix tailTrace_3124037
  have hstable : (prefixWord ++ tailWord_3124037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124037).length < 2 ^ (prefixWord ++ tailWord_3124037).sum := by decide
  have hdescent : baseEnd_3124037 < baseStart_3124037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124041 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 2, 4, 2]
def baseStart_3124041 : Nat := 118140960795 + 3124041 * 2 ^ 59
def prefixEnd_3124041 : Nat := 4983230072969 + 3 ^ 40 * 3124041 * 2
def baseEnd_3124041 : Nat := 1604134617352716908920303

theorem tailTrace_3124041 : CollatzResearch.WordTrace tailWord_3124041 prefixEnd_3124041 1604134617352716908920303 := by
  unfold tailWord_3124041
  simp only [CollatzResearch.WordTrace]
  refine ⟨113943136075140475570323977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75962090716760317046882651 113943136075140475570323977)
  ·
    refine ⟨85457352056355356677742983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113943136075140475570323977 85457352056355356677742983)
    ·
      refine ⟨128186028084533035016614475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85457352056355356677742983 128186028084533035016614475)
      ·
        refine ⟨192279042126799552524921713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128186028084533035016614475 192279042126799552524921713)
        ·
          refine ⟨144209281595099664393691285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192279042126799552524921713 144209281595099664393691285)
          ·
            refine ⟨6759810074770296768454279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144209281595099664393691285 6759810074770296768454279)
            ·
              refine ⟨10139715112155445152681419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6759810074770296768454279 10139715112155445152681419)
              ·
                refine ⟨15209572668233167729022129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10139715112155445152681419 15209572668233167729022129)
                ·
                  refine ⟨11407179501174875796766597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15209572668233167729022129 11407179501174875796766597)
                  ·
                    refine ⟨2138846156470289211893737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11407179501174875796766597 2138846156470289211893737)
                    ·
                      refine ⟨1604134617352716908920303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138846156470289211893737 1604134617352716908920303)
                      ·
                        rfl

theorem cell23_3124041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 4, 2].length) (baseStart_3124041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124041 prefixEnd_3124041 := by exact prefixLift 3124041
  have htrace : WordTrace (prefixWord ++ tailWord_3124041) baseStart_3124041 baseEnd_3124041 := by
    simpa [prefixWord, tailWord_3124041, baseEnd_3124041] using wordTrace_append hprefix tailTrace_3124041
  have hstable : (prefixWord ++ tailWord_3124041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124041).length < 2 ^ (prefixWord ++ tailWord_3124041).sum := by decide
  have hdescent : baseEnd_3124041 < baseStart_3124041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124068 : List Nat := [2, 3, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_3124068 : Nat := 118140960795 + 3124068 * 2 ^ 59
def prefixEnd_3124068 : Nat := 4983230072969 + 3 ^ 40 * 3124068 * 2
def baseEnd_3124068 : Nat := 534716160443462767760893

theorem tailTrace_3124068 : CollatzResearch.WordTrace tailWord_3124068 prefixEnd_3124068 534716160443462767760893 := by
  unfold tailWord_3124068
  simp only [CollatzResearch.WordTrace]
  refine ⟨56972060423021329590778429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75962747230695106121037905 56972060423021329590778429)
  ·
    refine ⟨21364522658632998596541911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56972060423021329590778429 21364522658632998596541911)
    ·
      refine ⟨32046783987949497894812867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21364522658632998596541911 32046783987949497894812867)
      ·
        refine ⟨48070175981924246842219301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32046783987949497894812867 48070175981924246842219301)
        ·
          refine ⟨9013157996610796282916119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48070175981924246842219301 9013157996610796282916119)
          ·
            refine ⟨13519736994916194424374179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9013157996610796282916119 13519736994916194424374179)
            ·
              refine ⟨20279605492374291636561269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13519736994916194424374179 20279605492374291636561269)
              ·
                refine ⟨1901213014910089840927619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20279605492374291636561269 1901213014910089840927619)
                ·
                  refine ⟨2851819522365134761391429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901213014910089840927619 2851819522365134761391429)
                  ·
                    refine ⟨534716160443462767760893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2851819522365134761391429 534716160443462767760893)
                    ·
                      rfl

theorem cell23_3124068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_3124068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124068 prefixEnd_3124068 := by exact prefixLift 3124068
  have htrace : WordTrace (prefixWord ++ tailWord_3124068) baseStart_3124068 baseEnd_3124068 := by
    simpa [prefixWord, tailWord_3124068, baseEnd_3124068] using wordTrace_append hprefix tailTrace_3124068
  have hstable : (prefixWord ++ tailWord_3124068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124068).length < 2 ^ (prefixWord ++ tailWord_3124068).sum := by decide
  have hdescent : baseEnd_3124068 < baseStart_3124068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124081 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 6]
def baseStart_3124081 : Nat := 118140960795 + 3124081 * 2 ^ 59
def prefixEnd_3124081 : Nat := 4983230072969 + 3 ^ 40 * 3124081 * 2
def baseEnd_3124081 : Nat := 178239461842099639157791

theorem tailTrace_3124081 : CollatzResearch.WordTrace tailWord_3124081 prefixEnd_3124081 178239461842099639157791 := by
  unfold tailWord_3124081
  simp only [CollatzResearch.WordTrace]
  refine ⟨113944594994995562401780097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75963063329997041601186731 113944594994995562401780097)
  ·
    refine ⟨85458446246246671801335073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113944594994995562401780097 85458446246246671801335073)
    ·
      refine ⟨64093834684685003851001305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85458446246246671801335073 64093834684685003851001305)
      ·
        refine ⟨48070376013513752888250979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64093834684685003851001305 48070376013513752888250979)
        ·
          refine ⟨72105564020270629332376469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48070376013513752888250979 72105564020270629332376469)
          ·
            refine ⟨3379948313450185749955147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72105564020270629332376469 3379948313450185749955147)
            ·
              refine ⟨5069922470175278624932721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379948313450185749955147 5069922470175278624932721)
              ·
                refine ⟨3802441852631458968699541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5069922470175278624932721 3802441852631458968699541)
                ·
                  refine ⟨178239461842099639157791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3802441852631458968699541 178239461842099639157791)
                  ·
                    rfl

theorem cell23_3124081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 6].length) (baseStart_3124081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124081 prefixEnd_3124081 := by exact prefixLift 3124081
  have htrace : WordTrace (prefixWord ++ tailWord_3124081) baseStart_3124081 baseEnd_3124081 := by
    simpa [prefixWord, tailWord_3124081, baseEnd_3124081] using wordTrace_append hprefix tailTrace_3124081
  have hstable : (prefixWord ++ tailWord_3124081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124081).length < 2 ^ (prefixWord ++ tailWord_3124081).sum := by decide
  have hdescent : baseEnd_3124081 < baseStart_3124081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124091 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 3, 1, 3]
def baseStart_3124091 : Nat := 118140960795 + 3124091 * 2 ^ 59
def prefixEnd_3124091 : Nat := 4983230072969 + 3 ^ 40 * 3124091 * 2
def baseEnd_3124091 : Nat := 1604160291385441713295073

theorem tailTrace_3124091 : CollatzResearch.WordTrace tailWord_3124091 prefixEnd_3124091 1604160291385441713295073 := by
  unfold tailWord_3124091
  simp only [CollatzResearch.WordTrace]
  refine ⟨113944959724959334109644127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75963306483306222739762751 113944959724959334109644127)
  ·
    refine ⟨170917439587439001164466191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113944959724959334109644127 170917439587439001164466191)
    ·
      refine ⟨256376159381158501746699287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170917439587439001164466191 256376159381158501746699287)
      ·
        refine ⟨384564239071737752620048931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256376159381158501746699287 384564239071737752620048931)
        ·
          refine ⟨576846358607606628930073397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384564239071737752620048931 576846358607606628930073397)
          ·
            refine ⟨54079346119463121462194381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 576846358607606628930073397 54079346119463121462194381)
            ·
              refine ⟨20279754794798670548322893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54079346119463121462194381 20279754794798670548322893)
              ·
                refine ⟨7604908048049501455621085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20279754794798670548322893 7604908048049501455621085)
                ·
                  refine ⟨2851840518018563045857907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7604908048049501455621085 2851840518018563045857907)
                  ·
                    refine ⟨4277760777027844568786861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2851840518018563045857907 4277760777027844568786861)
                    ·
                      refine ⟨1604160291385441713295073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4277760777027844568786861 1604160291385441713295073)
                      ·
                        rfl

theorem cell23_3124091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 1, 3].length) (baseStart_3124091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124091 prefixEnd_3124091 := by exact prefixLift 3124091
  have htrace : WordTrace (prefixWord ++ tailWord_3124091) baseStart_3124091 baseEnd_3124091 := by
    simpa [prefixWord, tailWord_3124091, baseEnd_3124091] using wordTrace_append hprefix tailTrace_3124091
  have hstable : (prefixWord ++ tailWord_3124091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124091).length < 2 ^ (prefixWord ++ tailWord_3124091).sum := by decide
  have hdescent : baseEnd_3124091 < baseStart_3124091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124101 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 1, 5, 2]
def baseStart_3124101 : Nat := 118140960795 + 3124101 * 2 ^ 59
def prefixEnd_3124101 : Nat := 4983230072969 + 3 ^ 40 * 3124101 * 2
def baseEnd_3124101 : Nat := 1604165426191986674170027

theorem tailTrace_3124101 : CollatzResearch.WordTrace tailWord_3124101 prefixEnd_3124101 1604165426191986674170027 := by
  unfold tailWord_3124101
  simp only [CollatzResearch.WordTrace]
  refine ⟨113945324454923105817508157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75963549636615403878338771 113945324454923105817508157)
  ·
    refine ⟨42729496670596164681565559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113945324454923105817508157 42729496670596164681565559)
    ·
      refine ⟨64094245005894247022348339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42729496670596164681565559 64094245005894247022348339)
      ·
        refine ⟨96141367508841370533522509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64094245005894247022348339 96141367508841370533522509)
        ·
          refine ⟨36053012815815513950070941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96141367508841370533522509 36053012815815513950070941)
          ·
            refine ⟨13519879805930817731276603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36053012815815513950070941 13519879805930817731276603)
            ·
              refine ⟨20279819708896226596914905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13519879805930817731276603 20279819708896226596914905)
              ·
                refine ⟨15209864781672169947686179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20279819708896226596914905 15209864781672169947686179)
                ·
                  refine ⟨22814797172508254921529269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15209864781672169947686179 22814797172508254921529269)
                  ·
                    refine ⟨2138887234922648898893369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22814797172508254921529269 2138887234922648898893369)
                    ·
                      refine ⟨1604165426191986674170027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138887234922648898893369 1604165426191986674170027)
                      ·
                        rfl

theorem cell23_3124101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_3124101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124101 prefixEnd_3124101 := by exact prefixLift 3124101
  have htrace : WordTrace (prefixWord ++ tailWord_3124101) baseStart_3124101 baseEnd_3124101 := by
    simpa [prefixWord, tailWord_3124101, baseEnd_3124101] using wordTrace_append hprefix tailTrace_3124101
  have hstable : (prefixWord ++ tailWord_3124101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124101).length < 2 ^ (prefixWord ++ tailWord_3124101).sum := by decide
  have hdescent : baseEnd_3124101 < baseStart_3124101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124131 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 4]
def baseStart_3124131 : Nat := 118140960795 + 3124131 * 2 ^ 59
def prefixEnd_3124131 : Nat := 4983230072969 + 3 ^ 40 * 3124131 * 2
def baseEnd_3124131 : Nat := 1604180830611621556794889

theorem tailTrace_3124131 : CollatzResearch.WordTrace tailWord_3124131 prefixEnd_3124131 1604180830611621556794889 := by
  unfold tailWord_3124131
  simp only [CollatzResearch.WordTrace]
  refine ⟨113946418644814420941100247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75964279096542947294066831 113946418644814420941100247)
  ·
    refine ⟨170919627967221631411650371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113946418644814420941100247 170919627967221631411650371)
    ·
      refine ⟨256379441950832447117475557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170919627967221631411650371 256379441950832447117475557)
      ·
        refine ⟨48071145365781083834526667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256379441950832447117475557 48071145365781083834526667)
        ·
          refine ⟨72106718048671625751790001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48071145365781083834526667 72106718048671625751790001)
          ·
            refine ⟨54080038536503719313842501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72106718048671625751790001 54080038536503719313842501)
            ·
              refine ⟨10140007225594447371345469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54080038536503719313842501 10140007225594447371345469)
              ·
                refine ⟨3802502709597917764254551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10140007225594447371345469 3802502709597917764254551)
                ·
                  refine ⟨5703754064396876646381827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802502709597917764254551 5703754064396876646381827)
                  ·
                    refine ⟨8555631096595314969572741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5703754064396876646381827 8555631096595314969572741)
                    ·
                      refine ⟨1604180830611621556794889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8555631096595314969572741 1604180830611621556794889)
                      ·
                        rfl

theorem cell23_3124131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_3124131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124131 prefixEnd_3124131 := by exact prefixLift 3124131
  have htrace : WordTrace (prefixWord ++ tailWord_3124131) baseStart_3124131 baseEnd_3124131 := by
    simpa [prefixWord, tailWord_3124131, baseEnd_3124131] using wordTrace_append hprefix tailTrace_3124131
  have hstable : (prefixWord ++ tailWord_3124131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124131).length < 2 ^ (prefixWord ++ tailWord_3124131).sum := by decide
  have hdescent : baseEnd_3124131 < baseStart_3124131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124135 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_3124135 : Nat := 118140960795 + 3124135 * 2 ^ 59
def prefixEnd_3124135 : Nat := 4983230072969 + 3 ^ 40 * 3124135 * 2
def baseEnd_3124135 : Nat := 1604182884534239541144871

theorem tailTrace_3124135 : CollatzResearch.WordTrace tailWord_3124135 prefixEnd_3124135 1604182884534239541144871 := by
  unfold tailWord_3124135
  simp only [CollatzResearch.WordTrace]
  refine ⟨113946564536799929624245859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75964376357866619749497239 113946564536799929624245859)
  ·
    refine ⟨170919846805199894436368789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113946564536799929624245859 170919846805199894436368789)
    ·
      refine ⟨8011867818993745051704787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170919846805199894436368789 8011867818993745051704787)
      ·
        refine ⟨12017801728490617577557181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8011867818993745051704787 12017801728490617577557181)
        ·
          refine ⟨4506675648183981591583943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12017801728490617577557181 4506675648183981591583943)
          ·
            refine ⟨6760013472275972387375915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506675648183981591583943 6760013472275972387375915)
            ·
              refine ⟨10140020208413958581063873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760013472275972387375915 10140020208413958581063873)
              ·
                refine ⟨7605015156310468935797905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10140020208413958581063873 7605015156310468935797905)
                ·
                  refine ⟨5703761367232851701848429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7605015156310468935797905 5703761367232851701848429)
                  ·
                    refine ⟨2138910512712319388193161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5703761367232851701848429 2138910512712319388193161)
                    ·
                      refine ⟨1604182884534239541144871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138910512712319388193161 1604182884534239541144871)
                      ·
                        rfl

theorem cell23_3124135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_3124135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124135 prefixEnd_3124135 := by exact prefixLift 3124135
  have htrace : WordTrace (prefixWord ++ tailWord_3124135) baseStart_3124135 baseEnd_3124135 := by
    simpa [prefixWord, tailWord_3124135, baseEnd_3124135] using wordTrace_append hprefix tailTrace_3124135
  have hstable : (prefixWord ++ tailWord_3124135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124135).length < 2 ^ (prefixWord ++ tailWord_3124135).sum := by decide
  have hdescent : baseEnd_3124135 < baseStart_3124135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124154 : List Nat := [3, 1, 1, 1, 2, 1, 6, 8]
def baseStart_3124154 : Nat := 118140960795 + 3124154 * 2 ^ 59
def prefixEnd_3124154 : Nat := 4983230072969 + 3 ^ 40 * 3124154 * 2
def baseEnd_3124154 : Nat := 59414542246913887659529

theorem tailTrace_3124154 : CollatzResearch.WordTrace tailWord_3124154 prefixEnd_3124154 59414542246913887659529 := by
  unfold tailWord_3124154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28486814380932773967296879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75964838349154063912791677 28486814380932773967296879)
  ·
    refine ⟨42730221571399160950945319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28486814380932773967296879 42730221571399160950945319)
    ·
      refine ⟨64095332357098741426417979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42730221571399160950945319 64095332357098741426417979)
      ·
        refine ⟨96142998535648112139626969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64095332357098741426417979 96142998535648112139626969)
        ·
          refine ⟨72107248901736084104720227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96142998535648112139626969 72107248901736084104720227)
          ·
            refine ⟨108160873352604126157080341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72107248901736084104720227 108160873352604126157080341)
            ·
              refine ⟨5070040938403318413613141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108160873352604126157080341 5070040938403318413613141)
              ·
                refine ⟨59414542246913887659529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5070040938403318413613141 59414542246913887659529)
                ·
                  rfl

theorem cell23_3124154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 8].length) (baseStart_3124154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124154 prefixEnd_3124154 := by exact prefixLift 3124154
  have htrace : WordTrace (prefixWord ++ tailWord_3124154) baseStart_3124154 baseEnd_3124154 := by
    simpa [prefixWord, tailWord_3124154, baseEnd_3124154] using wordTrace_append hprefix tailTrace_3124154
  have hstable : (prefixWord ++ tailWord_3124154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124154).length < 2 ^ (prefixWord ++ tailWord_3124154).sum := by decide
  have hdescent : baseEnd_3124154 < baseStart_3124154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124158 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_3124158 : Nat := 118140960795 + 3124158 * 2 ^ 59
def prefixEnd_3124158 : Nat := 4983230072969 + 3 ^ 40 * 3124158 * 2
def baseEnd_3124158 : Nat := 534731564863097650385755

theorem tailTrace_3124158 : CollatzResearch.WordTrace tailWord_3124158 prefixEnd_3124158 534731564863097650385755 := by
  unfold tailWord_3124158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14243425426964575569041641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75964935610477736368222085 14243425426964575569041641)
  ·
    refine ⟨10682569070223431676781231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14243425426964575569041641 10682569070223431676781231)
    ·
      refine ⟨16023853605335147515171847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10682569070223431676781231 16023853605335147515171847)
      ·
        refine ⟨24035780408002721272757771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16023853605335147515171847 24035780408002721272757771)
        ·
          refine ⟨36053670612004081909136657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24035780408002721272757771 36053670612004081909136657)
          ·
            refine ⟨27040252959003061431852493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36053670612004081909136657 27040252959003061431852493)
            ·
              refine ⟨10140094859626148036944685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27040252959003061431852493 10140094859626148036944685)
              ·
                refine ⟨3802535572359805513854257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10140094859626148036944685 3802535572359805513854257)
                ·
                  refine ⟨2851901679269854135390693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3802535572359805513854257 2851901679269854135390693)
                  ·
                    refine ⟨534731564863097650385755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2851901679269854135390693 534731564863097650385755)
                    ·
                      rfl

theorem cell23_3124158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_3124158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124158 prefixEnd_3124158 := by exact prefixLift 3124158
  have htrace : WordTrace (prefixWord ++ tailWord_3124158) baseStart_3124158 baseEnd_3124158 := by
    simpa [prefixWord, tailWord_3124158, baseEnd_3124158] using wordTrace_append hprefix tailTrace_3124158
  have hstable : (prefixWord ++ tailWord_3124158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124158).length < 2 ^ (prefixWord ++ tailWord_3124158).sum := by decide
  have hdescent : baseEnd_3124158 < baseStart_3124158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124168 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_3124168 : Nat := 118140960795 + 3124168 * 2 ^ 59
def prefixEnd_3124168 : Nat := 4983230072969 + 3 ^ 40 * 3124168 * 2
def baseEnd_3124168 : Nat := 1604199829395837912032219

theorem tailTrace_3124168 : CollatzResearch.WordTrace tailWord_3124168 prefixEnd_3124168 1604199829395837912032219 := by
  unfold tailWord_3124168
  simp only [CollatzResearch.WordTrace]
  refine ⟨56973884072840188130098579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75965178763786917506798105 56973884072840188130098579)
  ·
    refine ⟨85460826109260282195147869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56973884072840188130098579 85460826109260282195147869)
    ·
      refine ⟨32047809790972605823180451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85460826109260282195147869 32047809790972605823180451)
      ·
        refine ⟨48071714686458908734770677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32047809790972605823180451 48071714686458908734770677)
        ·
          refine ⟨4506723251855522693884751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48071714686458908734770677 4506723251855522693884751)
          ·
            refine ⟨6760084877783284040827127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506723251855522693884751 6760084877783284040827127)
            ·
              refine ⟨10140127316674926061240691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760084877783284040827127 10140127316674926061240691)
              ·
                refine ⟨15210190975012389091861037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10140127316674926061240691 15210190975012389091861037)
                ·
                  refine ⟨5703821615629645909447889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15210190975012389091861037 5703821615629645909447889)
                  ·
                    refine ⟨4277866211722234432085917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5703821615629645909447889 4277866211722234432085917)
                    ·
                      refine ⟨1604199829395837912032219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4277866211722234432085917 1604199829395837912032219)
                      ·
                        rfl

theorem cell23_3124168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_3124168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124168 prefixEnd_3124168 := by exact prefixLift 3124168
  have htrace : WordTrace (prefixWord ++ tailWord_3124168) baseStart_3124168 baseEnd_3124168 := by
    simpa [prefixWord, tailWord_3124168, baseEnd_3124168] using wordTrace_append hprefix tailTrace_3124168
  have hstable : (prefixWord ++ tailWord_3124168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124168).length < 2 ^ (prefixWord ++ tailWord_3124168).sum := by decide
  have hdescent : baseEnd_3124168 < baseStart_3124168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124178 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3124178 : Nat := 118140960795 + 3124178 * 2 ^ 59
def prefixEnd_3124178 : Nat := 4983230072969 + 3 ^ 40 * 3124178 * 2
def baseEnd_3124178 : Nat := 1604204964202382872907173

theorem tailTrace_3124178 : CollatzResearch.WordTrace tailWord_3124178 prefixEnd_3124178 1604204964202382872907173 := by
  unfold tailWord_3124178
  simp only [CollatzResearch.WordTrace]
  refine ⟨28487033218911036992015297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75965421917096098645374125 28487033218911036992015297)
  ·
    refine ⟨21365274914183277744011473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28487033218911036992015297 21365274914183277744011473)
    ·
      refine ⟨16023956185637458308008605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21365274914183277744011473 16023956185637458308008605)
      ·
        refine ⟨6008983569614046865503227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16023956185637458308008605 6008983569614046865503227)
        ·
          refine ⟨9013475354421070298254841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6008983569614046865503227 9013475354421070298254841)
          ·
            refine ⟨6760106515815802723691131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9013475354421070298254841 6760106515815802723691131)
            ·
              refine ⟨10140159773723704085536697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760106515815802723691131 10140159773723704085536697)
              ·
                refine ⟨7605119830292778064152523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10140159773723704085536697 7605119830292778064152523)
                ·
                  refine ⟨11407679745439167096228785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7605119830292778064152523 11407679745439167096228785)
                  ·
                    refine ⟨8555759809079375322171589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11407679745439167096228785 8555759809079375322171589)
                    ·
                      refine ⟨1604204964202382872907173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8555759809079375322171589 1604204964202382872907173)
                      ·
                        rfl

theorem cell23_3124178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3124178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124178 prefixEnd_3124178 := by exact prefixLift 3124178
  have htrace : WordTrace (prefixWord ++ tailWord_3124178) baseStart_3124178 baseEnd_3124178 := by
    simpa [prefixWord, tailWord_3124178, baseEnd_3124178] using wordTrace_append hprefix tailTrace_3124178
  have hstable : (prefixWord ++ tailWord_3124178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124178).length < 2 ^ (prefixWord ++ tailWord_3124178).sum := by decide
  have hdescent : baseEnd_3124178 < baseStart_3124178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124182 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_3124182 : Nat := 118140960795 + 3124182 * 2 ^ 59
def prefixEnd_3124182 : Nat := 4983230072969 + 3 ^ 40 * 3124182 * 2
def baseEnd_3124182 : Nat := 1604207018125000857257155

theorem tailTrace_3124182 : CollatzResearch.WordTrace tailWord_3124182 prefixEnd_3124182 1604207018125000857257155 := by
  unfold tailWord_3124182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121767422976853540700425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75965519178419771100804533 7121767422976853540700425)
  ·
    refine ⟨5341325567232640155525319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7121767422976853540700425 5341325567232640155525319)
    ·
      refine ⟨8011988350848960233287979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5341325567232640155525319 8011988350848960233287979)
      ·
        refine ⟨12017982526273440349931969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8011988350848960233287979 12017982526273440349931969)
        ·
          refine ⟨9013486894705080262448977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12017982526273440349931969 9013486894705080262448977)
          ·
            refine ⟨6760115171028810196836733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9013486894705080262448977 6760115171028810196836733)
            ·
              refine ⟨2535043189135803823813775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6760115171028810196836733 2535043189135803823813775)
              ·
                refine ⟨3802564783703705735720663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535043189135803823813775 3802564783703705735720663)
                ·
                  refine ⟨5703847175555558603580995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802564783703705735720663 5703847175555558603580995)
                  ·
                    refine ⟨8555770763333337905371493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5703847175555558603580995 8555770763333337905371493)
                    ·
                      refine ⟨1604207018125000857257155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8555770763333337905371493 1604207018125000857257155)
                      ·
                        rfl

theorem cell23_3124182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_3124182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124182 prefixEnd_3124182 := by exact prefixLift 3124182
  have htrace : WordTrace (prefixWord ++ tailWord_3124182) baseStart_3124182 baseEnd_3124182 := by
    simpa [prefixWord, tailWord_3124182, baseEnd_3124182] using wordTrace_append hprefix tailTrace_3124182
  have hstable : (prefixWord ++ tailWord_3124182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124182).length < 2 ^ (prefixWord ++ tailWord_3124182).sum := by decide
  have hdescent : baseEnd_3124182 < baseStart_3124182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124185 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 1, 2, 3]
def baseStart_3124185 : Nat := 118140960795 + 3124185 * 2 ^ 59
def prefixEnd_3124185 : Nat := 4983230072969 + 3 ^ 40 * 3124185 * 2
def baseEnd_3124185 : Nat := 1604208558566964345519641

theorem tailTrace_3124185 : CollatzResearch.WordTrace tailWord_3124185 prefixEnd_3124185 1604208558566964345519641 := by
  unfold tailWord_3124185
  simp only [CollatzResearch.WordTrace]
  refine ⟨113948388186618788163566009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75965592124412525442377339 113948388186618788163566009)
  ·
    refine ⟨85461291139964091122674507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113948388186618788163566009 85461291139964091122674507)
    ·
      refine ⟨128191936709946136684011761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85461291139964091122674507 128191936709946136684011761)
      ·
        refine ⟨96143952532459602513008821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128191936709946136684011761 96143952532459602513008821)
        ·
          refine ⟨9013495549918087735594577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96143952532459602513008821 9013495549918087735594577)
          ·
            refine ⟨6760121662438565801695933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9013495549918087735594577 6760121662438565801695933)
            ·
              refine ⟨2535045623414462175635975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6760121662438565801695933 2535045623414462175635975)
              ·
                refine ⟨3802568435121693263453963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535045623414462175635975 3802568435121693263453963)
                ·
                  refine ⟨5703852652682539895180945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802568435121693263453963 5703852652682539895180945)
                  ·
                    refine ⟨4277889489511904921385709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5703852652682539895180945 4277889489511904921385709)
                    ·
                      refine ⟨1604208558566964345519641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4277889489511904921385709 1604208558566964345519641)
                      ·
                        rfl

theorem cell23_3124185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_3124185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124185 prefixEnd_3124185 := by exact prefixLift 3124185
  have htrace : WordTrace (prefixWord ++ tailWord_3124185) baseStart_3124185 baseEnd_3124185 := by
    simpa [prefixWord, tailWord_3124185, baseEnd_3124185] using wordTrace_append hprefix tailTrace_3124185
  have hstable : (prefixWord ++ tailWord_3124185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124185).length < 2 ^ (prefixWord ++ tailWord_3124185).sum := by decide
  have hdescent : baseEnd_3124185 < baseStart_3124185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124199 : List Nat := [1, 1, 5, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_3124199 : Nat := 118140960795 + 3124199 * 2 ^ 59
def prefixEnd_3124199 : Nat := 4983230072969 + 3 ^ 40 * 3124199 * 2
def baseEnd_3124199 : Nat := 1604215747296127290744577

theorem tailTrace_3124199 : CollatzResearch.WordTrace tailWord_3124199 prefixEnd_3124199 1604215747296127290744577 := by
  unfold tailWord_3124199
  simp only [CollatzResearch.WordTrace]
  refine ⟨113948898808568068554575651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75965932539045379036383767 113948898808568068554575651)
  ·
    refine ⟨170923348212852102831863477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113948898808568068554575651 170923348212852102831863477)
    ·
      refine ⟨16024063894954884640487201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170923348212852102831863477 16024063894954884640487201)
      ·
        refine ⟨12018047921216163480365401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16024063894954884640487201 12018047921216163480365401)
        ·
          refine ⟨9013535940912122610274051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12018047921216163480365401 9013535940912122610274051)
          ·
            refine ⟨13520303911368183915411077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9013535940912122610274051 13520303911368183915411077)
            ·
              refine ⟨2535056983381534484139577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13520303911368183915411077 2535056983381534484139577)
              ·
                refine ⟨1901292737536150863104683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535056983381534484139577 1901292737536150863104683)
                ·
                  refine ⟨2851939106304226294657025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901292737536150863104683 2851939106304226294657025)
                  ·
                    refine ⟨2138954329728169720992769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2851939106304226294657025 2138954329728169720992769)
                    ·
                      refine ⟨1604215747296127290744577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138954329728169720992769 1604215747296127290744577)
                      ·
                        rfl

theorem cell23_3124199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_3124199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124199 prefixEnd_3124199 := by exact prefixLift 3124199
  have htrace : WordTrace (prefixWord ++ tailWord_3124199) baseStart_3124199 baseEnd_3124199 := by
    simpa [prefixWord, tailWord_3124199, baseEnd_3124199] using wordTrace_append hprefix tailTrace_3124199
  have hstable : (prefixWord ++ tailWord_3124199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124199).length < 2 ^ (prefixWord ++ tailWord_3124199).sum := by decide
  have hdescent : baseEnd_3124199 < baseStart_3124199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124255 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 4, 2, 2]
def baseStart_3124255 : Nat := 118140960795 + 3124255 * 2 ^ 59
def prefixEnd_3124255 : Nat := 4983230072969 + 3 ^ 40 * 3124255 * 2
def baseEnd_3124255 : Nat := 1604244502212779071644319

theorem tailTrace_3124255 : CollatzResearch.WordTrace tailWord_3124255 prefixEnd_3124255 1604244502212779071644319 := by
  unfold tailWord_3124255
  simp only [CollatzResearch.WordTrace]
  refine ⟨113950941296365190118614219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75967294197576793412409479 113950941296365190118614219)
  ·
    refine ⟨170926411944547785177921329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113950941296365190118614219 170926411944547785177921329)
    ·
      refine ⟨128194808958410838883440997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170926411944547785177921329 128194808958410838883440997)
      ·
        refine ⟨24036526679702032290645187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128194808958410838883440997 24036526679702032290645187)
        ·
          refine ⟨36054790019553048435967781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24036526679702032290645187 36054790019553048435967781)
          ·
            refine ⟨6760273128666196581743959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36054790019553048435967781 6760273128666196581743959)
            ·
              refine ⟨10140409692999294872615939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760273128666196581743959 10140409692999294872615939)
              ·
                refine ⟨15210614539498942308923909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10140409692999294872615939 15210614539498942308923909)
                ·
                  refine ⟨2851990226156051682923233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15210614539498942308923909 2851990226156051682923233)
                  ·
                    refine ⟨2138992669617038762192425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2851990226156051682923233 2138992669617038762192425)
                    ·
                      refine ⟨1604244502212779071644319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2138992669617038762192425 1604244502212779071644319)
                      ·
                        rfl

theorem cell23_3124255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_3124255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124255 prefixEnd_3124255 := by exact prefixLift 3124255
  have htrace : WordTrace (prefixWord ++ tailWord_3124255) baseStart_3124255 baseEnd_3124255 := by
    simpa [prefixWord, tailWord_3124255, baseEnd_3124255] using wordTrace_append hprefix tailTrace_3124255
  have hstable : (prefixWord ++ tailWord_3124255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124255).length < 2 ^ (prefixWord ++ tailWord_3124255).sum := by decide
  have hdescent : baseEnd_3124255 < baseStart_3124255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124261 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 7]
def baseStart_3124261 : Nat := 118140960795 + 3124261 * 2 ^ 59
def prefixEnd_3124261 : Nat := 4983230072969 + 3 ^ 40 * 3124261 * 2
def baseEnd_3124261 : Nat := 178249731455189560907699

theorem tailTrace_3124261 : CollatzResearch.WordTrace tailWord_3124261 prefixEnd_3124261 178249731455189560907699 := by
  unfold tailWord_3124261
  simp only [CollatzResearch.WordTrace]
  refine ⟨113951160134343453143332637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75967440089562302095555091 113951160134343453143332637)
  ·
    refine ⟨42731685050378794928749739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113951160134343453143332637 42731685050378794928749739)
    ·
      refine ⟨64097527575568192393124609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42731685050378794928749739 64097527575568192393124609)
      ·
        refine ⟨48073145681676144294843457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64097527575568192393124609 48073145681676144294843457)
        ·
          refine ⟨36054859261257108221132593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48073145681676144294843457 36054859261257108221132593)
          ·
            refine ⟨27041144445942831165849445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36054859261257108221132593 27041144445942831165849445)
            ·
              refine ⟨5070214583614280843596771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27041144445942831165849445 5070214583614280843596771)
              ·
                refine ⟨7605321875421421265395157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070214583614280843596771 7605321875421421265395157)
                ·
                  refine ⟨178249731455189560907699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7605321875421421265395157 178249731455189560907699)
                  ·
                    rfl

theorem cell23_3124261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_3124261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124261 prefixEnd_3124261 := by exact prefixLift 3124261
  have htrace : WordTrace (prefixWord ++ tailWord_3124261) baseStart_3124261 baseEnd_3124261 := by
    simpa [prefixWord, tailWord_3124261, baseEnd_3124261] using wordTrace_append hprefix tailTrace_3124261
  have hstable : (prefixWord ++ tailWord_3124261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124261).length < 2 ^ (prefixWord ++ tailWord_3124261).sum := by decide
  have hdescent : baseEnd_3124261 < baseStart_3124261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124272 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 2, 2, 2]
def baseStart_3124272 : Nat := 118140960795 + 3124272 * 2 ^ 59
def prefixEnd_3124272 : Nat := 4983230072969 + 3 ^ 40 * 3124272 * 2
def baseEnd_3124272 : Nat := 1604253231383905505131741

theorem tailTrace_3124272 : CollatzResearch.WordTrace tailWord_3124272 prefixEnd_3124272 1604253231383905505131741 := by
  unfold tailWord_3124272
  simp only [CollatzResearch.WordTrace]
  refine ⟨56975780668651801010991535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75967707558202401347988713 56975780668651801010991535)
  ·
    refine ⟨85463671002977701516487303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56975780668651801010991535 85463671002977701516487303)
    ·
      refine ⟨128195506504466552274730955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85463671002977701516487303 128195506504466552274730955)
      ·
        refine ⟨192293259756699828412096433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128195506504466552274730955 192293259756699828412096433)
        ·
          refine ⟨144219944817524871309072325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192293259756699828412096433 144219944817524871309072325)
          ·
            refine ⟨27041239653285913370451061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144219944817524871309072325 27041239653285913370451061)
            ·
              refine ⟨2535116217495554378479787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27041239653285913370451061 2535116217495554378479787)
              ·
                refine ⟨3802674326243331567719681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535116217495554378479787 3802674326243331567719681)
                ·
                  refine ⟨2852005744682498675789761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3802674326243331567719681 2852005744682498675789761)
                  ·
                    refine ⟨2139004308511874006842321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2852005744682498675789761 2139004308511874006842321)
                    ·
                      refine ⟨1604253231383905505131741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139004308511874006842321 1604253231383905505131741)
                      ·
                        rfl

theorem cell23_3124272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 2, 2, 2].length) (baseStart_3124272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124272 prefixEnd_3124272 := by exact prefixLift 3124272
  have htrace : WordTrace (prefixWord ++ tailWord_3124272) baseStart_3124272 baseEnd_3124272 := by
    simpa [prefixWord, tailWord_3124272, baseEnd_3124272] using wordTrace_append hprefix tailTrace_3124272
  have hstable : (prefixWord ++ tailWord_3124272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124272).length < 2 ^ (prefixWord ++ tailWord_3124272).sum := by decide
  have hdescent : baseEnd_3124272 < baseStart_3124272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124278 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_3124278 : Nat := 118140960795 + 3124278 * 2 ^ 59
def prefixEnd_3124278 : Nat := 4983230072969 + 3 ^ 40 * 3124278 * 2
def baseEnd_3124278 : Nat := 178250701363092497961857

theorem tailTrace_3124278 : CollatzResearch.WordTrace tailWord_3124278 prefixEnd_3124278 178250701363092497961857 := by
  unfold tailWord_3124278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121986260955116565418843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75967853450187910031134325 7121986260955116565418843)
  ·
    refine ⟨10682979391432674848128265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7121986260955116565418843 10682979391432674848128265)
    ·
      refine ⟨8012234543574506136096199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10682979391432674848128265 8012234543574506136096199)
      ·
        refine ⟨12018351815361759204144299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8012234543574506136096199 12018351815361759204144299)
        ·
          refine ⟨18027527723042638806216449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12018351815361759204144299 18027527723042638806216449)
          ·
            refine ⟨13520645792281979104662337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18027527723042638806216449 13520645792281979104662337)
            ·
              refine ⟨10140484344211484328496753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13520645792281979104662337 10140484344211484328496753)
              ·
                refine ⟨7605363258158613246372565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10140484344211484328496753 7605363258158613246372565)
                ·
                  refine ⟨178250701363092497961857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7605363258158613246372565 178250701363092497961857)
                  ·
                    rfl

theorem cell23_3124278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_3124278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124278 prefixEnd_3124278 := by exact prefixLift 3124278
  have htrace : WordTrace (prefixWord ++ tailWord_3124278) baseStart_3124278 baseEnd_3124278 := by
    simpa [prefixWord, tailWord_3124278, baseEnd_3124278] using wordTrace_append hprefix tailTrace_3124278
  have hstable : (prefixWord ++ tailWord_3124278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124278).length < 2 ^ (prefixWord ++ tailWord_3124278).sum := by decide
  have hdescent : baseEnd_3124278 < baseStart_3124278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124291 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 2, 5]
def baseStart_3124291 : Nat := 118140960795 + 3124291 * 2 ^ 59
def prefixEnd_3124291 : Nat := 4983230072969 + 3 ^ 40 * 3124291 * 2
def baseEnd_3124291 : Nat := 534754329172113643598051

theorem tailTrace_3124291 : CollatzResearch.WordTrace tailWord_3124291 prefixEnd_3124291 534754329172113643598051 := by
  unfold tailWord_3124291
  simp only [CollatzResearch.WordTrace]
  refine ⟨113952254324234768266924727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75968169549489845511283151 113952254324234768266924727)
  ·
    refine ⟨170928381486352152400387091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113952254324234768266924727 170928381486352152400387091)
    ·
      refine ⟨256392572229528228600580637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170928381486352152400387091 256392572229528228600580637)
      ·
        refine ⟨96147214586073085725217739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256392572229528228600580637 96147214586073085725217739)
        ·
          refine ⟨144220821879109628587826609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96147214586073085725217739 144220821879109628587826609)
          ·
            refine ⟨108165616409332221440869957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144220821879109628587826609 108165616409332221440869957)
            ·
              refine ⟨20281053076749791520163117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108165616409332221440869957 20281053076749791520163117)
              ·
                refine ⟨7605394903781171820061169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20281053076749791520163117 7605394903781171820061169)
                ·
                  refine ⟨5704046177835878865045877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7605394903781171820061169 5704046177835878865045877)
                  ·
                    refine ⟨534754329172113643598051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5704046177835878865045877 534754329172113643598051)
                    ·
                      rfl

theorem cell23_3124291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 5].length) (baseStart_3124291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124291 prefixEnd_3124291 := by exact prefixLift 3124291
  have htrace : WordTrace (prefixWord ++ tailWord_3124291) baseStart_3124291 baseEnd_3124291 := by
    simpa [prefixWord, tailWord_3124291, baseEnd_3124291] using wordTrace_append hprefix tailTrace_3124291
  have hstable : (prefixWord ++ tailWord_3124291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124291).length < 2 ^ (prefixWord ++ tailWord_3124291).sum := by decide
  have hdescent : baseEnd_3124291 < baseStart_3124291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124295 : List Nat := [1, 1, 4, 1, 3, 4, 1, 3, 5]
def baseStart_3124295 : Nat := 118140960795 + 3124295 * 2 ^ 59
def prefixEnd_3124295 : Nat := 4983230072969 + 3 ^ 40 * 3124295 * 2
def baseEnd_3124295 : Nat := 178251671270995435016015

theorem tailTrace_3124295 : CollatzResearch.WordTrace tailWord_3124295 prefixEnd_3124295 178251671270995435016015 := by
  unfold tailWord_3124295
  simp only [CollatzResearch.WordTrace]
  refine ⟨113952400216220276950070339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75968266810813517966713559 113952400216220276950070339)
  ·
    refine ⟨170928600324330415425105509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113952400216220276950070339 170928600324330415425105509)
    ·
      refine ⟨32049112560811952892207283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170928600324330415425105509 32049112560811952892207283)
      ·
        refine ⟨48073668841217929338310925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32049112560811952892207283 48073668841217929338310925)
        ·
          refine ⟨18027625815456723501866597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48073668841217929338310925 18027625815456723501866597)
          ·
            refine ⟨3380179840398135656599987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18027625815456723501866597 3380179840398135656599987)
            ·
              refine ⟨5070269760597203484899981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380179840398135656599987 5070269760597203484899981)
              ·
                refine ⟨1901351160223951306837493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5070269760597203484899981 1901351160223951306837493)
                ·
                  refine ⟨178251671270995435016015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1901351160223951306837493 178251671270995435016015)
                  ·
                    rfl

theorem cell23_3124295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 5].length) (baseStart_3124295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124295 prefixEnd_3124295 := by exact prefixLift 3124295
  have htrace : WordTrace (prefixWord ++ tailWord_3124295) baseStart_3124295 baseEnd_3124295 := by
    simpa [prefixWord, tailWord_3124295, baseEnd_3124295] using wordTrace_append hprefix tailTrace_3124295
  have hstable : (prefixWord ++ tailWord_3124295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124295).length < 2 ^ (prefixWord ++ tailWord_3124295).sum := by decide
  have hdescent : baseEnd_3124295 < baseStart_3124295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124338 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_3124338 : Nat := 118140960795 + 3124338 * 2 ^ 59
def prefixEnd_3124338 : Nat := 4983230072969 + 3 ^ 40 * 3124338 * 2
def baseEnd_3124338 : Nat := 534762373702367415635479

theorem tailTrace_3124338 : CollatzResearch.WordTrace tailWord_3124338 prefixEnd_3124338 534762373702367415635479 := by
  unfold tailWord_3124338
  simp only [CollatzResearch.WordTrace]
  refine ⟨28488492138766123823471417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75969312370042996862590445 28488492138766123823471417)
  ·
    refine ⟨21366369104074592867603563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28488492138766123823471417 21366369104074592867603563)
    ·
      refine ⟨32049553656111889301405345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21366369104074592867603563 32049553656111889301405345)
      ·
        refine ⟨24037165242083916976054009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32049553656111889301405345 24037165242083916976054009)
        ·
          refine ⟨18027873931562937732040507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24037165242083916976054009 18027873931562937732040507)
          ·
            refine ⟨27041810897344406598060761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18027873931562937732040507 27041810897344406598060761)
            ·
              refine ⟨20281358173008304948545571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27041810897344406598060761 20281358173008304948545571)
              ·
                refine ⟨30422037259512457422818357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20281358173008304948545571 30422037259512457422818357)
                ·
                  refine ⟨2852065993079292883389221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30422037259512457422818357 2852065993079292883389221)
                  ·
                    refine ⟨534762373702367415635479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2852065993079292883389221 534762373702367415635479)
                    ·
                      rfl

theorem cell23_3124338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_3124338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124338 prefixEnd_3124338 := by exact prefixLift 3124338
  have htrace : WordTrace (prefixWord ++ tailWord_3124338) baseStart_3124338 baseEnd_3124338 := by
    simpa [prefixWord, tailWord_3124338, baseEnd_3124338] using wordTrace_append hprefix tailTrace_3124338
  have hstable : (prefixWord ++ tailWord_3124338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124338).length < 2 ^ (prefixWord ++ tailWord_3124338).sum := by decide
  have hdescent : baseEnd_3124338 < baseStart_3124338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124345 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 4]
def baseStart_3124345 : Nat := 118140960795 + 3124345 * 2 ^ 59
def prefixEnd_3124345 : Nat := 4983230072969 + 3 ^ 40 * 3124345 * 2
def baseEnd_3124345 : Nat := 1604290715471683719518905

theorem tailTrace_3124345 : CollatzResearch.WordTrace tailWord_3124345 prefixEnd_3124345 1604290715471683719518905 := by
  unfold tailWord_3124345
  simp only [CollatzResearch.WordTrace]
  refine ⟨113954223866039135489390489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75969482577359423659593659 113954223866039135489390489)
  ·
    refine ⟨85465667899529351617042867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113954223866039135489390489 85465667899529351617042867)
    ·
      refine ⟨128198501849294027425564301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85465667899529351617042867 128198501849294027425564301)
      ·
        refine ⟨48074438193485260284586613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128198501849294027425564301 48074438193485260284586613)
        ·
          refine ⟨4506978580639243151679995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48074438193485260284586613 4506978580639243151679995)
          ·
            refine ⟨6760467870958864727519993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506978580639243151679995 6760467870958864727519993)
            ·
              refine ⟨5070350903219148545639995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6760467870958864727519993 5070350903219148545639995)
              ·
                refine ⟨7605526354828722818459993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5070350903219148545639995 7605526354828722818459993)
                ·
                  refine ⟨5704144766121542113844995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7605526354828722818459993 5704144766121542113844995)
                  ·
                    refine ⟨8556217149182313170767493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5704144766121542113844995 8556217149182313170767493)
                    ·
                      refine ⟨1604290715471683719518905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8556217149182313170767493 1604290715471683719518905)
                      ·
                        rfl

theorem cell23_3124345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_3124345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124345 prefixEnd_3124345 := by exact prefixLift 3124345
  have htrace : WordTrace (prefixWord ++ tailWord_3124345) baseStart_3124345 baseEnd_3124345 := by
    simpa [prefixWord, tailWord_3124345, baseEnd_3124345] using wordTrace_append hprefix tailTrace_3124345
  have hstable : (prefixWord ++ tailWord_3124345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124345).length < 2 ^ (prefixWord ++ tailWord_3124345).sum := by decide
  have hdescent : baseEnd_3124345 < baseStart_3124345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124355 : List Nat := [1, 1, 1, 3, 3, 2, 2, 5, 1, 4]
def baseStart_3124355 : Nat := 118140960795 + 3124355 * 2 ^ 59
def prefixEnd_3124355 : Nat := 4983230072969 + 3 ^ 40 * 3124355 * 2
def baseEnd_3124355 : Nat := 534765283426076226797953

theorem tailTrace_3124355 : CollatzResearch.WordTrace tailWord_3124355 prefixEnd_3124355 534765283426076226797953 := by
  unfold tailWord_3124355
  simp only [CollatzResearch.WordTrace]
  refine ⟨113954588596002907197254519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75969725730668604798169679 113954588596002907197254519)
  ·
    refine ⟨170931882894004360795881779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113954588596002907197254519 170931882894004360795881779)
    ·
      refine ⟨256397824341006541193822669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170931882894004360795881779 256397824341006541193822669)
      ·
        refine ⟨96149184127877452947683501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256397824341006541193822669 96149184127877452947683501)
        ·
          refine ⟨36055944047954044855381313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96149184127877452947683501 36055944047954044855381313)
          ·
            refine ⟨27041958035965533641535985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36055944047954044855381313 27041958035965533641535985)
            ·
              refine ⟨20281468526974150231151989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27041958035965533641535985 20281468526974150231151989)
              ·
                refine ⟨1901387674403826584170499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20281468526974150231151989 1901387674403826584170499)
                ·
                  refine ⟨2852081511605739876255749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901387674403826584170499 2852081511605739876255749)
                  ·
                    refine ⟨534765283426076226797953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2852081511605739876255749 534765283426076226797953)
                    ·
                      rfl

theorem cell23_3124355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 1, 4].length) (baseStart_3124355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124355 prefixEnd_3124355 := by exact prefixLift 3124355
  have htrace : WordTrace (prefixWord ++ tailWord_3124355) baseStart_3124355 baseEnd_3124355 := by
    simpa [prefixWord, tailWord_3124355, baseEnd_3124355] using wordTrace_append hprefix tailTrace_3124355
  have hstable : (prefixWord ++ tailWord_3124355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124355).length < 2 ^ (prefixWord ++ tailWord_3124355).sum := by decide
  have hdescent : baseEnd_3124355 < baseStart_3124355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124411 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 3, 6]
def baseStart_3124411 : Nat := 118140960795 + 3124411 * 2 ^ 59
def prefixEnd_3124411 : Nat := 4983230072969 + 3 ^ 40 * 3124411 * 2
def baseEnd_3124411 : Nat := 534774868398293487097867

theorem tailTrace_3124411 : CollatzResearch.WordTrace tailWord_3124411 prefixEnd_3124411 534774868398293487097867 := by
  unfold tailWord_3124411
  simp only [CollatzResearch.WordTrace]
  refine ⟨113956631083800028761293087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75971087389200019174195391 113956631083800028761293087)
  ·
    refine ⟨170934946625700043141939631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113956631083800028761293087 170934946625700043141939631)
    ·
      refine ⟨256402419938550064712909447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170934946625700043141939631 256402419938550064712909447)
      ·
        refine ⟨384603629907825097069364171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256402419938550064712909447 384603629907825097069364171)
        ·
          refine ⟨576905444861737645604046257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384603629907825097069364171 576905444861737645604046257)
          ·
            refine ⟨432679083646303234203034693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576905444861737645604046257 432679083646303234203034693)
            ·
              refine ⟨81127328183681856413069005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 432679083646303234203034693 81127328183681856413069005)
              ·
                refine ⟨30422748068880696154900877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81127328183681856413069005 30422748068880696154900877)
                ·
                  refine ⟨11408530525830261058087829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30422748068880696154900877 11408530525830261058087829)
                  ·
                    refine ⟨534774868398293487097867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11408530525830261058087829 534774868398293487097867)
                    ·
                      rfl

theorem cell23_3124411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 6].length) (baseStart_3124411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124411 prefixEnd_3124411 := by exact prefixLift 3124411
  have htrace : WordTrace (prefixWord ++ tailWord_3124411) baseStart_3124411 baseEnd_3124411 := by
    simpa [prefixWord, tailWord_3124411, baseEnd_3124411] using wordTrace_append hprefix tailTrace_3124411
  have hstable : (prefixWord ++ tailWord_3124411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124411).length < 2 ^ (prefixWord ++ tailWord_3124411).sum := by decide
  have hdescent : baseEnd_3124411 < baseStart_3124411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124415 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 1, 5]
def baseStart_3124415 : Nat := 118140960795 + 3124415 * 2 ^ 59
def prefixEnd_3124415 : Nat := 4983230072969 + 3 ^ 40 * 3124415 * 2
def baseEnd_3124415 : Nat := 534775553039166148547861

theorem tailTrace_3124415 : CollatzResearch.WordTrace tailWord_3124415 prefixEnd_3124415 534775553039166148547861 := by
  unfold tailWord_3124415
  simp only [CollatzResearch.WordTrace]
  refine ⟨113956776975785537444438699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75971184650523691629625799 113956776975785537444438699)
  ·
    refine ⟨170935165463678306166658049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113956776975785537444438699 170935165463678306166658049)
    ·
      refine ⟨128201374097758729624993537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170935165463678306166658049 128201374097758729624993537)
      ·
        refine ⟨96151030573319047218745153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128201374097758729624993537 96151030573319047218745153)
        ·
          refine ⟨72113272929989285414058865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96151030573319047218745153 72113272929989285414058865)
          ·
            refine ⟨54084954697491964060544149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72113272929989285414058865 54084954697491964060544149)
            ·
              refine ⟨2535232251444935815338007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54084954697491964060544149 2535232251444935815338007)
              ·
                refine ⟨3802848377167403723007011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535232251444935815338007 3802848377167403723007011)
                ·
                  refine ⟨5704272565751105584510517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802848377167403723007011 5704272565751105584510517)
                  ·
                    refine ⟨534775553039166148547861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5704272565751105584510517 534775553039166148547861)
                    ·
                      rfl

theorem cell23_3124415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 5].length) (baseStart_3124415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124415 prefixEnd_3124415 := by exact prefixLift 3124415
  have htrace : WordTrace (prefixWord ++ tailWord_3124415) baseStart_3124415 baseEnd_3124415 := by
    simpa [prefixWord, tailWord_3124415, baseEnd_3124415] using wordTrace_append hprefix tailTrace_3124415
  have hstable : (prefixWord ++ tailWord_3124415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124415).length < 2 ^ (prefixWord ++ tailWord_3124415).sum := by decide
  have hdescent : baseEnd_3124415 < baseStart_3124415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124435 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 7, 2, 2]
def baseStart_3124435 : Nat := 118140960795 + 3124435 * 2 ^ 59
def prefixEnd_3124435 : Nat := 4983230072969 + 3 ^ 40 * 3124435 * 2
def baseEnd_3124435 : Nat := 1604336928730588367393491

theorem tailTrace_3124435 : CollatzResearch.WordTrace tailWord_3124435 prefixEnd_3124435 1604336928730588367393491 := by
  unfold tailWord_3124435
  simp only [CollatzResearch.WordTrace]
  refine ⟨113957506435713080860166759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75971670957142053906777839 113957506435713080860166759)
  ·
    refine ⟨170936259653569621290250139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113957506435713080860166759 170936259653569621290250139)
    ·
      refine ⟨256404389480354431935375209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170936259653569621290250139 256404389480354431935375209)
      ·
        refine ⟨192303292110265823951531407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256404389480354431935375209 192303292110265823951531407)
        ·
          refine ⟨288454938165398735927297111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192303292110265823951531407 288454938165398735927297111)
          ·
            refine ⟨432682407248098103890945667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288454938165398735927297111 432682407248098103890945667)
            ·
              refine ⟨649023610872147155836418501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432682407248098103890945667 649023610872147155836418501)
              ·
                refine ⟨121691927038527591719328469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649023610872147155836418501 121691927038527591719328469)
                ·
                  refine ⟨2852154539965490430921761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 121691927038527591719328469 2852154539965490430921761)
                  ·
                    refine ⟨2139115904974117823191321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2852154539965490430921761 2139115904974117823191321)
                    ·
                      refine ⟨1604336928730588367393491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139115904974117823191321 1604336928730588367393491)
                      ·
                        rfl

theorem cell23_3124435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 2, 2].length) (baseStart_3124435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124435 prefixEnd_3124435 := by exact prefixLift 3124435
  have htrace : WordTrace (prefixWord ++ tailWord_3124435) baseStart_3124435 baseEnd_3124435 := by
    simpa [prefixWord, tailWord_3124435, baseEnd_3124435] using wordTrace_append hprefix tailTrace_3124435
  have hstable : (prefixWord ++ tailWord_3124435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124435).length < 2 ^ (prefixWord ++ tailWord_3124435).sum := by decide
  have hdescent : baseEnd_3124435 < baseStart_3124435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124441 : List Nat := [1, 2, 1, 2, 3, 1, 1, 12]
def baseStart_3124441 : Nat := 118140960795 + 3124441 * 2 ^ 59
def prefixEnd_3124441 : Nat := 4983230072969 + 3 ^ 40 * 3124441 * 2
def baseEnd_3124441 : Nat := 59420000356093160885869

theorem tailTrace_3124441 : CollatzResearch.WordTrace tailWord_3124441 prefixEnd_3124441 59420000356093160885869 := by
  unfold tailWord_3124441
  simp only [CollatzResearch.WordTrace]
  refine ⟨113957725273691343884885177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75971816849127562589923451 113957725273691343884885177)
  ·
    refine ⟨85468293955268507913663883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113957725273691343884885177 85468293955268507913663883)
    ·
      refine ⟨128202440932902761870495825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85468293955268507913663883 128202440932902761870495825)
      ·
        refine ⟨96151830699677071402871869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128202440932902761870495825 96151830699677071402871869)
        ·
          refine ⟨36056936512378901776076951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96151830699677071402871869 36056936512378901776076951)
          ·
            refine ⟨54085404768568352664115427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36056936512378901776076951 54085404768568352664115427)
            ·
              refine ⟨81128107152852528996173141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54085404768568352664115427 81128107152852528996173141)
              ·
                refine ⟨59420000356093160885869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 81128107152852528996173141 59420000356093160885869)
                ·
                  rfl

theorem cell23_3124441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 12].length) (baseStart_3124441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124441 prefixEnd_3124441 := by exact prefixLift 3124441
  have htrace : WordTrace (prefixWord ++ tailWord_3124441) baseStart_3124441 baseEnd_3124441 := by
    simpa [prefixWord, tailWord_3124441, baseEnd_3124441] using wordTrace_append hprefix tailTrace_3124441
  have hstable : (prefixWord ++ tailWord_3124441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124441).length < 2 ^ (prefixWord ++ tailWord_3124441).sum := by decide
  have hdescent : baseEnd_3124441 < baseStart_3124441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124448 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 6]
def baseStart_3124448 : Nat := 118140960795 + 3124448 * 2 ^ 59
def prefixEnd_3124448 : Nat := 4983230072969 + 3 ^ 40 * 3124448 * 2
def baseEnd_3124448 : Nat := 1604343603979096816530931

theorem tailTrace_3124448 : CollatzResearch.WordTrace tailWord_3124448 prefixEnd_3124448 1604343603979096816530931 := by
  unfold tailWord_3124448
  simp only [CollatzResearch.WordTrace]
  refine ⟨56978990292332992040194999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75971987056443989386926665 56978990292332992040194999)
  ·
    refine ⟨85468485438499488060292499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56978990292332992040194999 85468485438499488060292499)
    ·
      refine ⟨128202728157749232090438749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85468485438499488060292499 128202728157749232090438749)
      ·
        refine ⟨48076023059155962033914531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128202728157749232090438749 48076023059155962033914531)
        ·
          refine ⟨72114034588733943050871797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48076023059155962033914531 72114034588733943050871797)
          ·
            refine ⟨6760690742693807161019231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72114034588733943050871797 6760690742693807161019231)
            ·
              refine ⟨10141036114040710741528847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760690742693807161019231 10141036114040710741528847)
              ·
                refine ⟨15211554171061066112293271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10141036114040710741528847 15211554171061066112293271)
                ·
                  refine ⟨22817331256591599168439907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15211554171061066112293271 22817331256591599168439907)
                  ·
                    refine ⟨34225996884887398752659861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22817331256591599168439907 34225996884887398752659861)
                    ·
                      refine ⟨1604343603979096816530931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34225996884887398752659861 1604343603979096816530931)
                      ·
                        rfl

theorem cell23_3124448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_3124448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124448 prefixEnd_3124448 := by exact prefixLift 3124448
  have htrace : WordTrace (prefixWord ++ tailWord_3124448) baseStart_3124448 baseEnd_3124448 := by
    simpa [prefixWord, tailWord_3124448, baseEnd_3124448] using wordTrace_append hprefix tailTrace_3124448
  have hstable : (prefixWord ++ tailWord_3124448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124448).length < 2 ^ (prefixWord ++ tailWord_3124448).sum := by decide
  have hdescent : baseEnd_3124448 < baseStart_3124448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124452 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 3, 2, 2]
def baseStart_3124452 : Nat := 118140960795 + 3124452 * 2 ^ 59
def prefixEnd_3124452 : Nat := 4983230072969 + 3 ^ 40 * 3124452 * 2
def baseEnd_3124452 : Nat := 1604345657901714800880913

theorem tailTrace_3124452 : CollatzResearch.WordTrace tailWord_3124452 prefixEnd_3124452 1604345657901714800880913 := by
  unfold tailWord_3124452
  simp only [CollatzResearch.WordTrace]
  refine ⟨56979063238325746381767805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75972084317767661842357073 56979063238325746381767805)
  ·
    refine ⟨21367148714372154893162927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56979063238325746381767805 21367148714372154893162927)
    ·
      refine ⟨32050723071558232339744391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21367148714372154893162927 32050723071558232339744391)
      ·
        refine ⟨48076084607337348509616587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32050723071558232339744391 48076084607337348509616587)
        ·
          refine ⟨72114126911006022764424881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48076084607337348509616587 72114126911006022764424881)
          ·
            refine ⟨54085595183254517073318661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72114126911006022764424881 54085595183254517073318661)
            ·
              refine ⟨10141049096860221951247249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54085595183254517073318661 10141049096860221951247249)
              ·
                refine ⟨7605786822645166463435437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10141049096860221951247249 7605786822645166463435437)
                ·
                  refine ⟨2852170058491937423788289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7605786822645166463435437 2852170058491937423788289)
                  ·
                    refine ⟨2139127543868953067841217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2852170058491937423788289 2139127543868953067841217)
                    ·
                      refine ⟨1604345657901714800880913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139127543868953067841217 1604345657901714800880913)
                      ·
                        rfl

theorem cell23_3124452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_3124452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124452 prefixEnd_3124452 := by exact prefixLift 3124452
  have htrace : WordTrace (prefixWord ++ tailWord_3124452) baseStart_3124452 baseEnd_3124452 := by
    simpa [prefixWord, tailWord_3124452, baseEnd_3124452] using wordTrace_append hprefix tailTrace_3124452
  have hstable : (prefixWord ++ tailWord_3124452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124452).length < 2 ^ (prefixWord ++ tailWord_3124452).sum := by decide
  have hdescent : baseEnd_3124452 < baseStart_3124452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124458 : List Nat := [3, 1, 3, 1, 1, 4, 1, 9]
def baseStart_3124458 : Nat := 118140960795 + 3124458 * 2 ^ 59
def prefixEnd_3124458 : Nat := 4983230072969 + 3 ^ 40 * 3124458 * 2
def baseEnd_3124458 : Nat := 59420323658727473237255

theorem tailTrace_3124458 : CollatzResearch.WordTrace tailWord_3124458 prefixEnd_3124458 59420323658727473237255 := by
  unfold tailWord_3124458
  simp only [CollatzResearch.WordTrace]
  refine ⟨28489586328657438947063507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75972230209753170525502685 28489586328657438947063507)
  ·
    refine ⟨42734379492986158420595261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28489586328657438947063507 42734379492986158420595261)
    ·
      refine ⟨16025392309869809407723223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42734379492986158420595261 16025392309869809407723223)
      ·
        refine ⟨24038088464804714111584835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16025392309869809407723223 24038088464804714111584835)
        ·
          refine ⟨36057132697207071167377253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24038088464804714111584835 36057132697207071167377253)
          ·
            refine ⟨6760712380726325843883235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36057132697207071167377253 6760712380726325843883235)
            ·
              refine ⟨10141068571089488765824853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760712380726325843883235 10141068571089488765824853)
              ·
                refine ⟨59420323658727473237255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10141068571089488765824853 59420323658727473237255)
                ·
                  rfl

theorem cell23_3124458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 9].length) (baseStart_3124458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124458 prefixEnd_3124458 := by exact prefixLift 3124458
  have htrace : WordTrace (prefixWord ++ tailWord_3124458) baseStart_3124458 baseEnd_3124458 := by
    simpa [prefixWord, tailWord_3124458, baseEnd_3124458] using wordTrace_append hprefix tailTrace_3124458
  have hstable : (prefixWord ++ tailWord_3124458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124458).length < 2 ^ (prefixWord ++ tailWord_3124458).sum := by decide
  have hdescent : baseEnd_3124458 < baseStart_3124458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124485 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 4, 1, 3]
def baseStart_3124485 : Nat := 118140960795 + 3124485 * 2 ^ 59
def prefixEnd_3124485 : Nat := 4983230072969 + 3 ^ 40 * 3124485 * 2
def baseEnd_3124485 : Nat := 1604362602763313171768261

theorem tailTrace_3124485 : CollatzResearch.WordTrace tailWord_3124485 prefixEnd_3124485 1604362602763313171768261 := by
  unfold tailWord_3124485
  simp only [CollatzResearch.WordTrace]
  refine ⟨113959330085531939399486909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75972886723687959599657939 113959330085531939399486909)
  ·
    refine ⟨42734748782074477274807591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113959330085531939399486909 42734748782074477274807591)
    ·
      refine ⟨64102123173111715912211387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42734748782074477274807591 64102123173111715912211387)
      ·
        refine ⟨96153184759667573868317081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64102123173111715912211387 96153184759667573868317081)
        ·
          refine ⟨72114888569750680401237811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96153184759667573868317081 72114888569750680401237811)
          ·
            refine ⟨108172332854626020601856717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72114888569750680401237811 108172332854626020601856717)
            ·
              refine ⟨40564624820484757725696269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108172332854626020601856717 40564624820484757725696269)
              ·
                refine ⟨15211734307681784147136101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40564624820484757725696269 15211734307681784147136101)
                ·
                  refine ⟨2852200182690334527588019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15211734307681784147136101 2852200182690334527588019)
                  ·
                    refine ⟨4278300274035501791382029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2852200182690334527588019 4278300274035501791382029)
                    ·
                      refine ⟨1604362602763313171768261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4278300274035501791382029 1604362602763313171768261)
                      ·
                        rfl

theorem cell23_3124485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_3124485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124485 prefixEnd_3124485 := by exact prefixLift 3124485
  have htrace : WordTrace (prefixWord ++ tailWord_3124485) baseStart_3124485 baseEnd_3124485 := by
    simpa [prefixWord, tailWord_3124485, baseEnd_3124485] using wordTrace_append hprefix tailTrace_3124485
  have hstable : (prefixWord ++ tailWord_3124485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124485).length < 2 ^ (prefixWord ++ tailWord_3124485).sum := by decide
  have hdescent : baseEnd_3124485 < baseStart_3124485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124528 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_3124528 : Nat := 118140960795 + 3124528 * 2 ^ 59
def prefixEnd_3124528 : Nat := 4983230072969 + 3 ^ 40 * 3124528 * 2
def baseEnd_3124528 : Nat := 1604384682431456503530563

theorem tailTrace_3124528 : CollatzResearch.WordTrace tailWord_3124528 prefixEnd_3124528 1604384682431456503530563 := by
  unfold tailWord_3124528
  simp only [CollatzResearch.WordTrace]
  refine ⟨56980449212188078871651119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75973932282917438495534825 56980449212188078871651119)
  ·
    refine ⟨85470673818282118307476679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56980449212188078871651119 85470673818282118307476679)
    ·
      refine ⟨128206010727423177461215019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85470673818282118307476679 128206010727423177461215019)
      ·
        refine ⟨192309016091134766191822529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128206010727423177461215019 192309016091134766191822529)
        ·
          refine ⟨144231762068351074643866897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192309016091134766191822529 144231762068351074643866897)
          ·
            refine ⟨108173821551263305982900173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144231762068351074643866897 108173821551263305982900173)
            ·
              refine ⟨40565183081723739743587565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108173821551263305982900173 40565183081723739743587565)
              ·
                refine ⟨15211943655646402403845337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40565183081723739743587565 15211943655646402403845337)
                ·
                  refine ⟨11408957741734801802884003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15211943655646402403845337 11408957741734801802884003)
                  ·
                    refine ⟨17113436612602202704326005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11408957741734801802884003 17113436612602202704326005)
                    ·
                      refine ⟨1604384682431456503530563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17113436612602202704326005 1604384682431456503530563)
                      ·
                        rfl

theorem cell23_3124528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_3124528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124528 prefixEnd_3124528 := by exact prefixLift 3124528
  have htrace : WordTrace (prefixWord ++ tailWord_3124528) baseStart_3124528 baseEnd_3124528 := by
    simpa [prefixWord, tailWord_3124528, baseEnd_3124528] using wordTrace_append hprefix tailTrace_3124528
  have hstable : (prefixWord ++ tailWord_3124528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124528).length < 2 ^ (prefixWord ++ tailWord_3124528).sum := by decide
  have hdescent : baseEnd_3124528 < baseStart_3124528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124542 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_3124542 : Nat := 118140960795 + 3124542 * 2 ^ 59
def prefixEnd_3124542 : Nat := 4983230072969 + 3 ^ 40 * 3124542 * 2
def baseEnd_3124542 : Nat := 1604391871160619448755499

theorem tailTrace_3124542 : CollatzResearch.WordTrace tailWord_3124542 prefixEnd_3124542 1604391871160619448755499 := by
  unfold tailWord_3124542
  simp only [CollatzResearch.WordTrace]
  refine ⟨14245176130790679766788985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75974272697550292089541253 14245176130790679766788985)
  ·
    refine ⟨10683882098093009825091739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14245176130790679766788985 10683882098093009825091739)
    ·
      refine ⟨16025823147139514737637609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10683882098093009825091739 16025823147139514737637609)
      ·
        refine ⟨12019367360354636053228207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16025823147139514737637609 12019367360354636053228207)
        ·
          refine ⟨18029051040531954079842311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12019367360354636053228207 18029051040531954079842311)
          ·
            refine ⟨27043576560797931119763467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18029051040531954079842311 27043576560797931119763467)
            ·
              refine ⟨40565364841196896679645201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27043576560797931119763467 40565364841196896679645201)
              ·
                refine ⟨30424023630897672509733901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40565364841196896679645201 30424023630897672509733901)
                ·
                  refine ⟨11409008861586627191150213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30424023630897672509733901 11409008861586627191150213)
                  ·
                    refine ⟨2139189161547492598340665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11409008861586627191150213 2139189161547492598340665)
                    ·
                      refine ⟨1604391871160619448755499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139189161547492598340665 1604391871160619448755499)
                      ·
                        rfl

theorem cell23_3124542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_3124542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124542 prefixEnd_3124542 := by exact prefixLift 3124542
  have htrace : WordTrace (prefixWord ++ tailWord_3124542) baseStart_3124542 baseEnd_3124542 := by
    simpa [prefixWord, tailWord_3124542, baseEnd_3124542] using wordTrace_append hprefix tailTrace_3124542
  have hstable : (prefixWord ++ tailWord_3124542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124542).length < 2 ^ (prefixWord ++ tailWord_3124542).sum := by decide
  have hdescent : baseEnd_3124542 < baseStart_3124542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124565 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 7]
def baseStart_3124565 : Nat := 118140960795 + 3124565 * 2 ^ 59
def prefixEnd_3124565 : Nat := 4983230072969 + 3 ^ 40 * 3124565 * 2
def baseEnd_3124565 : Nat := 178267075690630317640877

theorem tailTrace_3124565 : CollatzResearch.WordTrace tailWord_3124565 prefixEnd_3124565 178267075690630317640877 := by
  unfold tailWord_3124565
  simp only [CollatzResearch.WordTrace]
  refine ⟨113962247925242113062399149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75974831950161408708266099 113962247925242113062399149)
  ·
    refine ⟨42735842971965792398399681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113962247925242113062399149 42735842971965792398399681)
    ·
      refine ⟨32051882228974344298799761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42735842971965792398399681 32051882228974344298799761)
      ·
        refine ⟨24038911671730758224099821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32051882228974344298799761 24038911671730758224099821)
        ·
          refine ⟨9014591876899034334037433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24038911671730758224099821 9014591876899034334037433)
          ·
            refine ⟨6760943907674275750528075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9014591876899034334037433 6760943907674275750528075)
            ·
              refine ⟨10141415861511413625792113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760943907674275750528075 10141415861511413625792113)
              ·
                refine ⟨7606061896133560219344085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10141415861511413625792113 7606061896133560219344085)
                ·
                  refine ⟨178267075690630317640877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7606061896133560219344085 178267075690630317640877)
                  ·
                    rfl

theorem cell23_3124565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_3124565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124565 prefixEnd_3124565 := by exact prefixLift 3124565
  have htrace : WordTrace (prefixWord ++ tailWord_3124565) baseStart_3124565 baseEnd_3124565 := by
    simpa [prefixWord, tailWord_3124565, baseEnd_3124565] using wordTrace_append hprefix tailTrace_3124565
  have hstable : (prefixWord ++ tailWord_3124565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124565).length < 2 ^ (prefixWord ++ tailWord_3124565).sum := by decide
  have hdescent : baseEnd_3124565 < baseStart_3124565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124585 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 1, 7, 2]
def baseStart_3124585 : Nat := 118140960795 + 3124585 * 2 ^ 59
def prefixEnd_3124585 : Nat := 4983230072969 + 3 ^ 40 * 3124585 * 2
def baseEnd_3124585 : Nat := 1604413950828762780517801

theorem tailTrace_3124585 : CollatzResearch.WordTrace tailWord_3124585 prefixEnd_3124585 1604413950828762780517801 := by
  unfold tailWord_3124585
  simp only [CollatzResearch.WordTrace]
  refine ⟨113962977385169656478127209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75975318256779770985418139 113962977385169656478127209)
  ·
    refine ⟨85472233038877242358595407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113962977385169656478127209 85472233038877242358595407)
    ·
      refine ⟨128208349558315863537893111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85472233038877242358595407 128208349558315863537893111)
      ·
        refine ⟨192312524337473795306839667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128208349558315863537893111 192312524337473795306839667)
        ·
          refine ⟨288468786506210692960259501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192312524337473795306839667 288468786506210692960259501)
          ·
            refine ⟨108175794939829009860097313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288468786506210692960259501 108175794939829009860097313)
            ·
              refine ⟨81131846204871757395072985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108175794939829009860097313 81131846204871757395072985)
              ·
                refine ⟨60848884653653818046304739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81131846204871757395072985 60848884653653818046304739)
                ·
                  refine ⟨91273326980480727069457109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60848884653653818046304739 91273326980480727069457109)
                  ·
                    refine ⟨2139218601105017040690401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 91273326980480727069457109 2139218601105017040690401)
                    ·
                      refine ⟨1604413950828762780517801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139218601105017040690401 1604413950828762780517801)
                      ·
                        rfl

theorem cell23_3124585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 7, 2].length) (baseStart_3124585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124585 prefixEnd_3124585 := by exact prefixLift 3124585
  have htrace : WordTrace (prefixWord ++ tailWord_3124585) baseStart_3124585 baseEnd_3124585 := by
    simpa [prefixWord, tailWord_3124585, baseEnd_3124585] using wordTrace_append hprefix tailTrace_3124585
  have hstable : (prefixWord ++ tailWord_3124585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124585).length < 2 ^ (prefixWord ++ tailWord_3124585).sum := by decide
  have hdescent : baseEnd_3124585 < baseStart_3124585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124610 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_3124610 : Nat := 118140960795 + 3124610 * 2 ^ 59
def prefixEnd_3124610 : Nat := 4983230072969 + 3 ^ 40 * 3124610 * 2
def baseEnd_3124610 : Nat := 1604426787845125182705187

theorem tailTrace_3124610 : CollatzResearch.WordTrace tailWord_3124610 prefixEnd_3124610 1604426787845125182705187 := by
  unfold tailWord_3124610
  simp only [CollatzResearch.WordTrace]
  refine ⟨28490972302519771436946821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75975926140052723831858189 28490972302519771436946821)
  ·
    refine ⟨5342057306722457144427529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28490972302519771436946821 5342057306722457144427529)
    ·
      refine ⟨4006542980041842858320647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5342057306722457144427529 4006542980041842858320647)
      ·
        refine ⟨6009814470062764287480971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4006542980041842858320647 6009814470062764287480971)
        ·
          refine ⟨9014721705094146431221457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6009814470062764287480971 9014721705094146431221457)
          ·
            refine ⟨6761041278820609823416093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9014721705094146431221457 6761041278820609823416093)
            ·
              refine ⟨2535390479557728683781035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6761041278820609823416093 2535390479557728683781035)
              ·
                refine ⟨3803085719336593025671553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535390479557728683781035 3803085719336593025671553)
                ·
                  refine ⟨2852314289502444769253665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3803085719336593025671553 2852314289502444769253665)
                  ·
                    refine ⟨2139235717126833576940249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2852314289502444769253665 2139235717126833576940249)
                    ·
                      refine ⟨1604426787845125182705187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139235717126833576940249 1604426787845125182705187)
                      ·
                        rfl

theorem cell23_3124610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_3124610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124610 prefixEnd_3124610 := by exact prefixLift 3124610
  have htrace : WordTrace (prefixWord ++ tailWord_3124610) baseStart_3124610 baseEnd_3124610 := by
    simpa [prefixWord, tailWord_3124610, baseEnd_3124610] using wordTrace_append hprefix tailTrace_3124610
  have hstable : (prefixWord ++ tailWord_3124610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124610).length < 2 ^ (prefixWord ++ tailWord_3124610).sum := by decide
  have hdescent : baseEnd_3124610 < baseStart_3124610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124615 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_3124615 : Nat := 118140960795 + 3124615 * 2 ^ 59
def prefixEnd_3124615 : Nat := 4983230072969 + 3 ^ 40 * 3124615 * 2
def baseEnd_3124615 : Nat := 1604429355248397663142663

theorem tailTrace_3124615 : CollatzResearch.WordTrace tailWord_3124615 prefixEnd_3124615 1604429355248397663142663 := by
  unfold tailWord_3124615
  simp only [CollatzResearch.WordTrace]
  refine ⟨113964071575060971601719299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75976047716707314401146199 113964071575060971601719299)
  ·
    refine ⟨170946107362591457402578949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113964071575060971601719299 170946107362591457402578949)
    ·
      refine ⟨32052395130485898262983553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170946107362591457402578949 32052395130485898262983553)
      ·
        refine ⟨24039296347864423697237665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32052395130485898262983553 24039296347864423697237665)
        ·
          refine ⟨18029472260898317772928249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24039296347864423697237665 18029472260898317772928249)
          ·
            refine ⟨13522104195673738329696187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18029472260898317772928249 13522104195673738329696187)
            ·
              refine ⟨20283156293510607494544281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13522104195673738329696187 20283156293510607494544281)
              ·
                refine ⟨15212367220132955620908211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20283156293510607494544281 15212367220132955620908211)
                ·
                  refine ⟨22818550830199433431362317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15212367220132955620908211 22818550830199433431362317)
                  ·
                    refine ⟨8556956561324787536760869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22818550830199433431362317 8556956561324787536760869)
                    ·
                      refine ⟨1604429355248397663142663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8556956561324787536760869 1604429355248397663142663)
                      ·
                        rfl

theorem cell23_3124615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_3124615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124615 prefixEnd_3124615 := by exact prefixLift 3124615
  have htrace : WordTrace (prefixWord ++ tailWord_3124615) baseStart_3124615 baseEnd_3124615 := by
    simpa [prefixWord, tailWord_3124615, baseEnd_3124615] using wordTrace_append hprefix tailTrace_3124615
  have hstable : (prefixWord ++ tailWord_3124615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124615).length < 2 ^ (prefixWord ++ tailWord_3124615).sum := by decide
  have hdescent : baseEnd_3124615 < baseStart_3124615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124672 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 6]
def baseStart_3124672 : Nat := 118140960795 + 3124672 * 2 ^ 59
def prefixEnd_3124672 : Nat := 4983230072969 + 3 ^ 40 * 3124672 * 2
def baseEnd_3124672 : Nat := 178273180405078215569989

theorem tailTrace_3124672 : CollatzResearch.WordTrace tailWord_3124672 prefixEnd_3124672 178273180405078215569989 := by
  unfold tailWord_3124672
  simp only [CollatzResearch.WordTrace]
  refine ⟨56983075267927235168272135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75977433690569646891029513 56983075267927235168272135)
  ·
    refine ⟨85474612901890852752408203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56983075267927235168272135 85474612901890852752408203)
    ·
      refine ⟨128211919352836279128612305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85474612901890852752408203 128211919352836279128612305)
      ·
        refine ⟨96158939514627209346459229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128211919352836279128612305 96158939514627209346459229)
        ·
          refine ⟨36059602317985203504922211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96158939514627209346459229 36059602317985203504922211)
          ·
            refine ⟨54089403476977805257383317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36059602317985203504922211 54089403476977805257383317)
            ·
              refine ⟨2535440787983334621439843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54089403476977805257383317 2535440787983334621439843)
              ·
                refine ⟨3803161181975001932159765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535440787983334621439843 3803161181975001932159765)
                ·
                  refine ⟨178273180405078215569989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3803161181975001932159765 178273180405078215569989)
                  ·
                    rfl

theorem cell23_3124672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 6].length) (baseStart_3124672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124672 prefixEnd_3124672 := by exact prefixLift 3124672
  have htrace : WordTrace (prefixWord ++ tailWord_3124672) baseStart_3124672 baseEnd_3124672 := by
    simpa [prefixWord, tailWord_3124672, baseEnd_3124672] using wordTrace_append hprefix tailTrace_3124672
  have hstable : (prefixWord ++ tailWord_3124672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124672).length < 2 ^ (prefixWord ++ tailWord_3124672).sum := by decide
  have hdescent : baseEnd_3124672 < baseStart_3124672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124789 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_3124789 : Nat := 118140960795 + 3124789 * 2 ^ 59
def prefixEnd_3124789 : Nat := 4983230072969 + 3 ^ 40 * 3124789 * 2
def baseEnd_3124789 : Nat := 1604518700882279982366863

theorem tailTrace_3124789 : CollatzResearch.WordTrace tailWord_3124789 prefixEnd_3124789 1604518700882279982366863 := by
  unfold tailWord_3124789
  simp only [CollatzResearch.WordTrace]
  refine ⟨113970417876430599318553421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75980278584287066212368947 113970417876430599318553421)
  ·
    refine ⟨42738906703661474744457533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113970417876430599318553421 42738906703661474744457533)
    ·
      refine ⟨16027090013873053029171575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42738906703661474744457533 16027090013873053029171575)
      ·
        refine ⟨24040635020809579543757363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16027090013873053029171575 24040635020809579543757363)
        ·
          refine ⟨36060952531214369315636045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24040635020809579543757363 36060952531214369315636045)
          ·
            refine ⟨13522857199205388493363517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36060952531214369315636045 13522857199205388493363517)
            ·
              refine ⟨5071071449702020685011319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13522857199205388493363517 5071071449702020685011319)
              ·
                refine ⟨7606607174553031027516979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071071449702020685011319 7606607174553031027516979)
                ·
                  refine ⟨11409910761829546541275469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7606607174553031027516979 11409910761829546541275469)
                  ·
                    refine ⟨4278716535686079952978301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11409910761829546541275469 4278716535686079952978301)
                    ·
                      refine ⟨1604518700882279982366863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4278716535686079952978301 1604518700882279982366863)
                      ·
                        rfl

theorem cell23_3124789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_3124789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124789 prefixEnd_3124789 := by exact prefixLift 3124789
  have htrace : WordTrace (prefixWord ++ tailWord_3124789) baseStart_3124789 baseEnd_3124789 := by
    simpa [prefixWord, tailWord_3124789, baseEnd_3124789] using wordTrace_append hprefix tailTrace_3124789
  have hstable : (prefixWord ++ tailWord_3124789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124789).length < 2 ^ (prefixWord ++ tailWord_3124789).sum := by decide
  have hdescent : baseEnd_3124789 < baseStart_3124789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124796 : List Nat := [2, 2, 2, 2, 5, 1, 2, 7]
def baseStart_3124796 : Nat := 118140960795 + 3124796 * 2 ^ 59
def prefixEnd_3124796 : Nat := 4983230072969 + 3 ^ 40 * 3124796 * 2
def baseEnd_3124796 : Nat := 59426751675809683517753

theorem tailTrace_3124796 : CollatzResearch.WordTrace tailWord_3124796 prefixEnd_3124796 59426751675809683517753 := by
  unfold tailWord_3124796
  simp only [CollatzResearch.WordTrace]
  refine ⟨56985336593702619757029121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75980448791603493009372161 56985336593702619757029121)
  ·
    refine ⟨42739002445276964817771841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56985336593702619757029121 42739002445276964817771841)
    ·
      refine ⟨32054251833957723613328881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42739002445276964817771841 32054251833957723613328881)
      ·
        refine ⟨24040688875468292709996661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32054251833957723613328881 24040688875468292709996661)
        ·
          refine ⟨2253814582075152441562187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24040688875468292709996661 2253814582075152441562187)
          ·
            refine ⟨3380721873112728662343281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253814582075152441562187 3380721873112728662343281)
            ·
              refine ⟨2535541404834546496757461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3380721873112728662343281 2535541404834546496757461)
              ·
                refine ⟨59426751675809683517753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2535541404834546496757461 59426751675809683517753)
                ·
                  rfl

theorem cell23_3124796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 7].length) (baseStart_3124796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124796 prefixEnd_3124796 := by exact prefixLift 3124796
  have htrace : WordTrace (prefixWord ++ tailWord_3124796) baseStart_3124796 baseEnd_3124796 := by
    simpa [prefixWord, tailWord_3124796, baseEnd_3124796] using wordTrace_append hprefix tailTrace_3124796
  have hstable : (prefixWord ++ tailWord_3124796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124796).length < 2 ^ (prefixWord ++ tailWord_3124796).sum := by decide
  have hdescent : baseEnd_3124796 < baseStart_3124796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124807 : List Nat := [1, 1, 4, 1, 6, 1, 1, 3, 1, 2, 2]
def baseStart_3124807 : Nat := 118140960795 + 3124807 * 2 ^ 59
def prefixEnd_3124807 : Nat := 4983230072969 + 3 ^ 40 * 3124807 * 2
def baseEnd_3124807 : Nat := 1604527943534060911941781

theorem tailTrace_3124807 : CollatzResearch.WordTrace tailWord_3124807 prefixEnd_3124807 1604527943534060911941781 := by
  unfold tailWord_3124807
  simp only [CollatzResearch.WordTrace]
  refine ⟨113971074390365388392708675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75980716260243592261805783 113971074390365388392708675)
  ·
    refine ⟨170956611585548082589063013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113971074390365388392708675 170956611585548082589063013)
    ·
      refine ⟨32054364672290265485449315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170956611585548082589063013 32054364672290265485449315)
      ·
        refine ⟨48081547008435398228173973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32054364672290265485449315 48081547008435398228173973)
        ·
          refine ⟨2253822516020409291945655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48081547008435398228173973 2253822516020409291945655)
          ·
            refine ⟨3380733774030613937918483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253822516020409291945655 3380733774030613937918483)
            ·
              refine ⟨5071100661045920906877725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380733774030613937918483 5071100661045920906877725)
              ·
                refine ⟨1901662747892220340079147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5071100661045920906877725 1901662747892220340079147)
                ·
                  refine ⟨2852494121838330510118721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901662747892220340079147 2852494121838330510118721)
                  ·
                    refine ⟨2139370591378747882589041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2852494121838330510118721 2139370591378747882589041)
                    ·
                      refine ⟨1604527943534060911941781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139370591378747882589041 1604527943534060911941781)
                      ·
                        rfl

theorem cell23_3124807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_3124807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124807 prefixEnd_3124807 := by exact prefixLift 3124807
  have htrace : WordTrace (prefixWord ++ tailWord_3124807) baseStart_3124807 baseEnd_3124807 := by
    simpa [prefixWord, tailWord_3124807, baseEnd_3124807] using wordTrace_append hprefix tailTrace_3124807
  have hstable : (prefixWord ++ tailWord_3124807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124807).length < 2 ^ (prefixWord ++ tailWord_3124807).sum := by decide
  have hdescent : baseEnd_3124807 < baseStart_3124807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124832 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 3]
def baseStart_3124832 : Nat := 118140960795 + 3124832 * 2 ^ 59
def prefixEnd_3124832 : Nat := 4983230072969 + 3 ^ 40 * 3124832 * 2
def baseEnd_3124832 : Nat := 1604540780550423314129165

theorem tailTrace_3124832 : CollatzResearch.WordTrace tailWord_3124832 prefixEnd_3124832 1604540780550423314129165 := by
  unfold tailWord_3124832
  simp only [CollatzResearch.WordTrace]
  refine ⟨56985993107637408831184375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75981324143516545108245833 56985993107637408831184375)
  ·
    refine ⟨85478989661456113246776563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56985993107637408831184375 85478989661456113246776563)
    ·
      refine ⟨128218484492184169870164845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85478989661456113246776563 128218484492184169870164845)
      ·
        refine ⟨48081931684569063701311817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128218484492184169870164845 48081931684569063701311817)
        ·
          refine ⟨36061448763426797775983863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48081931684569063701311817 36061448763426797775983863)
          ·
            refine ⟨54092173145140196663975795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36061448763426797775983863 54092173145140196663975795)
            ·
              refine ⟨81138259717710294995963693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54092173145140196663975795 81138259717710294995963693)
              ·
                refine ⟨30426847394141360623486385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81138259717710294995963693 30426847394141360623486385)
                ·
                  refine ⟨22820135545606020467614789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30426847394141360623486385 22820135545606020467614789)
                  ·
                    refine ⟨4278775414801128837677773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22820135545606020467614789 4278775414801128837677773)
                    ·
                      refine ⟨1604540780550423314129165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4278775414801128837677773 1604540780550423314129165)
                      ·
                        rfl

theorem cell23_3124832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_3124832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124832 prefixEnd_3124832 := by exact prefixLift 3124832
  have htrace : WordTrace (prefixWord ++ tailWord_3124832) baseStart_3124832 baseEnd_3124832 := by
    simpa [prefixWord, tailWord_3124832, baseEnd_3124832] using wordTrace_append hprefix tailTrace_3124832
  have hstable : (prefixWord ++ tailWord_3124832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124832).length < 2 ^ (prefixWord ++ tailWord_3124832).sum := by decide
  have hdescent : baseEnd_3124832 < baseStart_3124832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124840 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_3124840 : Nat := 118140960795 + 3124840 * 2 ^ 59
def prefixEnd_3124840 : Nat := 4983230072969 + 3 ^ 40 * 3124840 * 2
def baseEnd_3124840 : Nat := 1604544888395659282829129

theorem tailTrace_3124840 : CollatzResearch.WordTrace tailWord_3124840 prefixEnd_3124840 1604544888395659282829129 := by
  unfold tailWord_3124840
  simp only [CollatzResearch.WordTrace]
  refine ⟨56986138999622917514329987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75981518666163890019106649 56986138999622917514329987)
  ·
    refine ⟨85479208499434376271494981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56986138999622917514329987 85479208499434376271494981)
    ·
      refine ⟨16027351593643945550905309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85479208499434376271494981 16027351593643945550905309)
      ·
        refine ⟨6010256847616479581589491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16027351593643945550905309 6010256847616479581589491)
        ·
          refine ⟨9015385271424719372384237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6010256847616479581589491 9015385271424719372384237)
          ·
            refine ⟨3380769476784269764644089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9015385271424719372384237 3380769476784269764644089)
            ·
              refine ⟨2535577107588202323483067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3380769476784269764644089 2535577107588202323483067)
              ·
                refine ⟨3803365661382303485224601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535577107588202323483067 3803365661382303485224601)
                ·
                  refine ⟨2852524246036727613918451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3803365661382303485224601 2852524246036727613918451)
                  ·
                    refine ⟨4278786369055091420877677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2852524246036727613918451 4278786369055091420877677)
                    ·
                      refine ⟨1604544888395659282829129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4278786369055091420877677 1604544888395659282829129)
                      ·
                        rfl

theorem cell23_3124840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_3124840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124840 prefixEnd_3124840 := by exact prefixLift 3124840
  have htrace : WordTrace (prefixWord ++ tailWord_3124840) baseStart_3124840 baseEnd_3124840 := by
    simpa [prefixWord, tailWord_3124840, baseEnd_3124840] using wordTrace_append hprefix tailTrace_3124840
  have hstable : (prefixWord ++ tailWord_3124840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124840).length < 2 ^ (prefixWord ++ tailWord_3124840).sum := by decide
  have hdescent : baseEnd_3124840 < baseStart_3124840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124869 : List Nat := [1, 3, 1, 1, 4, 1, 2, 5, 5]
def baseStart_3124869 : Nat := 118140960795 + 3124869 * 2 ^ 59
def prefixEnd_3124869 : Nat := 4983230072969 + 3 ^ 40 * 3124869 * 2
def baseEnd_3124869 : Nat := 178284419926071074374055

theorem tailTrace_3124869 : CollatzResearch.WordTrace tailWord_3124869 prefixEnd_3124869 178284419926071074374055 := by
  unfold tailWord_3124869
  simp only [CollatzResearch.WordTrace]
  refine ⟨113973335716140772981465661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75982223810760515320977107 113973335716140772981465661)
  ·
    refine ⟨42740000893552789868049623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113973335716140772981465661 42740000893552789868049623)
    ·
      refine ⟨64110001340329184802074435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42740000893552789868049623 64110001340329184802074435)
      ·
        refine ⟨96165002010493777203111653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64110001340329184802074435 96165002010493777203111653)
        ·
          refine ⟨18030937876967583225583435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96165002010493777203111653 18030937876967583225583435)
          ·
            refine ⟨27046406815451374838375153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18030937876967583225583435 27046406815451374838375153)
            ·
              refine ⟨20284805111588531128781365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27046406815451374838375153 20284805111588531128781365)
              ·
                refine ⟨1901700479211424793323253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20284805111588531128781365 1901700479211424793323253)
                ·
                  refine ⟨178284419926071074374055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1901700479211424793323253 178284419926071074374055)
                  ·
                    rfl

theorem cell23_3124869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_3124869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124869 prefixEnd_3124869 := by exact prefixLift 3124869
  have htrace : WordTrace (prefixWord ++ tailWord_3124869) baseStart_3124869 baseEnd_3124869 := by
    simpa [prefixWord, tailWord_3124869, baseEnd_3124869] using wordTrace_append hprefix tailTrace_3124869
  have hstable : (prefixWord ++ tailWord_3124869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124869).length < 2 ^ (prefixWord ++ tailWord_3124869).sum := by decide
  have hdescent : baseEnd_3124869 < baseStart_3124869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124919 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_3124919 : Nat := 118140960795 + 3124919 * 2 ^ 59
def prefixEnd_3124919 : Nat := 4983230072969 + 3 ^ 40 * 3124919 * 2
def baseEnd_3124919 : Nat := 1604585453367364473741265

theorem tailTrace_3124919 : CollatzResearch.WordTrace tailWord_3124919 prefixEnd_3124919 1604585453367364473741265 := by
  unfold tailWord_3124919
  simp only [CollatzResearch.WordTrace]
  refine ⟨113975159365959631520785811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75983439577306421013857207 113975159365959631520785811)
  ·
    refine ⟨170962739048939447281178717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113975159365959631520785811 170962739048939447281178717)
    ·
      refine ⟨64111027143352292730442019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170962739048939447281178717 64111027143352292730442019)
      ·
        refine ⟨96166540715028439095663029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64111027143352292730442019 96166540715028439095663029)
        ·
          refine ⟨9015613192033916165218409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96166540715028439095663029 9015613192033916165218409)
          ·
            refine ⟨6761709894025437123913807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9015613192033916165218409 6761709894025437123913807)
            ·
              refine ⟨10142564841038155685870711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6761709894025437123913807 10142564841038155685870711)
              ·
                refine ⟨15213847261557233528806067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10142564841038155685870711 15213847261557233528806067)
                ·
                  refine ⟨22820770892335850293209101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15213847261557233528806067 22820770892335850293209101)
                  ·
                    refine ⟨8557789084625943859953413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22820770892335850293209101 8557789084625943859953413)
                    ·
                      refine ⟨1604585453367364473741265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8557789084625943859953413 1604585453367364473741265)
                      ·
                        rfl

theorem cell23_3124919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_3124919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124919 prefixEnd_3124919 := by exact prefixLift 3124919
  have htrace : WordTrace (prefixWord ++ tailWord_3124919) baseStart_3124919 baseEnd_3124919 := by
    simpa [prefixWord, tailWord_3124919, baseEnd_3124919] using wordTrace_append hprefix tailTrace_3124919
  have hstable : (prefixWord ++ tailWord_3124919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124919).length < 2 ^ (prefixWord ++ tailWord_3124919).sum := by decide
  have hdescent : baseEnd_3124919 < baseStart_3124919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124939 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 3]
def baseStart_3124939 : Nat := 118140960795 + 3124939 * 2 ^ 59
def prefixEnd_3124939 : Nat := 4983230072969 + 3 ^ 40 * 3124939 * 2
def baseEnd_3124939 : Nat := 1604595722980454395491173

theorem tailTrace_3124939 : CollatzResearch.WordTrace tailWord_3124939 prefixEnd_3124939 1604595722980454395491173 := by
  unfold tailWord_3124939
  simp only [CollatzResearch.WordTrace]
  refine ⟨113975888825887174936513871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75983925883924783291009247 113975888825887174936513871)
  ·
    refine ⟨170963833238830762404770807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113975888825887174936513871 170963833238830762404770807)
    ·
      refine ⟨256445749858246143607156211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170963833238830762404770807 256445749858246143607156211)
      ·
        refine ⟨384668624787369215410734317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256445749858246143607156211 384668624787369215410734317)
        ·
          refine ⟨144250734295263455779025369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384668624787369215410734317 144250734295263455779025369)
          ·
            refine ⟨108188050721447591834269027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144250734295263455779025369 108188050721447591834269027)
            ·
              refine ⟨162282076082171387751403541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108188050721447591834269027 162282076082171387751403541)
              ·
                refine ⟨7606972316351783800847041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162282076082171387751403541 7606972316351783800847041)
                ·
                  refine ⟨5705229237263837850635281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7606972316351783800847041 5705229237263837850635281)
                  ·
                    refine ⟨4278921927947878387976461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5705229237263837850635281 4278921927947878387976461)
                    ·
                      refine ⟨1604595722980454395491173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4278921927947878387976461 1604595722980454395491173)
                      ·
                        rfl

theorem cell23_3124939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 3].length) (baseStart_3124939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124939 prefixEnd_3124939 := by exact prefixLift 3124939
  have htrace : WordTrace (prefixWord ++ tailWord_3124939) baseStart_3124939 baseEnd_3124939 := by
    simpa [prefixWord, tailWord_3124939, baseEnd_3124939] using wordTrace_append hprefix tailTrace_3124939
  have hstable : (prefixWord ++ tailWord_3124939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124939).length < 2 ^ (prefixWord ++ tailWord_3124939).sum := by decide
  have hdescent : baseEnd_3124939 < baseStart_3124939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3124946 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_3124946 : Nat := 118140960795 + 3124946 * 2 ^ 59
def prefixEnd_3124946 : Nat := 4983230072969 + 3 ^ 40 * 3124946 * 2
def baseEnd_3124946 : Nat := 534866439115011956034547

theorem tailTrace_3124946 : CollatzResearch.WordTrace tailWord_3124946 prefixEnd_3124946 534866439115011956034547 := by
  unfold tailWord_3124946
  simp only [CollatzResearch.WordTrace]
  refine ⟨28494036034215453783004673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75984096091241210088012461 28494036034215453783004673)
  ·
    refine ⟨21370527025661590337253505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28494036034215453783004673 21370527025661590337253505)
    ·
      refine ⟨16027895269246192752940129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21370527025661590337253505 16027895269246192752940129)
      ·
        refine ⟨12020921451934644564705097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16027895269246192752940129 12020921451934644564705097)
        ·
          refine ⟨9015691088950983423528823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12020921451934644564705097 9015691088950983423528823)
          ·
            refine ⟨13523536633426475135293235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9015691088950983423528823 13523536633426475135293235)
            ·
              refine ⟨20285304950139712702939853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13523536633426475135293235 20285304950139712702939853)
              ·
                refine ⟨7606989356302392263602445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20285304950139712702939853 7606989356302392263602445)
                ·
                  refine ⟨2852621008613397098850917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7606989356302392263602445 2852621008613397098850917)
                  ·
                    refine ⟨534866439115011956034547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2852621008613397098850917 534866439115011956034547)
                    ·
                      rfl

theorem cell23_3124946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_3124946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3124946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3124946 prefixEnd_3124946 := by exact prefixLift 3124946
  have htrace : WordTrace (prefixWord ++ tailWord_3124946) baseStart_3124946 baseEnd_3124946 := by
    simpa [prefixWord, tailWord_3124946, baseEnd_3124946] using wordTrace_append hprefix tailTrace_3124946
  have hstable : (prefixWord ++ tailWord_3124946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3124946).length < 2 ^ (prefixWord ++ tailWord_3124946).sum := by decide
  have hdescent : baseEnd_3124946 < baseStart_3124946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3124946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125003 : List Nat := [1, 1, 1, 1, 5, 1, 2, 6, 1, 1, 3]
def baseStart_3125003 : Nat := 118140960795 + 3125003 * 2 ^ 59
def prefixEnd_3125003 : Nat := 4983230072969 + 3 ^ 40 * 3125003 * 2
def baseEnd_3125003 : Nat := 1604628585742342145090879

theorem tailTrace_3125003 : CollatzResearch.WordTrace tailWord_3125003 prefixEnd_3125003 1604628585742342145090879 := by
  unfold tailWord_3125003
  simp only [CollatzResearch.WordTrace]
  refine ⟨113978223097655313866843663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75985482065103542577895775 113978223097655313866843663)
  ·
    refine ⟨170967334646482970800265495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113978223097655313866843663 170967334646482970800265495)
    ·
      refine ⟨256451001969724456200398243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170967334646482970800265495 256451001969724456200398243)
      ·
        refine ⟨384676502954586684300597365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256451001969724456200398243 384676502954586684300597365)
        ·
          refine ⟨36063422151992501653181003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 384676502954586684300597365 36063422151992501653181003)
          ·
            refine ⟨54095133227988752479771505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36063422151992501653181003 54095133227988752479771505)
            ·
              refine ⟨40571349920991564359828629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54095133227988752479771505 40571349920991564359828629)
              ·
                refine ⟨1901782027546479579366967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40571349920991564359828629 1901782027546479579366967)
                ·
                  refine ⟨2852673041319719369050451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901782027546479579366967 2852673041319719369050451)
                  ·
                    refine ⟨4279009561979579053575677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2852673041319719369050451 4279009561979579053575677)
                    ·
                      refine ⟨1604628585742342145090879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4279009561979579053575677 1604628585742342145090879)
                      ·
                        rfl

theorem cell23_3125003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 1, 1, 3].length) (baseStart_3125003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125003 prefixEnd_3125003 := by exact prefixLift 3125003
  have htrace : WordTrace (prefixWord ++ tailWord_3125003) baseStart_3125003 baseEnd_3125003 := by
    simpa [prefixWord, tailWord_3125003, baseEnd_3125003] using wordTrace_append hprefix tailTrace_3125003
  have hstable : (prefixWord ++ tailWord_3125003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125003).length < 2 ^ (prefixWord ++ tailWord_3125003).sum := by decide
  have hdescent : baseEnd_3125003 < baseStart_3125003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125009 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_3125009 : Nat := 118140960795 + 3125009 * 2 ^ 59
def prefixEnd_3125009 : Nat := 4983230072969 + 3 ^ 40 * 3125009 * 2
def baseEnd_3125009 : Nat := 1604631666626269121615851

theorem tailTrace_3125009 : CollatzResearch.WordTrace tailWord_3125009 prefixEnd_3125009 1604631666626269121615851 := by
  unfold tailWord_3125009
  simp only [CollatzResearch.WordTrace]
  refine ⟨113978441935633576891562081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75985627957089051261041387 113978441935633576891562081)
  ·
    refine ⟨85483831451725182668671561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113978441935633576891562081 85483831451725182668671561)
    ·
      refine ⟨64112873588793887001503671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85483831451725182668671561 64112873588793887001503671)
      ·
        refine ⟨96169310383190830502255507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64112873588793887001503671 96169310383190830502255507)
        ·
          refine ⟨144253965574786245753383261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96169310383190830502255507 144253965574786245753383261)
          ·
            refine ⟨54095237090544842157518723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144253965574786245753383261 54095237090544842157518723)
            ·
              refine ⟨81142855635817263236278085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54095237090544842157518723 81142855635817263236278085)
              ·
                refine ⟨15214285431715736856802141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81142855635817263236278085 15214285431715736856802141)
                ·
                  refine ⟨5705357036893401321300803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15214285431715736856802141 5705357036893401321300803)
                  ·
                    refine ⟨8558035555340101981951205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5705357036893401321300803 8558035555340101981951205)
                    ·
                      refine ⟨1604631666626269121615851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8558035555340101981951205 1604631666626269121615851)
                      ·
                        rfl

theorem cell23_3125009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_3125009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125009 prefixEnd_3125009 := by exact prefixLift 3125009
  have htrace : WordTrace (prefixWord ++ tailWord_3125009) baseStart_3125009 baseEnd_3125009 := by
    simpa [prefixWord, tailWord_3125009, baseEnd_3125009] using wordTrace_append hprefix tailTrace_3125009
  have hstable : (prefixWord ++ tailWord_3125009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125009).length < 2 ^ (prefixWord ++ tailWord_3125009).sum := by decide
  have hdescent : baseEnd_3125009 < baseStart_3125009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125010 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 6]
def baseStart_3125010 : Nat := 118140960795 + 3125010 * 2 ^ 59
def prefixEnd_3125010 : Nat := 4983230072969 + 3 ^ 40 * 3125010 * 2
def baseEnd_3125010 : Nat := 178292464456324846411483

theorem tailTrace_3125010 : CollatzResearch.WordTrace tailWord_3125010 prefixEnd_3125010 178292464456324846411483 := by
  unfold tailWord_3125010
  simp only [CollatzResearch.WordTrace]
  refine ⟨28494619602157488515587121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75985652272419969374898989 28494619602157488515587121)
  ·
    refine ⟨21370964701618116386690341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28494619602157488515587121 21370964701618116386690341)
    ·
      refine ⟨4007055881553396822504439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21370964701618116386690341 4007055881553396822504439)
      ·
        refine ⟨6010583822330095233756659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4007055881553396822504439 6010583822330095233756659)
        ·
          refine ⟨9015875733495142850634989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6010583822330095233756659 9015875733495142850634989)
          ·
            refine ⟨3380953400060678568988121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9015875733495142850634989 3380953400060678568988121)
            ·
              refine ⟨2535715050045508926741091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3380953400060678568988121 2535715050045508926741091)
              ·
                refine ⟨3803572575068263390111637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535715050045508926741091 3803572575068263390111637)
                ·
                  refine ⟨178292464456324846411483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3803572575068263390111637 178292464456324846411483)
                  ·
                    rfl

theorem cell23_3125010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_3125010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125010 prefixEnd_3125010 := by exact prefixLift 3125010
  have htrace : WordTrace (prefixWord ++ tailWord_3125010) baseStart_3125010 baseEnd_3125010 := by
    simpa [prefixWord, tailWord_3125010, baseEnd_3125010] using wordTrace_append hprefix tailTrace_3125010
  have hstable : (prefixWord ++ tailWord_3125010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125010).length < 2 ^ (prefixWord ++ tailWord_3125010).sum := by decide
  have hdescent : baseEnd_3125010 < baseStart_3125010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125026 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_3125026 : Nat := 118140960795 + 3125026 * 2 ^ 59
def prefixEnd_3125026 : Nat := 4983230072969 + 3 ^ 40 * 3125026 * 2
def baseEnd_3125026 : Nat := 1604640395797395555103273

theorem tailTrace_3125026 : CollatzResearch.WordTrace tailWord_3125026 prefixEnd_3125026 1604640395797395555103273 := by
  unfold tailWord_3125026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28494765494142997198732733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75986041317714659196620621 28494765494142997198732733)
  ·
    refine ⟨10685537060303623949524775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28494765494142997198732733 10685537060303623949524775)
    ·
      refine ⟨16028305590455435924287163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10685537060303623949524775 16028305590455435924287163)
      ·
        refine ⟨24042458385683153886430745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16028305590455435924287163 24042458385683153886430745)
        ·
          refine ⟨18031843789262365414823059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24042458385683153886430745 18031843789262365414823059)
          ·
            refine ⟨27047765683893548122234589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18031843789262365414823059 27047765683893548122234589)
            ·
              refine ⟨10142912131460080545837971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27047765683893548122234589 10142912131460080545837971)
              ·
                refine ⟨15214368197190120818756957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10142912131460080545837971 15214368197190120818756957)
                ·
                  refine ⟨5705388073946295307033859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15214368197190120818756957 5705388073946295307033859)
                  ·
                    refine ⟨8558082110919442960550789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5705388073946295307033859 8558082110919442960550789)
                    ·
                      refine ⟨1604640395797395555103273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8558082110919442960550789 1604640395797395555103273)
                      ·
                        rfl

theorem cell23_3125026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_3125026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125026 prefixEnd_3125026 := by exact prefixLift 3125026
  have htrace : WordTrace (prefixWord ++ tailWord_3125026) baseStart_3125026 baseEnd_3125026 := by
    simpa [prefixWord, tailWord_3125026, baseEnd_3125026] using wordTrace_append hprefix tailTrace_3125026
  have hstable : (prefixWord ++ tailWord_3125026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125026).length < 2 ^ (prefixWord ++ tailWord_3125026).sum := by decide
  have hdescent : baseEnd_3125026 < baseStart_3125026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125039 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 4]
def baseStart_3125039 : Nat := 118140960795 + 3125039 * 2 ^ 59
def prefixEnd_3125039 : Nat := 4983230072969 + 3 ^ 40 * 3125039 * 2
def baseEnd_3125039 : Nat := 1604647071045904004240713

theorem tailTrace_3125039 : CollatzResearch.WordTrace tailWord_3125039 prefixEnd_3125039 1604647071045904004240713 := by
  unfold tailWord_3125039
  simp only [CollatzResearch.WordTrace]
  refine ⟨113979536125524892015154171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75986357417016594676769447 113979536125524892015154171)
  ·
    refine ⟨170969304188287338022731257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113979536125524892015154171 170969304188287338022731257)
    ·
      refine ⟨128226978141215503517048443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170969304188287338022731257 128226978141215503517048443)
      ·
        refine ⟨192340467211823255275572665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128226978141215503517048443 192340467211823255275572665)
        ·
          refine ⟨144255350408867441456679499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192340467211823255275572665 144255350408867441456679499)
          ·
            refine ⟨216383025613301162185019249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144255350408867441456679499 216383025613301162185019249)
            ·
              refine ⟨162287269209975871638764437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216383025613301162185019249 162287269209975871638764437)
              ·
                refine ⟨7607215744217618983067083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162287269209975871638764437 7607215744217618983067083)
                ·
                  refine ⟨11410823616326428474600625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7607215744217618983067083 11410823616326428474600625)
                  ·
                    refine ⟨8558117712244821355950469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11410823616326428474600625 8558117712244821355950469)
                    ·
                      refine ⟨1604647071045904004240713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8558117712244821355950469 1604647071045904004240713)
                      ·
                        rfl

theorem cell23_3125039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_3125039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125039 prefixEnd_3125039 := by exact prefixLift 3125039
  have htrace : WordTrace (prefixWord ++ tailWord_3125039) baseStart_3125039 baseEnd_3125039 := by
    simpa [prefixWord, tailWord_3125039, baseEnd_3125039] using wordTrace_append hprefix tailTrace_3125039
  have hstable : (prefixWord ++ tailWord_3125039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125039).length < 2 ^ (prefixWord ++ tailWord_3125039).sum := by decide
  have hdescent : baseEnd_3125039 < baseStart_3125039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125049 : List Nat := [1, 2, 1, 7, 12]
def baseStart_3125049 : Nat := 118140960795 + 3125049 * 2 ^ 59
def prefixEnd_3125049 : Nat := 4983230072969 + 3 ^ 40 * 3125049 * 2
def baseEnd_3125049 : Nat := 2201169006656308594123

theorem tailTrace_3125049 : CollatzResearch.WordTrace tailWord_3125049 prefixEnd_3125049 2201169006656308594123 := by
  unfold tailWord_3125049
  simp only [CollatzResearch.WordTrace]
  refine ⟨113979900855488663723018201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75986600570325775815345467 113979900855488663723018201)
  ·
    refine ⟨85484925641616497792263651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113979900855488663723018201 85484925641616497792263651)
    ·
      refine ⟨128227388462424746688395477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85484925641616497792263651 128227388462424746688395477)
      ·
        refine ⟨3005329417088080000509269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 128227388462424746688395477 3005329417088080000509269)
        ·
          refine ⟨2201169006656308594123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3005329417088080000509269 2201169006656308594123)
          ·
            rfl

theorem cell23_3125049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 12].length) (baseStart_3125049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125049 prefixEnd_3125049 := by exact prefixLift 3125049
  have htrace : WordTrace (prefixWord ++ tailWord_3125049) baseStart_3125049 baseEnd_3125049 := by
    simpa [prefixWord, tailWord_3125049, baseEnd_3125049] using wordTrace_append hprefix tailTrace_3125049
  have hstable : (prefixWord ++ tailWord_3125049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125049).length < 2 ^ (prefixWord ++ tailWord_3125049).sum := by decide
  have hdescent : baseEnd_3125049 < baseStart_3125049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125053 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_3125053 : Nat := 118140960795 + 3125053 * 2 ^ 59
def prefixEnd_3125053 : Nat := 4983230072969 + 3 ^ 40 * 3125053 * 2
def baseEnd_3125053 : Nat := 534884753258355649821883

theorem tailTrace_3125053 : CollatzResearch.WordTrace tailWord_3125053 prefixEnd_3125053 534884753258355649821883 := by
  unfold tailWord_3125053
  simp only [CollatzResearch.WordTrace]
  refine ⟨113980046747474172406163813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75986697831649448270775875 113980046747474172406163813)
  ·
    refine ⟨21371258765151407326155715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113980046747474172406163813 21371258765151407326155715)
    ·
      refine ⟨32056888147727110989233573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21371258765151407326155715 32056888147727110989233573)
      ·
        refine ⟨6010666527698833310481295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32056888147727110989233573 6010666527698833310481295)
        ·
          refine ⟨9015999791548249965721943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6010666527698833310481295 9015999791548249965721943)
          ·
            refine ⟨13523999687322374948582915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9015999791548249965721943 13523999687322374948582915)
            ·
              refine ⟨20285999530983562422874373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13523999687322374948582915 20285999530983562422874373)
              ·
                refine ⟨3803624912059417954288945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20285999530983562422874373 3803624912059417954288945)
                ·
                  refine ⟨2852718684044563465716709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3803624912059417954288945 2852718684044563465716709)
                  ·
                    refine ⟨534884753258355649821883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2852718684044563465716709 534884753258355649821883)
                    ·
                      rfl

theorem cell23_3125053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_3125053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125053 prefixEnd_3125053 := by exact prefixLift 3125053
  have htrace : WordTrace (prefixWord ++ tailWord_3125053) baseStart_3125053 baseEnd_3125053 := by
    simpa [prefixWord, tailWord_3125053, baseEnd_3125053] using wordTrace_append hprefix tailTrace_3125053
  have hstable : (prefixWord ++ tailWord_3125053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125053).length < 2 ^ (prefixWord ++ tailWord_3125053).sum := by decide
  have hdescent : baseEnd_3125053 < baseStart_3125053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125054 : List Nat := [4, 2, 1, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_3125054 : Nat := 118140960795 + 3125054 * 2 ^ 59
def prefixEnd_3125054 : Nat := 4983230072969 + 3 ^ 40 * 3125054 * 2
def baseEnd_3125054 : Nat := 1604654773255721445553145

theorem tailTrace_3125054 : CollatzResearch.WordTrace tailWord_3125054 prefixEnd_3125054 1604654773255721445553145 := by
  unfold tailWord_3125054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14247510402558818697118777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75986722146980366384633477 14247510402558818697118777)
  ·
    refine ⟨10685632801919114022839083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14247510402558818697118777 10685632801919114022839083)
    ·
      refine ⟨16028449202878671034258625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10685632801919114022839083 16028449202878671034258625)
      ·
        refine ⟨12021336902159003275693969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16028449202878671034258625 12021336902159003275693969)
        ·
          refine ⟨9016002676619252456770477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12021336902159003275693969 9016002676619252456770477)
          ·
            refine ⟨3381001003732219671288929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9016002676619252456770477 3381001003732219671288929)
            ·
              refine ⟨2535750752799164753466697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3381001003732219671288929 2535750752799164753466697)
              ·
                refine ⟨1901813064599373565100023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535750752799164753466697 1901813064599373565100023)
                ·
                  refine ⟨2852719596899060347650035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1901813064599373565100023 2852719596899060347650035)
                  ·
                    refine ⟨4279079395348590521475053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2852719596899060347650035 4279079395348590521475053)
                    ·
                      refine ⟨1604654773255721445553145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4279079395348590521475053 1604654773255721445553145)
                      ·
                        rfl

theorem cell23_3125054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_3125054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125054 prefixEnd_3125054 := by exact prefixLift 3125054
  have htrace : WordTrace (prefixWord ++ tailWord_3125054) baseStart_3125054 baseEnd_3125054 := by
    simpa [prefixWord, tailWord_3125054, baseEnd_3125054] using wordTrace_append hprefix tailTrace_3125054
  have hstable : (prefixWord ++ tailWord_3125054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125054).length < 2 ^ (prefixWord ++ tailWord_3125054).sum := by decide
  have hdescent : baseEnd_3125054 < baseStart_3125054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125089 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_3125089 : Nat := 118140960795 + 3125089 * 2 ^ 59
def prefixEnd_3125089 : Nat := 4983230072969 + 3 ^ 40 * 3125089 * 2
def baseEnd_3125089 : Nat := 1604672745078628808615483

theorem tailTrace_3125089 : CollatzResearch.WordTrace tailWord_3125089 prefixEnd_3125089 1604672745078628808615483 := by
  unfold tailWord_3125089
  simp only [CollatzResearch.WordTrace]
  refine ⟨113981359775343750554474321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75987573183562500369649547 113981359775343750554474321)
  ·
    refine ⟨85486019831507812915855741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113981359775343750554474321 85486019831507812915855741)
    ·
      refine ⟨32057257436815429843445903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85486019831507812915855741 32057257436815429843445903)
      ·
        refine ⟨48085886155223144765168855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32057257436815429843445903 48085886155223144765168855)
        ·
          refine ⟨72128829232834717147753283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48085886155223144765168855 72128829232834717147753283)
          ·
            refine ⟨108193243849252075721629925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72128829232834717147753283 108193243849252075721629925)
            ·
              refine ⟨20286233221734764197805611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108193243849252075721629925 20286233221734764197805611)
              ·
                refine ⟨30429349832602146296708417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20286233221734764197805611 30429349832602146296708417)
                ·
                  refine ⟨22822012374451609722531313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30429349832602146296708417 22822012374451609722531313)
                  ·
                    refine ⟨17116509280838707291898485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22822012374451609722531313 17116509280838707291898485)
                    ·
                      refine ⟨1604672745078628808615483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17116509280838707291898485 1604672745078628808615483)
                      ·
                        rfl

theorem cell23_3125089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_3125089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125089 prefixEnd_3125089 := by exact prefixLift 3125089
  have htrace : WordTrace (prefixWord ++ tailWord_3125089) baseStart_3125089 baseEnd_3125089 := by
    simpa [prefixWord, tailWord_3125089, baseEnd_3125089] using wordTrace_append hprefix tailTrace_3125089
  have hstable : (prefixWord ++ tailWord_3125089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125089).length < 2 ^ (prefixWord ++ tailWord_3125089).sum := by decide
  have hdescent : baseEnd_3125089 < baseStart_3125089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125116 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 2, 8, 2]
def baseStart_3125116 : Nat := 118140960795 + 3125116 * 2 ^ 59
def prefixEnd_3125116 : Nat := 4983230072969 + 3 ^ 40 * 3125116 * 2
def baseEnd_3125116 : Nat := 1604686609056300202977859

theorem tailTrace_3125116 : CollatzResearch.WordTrace tailWord_3125116 prefixEnd_3125116 1604686609056300202977859 := by
  unfold tailWord_3125116
  simp only [CollatzResearch.WordTrace]
  refine ⟨56991172273122967082853601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75988229697497289443804801 56991172273122967082853601)
  ·
    refine ⟨42743379204842225312140201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56991172273122967082853601 42743379204842225312140201)
    ·
      refine ⟨32057534403631668984105151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42743379204842225312140201 32057534403631668984105151)
      ·
        refine ⟨48086301605447503476157727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32057534403631668984105151 48086301605447503476157727)
        ·
          refine ⟨72129452408171255214236591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48086301605447503476157727 72129452408171255214236591)
          ·
            refine ⟨108194178612256882821354887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72129452408171255214236591 108194178612256882821354887)
            ·
              refine ⟨162291267918385324232032331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108194178612256882821354887 162291267918385324232032331)
              ·
                refine ⟨243436901877577986348048497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162291267918385324232032331 243436901877577986348048497)
                ·
                  refine ⟨182577676408183489761036373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243436901877577986348048497 182577676408183489761036373)
                  ·
                    refine ⟨2139582145408400270637145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 182577676408183489761036373 2139582145408400270637145)
                    ·
                      refine ⟨1604686609056300202977859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139582145408400270637145 1604686609056300202977859)
                      ·
                        rfl

theorem cell23_3125116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_3125116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125116 prefixEnd_3125116 := by exact prefixLift 3125116
  have htrace : WordTrace (prefixWord ++ tailWord_3125116) baseStart_3125116 baseEnd_3125116 := by
    simpa [prefixWord, tailWord_3125116, baseEnd_3125116] using wordTrace_append hprefix tailTrace_3125116
  have hstable : (prefixWord ++ tailWord_3125116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125116).length < 2 ^ (prefixWord ++ tailWord_3125116).sum := by decide
  have hdescent : baseEnd_3125116 < baseStart_3125116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125119 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_3125119 : Nat := 118140960795 + 3125119 * 2 ^ 59
def prefixEnd_3125119 : Nat := 4983230072969 + 3 ^ 40 * 3125119 * 2
def baseEnd_3125119 : Nat := 1604688149498263691240345

theorem tailTrace_3125119 : CollatzResearch.WordTrace tailWord_3125119 prefixEnd_3125119 1604688149498263691240345 := by
  unfold tailWord_3125119
  simp only [CollatzResearch.WordTrace]
  refine ⟨113982453965235065678066411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75988302643490043785377607 113982453965235065678066411)
  ·
    refine ⟨170973680947852598517099617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113982453965235065678066411 170973680947852598517099617)
    ·
      refine ⟨128230260710889448887824713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170973680947852598517099617 128230260710889448887824713)
      ·
        refine ⟨96172695533167086665868535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128230260710889448887824713 96172695533167086665868535)
        ·
          refine ⟨144259043299750629998802803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96172695533167086665868535 144259043299750629998802803)
          ·
            refine ⟨216388564949625944998204205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144259043299750629998802803 216388564949625944998204205)
            ·
              refine ⟨81145711856109729374326577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216388564949625944998204205 81145711856109729374326577)
              ·
                refine ⟨60859283892082297030744933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81145711856109729374326577 60859283892082297030744933)
                ·
                  refine ⟨11411115729765430693264675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60859283892082297030744933 11411115729765430693264675)
                  ·
                    refine ⟨17116673594648146039897013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11411115729765430693264675 17116673594648146039897013)
                    ·
                      refine ⟨1604688149498263691240345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17116673594648146039897013 1604688149498263691240345)
                      ·
                        rfl

theorem cell23_3125119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_3125119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125119 prefixEnd_3125119 := by exact prefixLift 3125119
  have htrace : WordTrace (prefixWord ++ tailWord_3125119) baseStart_3125119 baseEnd_3125119 := by
    simpa [prefixWord, tailWord_3125119, baseEnd_3125119] using wordTrace_append hprefix tailTrace_3125119
  have hstable : (prefixWord ++ tailWord_3125119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125119).length < 2 ^ (prefixWord ++ tailWord_3125119).sum := by decide
  have hdescent : baseEnd_3125119 < baseStart_3125119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125127 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 2, 1, 3]
def baseStart_3125127 : Nat := 118140960795 + 3125127 * 2 ^ 59
def prefixEnd_3125127 : Nat := 4983230072969 + 3 ^ 40 * 3125127 * 2
def baseEnd_3125127 : Nat := 1604692257343499659940309

theorem tailTrace_3125127 : CollatzResearch.WordTrace tailWord_3125127 prefixEnd_3125127 1604692257343499659940309 := by
  unfold tailWord_3125127
  simp only [CollatzResearch.WordTrace]
  refine ⟨113982745749206083044357635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75988497166137388696238423 113982745749206083044357635)
  ·
    refine ⟨170974118623809124566536453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113982745749206083044357635 170974118623809124566536453)
    ·
      refine ⟨32057647241964210856225585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170974118623809124566536453 32057647241964210856225585)
      ·
        refine ⟨24043235431473158142169189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32057647241964210856225585 24043235431473158142169189)
        ·
          refine ⟨4508106643401217151656723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24043235431473158142169189 4508106643401217151656723)
          ·
            refine ⟨6762159965101825727485085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508106643401217151656723 6762159965101825727485085)
            ·
              refine ⟨2535809986913184647806907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6762159965101825727485085 2535809986913184647806907)
              ·
                refine ⟨3803714980369776971710361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535809986913184647806907 3803714980369776971710361)
                ·
                  refine ⟨2852786235277332728782771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3803714980369776971710361 2852786235277332728782771)
                  ·
                    refine ⟨4279179352915999093174157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2852786235277332728782771 4279179352915999093174157)
                    ·
                      refine ⟨1604692257343499659940309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4279179352915999093174157 1604692257343499659940309)
                      ·
                        rfl

theorem cell23_3125127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_3125127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125127 prefixEnd_3125127 := by exact prefixLift 3125127
  have htrace : WordTrace (prefixWord ++ tailWord_3125127) baseStart_3125127 baseEnd_3125127 := by
    simpa [prefixWord, tailWord_3125127, baseEnd_3125127] using wordTrace_append hprefix tailTrace_3125127
  have hstable : (prefixWord ++ tailWord_3125127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125127).length < 2 ^ (prefixWord ++ tailWord_3125127).sum := by decide
  have hdescent : baseEnd_3125127 < baseStart_3125127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125153 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3125153 : Nat := 118140960795 + 3125153 * 2 ^ 59
def prefixEnd_3125153 : Nat := 4983230072969 + 3 ^ 40 * 3125153 * 2
def baseEnd_3125153 : Nat := 1604705607840516558215189

theorem tailTrace_3125153 : CollatzResearch.WordTrace tailWord_3125153 prefixEnd_3125153 1604705607840516558215189 := by
  unfold tailWord_3125153
  simp only [CollatzResearch.WordTrace]
  refine ⟨113983694047111889484804113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75989129364741259656536075 113983694047111889484804113)
  ·
    refine ⟨85487770535333917113603085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113983694047111889484804113 85487770535333917113603085)
    ·
      refine ⟨32057913950750218917601157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85487770535333917113603085 32057913950750218917601157)
      ·
        refine ⟨6010858865765666047050217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32057913950750218917601157 6010858865765666047050217)
        ·
          refine ⟨4508144149324249535287663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6010858865765666047050217 4508144149324249535287663)
          ·
            refine ⟨6762216223986374302931495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508144149324249535287663 6762216223986374302931495)
            ·
              refine ⟨10143324335979561454397243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762216223986374302931495 10143324335979561454397243)
              ·
                refine ⟨15214986503969342181595865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10143324335979561454397243 15214986503969342181595865)
                ·
                  refine ⟨11411239877977006636196899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15214986503969342181595865 11411239877977006636196899)
                  ·
                    refine ⟨17116859816965509954295349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11411239877977006636196899 17116859816965509954295349)
                    ·
                      refine ⟨1604705607840516558215189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17116859816965509954295349 1604705607840516558215189)
                      ·
                        rfl

theorem cell23_3125153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3125153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125153 prefixEnd_3125153 := by exact prefixLift 3125153
  have htrace : WordTrace (prefixWord ++ tailWord_3125153) baseStart_3125153 baseEnd_3125153 := by
    simpa [prefixWord, tailWord_3125153, baseEnd_3125153] using wordTrace_append hprefix tailTrace_3125153
  have hstable : (prefixWord ++ tailWord_3125153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125153).length < 2 ^ (prefixWord ++ tailWord_3125153).sum := by decide
  have hdescent : baseEnd_3125153 < baseStart_3125153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125173 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 7]
def baseStart_3125173 : Nat := 118140960795 + 3125173 * 2 ^ 59
def prefixEnd_3125173 : Nat := 4983230072969 + 3 ^ 40 * 3125173 * 2
def baseEnd_3125173 : Nat := 178301764161511831107233

theorem tailTrace_3125173 : CollatzResearch.WordTrace tailWord_3125173 prefixEnd_3125173 178301764161511831107233 := by
  unfold tailWord_3125173
  simp only [CollatzResearch.WordTrace]
  refine ⟨113984423507039432900532173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75989615671359621933688115 113984423507039432900532173)
  ·
    refine ⟨42744158815139787337699565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113984423507039432900532173 42744158815139787337699565)
    ·
      refine ⟨16029059555677420251637337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42744158815139787337699565 16029059555677420251637337)
      ·
        refine ⟨12021794666758065188728003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16029059555677420251637337 12021794666758065188728003)
        ·
          refine ⟨18032692000137097783092005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12021794666758065188728003 18032692000137097783092005)
          ·
            refine ⟨3381129750025705834329751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18032692000137097783092005 3381129750025705834329751)
            ·
              refine ⟨5071694625038558751494627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381129750025705834329751 5071694625038558751494627)
              ·
                refine ⟨7607541937557838127241941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071694625038558751494627 7607541937557838127241941)
                ·
                  refine ⟨178301764161511831107233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7607541937557838127241941 178301764161511831107233)
                  ·
                    rfl

theorem cell23_3125173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_3125173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125173 prefixEnd_3125173 := by exact prefixLift 3125173
  have htrace : WordTrace (prefixWord ++ tailWord_3125173) baseStart_3125173 baseEnd_3125173 := by
    simpa [prefixWord, tailWord_3125173, baseEnd_3125173] using wordTrace_append hprefix tailTrace_3125173
  have hstable : (prefixWord ++ tailWord_3125173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125173).length < 2 ^ (prefixWord ++ tailWord_3125173).sum := by decide
  have hdescent : baseEnd_3125173 < baseStart_3125173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125179 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 7]
def baseStart_3125179 : Nat := 118140960795 + 3125179 * 2 ^ 59
def prefixEnd_3125179 : Nat := 4983230072969 + 3 ^ 40 * 3125179 * 2
def baseEnd_3125179 : Nat := 1604718958337533456490069

theorem tailTrace_3125179 : CollatzResearch.WordTrace tailWord_3125179 prefixEnd_3125179 1604718958337533456490069 := by
  unfold tailWord_3125179
  simp only [CollatzResearch.WordTrace]
  refine ⟨113984642345017695925250591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75989761563345130616833727 113984642345017695925250591)
  ·
    refine ⟨170976963517526543887875887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113984642345017695925250591 170976963517526543887875887)
    ·
      refine ⟨256465445276289815831813831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170976963517526543887875887 256465445276289815831813831)
      ·
        refine ⟨384698167914434723747720747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256465445276289815831813831 384698167914434723747720747)
        ·
          refine ⟨577047251871652085621581121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384698167914434723747720747 577047251871652085621581121)
          ·
            refine ⟨432785438903739064216185841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577047251871652085621581121 432785438903739064216185841)
            ·
              refine ⟨324589079177804298162139381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432785438903739064216185841 324589079177804298162139381)
              ·
                refine ⟨30430226172919152952700567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 324589079177804298162139381 30430226172919152952700567)
                ·
                  refine ⟨45645339259378729429050851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30430226172919152952700567 45645339259378729429050851)
                  ·
                    refine ⟨68468008889068094143576277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45645339259378729429050851 68468008889068094143576277)
                    ·
                      refine ⟨1604718958337533456490069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68468008889068094143576277 1604718958337533456490069)
                      ·
                        rfl

theorem cell23_3125179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_3125179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125179 prefixEnd_3125179 := by exact prefixLift 3125179
  have htrace : WordTrace (prefixWord ++ tailWord_3125179) baseStart_3125179 baseEnd_3125179 := by
    simpa [prefixWord, tailWord_3125179, baseEnd_3125179] using wordTrace_append hprefix tailTrace_3125179
  have hstable : (prefixWord ++ tailWord_3125179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125179).length < 2 ^ (prefixWord ++ tailWord_3125179).sum := by decide
  have hdescent : baseEnd_3125179 < baseStart_3125179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125226 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3125226 : Nat := 118140960795 + 3125226 * 2 ^ 59
def prefixEnd_3125226 : Nat := 4983230072969 + 3 ^ 40 * 3125226 * 2
def baseEnd_3125226 : Nat := 1604743091928294772602353

theorem tailTrace_3125226 : CollatzResearch.WordTrace tailWord_3125226 prefixEnd_3125226 1604743091928294772602353 := by
  unfold tailWord_3125226
  simp only [CollatzResearch.WordTrace]
  refine ⟨28496589143961855738052883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75990904383898281968141021 28496589143961855738052883)
  ·
    refine ⟨42744883715942783607079325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28496589143961855738052883 42744883715942783607079325)
    ·
      refine ⟨16029331393478543852654747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42744883715942783607079325 16029331393478543852654747)
      ·
        refine ⟨24043997090217815778982121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16029331393478543852654747 24043997090217815778982121)
        ·
          refine ⟨18032997817663361834236591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24043997090217815778982121 18032997817663361834236591)
          ·
            refine ⟨27049496726495042751354887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18032997817663361834236591 27049496726495042751354887)
            ·
              refine ⟨40574245089742564127032331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27049496726495042751354887 40574245089742564127032331)
              ·
                refine ⟨60861367634613846190548497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40574245089742564127032331 60861367634613846190548497)
                ·
                  refine ⟨45646025725960384642911373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60861367634613846190548497 45646025725960384642911373)
                  ·
                    refine ⟨17117259647235144241091765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45646025725960384642911373 17117259647235144241091765)
                    ·
                      refine ⟨1604743091928294772602353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17117259647235144241091765 1604743091928294772602353)
                      ·
                        rfl

theorem cell23_3125226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3125226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125226 prefixEnd_3125226 := by exact prefixLift 3125226
  have htrace : WordTrace (prefixWord ++ tailWord_3125226) baseStart_3125226 baseEnd_3125226 := by
    simpa [prefixWord, tailWord_3125226, baseEnd_3125226] using wordTrace_append hprefix tailTrace_3125226
  have hstable : (prefixWord ++ tailWord_3125226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125226).length < 2 ^ (prefixWord ++ tailWord_3125226).sum := by decide
  have hdescent : baseEnd_3125226 < baseStart_3125226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125254 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3125254 : Nat := 118140960795 + 3125254 * 2 ^ 59
def prefixEnd_3125254 : Nat := 4983230072969 + 3 ^ 40 * 3125254 * 2
def baseEnd_3125254 : Nat := 534919156462206887684075

theorem tailTrace_3125254 : CollatzResearch.WordTrace tailWord_3125254 prefixEnd_3125254 534919156462206887684075 := by
  unfold tailWord_3125254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562105556867061991694713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75991585213163989156153877 3562105556867061991694713)
  ·
    refine ⟨2671579167650296493771035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3562105556867061991694713 2671579167650296493771035)
    ·
      refine ⟨4007368751475444740656553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2671579167650296493771035 4007368751475444740656553)
      ·
        refine ⟨3005526563606583555492415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4007368751475444740656553 3005526563606583555492415)
        ·
          refine ⟨4508289845409875333238623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005526563606583555492415 4508289845409875333238623)
          ·
            refine ⟨6762434768114812999857935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508289845409875333238623 6762434768114812999857935)
            ·
              refine ⟨10143652152172219499786903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762434768114812999857935 10143652152172219499786903)
              ·
                refine ⟨15215478228258329249680355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10143652152172219499786903 15215478228258329249680355)
                ·
                  refine ⟨22823217342387493874520533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15215478228258329249680355 22823217342387493874520533)
                  ·
                    refine ⟨534919156462206887684075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22823217342387493874520533 534919156462206887684075)
                    ·
                      rfl

theorem cell23_3125254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3125254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125254 prefixEnd_3125254 := by exact prefixLift 3125254
  have htrace : WordTrace (prefixWord ++ tailWord_3125254) baseStart_3125254 baseEnd_3125254 := by
    simpa [prefixWord, tailWord_3125254, baseEnd_3125254] using wordTrace_append hprefix tailTrace_3125254
  have hstable : (prefixWord ++ tailWord_3125254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125254).length < 2 ^ (prefixWord ++ tailWord_3125254).sum := by decide
  have hdescent : baseEnd_3125254 < baseStart_3125254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125273 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 7, 1, 3]
def baseStart_3125273 : Nat := 118140960795 + 3125273 * 2 ^ 59
def prefixEnd_3125273 : Nat := 4983230072969 + 3 ^ 40 * 3125273 * 2
def baseEnd_3125273 : Nat := 1604767225519056088714637

theorem tailTrace_3125273 : CollatzResearch.WordTrace tailWord_3125273 prefixEnd_3125273 1604767225519056088714637 := by
  unfold tailWord_3125273
  simp only [CollatzResearch.WordTrace]
  refine ⟨113988070806677149979172473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75992047204451433319448315 113988070806677149979172473)
  ·
    refine ⟨85491053105007862484379355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113988070806677149979172473 85491053105007862484379355)
    ·
      refine ⟨128236579657511793726569033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85491053105007862484379355 128236579657511793726569033)
      ·
        refine ⟨96177434743133845294926775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128236579657511793726569033 96177434743133845294926775)
        ·
          refine ⟨144266152114700767942390163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96177434743133845294926775 144266152114700767942390163)
          ·
            refine ⟨216399228172051151913585245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144266152114700767942390163 216399228172051151913585245)
            ·
              refine ⟨81149710564519181967594467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216399228172051151913585245 81149710564519181967594467)
              ·
                refine ⟨121724565846778772951391701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81149710564519181967594467 121724565846778772951391701)
                ·
                  refine ⟨2852919512033877491048243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 121724565846778772951391701 2852919512033877491048243)
                  ·
                    refine ⟨4279379268050816236572365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2852919512033877491048243 4279379268050816236572365)
                    ·
                      refine ⟨1604767225519056088714637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4279379268050816236572365 1604767225519056088714637)
                      ·
                        rfl

theorem cell23_3125273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_3125273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125273 prefixEnd_3125273 := by exact prefixLift 3125273
  have htrace : WordTrace (prefixWord ++ tailWord_3125273) baseStart_3125273 baseEnd_3125273 := by
    simpa [prefixWord, tailWord_3125273, baseEnd_3125273] using wordTrace_append hprefix tailTrace_3125273
  have hstable : (prefixWord ++ tailWord_3125273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125273).length < 2 ^ (prefixWord ++ tailWord_3125273).sum := by decide
  have hdescent : baseEnd_3125273 < baseStart_3125273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125333 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3125333 : Nat := 118140960795 + 3125333 * 2 ^ 59
def prefixEnd_3125333 : Nat := 4983230072969 + 3 ^ 40 * 3125333 * 2
def baseEnd_3125333 : Nat := 1604798034358325853964361

theorem tailTrace_3125333 : CollatzResearch.WordTrace tailWord_3125333 prefixEnd_3125333 1604798034358325853964361 := by
  unfold tailWord_3125333
  simp only [CollatzResearch.WordTrace]
  refine ⟨113990259186459780226356653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75993506124306520150904435 113990259186459780226356653)
  ·
    refine ⟨42746347194922417584883745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113990259186459780226356653 42746347194922417584883745)
    ·
      refine ⟨32059760396191813188662809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42746347194922417584883745 32059760396191813188662809)
      ·
        refine ⟨24044820297143859891497107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32059760396191813188662809 24044820297143859891497107)
        ·
          refine ⟨36067230445715789837245661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24044820297143859891497107 36067230445715789837245661)
          ·
            refine ⟨13525211417143421188967123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36067230445715789837245661 13525211417143421188967123)
            ·
              refine ⟨20287817125715131783450685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13525211417143421188967123 20287817125715131783450685)
              ·
                refine ⟨7607931422143174418794007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20287817125715131783450685 7607931422143174418794007)
                ·
                  refine ⟨11411897133214761628191011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7607931422143174418794007 11411897133214761628191011)
                  ·
                    refine ⟨17117845699822142442286517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11411897133214761628191011 17117845699822142442286517)
                    ·
                      refine ⟨1604798034358325853964361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17117845699822142442286517 1604798034358325853964361)
                      ·
                        rfl

theorem cell23_3125333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3125333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125333 prefixEnd_3125333 := by exact prefixLift 3125333
  have htrace : WordTrace (prefixWord ++ tailWord_3125333) baseStart_3125333 baseEnd_3125333 := by
    simpa [prefixWord, tailWord_3125333, baseEnd_3125333] using wordTrace_append hprefix tailTrace_3125333
  have hstable : (prefixWord ++ tailWord_3125333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125333).length < 2 ^ (prefixWord ++ tailWord_3125333).sum := by decide
  have hdescent : baseEnd_3125333 < baseStart_3125333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125334 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_3125334 : Nat := 118140960795 + 3125334 * 2 ^ 59
def prefixEnd_3125334 : Nat := 4983230072969 + 3 ^ 40 * 3125334 * 2
def baseEnd_3125334 : Nat := 1604798547838980350051857

theorem tailTrace_3125334 : CollatzResearch.WordTrace tailWord_3125334 prefixEnd_3125334 1604798547838980350051857 := by
  unfold tailWord_3125334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7124393478716009837321441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75993530439637438264762037 7124393478716009837321441)
  ·
    refine ⟨5343295109037007377991081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7124393478716009837321441 5343295109037007377991081)
    ·
      refine ⟨4007471331777755533493311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5343295109037007377991081 4007471331777755533493311)
      ·
        refine ⟨6011206997666633300239967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4007471331777755533493311 6011206997666633300239967)
        ·
          refine ⟨9016810496499949950359951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6011206997666633300239967 9016810496499949950359951)
          ·
            refine ⟨13525215744749924925539927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9016810496499949950359951 13525215744749924925539927)
            ·
              refine ⟨20287823617124887388309891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13525215744749924925539927 20287823617124887388309891)
              ·
                refine ⟨30431735425687331082464837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20287823617124887388309891 30431735425687331082464837)
                ·
                  refine ⟨5705950392316374577962157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30431735425687331082464837 5705950392316374577962157)
                  ·
                    refine ⟨2139731397118640466735809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5705950392316374577962157 2139731397118640466735809)
                    ·
                      refine ⟨1604798547838980350051857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139731397118640466735809 1604798547838980350051857)
                      ·
                        rfl

theorem cell23_3125334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_3125334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125334 prefixEnd_3125334 := by exact prefixLift 3125334
  have htrace : WordTrace (prefixWord ++ tailWord_3125334) baseStart_3125334 baseEnd_3125334 := by
    simpa [prefixWord, tailWord_3125334, baseEnd_3125334] using wordTrace_append hprefix tailTrace_3125334
  have hstable : (prefixWord ++ tailWord_3125334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125334).length < 2 ^ (prefixWord ++ tailWord_3125334).sum := by decide
  have hdescent : baseEnd_3125334 < baseStart_3125334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125336 : List Nat := [2, 1, 2, 2, 1, 4, 11]
def baseStart_3125336 : Nat := 118140960795 + 3125336 * 2 ^ 59
def prefixEnd_3125336 : Nat := 4983230072969 + 3 ^ 40 * 3125336 * 2
def baseEnd_3125336 : Nat := 19812340429633201755887

theorem tailTrace_3125336 : CollatzResearch.WordTrace tailWord_3125336 prefixEnd_3125336 19812340429633201755887 := by
  unfold tailWord_3125336
  simp only [CollatzResearch.WordTrace]
  refine ⟨56995184302724455869357931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75993579070299274492477241 56995184302724455869357931)
  ·
    refine ⟨85492776454086683804036897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56995184302724455869357931 85492776454086683804036897)
    ·
      refine ⟨64119582340565012853027673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85492776454086683804036897 64119582340565012853027673)
      ·
        refine ⟨48089686755423759639770755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64119582340565012853027673 48089686755423759639770755)
        ·
          refine ⟨72134530133135639459656133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48089686755423759639770755 72134530133135639459656133)
          ·
            refine ⟨13525224399962932398685525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72134530133135639459656133 13525224399962932398685525)
            ·
              refine ⟨19812340429633201755887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13525224399962932398685525 19812340429633201755887)
              ·
                rfl

theorem cell23_3125336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 11].length) (baseStart_3125336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125336 prefixEnd_3125336 := by exact prefixLift 3125336
  have htrace : WordTrace (prefixWord ++ tailWord_3125336) baseStart_3125336 baseEnd_3125336 := by
    simpa [prefixWord, tailWord_3125336, baseEnd_3125336] using wordTrace_append hprefix tailTrace_3125336
  have hstable : (prefixWord ++ tailWord_3125336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125336).length < 2 ^ (prefixWord ++ tailWord_3125336).sum := by decide
  have hdescent : baseEnd_3125336 < baseStart_3125336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125340 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3125340 : Nat := 118140960795 + 3125340 * 2 ^ 59
def prefixEnd_3125340 : Nat := 4983230072969 + 3 ^ 40 * 3125340 * 2
def baseEnd_3125340 : Nat := 534933876240969108858943

theorem tailTrace_3125340 : CollatzResearch.WordTrace tailWord_3125340 prefixEnd_3125340 534933876240969108858943 := by
  unfold tailWord_3125340
  simp only [CollatzResearch.WordTrace]
  refine ⟨56995257248717210210930737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75993676331622946947907649 56995257248717210210930737)
  ·
    refine ⟨42746442936537907658198053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56995257248717210210930737 42746442936537907658198053)
    ·
      refine ⟨8014958050600857685912135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42746442936537907658198053 8014958050600857685912135)
      ·
        refine ⟨12022437075901286528868203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8014958050600857685912135 12022437075901286528868203)
        ·
          refine ⟨18033655613851929793302305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12022437075901286528868203 18033655613851929793302305)
          ·
            refine ⟨13525241710388947344976729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18033655613851929793302305 13525241710388947344976729)
            ·
              refine ⟨10143931282791710508732547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13525241710388947344976729 10143931282791710508732547)
              ·
                refine ⟨15215896924187565763098821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10143931282791710508732547 15215896924187565763098821)
                ·
                  refine ⟨2852980673285168580581029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15215896924187565763098821 2852980673285168580581029)
                  ·
                    refine ⟨534933876240969108858943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2852980673285168580581029 534933876240969108858943)
                    ·
                      rfl

theorem cell23_3125340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3125340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125340 prefixEnd_3125340 := by exact prefixLift 3125340
  have htrace : WordTrace (prefixWord ++ tailWord_3125340) baseStart_3125340 baseEnd_3125340 := by
    simpa [prefixWord, tailWord_3125340, baseEnd_3125340] using wordTrace_append hprefix tailTrace_3125340
  have hstable : (prefixWord ++ tailWord_3125340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125340).length < 2 ^ (prefixWord ++ tailWord_3125340).sum := by decide
  have hdescent : baseEnd_3125340 < baseStart_3125340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125347 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 3, 2, 2]
def baseStart_3125347 : Nat := 118140960795 + 3125347 * 2 ^ 59
def prefixEnd_3125347 : Nat := 4983230072969 + 3 ^ 40 * 3125347 * 2
def baseEnd_3125347 : Nat := 1604805223087488799189297

theorem tailTrace_3125347 : CollatzResearch.WordTrace tailWord_3125347 prefixEnd_3125347 1604805223087488799189297 := by
  unfold tailWord_3125347
  simp only [CollatzResearch.WordTrace]
  refine ⟨113990769808409060617366295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75993846538939373744910863 113990769808409060617366295)
  ·
    refine ⟨170986154712613590926049443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113990769808409060617366295 170986154712613590926049443)
    ·
      refine ⟨256479232068920386389074165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170986154712613590926049443 256479232068920386389074165)
      ·
        refine ⟨24044928006461286223975703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256479232068920386389074165 24044928006461286223975703)
        ·
          refine ⟨36067392009691929335963555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24044928006461286223975703 36067392009691929335963555)
          ·
            refine ⟨54101088014537894003945333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36067392009691929335963555 54101088014537894003945333)
            ·
              refine ⟨5071977001362927562869875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54101088014537894003945333 5071977001362927562869875)
              ·
                refine ⟨7607965502044391344304813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071977001362927562869875 7607965502044391344304813)
                ·
                  refine ⟨2852987063266646754114305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7607965502044391344304813 2852987063266646754114305)
                  ·
                    refine ⟨2139740297449985065585729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2852987063266646754114305 2139740297449985065585729)
                    ·
                      refine ⟨1604805223087488799189297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139740297449985065585729 1604805223087488799189297)
                      ·
                        rfl

theorem cell23_3125347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_3125347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125347 prefixEnd_3125347 := by exact prefixLift 3125347
  have htrace : WordTrace (prefixWord ++ tailWord_3125347) baseStart_3125347 baseEnd_3125347 := by
    simpa [prefixWord, tailWord_3125347, baseEnd_3125347] using wordTrace_append hprefix tailTrace_3125347
  have hstable : (prefixWord ++ tailWord_3125347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125347).length < 2 ^ (prefixWord ++ tailWord_3125347).sum := by decide
  have hdescent : baseEnd_3125347 < baseStart_3125347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125367 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 1, 2, 3]
def baseStart_3125367 : Nat := 118140960795 + 3125367 * 2 ^ 59
def prefixEnd_3125367 : Nat := 4983230072969 + 3 ^ 40 * 3125367 * 2
def baseEnd_3125367 : Nat := 1604815492700578720939205

theorem tailTrace_3125367 : CollatzResearch.WordTrace tailWord_3125367 prefixEnd_3125367 1604815492700578720939205 := by
  unfold tailWord_3125367
  simp only [CollatzResearch.WordTrace]
  refine ⟨113991499268336604033094355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75994332845557736022062903 113991499268336604033094355)
  ·
    refine ⟨170987248902504906049641533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113991499268336604033094355 170987248902504906049641533)
    ·
      refine ⟨64120218338439339768615575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170987248902504906049641533 64120218338439339768615575)
      ·
        refine ⟨96180327507659009652923363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64120218338439339768615575 96180327507659009652923363)
        ·
          refine ⟨144270491261488514479385045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96180327507659009652923363 144270491261488514479385045)
          ·
            refine ⟨3381339638941137058110587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 144270491261488514479385045 3381339638941137058110587)
            ·
              refine ⟨5072009458411705587165881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381339638941137058110587 5072009458411705587165881)
              ·
                refine ⟨3804007093808779190374411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5072009458411705587165881 3804007093808779190374411)
                ·
                  refine ⟨5706010640713168785561617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804007093808779190374411 5706010640713168785561617)
                  ·
                    refine ⟨4279507980534876589171213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5706010640713168785561617 4279507980534876589171213)
                    ·
                      refine ⟨1604815492700578720939205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4279507980534876589171213 1604815492700578720939205)
                      ·
                        rfl

theorem cell23_3125367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_3125367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125367 prefixEnd_3125367 := by exact prefixLift 3125367
  have htrace : WordTrace (prefixWord ++ tailWord_3125367) baseStart_3125367 baseEnd_3125367 := by
    simpa [prefixWord, tailWord_3125367, baseEnd_3125367] using wordTrace_append hprefix tailTrace_3125367
  have hstable : (prefixWord ++ tailWord_3125367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125367).length < 2 ^ (prefixWord ++ tailWord_3125367).sum := by decide
  have hdescent : baseEnd_3125367 < baseStart_3125367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125380 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_3125380 : Nat := 118140960795 + 3125380 * 2 ^ 59
def prefixEnd_3125380 : Nat := 4983230072969 + 3 ^ 40 * 3125380 * 2
def baseEnd_3125380 : Nat := 1604822167949087170076645

theorem tailTrace_3125380 : CollatzResearch.WordTrace tailWord_3125380 prefixEnd_3125380 1604822167949087170076645 := by
  unfold tailWord_3125380
  simp only [CollatzResearch.WordTrace]
  refine ⟨56995986708644753626658797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75994648944859671502211729 56995986708644753626658797)
  ·
    refine ⟨21373495015741782609997049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56995986708644753626658797 21373495015741782609997049)
    ·
      refine ⟨16030121261806336957497787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21373495015741782609997049 16030121261806336957497787)
      ·
        refine ⟨24045181892709505436246681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16030121261806336957497787 24045181892709505436246681)
        ·
          refine ⟨18033886419532129077185011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24045181892709505436246681 18033886419532129077185011)
          ·
            refine ⟨27050829629298193615777517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18033886419532129077185011 27050829629298193615777517)
            ·
              refine ⟨10144061110986822605916569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27050829629298193615777517 10144061110986822605916569)
              ·
                refine ⟨7608045833240116954437427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10144061110986822605916569 7608045833240116954437427)
                ·
                  refine ⟨11412068749860175431656141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7608045833240116954437427 11412068749860175431656141)
                  ·
                    refine ⟨4279525781197565786871053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11412068749860175431656141 4279525781197565786871053)
                    ·
                      refine ⟨1604822167949087170076645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4279525781197565786871053 1604822167949087170076645)
                      ·
                        rfl

theorem cell23_3125380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_3125380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125380 prefixEnd_3125380 := by exact prefixLift 3125380
  have htrace : WordTrace (prefixWord ++ tailWord_3125380) baseStart_3125380 baseEnd_3125380 := by
    simpa [prefixWord, tailWord_3125380, baseEnd_3125380] using wordTrace_append hprefix tailTrace_3125380
  have hstable : (prefixWord ++ tailWord_3125380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125380).length < 2 ^ (prefixWord ++ tailWord_3125380).sum := by decide
  have hdescent : baseEnd_3125380 < baseStart_3125380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125384 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 1, 2, 3]
def baseStart_3125384 : Nat := 118140960795 + 3125384 * 2 ^ 59
def prefixEnd_3125384 : Nat := 4983230072969 + 3 ^ 40 * 3125384 * 2
def baseEnd_3125384 : Nat := 1604824221871705154426627

theorem tailTrace_3125384 : CollatzResearch.WordTrace tailWord_3125384 prefixEnd_3125384 1604824221871705154426627 := by
  unfold tailWord_3125384
  simp only [CollatzResearch.WordTrace]
  refine ⟨56996059654637507968231603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75994746206183343957642137 56996059654637507968231603)
  ·
    refine ⟨85494089481956261952347405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56996059654637507968231603 85494089481956261952347405)
    ·
      refine ⟨32060283555733598232130277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85494089481956261952347405 32060283555733598232130277)
      ·
        refine ⟨6011303166700049668524427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32060283555733598232130277 6011303166700049668524427)
        ·
          refine ⟨9016954750050074502786641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6011303166700049668524427 9016954750050074502786641)
          ·
            refine ⟨6762716062537555877089981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9016954750050074502786641 6762716062537555877089981)
            ·
              refine ⟨2536018523451583453908743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6762716062537555877089981 2536018523451583453908743)
              ·
                refine ⟨3804027785177375180863115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536018523451583453908743 3804027785177375180863115)
                ·
                  refine ⟨5706041677766062771294673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804027785177375180863115 5706041677766062771294673)
                  ·
                    refine ⟨4279531258324547078471005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5706041677766062771294673 4279531258324547078471005)
                    ·
                      refine ⟨1604824221871705154426627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4279531258324547078471005 1604824221871705154426627)
                      ·
                        rfl

theorem cell23_3125384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_3125384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125384 prefixEnd_3125384 := by exact prefixLift 3125384
  have htrace : WordTrace (prefixWord ++ tailWord_3125384) baseStart_3125384 baseEnd_3125384 := by
    simpa [prefixWord, tailWord_3125384, baseEnd_3125384] using wordTrace_append hprefix tailTrace_3125384
  have hstable : (prefixWord ++ tailWord_3125384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125384).length < 2 ^ (prefixWord ++ tailWord_3125384).sum := by decide
  have hdescent : baseEnd_3125384 < baseStart_3125384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125397 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_3125397 : Nat := 118140960795 + 3125397 * 2 ^ 59
def prefixEnd_3125397 : Nat := 4983230072969 + 3 ^ 40 * 3125397 * 2
def baseEnd_3125397 : Nat := 1604830897120213603564067

theorem tailTrace_3125397 : CollatzResearch.WordTrace tailWord_3125397 prefixEnd_3125397 1604830897120213603564067 := by
  unfold tailWord_3125397
  simp only [CollatzResearch.WordTrace]
  refine ⟨113992593458227919156686445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75995062305485279437790963 113992593458227919156686445)
  ·
    refine ⟨42747222546835469683757417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113992593458227919156686445 42747222546835469683757417)
    ·
      refine ⟨32060416910126602262818063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42747222546835469683757417 32060416910126602262818063)
      ·
        refine ⟨48090625365189903394227095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32060416910126602262818063 48090625365189903394227095)
        ·
          refine ⟨72135938047784855091340643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48090625365189903394227095 72135938047784855091340643)
          ·
            refine ⟨108203907071677282637010965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72135938047784855091340643 108203907071677282637010965)
            ·
              refine ⟨5072058143984872623609889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108203907071677282637010965 5072058143984872623609889)
              ·
                refine ⟨3804043607988654467707417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5072058143984872623609889 3804043607988654467707417)
                ·
                  refine ⟨2853032705991490850780563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3804043607988654467707417 2853032705991490850780563)
                  ·
                    refine ⟨4279549058987236276170845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2853032705991490850780563 4279549058987236276170845)
                    ·
                      refine ⟨1604830897120213603564067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4279549058987236276170845 1604830897120213603564067)
                      ·
                        rfl

theorem cell23_3125397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_3125397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125397 prefixEnd_3125397 := by exact prefixLift 3125397
  have htrace : WordTrace (prefixWord ++ tailWord_3125397) baseStart_3125397 baseEnd_3125397 := by
    simpa [prefixWord, tailWord_3125397, baseEnd_3125397] using wordTrace_append hprefix tailTrace_3125397
  have hstable : (prefixWord ++ tailWord_3125397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125397).length < 2 ^ (prefixWord ++ tailWord_3125397).sum := by decide
  have hdescent : baseEnd_3125397 < baseStart_3125397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125407 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 3, 3, 2]
def baseStart_3125407 : Nat := 118140960795 + 3125407 * 2 ^ 59
def prefixEnd_3125407 : Nat := 4983230072969 + 3 ^ 40 * 3125407 * 2
def baseEnd_3125407 : Nat := 1604836031926758564439021

theorem tailTrace_3125407 : CollatzResearch.WordTrace tailWord_3125407 prefixEnd_3125407 1604836031926758564439021 := by
  unfold tailWord_3125407
  simp only [CollatzResearch.WordTrace]
  refine ⟨113992958188191690864550475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75995305458794460576366983 113992958188191690864550475)
  ·
    refine ⟨170989437282287536296825713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113992958188191690864550475 170989437282287536296825713)
    ·
      refine ⟨128242077961715652222619285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170989437282287536296825713 128242077961715652222619285)
      ·
        refine ⟨6011347404455421197935279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128242077961715652222619285 6011347404455421197935279)
        ·
          refine ⟨9017021106683131796902919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6011347404455421197935279 9017021106683131796902919)
          ·
            refine ⟨13525531660024697695354379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9017021106683131796902919 13525531660024697695354379)
            ·
              refine ⟨20288297490037046543031569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13525531660024697695354379 20288297490037046543031569)
              ·
                refine ⟨15216223117527784907273677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20288297490037046543031569 15216223117527784907273677)
                ·
                  refine ⟨5706083669072919340227629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15216223117527784907273677 5706083669072919340227629)
                  ·
                    refine ⟨2139781375902344752585361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5706083669072919340227629 2139781375902344752585361)
                    ·
                      refine ⟨1604836031926758564439021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139781375902344752585361 1604836031926758564439021)
                      ·
                        rfl

theorem cell23_3125407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_3125407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125407 prefixEnd_3125407 := by exact prefixLift 3125407
  have htrace : WordTrace (prefixWord ++ tailWord_3125407) baseStart_3125407 baseEnd_3125407 := by
    simpa [prefixWord, tailWord_3125407, baseEnd_3125407] using wordTrace_append hprefix tailTrace_3125407
  have hstable : (prefixWord ++ tailWord_3125407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125407).length < 2 ^ (prefixWord ++ tailWord_3125407).sum := by decide
  have hdescent : baseEnd_3125407 < baseStart_3125407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125413 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_3125413 : Nat := 118140960795 + 3125413 * 2 ^ 59
def prefixEnd_3125413 : Nat := 4983230072969 + 3 ^ 40 * 3125413 * 2
def baseEnd_3125413 : Nat := 534946370936895180321331

theorem tailTrace_3125413 : CollatzResearch.WordTrace tailWord_3125413 prefixEnd_3125413 534946370936895180321331 := by
  unfold tailWord_3125413
  simp only [CollatzResearch.WordTrace]
  refine ⟨113993177026169953889268893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75995451350779969259512595 113993177026169953889268893)
  ·
    refine ⟨42747441384813732708475835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113993177026169953889268893 42747441384813732708475835)
    ·
      refine ⟨64121162077220599062713753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42747441384813732708475835 64121162077220599062713753)
      ·
        refine ⟨48090871557915449297035315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64121162077220599062713753 48090871557915449297035315)
        ·
          refine ⟨72136307336873173945552973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48090871557915449297035315 72136307336873173945552973)
          ·
            refine ⟨27051115251327440229582365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72136307336873173945552973 27051115251327440229582365)
            ·
              refine ⟨10144168219247790086093387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27051115251327440229582365 10144168219247790086093387)
              ·
                refine ⟨15216252328871685129140081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10144168219247790086093387 15216252328871685129140081)
                ·
                  refine ⟨11412189246653763846855061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15216252328871685129140081 11412189246653763846855061)
                  ·
                    refine ⟨534946370936895180321331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11412189246653763846855061 534946370936895180321331)
                    ·
                      rfl

theorem cell23_3125413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_3125413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125413 prefixEnd_3125413 := by exact prefixLift 3125413
  have htrace : WordTrace (prefixWord ++ tailWord_3125413) baseStart_3125413 baseEnd_3125413 := by
    simpa [prefixWord, tailWord_3125413, baseEnd_3125413] using wordTrace_append hprefix tailTrace_3125413
  have hstable : (prefixWord ++ tailWord_3125413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125413).length < 2 ^ (prefixWord ++ tailWord_3125413).sum := by decide
  have hdescent : baseEnd_3125413 < baseStart_3125413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125423 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 3]
def baseStart_3125423 : Nat := 118140960795 + 3125423 * 2 ^ 59
def prefixEnd_3125423 : Nat := 4983230072969 + 3 ^ 40 * 3125423 * 2
def baseEnd_3125423 : Nat := 1604844247617230501838947

theorem tailTrace_3125423 : CollatzResearch.WordTrace tailWord_3125423 prefixEnd_3125423 1604844247617230501838947 := by
  unfold tailWord_3125423
  simp only [CollatzResearch.WordTrace]
  refine ⟨113993541756133725597132923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75995694504089150398088615 113993541756133725597132923)
  ·
    refine ⟨170990312634200588395699385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113993541756133725597132923 170990312634200588395699385)
    ·
      refine ⟨128242734475650441296774539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170990312634200588395699385 128242734475650441296774539)
      ·
        refine ⟨192364101713475661945161809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128242734475650441296774539 192364101713475661945161809)
        ·
          refine ⟨144273076285106746458871357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192364101713475661945161809 144273076285106746458871357)
          ·
            refine ⟨54102403606915029922076759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144273076285106746458871357 54102403606915029922076759)
            ·
              refine ⟨81153605410372544883115139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54102403606915029922076759 81153605410372544883115139)
              ·
                refine ⟨121730408115558817324672709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81153605410372544883115139 121730408115558817324672709)
                ·
                  refine ⟨22824451521667278248376133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121730408115558817324672709 22824451521667278248376133)
                  ·
                    refine ⟨4279584660312614671570525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22824451521667278248376133 4279584660312614671570525)
                    ·
                      refine ⟨1604844247617230501838947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4279584660312614671570525 1604844247617230501838947)
                      ·
                        rfl

theorem cell23_3125423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 3].length) (baseStart_3125423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125423 prefixEnd_3125423 := by exact prefixLift 3125423
  have htrace : WordTrace (prefixWord ++ tailWord_3125423) baseStart_3125423 baseEnd_3125423 := by
    simpa [prefixWord, tailWord_3125423, baseEnd_3125423] using wordTrace_append hprefix tailTrace_3125423
  have hstable : (prefixWord ++ tailWord_3125423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125423).length < 2 ^ (prefixWord ++ tailWord_3125423).sum := by decide
  have hdescent : baseEnd_3125423 < baseStart_3125423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125433 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3125433 : Nat := 118140960795 + 3125433 * 2 ^ 59
def prefixEnd_3125433 : Nat := 4983230072969 + 3 ^ 40 * 3125433 * 2
def baseEnd_3125433 : Nat := 1604849382423775462713901

theorem tailTrace_3125433 : CollatzResearch.WordTrace tailWord_3125433 prefixEnd_3125433 1604849382423775462713901 := by
  unfold tailWord_3125433
  simp only [CollatzResearch.WordTrace]
  refine ⟨113993906486097497304996953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75995937657398331536664635 113993906486097497304996953)
  ·
    refine ⟨85495429864573122978747715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113993906486097497304996953 85495429864573122978747715)
    ·
      refine ⟨128243144796859684468121573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85495429864573122978747715 128243144796859684468121573)
      ·
        refine ⟨24045589649411190837772795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128243144796859684468121573 24045589649411190837772795)
        ·
          refine ⟨36068384474116786256659193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24045589649411190837772795 36068384474116786256659193)
          ·
            refine ⟨27051288355587589692494395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36068384474116786256659193 27051288355587589692494395)
            ·
              refine ⟨40576932533381384538741593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27051288355587589692494395 40576932533381384538741593)
              ·
                refine ⟨30432699400036038404056195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40576932533381384538741593 30432699400036038404056195)
                ·
                  refine ⟨45649049100054057606084293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30432699400036038404056195 45649049100054057606084293)
                  ·
                    refine ⟨8559196706260135801140805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45649049100054057606084293 8559196706260135801140805)
                    ·
                      refine ⟨1604849382423775462713901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8559196706260135801140805 1604849382423775462713901)
                      ·
                        rfl

theorem cell23_3125433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3125433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125433 prefixEnd_3125433 := by exact prefixLift 3125433
  have htrace : WordTrace (prefixWord ++ tailWord_3125433) baseStart_3125433 baseEnd_3125433 := by
    simpa [prefixWord, tailWord_3125433, baseEnd_3125433] using wordTrace_append hprefix tailTrace_3125433
  have hstable : (prefixWord ++ tailWord_3125433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125433).length < 2 ^ (prefixWord ++ tailWord_3125433).sum := by decide
  have hdescent : baseEnd_3125433 < baseStart_3125433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125437 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 4, 2, 2]
def baseStart_3125437 : Nat := 118140960795 + 3125437 * 2 ^ 59
def prefixEnd_3125437 : Nat := 4983230072969 + 3 ^ 40 * 3125437 * 2
def baseEnd_3125437 : Nat := 1604851436346393447063883

theorem tailTrace_3125437 : CollatzResearch.WordTrace tailWord_3125437 prefixEnd_3125437 1604851436346393447063883 := by
  unfold tailWord_3125437
  simp only [CollatzResearch.WordTrace]
  refine ⟨113994052378083005988142565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75996034918722003992095043 113994052378083005988142565)
  ·
    refine ⟨21373884820890563622776731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113994052378083005988142565 21373884820890563622776731)
    ·
      refine ⟨32060827231335845434165097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21373884820890563622776731 32060827231335845434165097)
      ·
        refine ⟨24045620423501884075623823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32060827231335845434165097 24045620423501884075623823)
        ·
          refine ⟨36068430635252826113435735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24045620423501884075623823 36068430635252826113435735)
          ·
            refine ⟨54102645952879239170153603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36068430635252826113435735 54102645952879239170153603)
            ·
              refine ⟨81153968929318858755230405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54102645952879239170153603 81153968929318858755230405)
              ·
                refine ⟨15216369174247286016605701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81153968929318858755230405 15216369174247286016605701)
                ·
                  refine ⟨2853069220171366128113569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15216369174247286016605701 2853069220171366128113569)
                  ·
                    refine ⟨2139801915128524596085177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2853069220171366128113569 2139801915128524596085177)
                    ·
                      refine ⟨1604851436346393447063883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139801915128524596085177 1604851436346393447063883)
                      ·
                        rfl

theorem cell23_3125437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_3125437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125437 prefixEnd_3125437 := by exact prefixLift 3125437
  have htrace : WordTrace (prefixWord ++ tailWord_3125437) baseStart_3125437 baseEnd_3125437 := by
    simpa [prefixWord, tailWord_3125437, baseEnd_3125437] using wordTrace_append hprefix tailTrace_3125437
  have hstable : (prefixWord ++ tailWord_3125437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125437).length < 2 ^ (prefixWord ++ tailWord_3125437).sum := by decide
  have hdescent : baseEnd_3125437 < baseStart_3125437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125441 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3125441 : Nat := 118140960795 + 3125441 * 2 ^ 59
def prefixEnd_3125441 : Nat := 4983230072969 + 3 ^ 40 * 3125441 * 2
def baseEnd_3125441 : Nat := 1604853490269011431413865

theorem tailTrace_3125441 : CollatzResearch.WordTrace tailWord_3125441 prefixEnd_3125441 1604853490269011431413865 := by
  unfold tailWord_3125441
  simp only [CollatzResearch.WordTrace]
  refine ⟨113994198270068514671288177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75996132180045676447525451 113994198270068514671288177)
  ·
    refine ⟨85495648702551386003466133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113994198270068514671288177 85495648702551386003466133)
    ·
      refine ⟨4007608532932096218912475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85495648702551386003466133 4007608532932096218912475)
      ·
        refine ⟨6011412799398144328368713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4007608532932096218912475 6011412799398144328368713)
        ·
          refine ⟨4508559599548608246276535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6011412799398144328368713 4508559599548608246276535)
          ·
            refine ⟨6762839399322912369414803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508559599548608246276535 6762839399322912369414803)
            ·
              refine ⟨10144259098984368554122205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762839399322912369414803 10144259098984368554122205)
              ·
                refine ⟨3804097162119138207795827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10144259098984368554122205 3804097162119138207795827)
                ·
                  refine ⟨5706145743178707311693741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804097162119138207795827 5706145743178707311693741)
                  ·
                    refine ⟨2139804653692015241885153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5706145743178707311693741 2139804653692015241885153)
                    ·
                      refine ⟨1604853490269011431413865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139804653692015241885153 1604853490269011431413865)
                      ·
                        rfl

theorem cell23_3125441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3125441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125441 prefixEnd_3125441 := by exact prefixLift 3125441
  have htrace : WordTrace (prefixWord ++ tailWord_3125441) baseStart_3125441 baseEnd_3125441 := by
    simpa [prefixWord, tailWord_3125441, baseEnd_3125441] using wordTrace_append hprefix tailTrace_3125441
  have hstable : (prefixWord ++ tailWord_3125441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125441).length < 2 ^ (prefixWord ++ tailWord_3125441).sum := by decide
  have hdescent : baseEnd_3125441 < baseStart_3125441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125454 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2]
def baseStart_3125454 : Nat := 118140960795 + 3125454 * 2 ^ 59
def prefixEnd_3125454 : Nat := 4983230072969 + 3 ^ 40 * 3125454 * 2
def baseEnd_3125454 : Nat := 1604860165517519880551305

theorem tailTrace_3125454 : CollatzResearch.WordTrace tailWord_3125454 prefixEnd_3125454 1604860165517519880551305 := by
  unfold tailWord_3125454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14249334052377677236438927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75996448279347611927674277 14249334052377677236438927)
  ·
    refine ⟨21374001078566515854658391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14249334052377677236438927 21374001078566515854658391)
    ·
      refine ⟨32061001617849773781987587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21374001078566515854658391 32061001617849773781987587)
      ·
        refine ⟨48091502426774660672981381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32061001617849773781987587 48091502426774660672981381)
        ·
          refine ⟨9017156705020248876184009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48091502426774660672981381 9017156705020248876184009)
          ·
            refine ⟨6762867528765186657138007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9017156705020248876184009 6762867528765186657138007)
            ·
              refine ⟨10144301293147779985707011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6762867528765186657138007 10144301293147779985707011)
              ·
                refine ⟨15216451939721669978560517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10144301293147779985707011 15216451939721669978560517)
                ·
                  refine ⟨2853084738697813120980097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15216451939721669978560517 2853084738697813120980097)
                  ·
                    refine ⟨2139813554023359840735073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2853084738697813120980097 2139813554023359840735073)
                    ·
                      refine ⟨1604860165517519880551305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139813554023359840735073 1604860165517519880551305)
                      ·
                        rfl

theorem cell23_3125454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_3125454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125454 prefixEnd_3125454 := by exact prefixLift 3125454
  have htrace : WordTrace (prefixWord ++ tailWord_3125454) baseStart_3125454 baseEnd_3125454 := by
    simpa [prefixWord, tailWord_3125454, baseEnd_3125454] using wordTrace_append hprefix tailTrace_3125454
  have hstable : (prefixWord ++ tailWord_3125454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125454).length < 2 ^ (prefixWord ++ tailWord_3125454).sum := by decide
  have hdescent : baseEnd_3125454 < baseStart_3125454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125473 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 3, 7]
def baseStart_3125473 : Nat := 118140960795 + 3125473 * 2 ^ 59
def prefixEnd_3125473 : Nat := 4983230072969 + 3 ^ 40 * 3125473 * 2
def baseEnd_3125473 : Nat := 534956640549985102071239

theorem tailTrace_3125473 : CollatzResearch.WordTrace tailWord_3125473 prefixEnd_3125473 534956640549985102071239 := by
  unfold tailWord_3125473
  simp only [CollatzResearch.WordTrace]
  refine ⟨113995365405952584136453073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75996910270635056090968715 113995365405952584136453073)
  ·
    refine ⟨85496524054464438102339805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113995365405952584136453073 85496524054464438102339805)
    ·
      refine ⟨32061196520424164288377427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85496524054464438102339805 32061196520424164288377427)
      ·
        refine ⟨48091794780636246432566141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32061196520424164288377427 48091794780636246432566141)
        ·
          refine ⟨18034423042738592412212303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48091794780636246432566141 18034423042738592412212303)
          ·
            refine ⟨27051634564107888618318455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18034423042738592412212303 27051634564107888618318455)
            ·
              refine ⟨40577451846161832927477683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27051634564107888618318455 40577451846161832927477683)
              ·
                refine ⟨60866177769242749391216525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40577451846161832927477683 60866177769242749391216525)
                ·
                  refine ⟨22824816663466031021706197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60866177769242749391216525 22824816663466031021706197)
                  ·
                    refine ⟨534956640549985102071239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22824816663466031021706197 534956640549985102071239)
                    ·
                      rfl

theorem cell23_3125473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_3125473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125473 prefixEnd_3125473 := by exact prefixLift 3125473
  have htrace : WordTrace (prefixWord ++ tailWord_3125473) baseStart_3125473 baseEnd_3125473 := by
    simpa [prefixWord, tailWord_3125473, baseEnd_3125473] using wordTrace_append hprefix tailTrace_3125473
  have hstable : (prefixWord ++ tailWord_3125473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125473).length < 2 ^ (prefixWord ++ tailWord_3125473).sum := by decide
  have hdescent : baseEnd_3125473 < baseStart_3125473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125490 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_3125490 : Nat := 118140960795 + 3125490 * 2 ^ 59
def prefixEnd_3125490 : Nat := 4983230072969 + 3 ^ 40 * 3125490 * 2
def baseEnd_3125490 : Nat := 534959550273693913233713

theorem tailTrace_3125490 : CollatzResearch.WordTrace tailWord_3125490 prefixEnd_3125490 534959550273693913233713 := by
  unfold tailWord_3125490
  simp only [CollatzResearch.WordTrace]
  refine ⟨28498996361722749009955481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75997323631260664026547949 28498996361722749009955481)
  ·
    refine ⟨21374247271292061757466611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28498996361722749009955481 21374247271292061757466611)
    ·
      refine ⟨32061370906938092636199917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21374247271292061757466611 32061370906938092636199917)
      ·
        refine ⟨12023014090101784738574969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32061370906938092636199917 12023014090101784738574969)
        ·
          refine ⟨9017260567576338553931227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12023014090101784738574969 9017260567576338553931227)
          ·
            refine ⟨13525890851364507830896841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9017260567576338553931227 13525890851364507830896841)
            ·
              refine ⟨10144418138523380873172631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13525890851364507830896841 10144418138523380873172631)
              ·
                refine ⟨15216627207785071309758947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10144418138523380873172631 15216627207785071309758947)
                ·
                  refine ⟨22824940811677606964638421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15216627207785071309758947 22824940811677606964638421)
                  ·
                    refine ⟨534959550273693913233713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22824940811677606964638421 534959550273693913233713)
                    ·
                      rfl

theorem cell23_3125490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_3125490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125490 prefixEnd_3125490 := by exact prefixLift 3125490
  have htrace : WordTrace (prefixWord ++ tailWord_3125490) baseStart_3125490 baseEnd_3125490 := by
    simpa [prefixWord, tailWord_3125490, baseEnd_3125490] using wordTrace_append hprefix tailTrace_3125490
  have hstable : (prefixWord ++ tailWord_3125490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125490).length < 2 ^ (prefixWord ++ tailWord_3125490).sum := by decide
  have hdescent : baseEnd_3125490 < baseStart_3125490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125511 : List Nat := [1, 1, 4, 5, 1, 1, 3, 2, 5]
def baseStart_3125511 : Nat := 118140960795 + 3125511 * 2 ^ 59
def prefixEnd_3125511 : Nat := 4983230072969 + 3 ^ 40 * 3125511 * 2
def baseEnd_3125511 : Nat := 178321048212758461948727

theorem tailTrace_3125511 : CollatzResearch.WordTrace tailWord_3125511 prefixEnd_3125511 178321048212758461948727 := by
  unfold tailWord_3125511
  simp only [CollatzResearch.WordTrace]
  refine ⟨113996751379814916626336387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75997834253209944417557591 113996751379814916626336387)
  ·
    refine ⟨170995127069722374939504581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113996751379814916626336387 170995127069722374939504581)
    ·
      refine ⟨32061586325572945301157109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170995127069722374939504581 32061586325572945301157109)
      ·
        refine ⟨3005773718022463621983479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32061586325572945301157109 3005773718022463621983479)
        ·
          refine ⟨4508660577033695432975219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005773718022463621983479 4508660577033695432975219)
          ·
            refine ⟨6762990865550543149462829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508660577033695432975219 6762990865550543149462829)
            ·
              refine ⟨2536121574581453681048561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6762990865550543149462829 2536121574581453681048561)
              ·
                refine ⟨1902091180936090260786421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2536121574581453681048561 1902091180936090260786421)
                ·
                  refine ⟨178321048212758461948727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1902091180936090260786421 178321048212758461948727)
                  ·
                    rfl

theorem cell23_3125511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 5].length) (baseStart_3125511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125511 prefixEnd_3125511 := by exact prefixLift 3125511
  have htrace : WordTrace (prefixWord ++ tailWord_3125511) baseStart_3125511 baseEnd_3125511 := by
    simpa [prefixWord, tailWord_3125511, baseEnd_3125511] using wordTrace_append hprefix tailTrace_3125511
  have hstable : (prefixWord ++ tailWord_3125511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125511).length < 2 ^ (prefixWord ++ tailWord_3125511).sum := by decide
  have hdescent : baseEnd_3125511 < baseStart_3125511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125523 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 6]
def baseStart_3125523 : Nat := 118140960795 + 3125523 * 2 ^ 59
def prefixEnd_3125523 : Nat := 4983230072969 + 3 ^ 40 * 3125523 * 2
def baseEnd_3125523 : Nat := 1604895595682680110588487

theorem tailTrace_3125523 : CollatzResearch.WordTrace tailWord_3125523 prefixEnd_3125523 1604895595682680110588487 := by
  unfold tailWord_3125523
  simp only [CollatzResearch.WordTrace]
  refine ⟨113997189055771442675773223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75998126037180961783848815 113997189055771442675773223)
  ·
    refine ⟨170995783583657164013659835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113997189055771442675773223 170995783583657164013659835)
    ·
      refine ⟨256493675375485746020489753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170995783583657164013659835 256493675375485746020489753)
      ·
        refine ⟨192370256531614309515367315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256493675375485746020489753 192370256531614309515367315)
        ·
          refine ⟨288555384797421464273050973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192370256531614309515367315 288555384797421464273050973)
          ·
            refine ⟨108208269299033049102394115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288555384797421464273050973 108208269299033049102394115)
            ·
              refine ⟨162312403948549573653591173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108208269299033049102394115 162312403948549573653591173)
              ·
                refine ⟨30433575740353045060048345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162312403948549573653591173 30433575740353045060048345)
                ·
                  refine ⟨22825181805264783795036259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30433575740353045060048345 22825181805264783795036259)
                  ·
                    refine ⟨34237772707897175692554389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22825181805264783795036259 34237772707897175692554389)
                    ·
                      refine ⟨1604895595682680110588487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34237772707897175692554389 1604895595682680110588487)
                      ·
                        rfl

theorem cell23_3125523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_3125523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125523 prefixEnd_3125523 := by exact prefixLift 3125523
  have htrace : WordTrace (prefixWord ++ tailWord_3125523) baseStart_3125523 baseEnd_3125523 := by
    simpa [prefixWord, tailWord_3125523, baseEnd_3125523] using wordTrace_append hprefix tailTrace_3125523
  have hstable : (prefixWord ++ tailWord_3125523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125523).length < 2 ^ (prefixWord ++ tailWord_3125523).sum := by decide
  have hdescent : baseEnd_3125523 < baseStart_3125523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125544 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3125544 : Nat := 118140960795 + 3125544 * 2 ^ 59
def prefixEnd_3125544 : Nat := 4983230072969 + 3 ^ 40 * 3125544 * 2
def baseEnd_3125544 : Nat := 1604906378776424528425891

theorem tailTrace_3125544 : CollatzResearch.WordTrace tailWord_3125544 prefixEnd_3125544 1604906378776424528425891 := by
  unfold tailWord_3125544
  simp only [CollatzResearch.WordTrace]
  refine ⟨56998977494347681631143843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75998636659130242174858457 56998977494347681631143843)
  ·
    refine ⟨85498466241521522446715765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56998977494347681631143843 85498466241521522446715765)
    ·
      refine ⟨8015481210142642729379603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85498466241521522446715765 8015481210142642729379603)
      ·
        refine ⟨12023221815213964094069405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8015481210142642729379603 12023221815213964094069405)
        ·
          refine ⟨4508708180705236535276027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12023221815213964094069405 4508708180705236535276027)
          ·
            refine ⟨6763062271057854802914041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508708180705236535276027 6763062271057854802914041)
            ·
              refine ⟨5072296703293391102185531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6763062271057854802914041 5072296703293391102185531)
              ·
                refine ⟨7608445054940086653278297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072296703293391102185531 7608445054940086653278297)
                ·
                  refine ⟨5706333791205064989958723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7608445054940086653278297 5706333791205064989958723)
                  ·
                    refine ⟨8559500686807597484938085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5706333791205064989958723 8559500686807597484938085)
                    ·
                      refine ⟨1604906378776424528425891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8559500686807597484938085 1604906378776424528425891)
                      ·
                        rfl

theorem cell23_3125544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3125544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125544 prefixEnd_3125544 := by exact prefixLift 3125544
  have htrace : WordTrace (prefixWord ++ tailWord_3125544) baseStart_3125544 baseEnd_3125544 := by
    simpa [prefixWord, tailWord_3125544, baseEnd_3125544] using wordTrace_append hprefix tailTrace_3125544
  have hstable : (prefixWord ++ tailWord_3125544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125544).length < 2 ^ (prefixWord ++ tailWord_3125544).sum := by decide
  have hdescent : baseEnd_3125544 < baseStart_3125544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125577 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 3, 1, 3]
def baseStart_3125577 : Nat := 118140960795 + 3125577 * 2 ^ 59
def prefixEnd_3125577 : Nat := 4983230072969 + 3 ^ 40 * 3125577 * 2
def baseEnd_3125577 : Nat := 1604923323638022899313239

theorem tailTrace_3125577 : CollatzResearch.WordTrace tailWord_3125577 prefixEnd_3125577 1604923323638022899313239 := by
  unfold tailWord_3125577
  simp only [CollatzResearch.WordTrace]
  refine ⟨113999158597575809898238985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75999439065050539932159323 113999158597575809898238985)
  ·
    refine ⟨85499368948181857423679239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113999158597575809898238985 85499368948181857423679239)
    ·
      refine ⟨128249053422272786135518859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85499368948181857423679239 128249053422272786135518859)
      ·
        refine ⟨192373580133409179203278289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128249053422272786135518859 192373580133409179203278289)
        ·
          refine ⟨144280185100056884402458717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192373580133409179203278289 144280185100056884402458717)
          ·
            refine ⟨54105069412521331650922019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144280185100056884402458717 54105069412521331650922019)
            ·
              refine ⟨81157604118781997476383029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54105069412521331650922019 81157604118781997476383029)
              ·
                refine ⟨7608525386135812263410909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81157604118781997476383029 7608525386135812263410909)
                ·
                  refine ⟨2853197019800929598779091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7608525386135812263410909 2853197019800929598779091)
                  ·
                    refine ⟨4279795529701394398168637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2853197019800929598779091 4279795529701394398168637)
                    ·
                      refine ⟨1604923323638022899313239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4279795529701394398168637 1604923323638022899313239)
                      ·
                        rfl

theorem cell23_3125577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 1, 3].length) (baseStart_3125577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125577 prefixEnd_3125577 := by exact prefixLift 3125577
  have htrace : WordTrace (prefixWord ++ tailWord_3125577) baseStart_3125577 baseEnd_3125577 := by
    simpa [prefixWord, tailWord_3125577, baseEnd_3125577] using wordTrace_append hprefix tailTrace_3125577
  have hstable : (prefixWord ++ tailWord_3125577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125577).length < 2 ^ (prefixWord ++ tailWord_3125577).sum := by decide
  have hdescent : baseEnd_3125577 < baseStart_3125577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125580 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_3125580 : Nat := 118140960795 + 3125580 * 2 ^ 59
def prefixEnd_3125580 : Nat := 4983230072969 + 3 ^ 40 * 3125580 * 2
def baseEnd_3125580 : Nat := 534974954693328795858575

theorem tailTrace_3125580 : CollatzResearch.WordTrace tailWord_3125580 prefixEnd_3125580 534974954693328795858575 := by
  unfold tailWord_3125580
  simp only [CollatzResearch.WordTrace]
  refine ⟨56999634008282470705299097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75999512011043294273732129 56999634008282470705299097)
  ·
    refine ⟨42749725506211853028974323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56999634008282470705299097 42749725506211853028974323)
    ·
      refine ⟨64124588259317779543461485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42749725506211853028974323 64124588259317779543461485)
      ·
        refine ⟨24046720597244167328798057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64124588259317779543461485 24046720597244167328798057)
        ·
          refine ⟨18035040447933125496598543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24046720597244167328798057 18035040447933125496598543)
          ·
            refine ⟨27052560671899688244897815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18035040447933125496598543 27052560671899688244897815)
            ·
              refine ⟨40578841007849532367346723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27052560671899688244897815 40578841007849532367346723)
              ·
                refine ⟨60868261511774298551020085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40578841007849532367346723 60868261511774298551020085)
                ·
                  refine ⟨5706399516728840489158133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60868261511774298551020085 5706399516728840489158133)
                  ·
                    refine ⟨534974954693328795858575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5706399516728840489158133 534974954693328795858575)
                    ·
                      rfl

theorem cell23_3125580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_3125580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125580 prefixEnd_3125580 := by exact prefixLift 3125580
  have htrace : WordTrace (prefixWord ++ tailWord_3125580) baseStart_3125580 baseEnd_3125580 := by
    simpa [prefixWord, tailWord_3125580, baseEnd_3125580] using wordTrace_append hprefix tailTrace_3125580
  have hstable : (prefixWord ++ tailWord_3125580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125580).length < 2 ^ (prefixWord ++ tailWord_3125580).sum := by decide
  have hdescent : baseEnd_3125580 < baseStart_3125580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125627 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 4, 4]
def baseStart_3125627 : Nat := 118140960795 + 3125627 * 2 ^ 59
def prefixEnd_3125627 : Nat := 4983230072969 + 3 ^ 40 * 3125627 * 2
def baseEnd_3125627 : Nat := 534982999223582567896003

theorem tailTrace_3125627 : CollatzResearch.WordTrace tailWord_3125627 prefixEnd_3125627 534982999223582567896003 := by
  unfold tailWord_3125627
  simp only [CollatzResearch.WordTrace]
  refine ⟨114000982247394668437559135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76000654831596445625039423 114000982247394668437559135)
  ·
    refine ⟨171001473371092002656338703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114000982247394668437559135 171001473371092002656338703)
    ·
      refine ⟨256502210056638003984508055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171001473371092002656338703 256502210056638003984508055)
      ·
        refine ⟨384753315084957005976762083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256502210056638003984508055 384753315084957005976762083)
        ·
          refine ⟨577129972627435508965143125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384753315084957005976762083 577129972627435508965143125)
          ·
            refine ⟨6763241866727759870685271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 577129972627435508965143125 6763241866727759870685271)
            ·
              refine ⟨10144862800091639806027907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763241866727759870685271 10144862800091639806027907)
              ·
                refine ⟨15217294200137459709041861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10144862800091639806027907 15217294200137459709041861)
                ·
                  refine ⟨2853242662525773695445349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15217294200137459709041861 2853242662525773695445349)
                  ·
                    refine ⟨534982999223582567896003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2853242662525773695445349 534982999223582567896003)
                    ·
                      rfl

theorem cell23_3125627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 4].length) (baseStart_3125627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125627 prefixEnd_3125627 := by exact prefixLift 3125627
  have htrace : WordTrace (prefixWord ++ tailWord_3125627) baseStart_3125627 baseEnd_3125627 := by
    simpa [prefixWord, tailWord_3125627, baseEnd_3125627] using wordTrace_append hprefix tailTrace_3125627
  have hstable : (prefixWord ++ tailWord_3125627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125627).length < 2 ^ (prefixWord ++ tailWord_3125627).sum := by decide
  have hdescent : baseEnd_3125627 < baseStart_3125627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125640 : List Nat := [2, 1, 3, 3, 1, 1, 2, 10]
def baseStart_3125640 : Nat := 118140960795 + 3125640 * 2 ^ 59
def prefixEnd_3125640 : Nat := 4983230072969 + 3 ^ 40 * 3125640 * 2
def baseEnd_3125640 : Nat := 59442802700713190845387

theorem tailTrace_3125640 : CollatzResearch.WordTrace tailWord_3125640 prefixEnd_3125640 59442802700713190845387 := by
  unfold tailWord_3125640
  simp only [CollatzResearch.WordTrace]
  refine ⟨57000728198173785828891187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76000970930898381105188249 57000728198173785828891187)
  ·
    refine ⟨85501092297260678743336781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57000728198173785828891187 85501092297260678743336781)
    ·
      refine ⟨32062909611472754528751293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85501092297260678743336781 32062909611472754528751293)
      ·
        refine ⟨12023591104302282948281735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32062909611472754528751293 12023591104302282948281735)
        ·
          refine ⟨18035386656453424422422603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12023591104302282948281735 18035386656453424422422603)
          ·
            refine ⟨27053079984680136633633905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18035386656453424422422603 27053079984680136633633905)
            ·
              refine ⟨20289809988510102475225429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27053079984680136633633905 20289809988510102475225429)
              ·
                refine ⟨59442802700713190845387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20289809988510102475225429 59442802700713190845387)
                ·
                  rfl

theorem cell23_3125640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 10].length) (baseStart_3125640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125640 prefixEnd_3125640 := by exact prefixLift 3125640
  have htrace : WordTrace (prefixWord ++ tailWord_3125640) baseStart_3125640 baseEnd_3125640 := by
    simpa [prefixWord, tailWord_3125640, baseEnd_3125640] using wordTrace_append hprefix tailTrace_3125640
  have hstable : (prefixWord ++ tailWord_3125640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125640).length < 2 ^ (prefixWord ++ tailWord_3125640).sum := by decide
  have hdescent : baseEnd_3125640 < baseStart_3125640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125668 : List Nat := [2, 3, 1, 2, 1, 1, 5, 3, 1, 2, 2]
def baseStart_3125668 : Nat := 118140960795 + 3125668 * 2 ^ 59
def prefixEnd_3125668 : Nat := 4983230072969 + 3 ^ 40 * 3125668 * 2
def baseEnd_3125668 : Nat := 1604970050377582043275321

theorem tailTrace_3125668 : CollatzResearch.WordTrace tailWord_3125668 prefixEnd_3125668 1604970050377582043275321 := by
  unfold tailWord_3125668
  simp only [CollatzResearch.WordTrace]
  refine ⟨57001238820123066219900829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76001651760164088293201105 57001238820123066219900829)
  ·
    refine ⟨21375464557546149832462811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57001238820123066219900829 21375464557546149832462811)
    ·
      refine ⟨32063196836319224748694217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21375464557546149832462811 32063196836319224748694217)
      ·
        refine ⟨24047397627239418561520663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32063196836319224748694217 24047397627239418561520663)
        ·
          refine ⟨36071096440859127842280995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24047397627239418561520663 36071096440859127842280995)
          ·
            refine ⟨54106644661288691763421493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36071096440859127842280995 54106644661288691763421493)
            ·
              refine ⟨5072497936995814852820765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54106644661288691763421493 5072497936995814852820765)
              ·
                refine ⟨1902186726373430569807787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5072497936995814852820765 1902186726373430569807787)
                ·
                  refine ⟨2853280089560145854711681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1902186726373430569807787 2853280089560145854711681)
                  ·
                    refine ⟨2139960067170109391033761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2853280089560145854711681 2139960067170109391033761)
                    ·
                      refine ⟨1604970050377582043275321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139960067170109391033761 1604970050377582043275321)
                      ·
                        rfl

theorem cell23_3125668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_3125668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125668 prefixEnd_3125668 := by exact prefixLift 3125668
  have htrace : WordTrace (prefixWord ++ tailWord_3125668) baseStart_3125668 baseEnd_3125668 := by
    simpa [prefixWord, tailWord_3125668, baseEnd_3125668] using wordTrace_append hprefix tailTrace_3125668
  have hstable : (prefixWord ++ tailWord_3125668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125668).length < 2 ^ (prefixWord ++ tailWord_3125668).sum := by decide
  have hdescent : baseEnd_3125668 < baseStart_3125668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125685 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_3125685 : Nat := 118140960795 + 3125685 * 2 ^ 59
def prefixEnd_3125685 : Nat := 4983230072969 + 3 ^ 40 * 3125685 * 2
def baseEnd_3125685 : Nat := 1604978779548708476762743

theorem tailTrace_3125685 : CollatzResearch.WordTrace tailWord_3125685 prefixEnd_3125685 1604978779548708476762743 := by
  unfold tailWord_3125685
  simp only [CollatzResearch.WordTrace]
  refine ⟨114003097681184544343170509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76002065120789696228780339 114003097681184544343170509)
  ·
    refine ⟨42751161630444204128688941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114003097681184544343170509 42751161630444204128688941)
    ·
      refine ⟨16031685611416576548258353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42751161630444204128688941 16031685611416576548258353)
      ·
        refine ⟨12023764208562432411193765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16031685611416576548258353 12023764208562432411193765)
        ·
          refine ⟨2254455789105456077098831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12023764208562432411193765 2254455789105456077098831)
          ·
            refine ⟨3381683683658184115648247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254455789105456077098831 3381683683658184115648247)
            ·
              refine ⟨5072525525487276173472371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381683683658184115648247 5072525525487276173472371)
              ·
                refine ⟨7608788288230914260208557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072525525487276173472371 7608788288230914260208557)
                ·
                  refine ⟨2853295608086592847578209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7608788288230914260208557 2853295608086592847578209)
                  ·
                    refine ⟨2139971706064944635683657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2853295608086592847578209 2139971706064944635683657)
                    ·
                      refine ⟨1604978779548708476762743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2139971706064944635683657 1604978779548708476762743)
                      ·
                        rfl

theorem cell23_3125685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_3125685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125685 prefixEnd_3125685 := by exact prefixLift 3125685
  have htrace : WordTrace (prefixWord ++ tailWord_3125685) baseStart_3125685 baseEnd_3125685 := by
    simpa [prefixWord, tailWord_3125685, baseEnd_3125685] using wordTrace_append hprefix tailTrace_3125685
  have hstable : (prefixWord ++ tailWord_3125685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125685).length < 2 ^ (prefixWord ++ tailWord_3125685).sum := by decide
  have hdescent : baseEnd_3125685 < baseStart_3125685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125727 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_3125727 : Nat := 118140960795 + 3125727 * 2 ^ 59
def prefixEnd_3125727 : Nat := 4983230072969 + 3 ^ 40 * 3125727 * 2
def baseEnd_3125727 : Nat := 1605000345736197312437549

theorem tailTrace_3125727 : CollatzResearch.WordTrace tailWord_3125727 prefixEnd_3125727 1605000345736197312437549 := by
  unfold tailWord_3125727
  simp only [CollatzResearch.WordTrace]
  refine ⟨114004629547032385516199435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76003086364688257010799623 114004629547032385516199435)
  ·
    refine ⟨171006944320548578274299153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114004629547032385516199435 171006944320548578274299153)
    ·
      refine ⟨128255208240411433705724365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171006944320548578274299153 128255208240411433705724365)
      ·
        refine ⟨48095703090154287639646637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128255208240411433705724365 48095703090154287639646637)
        ·
          refine ⟨18035888658807857864867489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48095703090154287639646637 18035888658807857864867489)
          ·
            refine ⟨13526916494105893398650617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18035888658807857864867489 13526916494105893398650617)
            ·
              refine ⟨10145187370579420048987963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13526916494105893398650617 10145187370579420048987963)
              ·
                refine ⟨15217781055869130073481945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10145187370579420048987963 15217781055869130073481945)
                ·
                  refine ⟨11413335791901847555111459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15217781055869130073481945 11413335791901847555111459)
                  ·
                    refine ⟨17120003687852771332667189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11413335791901847555111459 17120003687852771332667189)
                    ·
                      refine ⟨1605000345736197312437549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17120003687852771332667189 1605000345736197312437549)
                      ·
                        rfl

theorem cell23_3125727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_3125727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125727 prefixEnd_3125727 := by exact prefixLift 3125727
  have htrace : WordTrace (prefixWord ++ tailWord_3125727) baseStart_3125727 baseEnd_3125727 := by
    simpa [prefixWord, tailWord_3125727, baseEnd_3125727] using wordTrace_append hprefix tailTrace_3125727
  have hstable : (prefixWord ++ tailWord_3125727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125727).length < 2 ^ (prefixWord ++ tailWord_3125727).sum := by decide
  have hdescent : baseEnd_3125727 < baseStart_3125727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125764 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 7]
def baseStart_3125764 : Nat := 118140960795 + 3125764 * 2 ^ 59
def prefixEnd_3125764 : Nat := 4983230072969 + 3 ^ 40 * 3125764 * 2
def baseEnd_3125764 : Nat := 178335482724490407519431

theorem tailTrace_3125764 : CollatzResearch.WordTrace tailWord_3125764 prefixEnd_3125764 178335482724490407519431 := by
  unfold tailWord_3125764
  simp only [CollatzResearch.WordTrace]
  refine ⟨57002989523949170417648173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76003986031932227223530897 57002989523949170417648173)
  ·
    refine ⟨21376121071480938906618065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57002989523949170417648173 21376121071480938906618065)
    ·
      refine ⟨16032090803610704179963549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21376121071480938906618065 16032090803610704179963549)
      ·
        refine ⟨6012034051354014067486331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16032090803610704179963549 6012034051354014067486331)
        ·
          refine ⟨9018051077031021101229497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6012034051354014067486331 9018051077031021101229497)
          ·
            refine ⟨6763538307773265825922123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9018051077031021101229497 6763538307773265825922123)
            ·
              refine ⟨10145307461659898738883185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763538307773265825922123 10145307461659898738883185)
              ·
                refine ⟨7608980596244924054162389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10145307461659898738883185 7608980596244924054162389)
                ·
                  refine ⟨178335482724490407519431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7608980596244924054162389 178335482724490407519431)
                  ·
                    rfl

theorem cell23_3125764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_3125764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125764 prefixEnd_3125764 := by exact prefixLift 3125764
  have htrace : WordTrace (prefixWord ++ tailWord_3125764) baseStart_3125764 baseEnd_3125764 := by
    simpa [prefixWord, tailWord_3125764, baseEnd_3125764] using wordTrace_append hprefix tailTrace_3125764
  have hstable : (prefixWord ++ tailWord_3125764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125764).length < 2 ^ (prefixWord ++ tailWord_3125764).sum := by decide
  have hdescent : baseEnd_3125764 < baseStart_3125764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125777 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 2, 5]
def baseStart_3125777 : Nat := 118140960795 + 3125777 * 2 ^ 59
def prefixEnd_3125777 : Nat := 4983230072969 + 3 ^ 40 * 3125777 * 2
def baseEnd_3125777 : Nat := 535008673256307372270773

theorem tailTrace_3125777 : CollatzResearch.WordTrace tailWord_3125777 prefixEnd_3125777 535008673256307372270773 := by
  unfold tailWord_3125777
  simp only [CollatzResearch.WordTrace]
  refine ⟨114006453196851244055519585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76004302131234162703679723 114006453196851244055519585)
  ·
    refine ⟨85504839897638433041639689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114006453196851244055519585 85504839897638433041639689)
    ·
      refine ⟨64128629923228824781229767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85504839897638433041639689 64128629923228824781229767)
      ·
        refine ⟨96192944884843237171844651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64128629923228824781229767 96192944884843237171844651)
        ·
          refine ⟨144289417327264855757766977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96192944884843237171844651 144289417327264855757766977)
          ·
            refine ⟨108217062995448641818325233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144289417327264855757766977 108217062995448641818325233)
            ·
              refine ⟨81162797246586481363743925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108217062995448641818325233 81162797246586481363743925)
              ·
                refine ⟨7609012241867482627850993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81162797246586481363743925 7609012241867482627850993)
                ·
                  refine ⟨5706759181400611970888245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7609012241867482627850993 5706759181400611970888245)
                  ·
                    refine ⟨535008673256307372270773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5706759181400611970888245 535008673256307372270773)
                    ·
                      rfl

theorem cell23_3125777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_3125777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125777 prefixEnd_3125777 := by exact prefixLift 3125777
  have htrace : WordTrace (prefixWord ++ tailWord_3125777) baseStart_3125777 baseEnd_3125777 := by
    simpa [prefixWord, tailWord_3125777, baseEnd_3125777] using wordTrace_append hprefix tailTrace_3125777
  have hstable : (prefixWord ++ tailWord_3125777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125777).length < 2 ^ (prefixWord ++ tailWord_3125777).sum := by decide
  have hdescent : baseEnd_3125777 < baseStart_3125777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125792 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3125792 : Nat := 118140960795 + 3125792 * 2 ^ 59
def prefixEnd_3125792 : Nat := 4983230072969 + 3 ^ 40 * 3125792 * 2
def baseEnd_3125792 : Nat := 1605033721978739558124751

theorem tailTrace_3125792 : CollatzResearch.WordTrace tailWord_3125792 prefixEnd_3125792 1605033721978739558124751 := by
  unfold tailWord_3125792
  simp only [CollatzResearch.WordTrace]
  refine ⟨57003500145898450808657815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76004666861197934411543753 57003500145898450808657815)
  ·
    refine ⟨85505250218847676212986723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57003500145898450808657815 85505250218847676212986723)
    ·
      refine ⟨128257875328271514319480085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85505250218847676212986723 128257875328271514319480085)
      ·
        refine ⟨6012087906012727233725629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128257875328271514319480085 6012087906012727233725629)
        ·
          refine ⟨2254532964754772712647111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6012087906012727233725629 2254532964754772712647111)
          ·
            refine ⟨3381799447132159068970667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254532964754772712647111 3381799447132159068970667)
            ·
              refine ⟨5072699170698238603456001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381799447132159068970667 5072699170698238603456001)
              ·
                refine ⟨3804524378023678952592001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5072699170698238603456001 3804524378023678952592001)
                ·
                  refine ⟨2853393283517759214444001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3804524378023678952592001 2853393283517759214444001)
                  ·
                    refine ⟨2140044962638319410833001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2853393283517759214444001 2140044962638319410833001)
                    ·
                      refine ⟨1605033721978739558124751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140044962638319410833001 1605033721978739558124751)
                      ·
                        rfl

theorem cell23_3125792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3125792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125792 prefixEnd_3125792 := by exact prefixLift 3125792
  have htrace : WordTrace (prefixWord ++ tailWord_3125792) baseStart_3125792 baseEnd_3125792 := by
    simpa [prefixWord, tailWord_3125792, baseEnd_3125792] using wordTrace_append hprefix tailTrace_3125792
  have hstable : (prefixWord ++ tailWord_3125792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125792).length < 2 ^ (prefixWord ++ tailWord_3125792).sum := by decide
  have hdescent : baseEnd_3125792 < baseStart_3125792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125824 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 3, 4]
def baseStart_3125824 : Nat := 118140960795 + 3125824 * 2 ^ 59
def prefixEnd_3125824 : Nat := 4983230072969 + 3 ^ 40 * 3125824 * 2
def baseEnd_3125824 : Nat := 535016717786561144308201

theorem tailTrace_3125824 : CollatzResearch.WordTrace tailWord_3125824 prefixEnd_3125824 535016717786561144308201 := by
  unfold tailWord_3125824
  simp only [CollatzResearch.WordTrace]
  refine ⟨57004083713840485541240263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76005444951787314054987017 57004083713840485541240263)
  ·
    refine ⟨85506125570760728311860395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57004083713840485541240263 85506125570760728311860395)
    ·
      refine ⟨128259188356141092467790593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85506125570760728311860395 128259188356141092467790593)
      ·
        refine ⟨96194391267105819350842945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128259188356141092467790593 96194391267105819350842945)
        ·
          refine ⟨72145793450329364513132209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96194391267105819350842945 72145793450329364513132209)
          ·
            refine ⟨54109345087747023384849157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72145793450329364513132209 54109345087747023384849157)
            ·
              refine ⟨10145502203952566884659217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54109345087747023384849157 10145502203952566884659217)
              ·
                refine ⟨7609126652964425163494413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10145502203952566884659217 7609126652964425163494413)
                ·
                  refine ⟨2853422494861659436310405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7609126652964425163494413 2853422494861659436310405)
                  ·
                    refine ⟨535016717786561144308201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2853422494861659436310405 535016717786561144308201)
                    ·
                      rfl

theorem cell23_3125824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3, 4].length) (baseStart_3125824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125824 prefixEnd_3125824 := by exact prefixLift 3125824
  have htrace : WordTrace (prefixWord ++ tailWord_3125824) baseStart_3125824 baseEnd_3125824 := by
    simpa [prefixWord, tailWord_3125824, baseEnd_3125824] using wordTrace_append hprefix tailTrace_3125824
  have hstable : (prefixWord ++ tailWord_3125824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125824).length < 2 ^ (prefixWord ++ tailWord_3125824).sum := by decide
  have hdescent : baseEnd_3125824 < baseStart_3125824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125834 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_3125834 : Nat := 118140960795 + 3125834 * 2 ^ 59
def prefixEnd_3125834 : Nat := 4983230072969 + 3 ^ 40 * 3125834 * 2
def baseEnd_3125834 : Nat := 1605055288166228393799557

theorem tailTrace_3125834 : CollatzResearch.WordTrace tailWord_3125834 prefixEnd_3125834 1605055288166228393799557 := by
  unfold tailWord_3125834
  simp only [CollatzResearch.WordTrace]
  refine ⟨28502133039411185697586139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76005688105096495193563037 28502133039411185697586139)
  ·
    refine ⟨42753199559116778546379209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28502133039411185697586139 42753199559116778546379209)
    ·
      refine ⟨32064899669337583909784407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42753199559116778546379209 32064899669337583909784407)
      ·
        refine ⟨48097349504006375864676611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32064899669337583909784407 48097349504006375864676611)
        ·
          refine ⟨72146024256009563797014917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48097349504006375864676611 72146024256009563797014917)
          ·
            refine ⟨13527379548001793211940297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72146024256009563797014917 13527379548001793211940297)
            ·
              refine ⟨10145534661001344908955223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13527379548001793211940297 10145534661001344908955223)
              ·
                refine ⟨15218301991502017363432835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10145534661001344908955223 15218301991502017363432835)
                ·
                  refine ⟨22827452987253026045149253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15218301991502017363432835 22827452987253026045149253)
                  ·
                    refine ⟨4280147435109942383465485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22827452987253026045149253 4280147435109942383465485)
                    ·
                      refine ⟨1605055288166228393799557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4280147435109942383465485 1605055288166228393799557)
                      ·
                        rfl

theorem cell23_3125834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_3125834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125834 prefixEnd_3125834 := by exact prefixLift 3125834
  have htrace : WordTrace (prefixWord ++ tailWord_3125834) baseStart_3125834 baseEnd_3125834 := by
    simpa [prefixWord, tailWord_3125834, baseEnd_3125834] using wordTrace_append hprefix tailTrace_3125834
  have hstable : (prefixWord ++ tailWord_3125834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125834).length < 2 ^ (prefixWord ++ tailWord_3125834).sum := by decide
  have hdescent : baseEnd_3125834 < baseStart_3125834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125891 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 2, 3, 2]
def baseStart_3125891 : Nat := 118140960795 + 3125891 * 2 ^ 59
def prefixEnd_3125891 : Nat := 4983230072969 + 3 ^ 40 * 3125891 * 2
def baseEnd_3125891 : Nat := 1605084556563534670786795

theorem tailTrace_3125891 : CollatzResearch.WordTrace tailWord_3125891 prefixEnd_3125891 1605084556563534670786795 := by
  unfold tailWord_3125891
  simp only [CollatzResearch.WordTrace]
  refine ⟨114010611118438241525169527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76007074078958827683446351 114010611118438241525169527)
  ·
    refine ⟨171015916677657362287754291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114010611118438241525169527 171015916677657362287754291)
    ·
      refine ⟨256523875016486043431631437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171015916677657362287754291 256523875016486043431631437)
      ·
        refine ⟨96196453131182266286861789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256523875016486043431631437 96196453131182266286861789)
        ·
          refine ⟨36073669924193349857573171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96196453131182266286861789 36073669924193349857573171)
          ·
            refine ⟨54110504886290024786359757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36073669924193349857573171 54110504886290024786359757)
            ·
              refine ⟨20291439332358759294884909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54110504886290024786359757 20291439332358759294884909)
              ·
                refine ⟨7609289749634534735581841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20291439332358759294884909 7609289749634534735581841)
                ·
                  refine ⟨5706967312225901051686381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7609289749634534735581841 5706967312225901051686381)
                  ·
                    refine ⟨2140112742084712894382393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5706967312225901051686381 2140112742084712894382393)
                    ·
                      refine ⟨1605084556563534670786795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140112742084712894382393 1605084556563534670786795)
                      ·
                        rfl

theorem cell23_3125891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_3125891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125891 prefixEnd_3125891 := by exact prefixLift 3125891
  have htrace : WordTrace (prefixWord ++ tailWord_3125891) baseStart_3125891 baseEnd_3125891 := by
    simpa [prefixWord, tailWord_3125891, baseEnd_3125891] using wordTrace_append hprefix tailTrace_3125891
  have hstable : (prefixWord ++ tailWord_3125891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125891).length < 2 ^ (prefixWord ++ tailWord_3125891).sum := by decide
  have hdescent : baseEnd_3125891 < baseStart_3125891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125924 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_3125924 : Nat := 118140960795 + 3125924 * 2 ^ 59
def prefixEnd_3125924 : Nat := 4983230072969 + 3 ^ 40 * 3125924 * 2
def baseEnd_3125924 : Nat := 1605101501425133041674143

theorem tailTrace_3125924 : CollatzResearch.WordTrace tailWord_3125924 prefixEnd_3125924 1605101501425133041674143 := by
  unfold tailWord_3125924
  simp only [CollatzResearch.WordTrace]
  refine ⟨57005907363659344080560413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76007876484879125440747217 57005907363659344080560413)
  ·
    refine ⟨21377215261372254030210155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57005907363659344080560413 21377215261372254030210155)
    ·
      refine ⟨32065822892058381045315233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21377215261372254030210155 32065822892058381045315233)
      ·
        refine ⟨24049367169043785783986425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32065822892058381045315233 24049367169043785783986425)
        ·
          refine ⟨18037025376782839337989819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24049367169043785783986425 18037025376782839337989819)
          ·
            refine ⟨27055538065174259006984729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18037025376782839337989819 27055538065174259006984729)
            ·
              refine ⟨20291653548880694255238547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27055538065174259006984729 20291653548880694255238547)
              ·
                refine ⟨30437480323321041382857821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20291653548880694255238547 30437480323321041382857821)
                ·
                  refine ⟨11414055121245390518571683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30437480323321041382857821 11414055121245390518571683)
                  ·
                    refine ⟨17121082681868085777857525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11414055121245390518571683 17121082681868085777857525)
                    ·
                      refine ⟨1605101501425133041674143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17121082681868085777857525 1605101501425133041674143)
                      ·
                        rfl

theorem cell23_3125924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_3125924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125924 prefixEnd_3125924 := by exact prefixLift 3125924
  have htrace : WordTrace (prefixWord ++ tailWord_3125924) baseStart_3125924 baseEnd_3125924 := by
    simpa [prefixWord, tailWord_3125924, baseEnd_3125924] using wordTrace_append hprefix tailTrace_3125924
  have hstable : (prefixWord ++ tailWord_3125924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125924).length < 2 ^ (prefixWord ++ tailWord_3125924).sum := by decide
  have hdescent : baseEnd_3125924 < baseStart_3125924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125965 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3125965 : Nat := 118140960795 + 3125965 * 2 ^ 59
def prefixEnd_3125965 : Nat := 4983230072969 + 3 ^ 40 * 3125965 * 2
def baseEnd_3125965 : Nat := 535040851377322460420485

theorem tailTrace_3125965 : CollatzResearch.WordTrace tailWord_3125965 prefixEnd_3125965 535040851377322460420485 := by
  unfold tailWord_3125965
  simp only [CollatzResearch.WordTrace]
  refine ⟨114013310120170152163363349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76008873413446768108908899 114013310120170152163363349)
  ·
    refine ⟨5344373911882975882657657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114013310120170152163363349 5344373911882975882657657)
    ·
      refine ⟨4008280433912231911993243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5344373911882975882657657 4008280433912231911993243)
      ·
        refine ⟨6012420650868347867989865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4008280433912231911993243 6012420650868347867989865)
        ·
          refine ⟨4509315488151260900992399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6012420650868347867989865 4509315488151260900992399)
          ·
            refine ⟨6763973232226891351488599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4509315488151260900992399 6763973232226891351488599)
            ·
              refine ⟨10145959848340337027232899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763973232226891351488599 10145959848340337027232899)
              ·
                refine ⟨15218939772510505540849349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10145959848340337027232899 15218939772510505540849349)
                ·
                  refine ⟨2853551207345719788909253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15218939772510505540849349 2853551207345719788909253)
                  ·
                    refine ⟨535040851377322460420485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2853551207345719788909253 535040851377322460420485)
                    ·
                      rfl

theorem cell23_3125965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3125965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125965 prefixEnd_3125965 := by exact prefixLift 3125965
  have htrace : WordTrace (prefixWord ++ tailWord_3125965) baseStart_3125965 baseEnd_3125965 := by
    simpa [prefixWord, tailWord_3125965, baseEnd_3125965] using wordTrace_append hprefix tailTrace_3125965
  have hstable : (prefixWord ++ tailWord_3125965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125965).length < 2 ^ (prefixWord ++ tailWord_3125965).sum := by decide
  have hdescent : baseEnd_3125965 < baseStart_3125965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125972 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3125972 : Nat := 118140960795 + 3125972 * 2 ^ 59
def prefixEnd_3125972 : Nat := 4983230072969 + 3 ^ 40 * 3125972 * 2
def baseEnd_3125972 : Nat := 1605126148496548853873923

theorem tailTrace_3125972 : CollatzResearch.WordTrace tailWord_3125972 prefixEnd_3125972 1605126148496548853873923 := by
  unfold tailWord_3125972
  simp only [CollatzResearch.WordTrace]
  refine ⟨57006782715572396179434085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76009043620763194905912113 57006782715572396179434085)
  ·
    refine ⟨10688771759169824283643891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57006782715572396179434085 10688771759169824283643891)
    ·
      refine ⟨16033157638754736425465837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10688771759169824283643891 16033157638754736425465837)
      ·
        refine ⟨6012434114533026159549689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16033157638754736425465837 6012434114533026159549689)
        ·
          refine ⟨4509325585899769619662267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6012434114533026159549689 4509325585899769619662267)
          ·
            refine ⟨6763988378849654429493401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4509325585899769619662267 6763988378849654429493401)
            ·
              refine ⟨5072991284137240822120051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6763988378849654429493401 5072991284137240822120051)
              ·
                refine ⟨7609486926205861233180077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072991284137240822120051 7609486926205861233180077)
                ·
                  refine ⟨2853557597327197962442529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7609486926205861233180077 2853557597327197962442529)
                  ·
                    refine ⟨2140168197995398471831897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2853557597327197962442529 2140168197995398471831897)
                    ·
                      refine ⟨1605126148496548853873923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140168197995398471831897 1605126148496548853873923)
                      ·
                        rfl

theorem cell23_3125972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3125972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125972 prefixEnd_3125972 := by exact prefixLift 3125972
  have htrace : WordTrace (prefixWord ++ tailWord_3125972) baseStart_3125972 baseEnd_3125972 := by
    simpa [prefixWord, tailWord_3125972, baseEnd_3125972] using wordTrace_append hprefix tailTrace_3125972
  have hstable : (prefixWord ++ tailWord_3125972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125972).length < 2 ^ (prefixWord ++ tailWord_3125972).sum := by decide
  have hdescent : baseEnd_3125972 < baseStart_3125972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3125988 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_3125988 : Nat := 118140960795 + 3125988 * 2 ^ 59
def prefixEnd_3125988 : Nat := 4983230072969 + 3 ^ 40 * 3125988 * 2
def baseEnd_3125988 : Nat := 1605134364187020791273849

theorem tailTrace_3125988 : CollatzResearch.WordTrace tailWord_3125988 prefixEnd_3125988 1605134364187020791273849 := by
  unfold tailWord_3125988
  simp only [CollatzResearch.WordTrace]
  refine ⟨57007074499543413545725309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76009432666057884727633745 57007074499543413545725309)
  ·
    refine ⟨21377652937328780079646991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57007074499543413545725309 21377652937328780079646991)
    ·
      refine ⟨32066479405993170119470487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21377652937328780079646991 32066479405993170119470487)
      ·
        refine ⟨48099719108989755179205731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32066479405993170119470487 48099719108989755179205731)
        ·
          refine ⟨72149578663484632768808597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48099719108989755179205731 72149578663484632768808597)
          ·
            refine ⟨3382011499850842161037903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72149578663484632768808597 3382011499850842161037903)
            ·
              refine ⟨5073017249776263241556855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382011499850842161037903 5073017249776263241556855)
              ·
                refine ⟨7609525874664394862335283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5073017249776263241556855 7609525874664394862335283)
                ·
                  refine ⟨11414288811996592293502925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7609525874664394862335283 11414288811996592293502925)
                  ·
                    refine ⟨4280358304498722110063597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11414288811996592293502925 4280358304498722110063597)
                    ·
                      refine ⟨1605134364187020791273849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4280358304498722110063597 1605134364187020791273849)
                      ·
                        rfl

theorem cell23_3125988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_3125988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3125988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3125988 prefixEnd_3125988 := by exact prefixLift 3125988
  have htrace : WordTrace (prefixWord ++ tailWord_3125988) baseStart_3125988 baseEnd_3125988 := by
    simpa [prefixWord, tailWord_3125988, baseEnd_3125988] using wordTrace_append hprefix tailTrace_3125988
  have hstable : (prefixWord ++ tailWord_3125988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3125988).length < 2 ^ (prefixWord ++ tailWord_3125988).sum := by decide
  have hdescent : baseEnd_3125988 < baseStart_3125988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3125988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126039 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 2, 1, 3]
def baseStart_3126039 : Nat := 118140960795 + 3126039 * 2 ^ 59
def prefixEnd_3126039 : Nat := 4983230072969 + 3 ^ 40 * 3126039 * 2
def baseEnd_3126039 : Nat := 1605160551700400091736115

theorem tailTrace_3126039 : CollatzResearch.WordTrace tailWord_3126039 prefixEnd_3126039 1605160551700400091736115 := by
  unfold tailWord_3126039
  simp only [CollatzResearch.WordTrace]
  refine ⟨114016009121902062801557171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76010672747934708534371447 114016009121902062801557171)
  ·
    refine ⟨171024013682853094202335757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114016009121902062801557171 171024013682853094202335757)
    ·
      refine ⟨64134005131069910325875909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171024013682853094202335757 64134005131069910325875909)
      ·
        refine ⟨12025125962075608186101733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64134005131069910325875909 12025125962075608186101733)
        ·
          refine ⟨2254711117889176534894075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12025125962075608186101733 2254711117889176534894075)
          ·
            refine ⟨3382066676833764802341113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254711117889176534894075 3382066676833764802341113)
            ·
              refine ⟨2536550007625323601755835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3382066676833764802341113 2536550007625323601755835)
              ·
                refine ⟨3804825011437985402633753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536550007625323601755835 3804825011437985402633753)
                ·
                  refine ⟨2853618758578489051975315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3804825011437985402633753 2853618758578489051975315)
                  ·
                    refine ⟨4280428137867733577962973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2853618758578489051975315 4280428137867733577962973)
                    ·
                      refine ⟨1605160551700400091736115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4280428137867733577962973 1605160551700400091736115)
                      ·
                        rfl

theorem cell23_3126039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_3126039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126039 prefixEnd_3126039 := by exact prefixLift 3126039
  have htrace : WordTrace (prefixWord ++ tailWord_3126039) baseStart_3126039 baseEnd_3126039 := by
    simpa [prefixWord, tailWord_3126039, baseEnd_3126039] using wordTrace_append hprefix tailTrace_3126039
  have hstable : (prefixWord ++ tailWord_3126039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126039).length < 2 ^ (prefixWord ++ tailWord_3126039).sum := by decide
  have hdescent : baseEnd_3126039 < baseStart_3126039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126064 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 1, 7]
def baseStart_3126064 : Nat := 118140960795 + 3126064 * 2 ^ 59
def prefixEnd_3126064 : Nat := 4983230072969 + 3 ^ 40 * 3126064 * 2
def baseEnd_3126064 : Nat := 535057796238920831307833

theorem tailTrace_3126064 : CollatzResearch.WordTrace tailWord_3126064 prefixEnd_3126064 535057796238920831307833 := by
  unfold tailWord_3126064
  simp only [CollatzResearch.WordTrace]
  refine ⟨57008460473405746035608623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76011280631207661380811497 57008460473405746035608623)
  ·
    refine ⟨85512690710108619053412935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57008460473405746035608623 85512690710108619053412935)
    ·
      refine ⟨128269036065162928580119403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85512690710108619053412935 128269036065162928580119403)
      ·
        refine ⟨192403554097744392870179105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128269036065162928580119403 192403554097744392870179105)
        ·
          refine ⟨144302665573308294652634329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192403554097744392870179105 144302665573308294652634329)
          ·
            refine ⟨108226999179981220989475747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144302665573308294652634329 108226999179981220989475747)
            ·
              refine ⟨162340498769971831484213621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108226999179981220989475747 162340498769971831484213621)
              ·
                refine ⟨15219421759684859201645027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162340498769971831484213621 15219421759684859201645027)
                ·
                  refine ⟨22829132639527288802467541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15219421759684859201645027 22829132639527288802467541)
                  ·
                    refine ⟨535057796238920831307833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22829132639527288802467541 535057796238920831307833)
                    ·
                      rfl

theorem cell23_3126064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_3126064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126064 prefixEnd_3126064 := by exact prefixLift 3126064
  have htrace : WordTrace (prefixWord ++ tailWord_3126064) baseStart_3126064 baseEnd_3126064 := by
    simpa [prefixWord, tailWord_3126064, baseEnd_3126064] using wordTrace_append hprefix tailTrace_3126064
  have hstable : (prefixWord ++ tailWord_3126064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126064).length < 2 ^ (prefixWord ++ tailWord_3126064).sum := by decide
  have hdescent : baseEnd_3126064 < baseStart_3126064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126101 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3126101 : Nat := 118140960795 + 3126101 * 2 ^ 59
def prefixEnd_3126101 : Nat := 4983230072969 + 3 ^ 40 * 3126101 * 2
def baseEnd_3126101 : Nat := 1605192387500978849160829

theorem tailTrace_3126101 : CollatzResearch.WordTrace tailWord_3126101 prefixEnd_3126101 1605192387500978849160829 := by
  unfold tailWord_3126101
  simp only [CollatzResearch.WordTrace]
  refine ⟨114018270447677447390314157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76012180298451631593542771 114018270447677447390314157)
  ·
    refine ⟨42756851417879042771367809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114018270447677447390314157 42756851417879042771367809)
    ·
      refine ⟨32067638563409282078525857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42756851417879042771367809 32067638563409282078525857)
      ·
        refine ⟨24050728922556961558894393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32067638563409282078525857 24050728922556961558894393)
        ·
          refine ⟨18038046691917721169170795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24050728922556961558894393 18038046691917721169170795)
          ·
            refine ⟨27057070037876581753756193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18038046691917721169170795 27057070037876581753756193)
            ·
              refine ⟨20292802528407436315317145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27057070037876581753756193 20292802528407436315317145)
              ·
                refine ⟨15219601896305577236487859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20292802528407436315317145 15219601896305577236487859)
                ·
                  refine ⟨22829402844458365854731789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15219601896305577236487859 22829402844458365854731789)
                  ·
                    refine ⟨8561026066671887195524421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22829402844458365854731789 8561026066671887195524421)
                    ·
                      refine ⟨1605192387500978849160829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8561026066671887195524421 1605192387500978849160829)
                      ·
                        rfl

theorem cell23_3126101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3126101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126101 prefixEnd_3126101 := by exact prefixLift 3126101
  have htrace : WordTrace (prefixWord ++ tailWord_3126101) baseStart_3126101 baseEnd_3126101 := by
    simpa [prefixWord, tailWord_3126101, baseEnd_3126101] using wordTrace_append hprefix tailTrace_3126101
  have hstable : (prefixWord ++ tailWord_3126101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126101).length < 2 ^ (prefixWord ++ tailWord_3126101).sum := by decide
  have hdescent : baseEnd_3126101 < baseStart_3126101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126196 : List Nat := [2, 5, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3126196 : Nat := 118140960795 + 3126196 * 2 ^ 59
def prefixEnd_3126196 : Nat := 4983230072969 + 3 ^ 40 * 3126196 * 2
def baseEnd_3126196 : Nat := 535080389387718659157631

theorem tailTrace_3126196 : CollatzResearch.WordTrace tailWord_3126196 prefixEnd_3126196 535080389387718659157631 := by
  unfold tailWord_3126196
  simp only [CollatzResearch.WordTrace]
  refine ⟨57010867691166639307511221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76014490254888852410014961 57010867691166639307511221)
  ·
    refine ⟨5344768846046872435079177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57010867691166639307511221 5344768846046872435079177)
    ·
      refine ⟨4008576634535154326309383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5344768846046872435079177 4008576634535154326309383)
      ·
        refine ⟨6012864951802731489464075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4008576634535154326309383 6012864951802731489464075)
        ·
          refine ⟨9019297427704097234196113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6012864951802731489464075 9019297427704097234196113)
          ·
            refine ⟨6764473070778072925647085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9019297427704097234196113 6764473070778072925647085)
            ·
              refine ⟨2536677401541777347117657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6764473070778072925647085 2536677401541777347117657)
              ·
                refine ⟨1902508051156333010338243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2536677401541777347117657 1902508051156333010338243)
                ·
                  refine ⟨2853762076734499515507365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1902508051156333010338243 2853762076734499515507365)
                  ·
                    refine ⟨535080389387718659157631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2853762076734499515507365 535080389387718659157631)
                    ·
                      rfl

theorem cell23_3126196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3126196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126196 prefixEnd_3126196 := by exact prefixLift 3126196
  have htrace : WordTrace (prefixWord ++ tailWord_3126196) baseStart_3126196 baseEnd_3126196 := by
    simpa [prefixWord, tailWord_3126196, baseEnd_3126196] using wordTrace_append hprefix tailTrace_3126196
  have hstable : (prefixWord ++ tailWord_3126196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126196).length < 2 ^ (prefixWord ++ tailWord_3126196).sum := by decide
  have hdescent : baseEnd_3126196 < baseStart_3126196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126225 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 5, 2, 2]
def baseStart_3126225 : Nat := 118140960795 + 3126225 * 2 ^ 59
def prefixEnd_3126225 : Nat := 4983230072969 + 3 ^ 40 * 3126225 * 2
def baseEnd_3126225 : Nat := 1605256059102136364010259

theorem tailTrace_3126225 : CollatzResearch.WordTrace tailWord_3126225 prefixEnd_3126225 1605256059102136364010259 := by
  unfold tailWord_3126225
  simp only [CollatzResearch.WordTrace]
  refine ⟨114022793099228216567828129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76015195399485477711885419 114022793099228216567828129)
  ·
    refine ⟨85517094824421162425871097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114022793099228216567828129 85517094824421162425871097)
    ·
      refine ⟨64137821118315871819403323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85517094824421162425871097 64137821118315871819403323)
      ·
        refine ⟨96206731677473807729104985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64137821118315871819403323 96206731677473807729104985)
        ·
          refine ⟨72155048758105355796828739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96206731677473807729104985 72155048758105355796828739)
          ·
            refine ⟨108232573137158033695243109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72155048758105355796828739 108232573137158033695243109)
            ·
              refine ⟨20293607463217131317858083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108232573137158033695243109 20293607463217131317858083)
              ·
                refine ⟨30440411194825696976787125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20293607463217131317858083 30440411194825696976787125)
                ·
                  refine ⟨2853788549514909091573793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30440411194825696976787125 2853788549514909091573793)
                  ·
                    refine ⟨2140341412136181818680345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2853788549514909091573793 2140341412136181818680345)
                    ·
                      refine ⟨1605256059102136364010259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140341412136181818680345 1605256059102136364010259)
                      ·
                        rfl

theorem cell23_3126225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_3126225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126225 prefixEnd_3126225 := by exact prefixLift 3126225
  have htrace : WordTrace (prefixWord ++ tailWord_3126225) baseStart_3126225 baseEnd_3126225 := by
    simpa [prefixWord, tailWord_3126225, baseEnd_3126225] using wordTrace_append hprefix tailTrace_3126225
  have hstable : (prefixWord ++ tailWord_3126225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126225).length < 2 ^ (prefixWord ++ tailWord_3126225).sum := by decide
  have hdescent : baseEnd_3126225 < baseStart_3126225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126271 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_3126271 : Nat := 118140960795 + 3126271 * 2 ^ 59
def prefixEnd_3126271 : Nat := 4983230072969 + 3 ^ 40 * 3126271 * 2
def baseEnd_3126271 : Nat := 1605279679212243184035047

theorem tailTrace_3126271 : CollatzResearch.WordTrace tailWord_3126271 prefixEnd_3126271 1605279679212243184035047 := by
  unfold tailWord_3126271
  simp only [CollatzResearch.WordTrace]
  refine ⟨114024470857061566424002667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76016313904707710949335111 114024470857061566424002667)
  ·
    refine ⟨171036706285592349636004001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114024470857061566424002667 171036706285592349636004001)
    ·
      refine ⟨128277529714194262227003001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171036706285592349636004001 128277529714194262227003001)
      ·
        refine ⟨96208147285645696670252251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128277529714194262227003001 96208147285645696670252251)
        ·
          refine ⟨144312220928468545005378377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96208147285645696670252251 144312220928468545005378377)
          ·
            refine ⟨108234165696351408754033783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144312220928468545005378377 108234165696351408754033783)
            ·
              refine ⟨162351248544527113131050675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108234165696351408754033783 162351248544527113131050675)
              ·
                refine ⟨243526872816790669696576013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162351248544527113131050675 243526872816790669696576013)
                ·
                  refine ⟨91322577306296501136216005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243526872816790669696576013 91322577306296501136216005)
                  ·
                    refine ⟨17122983244930593963040501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91322577306296501136216005 17122983244930593963040501)
                    ·
                      refine ⟨1605279679212243184035047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17122983244930593963040501 1605279679212243184035047)
                      ·
                        rfl

theorem cell23_3126271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_3126271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126271 prefixEnd_3126271 := by exact prefixLift 3126271
  have htrace : WordTrace (prefixWord ++ tailWord_3126271) baseStart_3126271 baseEnd_3126271 := by
    simpa [prefixWord, tailWord_3126271, baseEnd_3126271] using wordTrace_append hprefix tailTrace_3126271
  have hstable : (prefixWord ++ tailWord_3126271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126271).length < 2 ^ (prefixWord ++ tailWord_3126271).sum := by decide
  have hdescent : baseEnd_3126271 < baseStart_3126271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126291 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 3, 8]
def baseStart_3126291 : Nat := 118140960795 + 3126291 * 2 ^ 59
def prefixEnd_3126291 : Nat := 4983230072969 + 3 ^ 40 * 3126291 * 2
def baseEnd_3126291 : Nat := 535096649608444368594985

theorem tailTrace_3126291 : CollatzResearch.WordTrace tailWord_3126291 prefixEnd_3126291 535096649608444368594985 := by
  unfold tailWord_3126291
  simp only [CollatzResearch.WordTrace]
  refine ⟨114025200316989109839730727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76016800211326073226487151 114025200316989109839730727)
  ·
    refine ⟨171037800475483664759596091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114025200316989109839730727 171037800475483664759596091)
    ·
      refine ⟨256556700713225497139394137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171037800475483664759596091 256556700713225497139394137)
      ·
        refine ⟨192417525534919122854545603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256556700713225497139394137 192417525534919122854545603)
        ·
          refine ⟨288626288302378684281818405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192417525534919122854545603 288626288302378684281818405)
          ·
            refine ⟨54117429056696003302840951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288626288302378684281818405 54117429056696003302840951)
            ·
              refine ⟨81176143585044004954261427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54117429056696003302840951 81176143585044004954261427)
              ·
                refine ⟨121764215377566007431392141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81176143585044004954261427 121764215377566007431392141)
                ·
                  refine ⟨45661580766587252786772053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121764215377566007431392141 45661580766587252786772053)
                  ·
                    refine ⟨535096649608444368594985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45661580766587252786772053 535096649608444368594985)
                    ·
                      rfl

theorem cell23_3126291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 8].length) (baseStart_3126291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126291 prefixEnd_3126291 := by exact prefixLift 3126291
  have htrace : WordTrace (prefixWord ++ tailWord_3126291) baseStart_3126291 baseEnd_3126291 := by
    simpa [prefixWord, tailWord_3126291, baseEnd_3126291] using wordTrace_append hprefix tailTrace_3126291
  have hstable : (prefixWord ++ tailWord_3126291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126291).length < 2 ^ (prefixWord ++ tailWord_3126291).sum := by decide
  have hdescent : baseEnd_3126291 < baseStart_3126291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126326 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_3126326 : Nat := 118140960795 + 3126326 * 2 ^ 59
def prefixEnd_3126326 : Nat := 4983230072969 + 3 ^ 40 * 3126326 * 2
def baseEnd_3126326 : Nat := 1605307920648240468847295

theorem tailTrace_3126326 : CollatzResearch.WordTrace tailWord_3126326 prefixEnd_3126326 1605307920648240468847295 := by
  unfold tailWord_3126326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7126654804491394426078427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76017651247908207211503221 7126654804491394426078427)
  ·
    refine ⟨10689982206737091639117641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7126654804491394426078427 10689982206737091639117641)
    ·
      refine ⟨8017486655052818729338231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10689982206737091639117641 8017486655052818729338231)
      ·
        refine ⟨12026229982579228094007347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8017486655052818729338231 12026229982579228094007347)
        ·
          refine ⟨18039344973868842141011021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12026229982579228094007347 18039344973868842141011021)
          ·
            refine ⟨6764754365200815802879133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18039344973868842141011021 6764754365200815802879133)
            ·
              refine ⟨2536782886950305926079675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6764754365200815802879133 2536782886950305926079675)
              ·
                refine ⟨3805174330425458889119513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536782886950305926079675 3805174330425458889119513)
                ·
                  refine ⟨2853880747819094166839635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3805174330425458889119513 2853880747819094166839635)
                  ·
                    refine ⟨4280821121728641250259453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2853880747819094166839635 4280821121728641250259453)
                    ·
                      refine ⟨1605307920648240468847295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4280821121728641250259453 1605307920648240468847295)
                      ·
                        rfl

theorem cell23_3126326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_3126326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126326 prefixEnd_3126326 := by exact prefixLift 3126326
  have htrace : WordTrace (prefixWord ++ tailWord_3126326) baseStart_3126326 baseEnd_3126326 := by
    simpa [prefixWord, tailWord_3126326, baseEnd_3126326] using wordTrace_append hprefix tailTrace_3126326
  have hstable : (prefixWord ++ tailWord_3126326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126326).length < 2 ^ (prefixWord ++ tailWord_3126326).sum := by decide
  have hdescent : baseEnd_3126326 < baseStart_3126326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126332 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 1, 4, 2]
def baseStart_3126332 : Nat := 118140960795 + 3126332 * 2 ^ 59
def prefixEnd_3126332 : Nat := 4983230072969 + 3 ^ 40 * 3126332 * 2
def baseEnd_3126332 : Nat := 1605311001532167445372267

theorem tailTrace_3126332 : CollatzResearch.WordTrace tailWord_3126332 prefixEnd_3126332 1605311001532167445372267 := by
  unfold tailWord_3126332
  simp only [CollatzResearch.WordTrace]
  refine ⟨57013347854920286920986625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76017797139893715894648833 57013347854920286920986625)
  ·
    refine ⟨42760010891190215190739969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57013347854920286920986625 42760010891190215190739969)
    ·
      refine ⟨32070008168392661393054977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42760010891190215190739969 32070008168392661393054977)
      ·
        refine ⟨24052506126294496044791233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32070008168392661393054977 24052506126294496044791233)
        ·
          refine ⟨18039379594720872033593425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24052506126294496044791233 18039379594720872033593425)
          ·
            refine ⟨13529534696040654025195069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18039379594720872033593425 13529534696040654025195069)
            ·
              refine ⟨5073575511015245259448151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13529534696040654025195069 5073575511015245259448151)
              ·
                refine ⟨7610363266522867889172227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5073575511015245259448151 7610363266522867889172227)
                ·
                  refine ⟨11415544899784301833758341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7610363266522867889172227 11415544899784301833758341)
                  ·
                    refine ⟨2140414668709556593829689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11415544899784301833758341 2140414668709556593829689)
                    ·
                      refine ⟨1605311001532167445372267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140414668709556593829689 1605311001532167445372267)
                      ·
                        rfl

theorem cell23_3126332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_3126332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126332 prefixEnd_3126332 := by exact prefixLift 3126332
  have htrace : WordTrace (prefixWord ++ tailWord_3126332) baseStart_3126332 baseEnd_3126332 := by
    simpa [prefixWord, tailWord_3126332, baseEnd_3126332] using wordTrace_append hprefix tailTrace_3126332
  have hstable : (prefixWord ++ tailWord_3126332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126332).length < 2 ^ (prefixWord ++ tailWord_3126332).sum := by decide
  have hdescent : baseEnd_3126332 < baseStart_3126332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126349 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_3126349 : Nat := 118140960795 + 3126349 * 2 ^ 59
def prefixEnd_3126349 : Nat := 4983230072969 + 3 ^ 40 * 3126349 * 2
def baseEnd_3126349 : Nat := 1605319730703293878859689

theorem tailTrace_3126349 : CollatzResearch.WordTrace tailWord_3126349 prefixEnd_3126349 1605319730703293878859689 := by
  unfold tailWord_3126349
  simp only [CollatzResearch.WordTrace]
  refine ⟨114027315750778985745342101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76018210500519323830228067 114027315750778985745342101)
  ·
    refine ⟨5345030425817764956812911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114027315750778985745342101 5345030425817764956812911)
    ·
      refine ⟨8017545638726647435219367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5345030425817764956812911 8017545638726647435219367)
      ·
        refine ⟨12026318458089971152829051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8017545638726647435219367 12026318458089971152829051)
        ·
          refine ⟨18039477687134956729243577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12026318458089971152829051 18039477687134956729243577)
          ·
            refine ⟨13529608265351217546932683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18039477687134956729243577 13529608265351217546932683)
            ·
              refine ⟨20294412398026826320399025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13529608265351217546932683 20294412398026826320399025)
              ·
                refine ⟨15220809298520119740299269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20294412398026826320399025 15220809298520119740299269)
                ·
                  refine ⟨2853901743472522451306113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15220809298520119740299269 2853901743472522451306113)
                  ·
                    refine ⟨2140426307604391838479585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2853901743472522451306113 2140426307604391838479585)
                    ·
                      refine ⟨1605319730703293878859689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140426307604391838479585 1605319730703293878859689)
                      ·
                        rfl

theorem cell23_3126349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_3126349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126349 prefixEnd_3126349 := by exact prefixLift 3126349
  have htrace : WordTrace (prefixWord ++ tailWord_3126349) baseStart_3126349 baseEnd_3126349 := by
    simpa [prefixWord, tailWord_3126349, baseEnd_3126349] using wordTrace_append hprefix tailTrace_3126349
  have hstable : (prefixWord ++ tailWord_3126349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126349).length < 2 ^ (prefixWord ++ tailWord_3126349).sum := by decide
  have hdescent : baseEnd_3126349 < baseStart_3126349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126439 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_3126439 : Nat := 118140960795 + 3126439 * 2 ^ 59
def prefixEnd_3126439 : Nat := 4983230072969 + 3 ^ 40 * 3126439 * 2
def baseEnd_3126439 : Nat := 1605365943962198526734275

theorem tailTrace_3126439 : CollatzResearch.WordTrace tailWord_3126439 prefixEnd_3126439 1605365943962198526734275 := by
  unfold tailWord_3126439
  simp only [CollatzResearch.WordTrace]
  refine ⟨114030598320452931116118371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76020398880301954077412247 114030598320452931116118371)
  ·
    refine ⟨171045897480679396674177557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114030598320452931116118371 171045897480679396674177557)
    ·
      refine ⟨8017776444406846719102073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 171045897480679396674177557 8017776444406846719102073)
      ·
        refine ⟨6013332333305135039326555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8017776444406846719102073 6013332333305135039326555)
        ·
          refine ⟨9019998499957702558989833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6013332333305135039326555 9019998499957702558989833)
          ·
            refine ⟨6764998874968276919242375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9019998499957702558989833 6764998874968276919242375)
            ·
              refine ⟨10147498312452415378863563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6764998874968276919242375 10147498312452415378863563)
              ·
                refine ⟨15221247468678623068295345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10147498312452415378863563 15221247468678623068295345)
                ·
                  refine ⟨11415935601508967301221509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15221247468678623068295345 11415935601508967301221509)
                  ·
                    refine ⟨2140487925282931368979033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11415935601508967301221509 2140487925282931368979033)
                    ·
                      refine ⟨1605365943962198526734275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140487925282931368979033 1605365943962198526734275)
                      ·
                        rfl

theorem cell23_3126439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_3126439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126439 prefixEnd_3126439 := by exact prefixLift 3126439
  have htrace : WordTrace (prefixWord ++ tailWord_3126439) baseStart_3126439 baseEnd_3126439 := by
    simpa [prefixWord, tailWord_3126439, baseEnd_3126439] using wordTrace_append hprefix tailTrace_3126439
  have hstable : (prefixWord ++ tailWord_3126439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126439).length < 2 ^ (prefixWord ++ tailWord_3126439).sum := by decide
  have hdescent : baseEnd_3126439 < baseStart_3126439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126448 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_3126448 : Nat := 118140960795 + 3126448 * 2 ^ 59
def prefixEnd_3126448 : Nat := 4983230072969 + 3 ^ 40 * 3126448 * 2
def baseEnd_3126448 : Nat := 1605370565288088991521733

theorem tailTrace_3126448 : CollatzResearch.WordTrace tailWord_3126448 prefixEnd_3126448 1605370565288088991521733 := by
  unfold tailWord_3126448
  simp only [CollatzResearch.WordTrace]
  refine ⟨57015463288710162826597999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76020617718280217102130665 57015463288710162826597999)
  ·
    refine ⟨85523194933065244239896999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57015463288710162826597999 85523194933065244239896999)
    ·
      refine ⟨128284792399597866359845499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85523194933065244239896999 128284792399597866359845499)
      ·
        refine ⟨192427188599396799539768249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128284792399597866359845499 192427188599396799539768249)
        ·
          refine ⟨144320391449547599654826187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192427188599396799539768249 144320391449547599654826187)
          ·
            refine ⟨216480587174321399482239281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144320391449547599654826187 216480587174321399482239281)
            ·
              refine ⟨162360440380741049611679461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216480587174321399482239281 162360440380741049611679461)
              ·
                refine ⟨30442582571388946802189899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162360440380741049611679461 30442582571388946802189899)
                ·
                  refine ⟨45663873857083420203284849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30442582571388946802189899 45663873857083420203284849)
                  ·
                    refine ⟨34247905392812565152463637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45663873857083420203284849 34247905392812565152463637)
                    ·
                      refine ⟨1605370565288088991521733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34247905392812565152463637 1605370565288088991521733)
                      ·
                        rfl

theorem cell23_3126448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_3126448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126448 prefixEnd_3126448 := by exact prefixLift 3126448
  have htrace : WordTrace (prefixWord ++ tailWord_3126448) baseStart_3126448 baseEnd_3126448 := by
    simpa [prefixWord, tailWord_3126448, baseEnd_3126448] using wordTrace_append hprefix tailTrace_3126448
  have hstable : (prefixWord ++ tailWord_3126448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126448).length < 2 ^ (prefixWord ++ tailWord_3126448).sum := by decide
  have hdescent : baseEnd_3126448 < baseStart_3126448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126495 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 4]
def baseStart_3126495 : Nat := 118140960795 + 3126495 * 2 ^ 59
def prefixEnd_3126495 : Nat := 4983230072969 + 3 ^ 40 * 3126495 * 2
def baseEnd_3126495 : Nat := 1605394698878850307634017

theorem tailTrace_3126495 : CollatzResearch.WordTrace tailWord_3126495 prefixEnd_3126495 1605394698878850307634017 := by
  unfold tailWord_3126495
  simp only [CollatzResearch.WordTrace]
  refine ⟨114032640808250052680156939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76021760538833368453437959 114032640808250052680156939)
  ·
    refine ⟨171048961212375079020235409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114032640808250052680156939 171048961212375079020235409)
    ·
      refine ⟨128286720909281309265176557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171048961212375079020235409 128286720909281309265176557)
      ·
        refine ⟨48107520340980490974441209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128286720909281309265176557 48107520340980490974441209)
        ·
          refine ⟨36080640255735368230830907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48107520340980490974441209 36080640255735368230830907)
          ·
            refine ⟨54120960383603052346246361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36080640255735368230830907 54120960383603052346246361)
            ·
              refine ⟨40590720287702289259684771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54120960383603052346246361 40590720287702289259684771)
              ·
                refine ⟨60886080431553433889527157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40590720287702289259684771 60886080431553433889527157)
                ·
                  refine ⟨5708070040458134427143171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60886080431553433889527157 5708070040458134427143171)
                  ·
                    refine ⟨8562105060687201640714757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5708070040458134427143171 8562105060687201640714757)
                    ·
                      refine ⟨1605394698878850307634017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8562105060687201640714757 1605394698878850307634017)
                      ·
                        rfl

theorem cell23_3126495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_3126495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126495 prefixEnd_3126495 := by exact prefixLift 3126495
  have htrace : WordTrace (prefixWord ++ tailWord_3126495) baseStart_3126495 baseEnd_3126495 := by
    simpa [prefixWord, tailWord_3126495, baseEnd_3126495] using wordTrace_append hprefix tailTrace_3126495
  have hstable : (prefixWord ++ tailWord_3126495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126495).length < 2 ^ (prefixWord ++ tailWord_3126495).sum := by decide
  have hdescent : baseEnd_3126495 < baseStart_3126495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126505 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 8, 4]
def baseStart_3126505 : Nat := 118140960795 + 3126505 * 2 ^ 59
def prefixEnd_3126505 : Nat := 4983230072969 + 3 ^ 40 * 3126505 * 2
def baseEnd_3126505 : Nat := 535133277895131756169657

theorem tailTrace_3126505 : CollatzResearch.WordTrace tailWord_3126505 prefixEnd_3126505 535133277895131756169657 := by
  unfold tailWord_3126505
  simp only [CollatzResearch.WordTrace]
  refine ⟨114033005538213824388020969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76022003692142549592013979 114033005538213824388020969)
  ·
    refine ⟨85524754153660368291015727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114033005538213824388020969 85524754153660368291015727)
    ·
      refine ⟨128287131230490552436523591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85524754153660368291015727 128287131230490552436523591)
      ·
        refine ⟨192430696845735828654785387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128287131230490552436523591 192430696845735828654785387)
        ·
          refine ⟨288646045268603742982178081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192430696845735828654785387 288646045268603742982178081)
          ·
            refine ⟨216484533951452807236633561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288646045268603742982178081 216484533951452807236633561)
            ·
              refine ⟨162363400463589605427475171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216484533951452807236633561 162363400463589605427475171)
              ·
                refine ⟨243545100695384408141212757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162363400463589605427475171 243545100695384408141212757)
                ·
                  refine ⟨2854044148774036032904837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 243545100695384408141212757 2854044148774036032904837)
                  ·
                    refine ⟨535133277895131756169657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2854044148774036032904837 535133277895131756169657)
                    ·
                      rfl

theorem cell23_3126505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 4].length) (baseStart_3126505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126505 prefixEnd_3126505 := by exact prefixLift 3126505
  have htrace : WordTrace (prefixWord ++ tailWord_3126505) baseStart_3126505 baseEnd_3126505 := by
    simpa [prefixWord, tailWord_3126505, baseEnd_3126505] using wordTrace_append hprefix tailTrace_3126505
  have hstable : (prefixWord ++ tailWord_3126505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126505).length < 2 ^ (prefixWord ++ tailWord_3126505).sum := by decide
  have hdescent : baseEnd_3126505 < baseStart_3126505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126509 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_3126509 : Nat := 118140960795 + 3126509 * 2 ^ 59
def prefixEnd_3126509 : Nat := 4983230072969 + 3 ^ 40 * 3126509 * 2
def baseEnd_3126509 : Nat := 535133962536004417619651

theorem tailTrace_3126509 : CollatzResearch.WordTrace tailWord_3126509 prefixEnd_3126509 535133962536004417619651 := by
  unfold tailWord_3126509
  simp only [CollatzResearch.WordTrace]
  refine ⟨114033151430199333071166581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76022100953466222047444387 114033151430199333071166581)
  ·
    refine ⟨10690607946581187475421867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114033151430199333071166581 10690607946581187475421867)
    ·
      refine ⟨16035911919871781213132801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10690607946581187475421867 16035911919871781213132801)
      ·
        refine ⟨12026933939903835909849601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16035911919871781213132801 12026933939903835909849601)
        ·
          refine ⟨9020200454927876932387201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12026933939903835909849601 9020200454927876932387201)
          ·
            refine ⟨6765150341195907699290401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9020200454927876932387201 6765150341195907699290401)
            ·
              refine ⟨5073862755896930774467801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6765150341195907699290401 5073862755896930774467801)
              ·
                refine ⟨3805397066922698080850851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5073862755896930774467801 3805397066922698080850851)
                ·
                  refine ⟨5708095600384047121276277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3805397066922698080850851 5708095600384047121276277)
                  ·
                    refine ⟨535133962536004417619651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5708095600384047121276277 535133962536004417619651)
                    ·
                      rfl

theorem cell23_3126509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_3126509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126509 prefixEnd_3126509 := by exact prefixLift 3126509
  have htrace : WordTrace (prefixWord ++ tailWord_3126509) baseStart_3126509 baseEnd_3126509 := by
    simpa [prefixWord, tailWord_3126509, baseEnd_3126509] using wordTrace_append hprefix tailTrace_3126509
  have hstable : (prefixWord ++ tailWord_3126509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126509).length < 2 ^ (prefixWord ++ tailWord_3126509).sum := by decide
  have hdescent : baseEnd_3126509 < baseStart_3126509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126532 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3126532 : Nat := 118140960795 + 3126532 * 2 ^ 59
def prefixEnd_3126532 : Nat := 4983230072969 + 3 ^ 40 * 3126532 * 2
def baseEnd_3126532 : Nat := 1605413697663066662871347

theorem tailTrace_3126532 : CollatzResearch.WordTrace tailWord_3126532 prefixEnd_3126532 1605413697663066662871347 := by
  unfold tailWord_3126532
  simp only [CollatzResearch.WordTrace]
  refine ⟨57016995154558003999626925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76022660206077338666169233 57016995154558003999626925)
  ·
    refine ⟨21381373182959251499860097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57016995154558003999626925 21381373182959251499860097)
    ·
      refine ⟨16036029887219438624895073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21381373182959251499860097 16036029887219438624895073)
      ·
        refine ⟨12027022415414578968671305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16036029887219438624895073 12027022415414578968671305)
        ·
          refine ⟨9020266811560934226503479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12027022415414578968671305 9020266811560934226503479)
          ·
            refine ⟨13530400217341401339755219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9020266811560934226503479 13530400217341401339755219)
            ·
              refine ⟨20295600326012102009632829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13530400217341401339755219 20295600326012102009632829)
              ·
                refine ⟨7610850122254538253612311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20295600326012102009632829 7610850122254538253612311)
                ·
                  refine ⟨11416275183381807380418467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7610850122254538253612311 11416275183381807380418467)
                  ·
                    refine ⟨17124412775072711070627701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11416275183381807380418467 17124412775072711070627701)
                    ·
                      refine ⟨1605413697663066662871347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17124412775072711070627701 1605413697663066662871347)
                      ·
                        rfl

theorem cell23_3126532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3126532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126532 prefixEnd_3126532 := by exact prefixLift 3126532
  have htrace : WordTrace (prefixWord ++ tailWord_3126532) baseStart_3126532 baseEnd_3126532 := by
    simpa [prefixWord, tailWord_3126532, baseEnd_3126532] using wordTrace_append hprefix tailTrace_3126532
  have hstable : (prefixWord ++ tailWord_3126532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126532).length < 2 ^ (prefixWord ++ tailWord_3126532).sum := by decide
  have hdescent : baseEnd_3126532 < baseStart_3126532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126595 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 2, 6]
def baseStart_3126595 : Nat := 118140960795 + 3126595 * 2 ^ 59
def prefixEnd_3126595 : Nat := 4983230072969 + 3 ^ 40 * 3126595 * 2
def baseEnd_3126595 : Nat := 535148682314766638794519

theorem tailTrace_3126595 : CollatzResearch.WordTrace tailWord_3126595 prefixEnd_3126595 535148682314766638794519 := by
  unfold tailWord_3126595
  simp only [CollatzResearch.WordTrace]
  refine ⟨114036288107887769758797239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76024192071925179839198159 114036288107887769758797239)
  ·
    refine ⟨171054432161831654638195859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114036288107887769758797239 171054432161831654638195859)
    ·
      refine ⟨256581648242747481957293789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171054432161831654638195859 256581648242747481957293789)
      ·
        refine ⟨96218118091030305733985171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256581648242747481957293789 96218118091030305733985171)
        ·
          refine ⟨144327177136545458600977757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96218118091030305733985171 144327177136545458600977757)
          ·
            refine ⟨54122691426204546975366659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144327177136545458600977757 54122691426204546975366659)
            ·
              refine ⟨81184037139306820463049989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54122691426204546975366659 81184037139306820463049989)
              ·
                refine ⟨15222006963620028836821873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81184037139306820463049989 15222006963620028836821873)
                ·
                  refine ⟨11416505222715021627616405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15222006963620028836821873 11416505222715021627616405)
                  ·
                    refine ⟨535148682314766638794519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11416505222715021627616405 535148682314766638794519)
                    ·
                      rfl

theorem cell23_3126595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 6].length) (baseStart_3126595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126595 prefixEnd_3126595 := by exact prefixLift 3126595
  have htrace : WordTrace (prefixWord ++ tailWord_3126595) baseStart_3126595 baseEnd_3126595 := by
    simpa [prefixWord, tailWord_3126595, baseEnd_3126595] using wordTrace_append hprefix tailTrace_3126595
  have hstable : (prefixWord ++ tailWord_3126595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126595).length < 2 ^ (prefixWord ++ tailWord_3126595).sum := by decide
  have hdescent : baseEnd_3126595 < baseStart_3126595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126612 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_3126612 : Nat := 118140960795 + 3126612 * 2 ^ 59
def prefixEnd_3126612 : Nat := 4983230072969 + 3 ^ 40 * 3126612 * 2
def baseEnd_3126612 : Nat := 535151592038475449956993

theorem tailTrace_3126612 : CollatzResearch.WordTrace tailWord_3126612 prefixEnd_3126612 535151592038475449956993 := by
  unfold tailWord_3126612
  simp only [CollatzResearch.WordTrace]
  refine ⟨57018454074413090831083045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76024605432550787774777393 57018454074413090831083045)
  ·
    refine ⟨10690960138952454530828071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57018454074413090831083045 10690960138952454530828071)
    ·
      refine ⟨16036440208428681796242107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10690960138952454530828071 16036440208428681796242107)
      ·
        refine ⟨24054660312643022694363161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16036440208428681796242107 24054660312643022694363161)
        ·
          refine ⟨18040995234482267020772371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24054660312643022694363161 18040995234482267020772371)
          ·
            refine ⟨27061492851723400531158557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18040995234482267020772371 27061492851723400531158557)
            ·
              refine ⟨10148059819396275199184459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27061492851723400531158557 10148059819396275199184459)
              ·
                refine ⟨15222089729094412798776689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10148059819396275199184459 15222089729094412798776689)
                ·
                  refine ⟨11416567296820809599082517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15222089729094412798776689 11416567296820809599082517)
                  ·
                    refine ⟨535151592038475449956993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11416567296820809599082517 535151592038475449956993)
                    ·
                      rfl

theorem cell23_3126612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_3126612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126612 prefixEnd_3126612 := by exact prefixLift 3126612
  have htrace : WordTrace (prefixWord ++ tailWord_3126612) baseStart_3126612 baseEnd_3126612 := by
    simpa [prefixWord, tailWord_3126612, baseEnd_3126612] using wordTrace_append hprefix tailTrace_3126612
  have hstable : (prefixWord ++ tailWord_3126612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126612).length < 2 ^ (prefixWord ++ tailWord_3126612).sum := by decide
  have hdescent : baseEnd_3126612 < baseStart_3126612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126652 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_3126652 : Nat := 118140960795 + 3126652 * 2 ^ 59
def prefixEnd_3126652 : Nat := 4983230072969 + 3 ^ 40 * 3126652 * 2
def baseEnd_3126652 : Nat := 1605475315341606193370795

theorem tailTrace_3126652 : CollatzResearch.WordTrace tailWord_3126652 prefixEnd_3126652 1605475315341606193370795 := by
  unfold tailWord_3126652
  simp only [CollatzResearch.WordTrace]
  refine ⟨57019183534340634246811105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76025578045787512329081473 57019183534340634246811105)
  ·
    refine ⟨42764387650755475685108329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57019183534340634246811105 42764387650755475685108329)
    ·
      refine ⟨32073290738066606763831247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42764387650755475685108329 32073290738066606763831247)
      ·
        refine ⟨48109936107099910145746871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32073290738066606763831247 48109936107099910145746871)
        ·
          refine ⟨72164904160649865218620307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48109936107099910145746871 72164904160649865218620307)
          ·
            refine ⟨108247356240974797827930461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72164904160649865218620307 108247356240974797827930461)
            ·
              refine ⟨40592758590365549185473923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108247356240974797827930461 40592758590365549185473923)
              ·
                refine ⟨60889137885548323778210885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40592758590365549185473923 60889137885548323778210885)
                ·
                  refine ⟨11416713353540310708414541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60889137885548323778210885 11416713353540310708414541)
                  ·
                    refine ⟨4281267507577616515655453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11416713353540310708414541 4281267507577616515655453)
                    ·
                      refine ⟨1605475315341606193370795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4281267507577616515655453 1605475315341606193370795)
                      ·
                        rfl

theorem cell23_3126652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_3126652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126652 prefixEnd_3126652 := by exact prefixLift 3126652
  have htrace : WordTrace (prefixWord ++ tailWord_3126652) baseStart_3126652 baseEnd_3126652 := by
    simpa [prefixWord, tailWord_3126652, baseEnd_3126652] using wordTrace_append hprefix tailTrace_3126652
  have hstable : (prefixWord ++ tailWord_3126652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126652).length < 2 ^ (prefixWord ++ tailWord_3126652).sum := by decide
  have hdescent : baseEnd_3126652 < baseStart_3126652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126655 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 5, 7]
def baseStart_3126655 : Nat := 118140960795 + 3126655 * 2 ^ 59
def prefixEnd_3126655 : Nat := 4983230072969 + 3 ^ 40 * 3126655 * 2
def baseEnd_3126655 : Nat := 535158951927856560544427

theorem tailTrace_3126655 : CollatzResearch.WordTrace tailWord_3126655 prefixEnd_3126655 535158951927856560544427 := by
  unfold tailWord_3126655
  simp only [CollatzResearch.WordTrace]
  refine ⟨114038476487670400005981419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76025650991780266670654279 114038476487670400005981419)
  ·
    refine ⟨171057714731505600008972129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114038476487670400005981419 171057714731505600008972129)
    ·
      refine ⟨128293286048629200006729097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171057714731505600008972129 128293286048629200006729097)
      ·
        refine ⟨96219964536471900005046823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128293286048629200006729097 96219964536471900005046823)
        ·
          refine ⟨144329946804707850007570235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96219964536471900005046823 144329946804707850007570235)
          ·
            refine ⟨216494920207061775011355353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144329946804707850007570235 216494920207061775011355353)
            ·
              refine ⟨162371190155296331258516515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216494920207061775011355353 162371190155296331258516515)
              ·
                refine ⟨243556785232944496887774773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162371190155296331258516515 243556785232944496887774773)
                ·
                  refine ⟨22833448615588546583228885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243556785232944496887774773 22833448615588546583228885)
                  ·
                    refine ⟨535158951927856560544427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22833448615588546583228885 535158951927856560544427)
                    ·
                      rfl

theorem cell23_3126655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_3126655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126655 prefixEnd_3126655 := by exact prefixLift 3126655
  have htrace : WordTrace (prefixWord ++ tailWord_3126655) baseStart_3126655 baseEnd_3126655 := by
    simpa [prefixWord, tailWord_3126655, baseEnd_3126655] using wordTrace_append hprefix tailTrace_3126655
  have hstable : (prefixWord ++ tailWord_3126655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126655).length < 2 ^ (prefixWord ++ tailWord_3126655).sum := by decide
  have hdescent : baseEnd_3126655 < baseStart_3126655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126659 : List Nat := [1, 1, 1, 3, 5, 1, 2, 4, 5]
def baseStart_3126659 : Nat := 118140960795 + 3126659 * 2 ^ 59
def prefixEnd_3126659 : Nat := 4983230072969 + 3 ^ 40 * 3126659 * 2
def baseEnd_3126659 : Nat := 178386545522909740664807

theorem tailTrace_3126659 : CollatzResearch.WordTrace tailWord_3126659 prefixEnd_3126659 178386545522909740664807 := by
  unfold tailWord_3126659
  simp only [CollatzResearch.WordTrace]
  refine ⟨114038622379655908689127031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76025748253103939126084687 114038622379655908689127031)
  ·
    refine ⟨171057933569483863033690547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114038622379655908689127031 171057933569483863033690547)
    ·
      refine ⟨256586900354225794550535821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171057933569483863033690547 256586900354225794550535821)
      ·
        refine ⟨96220087632834672956450933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256586900354225794550535821 96220087632834672956450933)
        ·
          refine ⟨9020633215578250589667275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96220087632834672956450933 9020633215578250589667275)
          ·
            refine ⟨13530949823367375884500913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9020633215578250589667275 13530949823367375884500913)
            ·
              refine ⟨10148212367525531913375685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13530949823367375884500913 10148212367525531913375685)
              ·
                refine ⟨1902789818911037233757941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10148212367525531913375685 1902789818911037233757941)
                ·
                  refine ⟨178386545522909740664807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1902789818911037233757941 178386545522909740664807)
                  ·
                    rfl

theorem cell23_3126659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 5].length) (baseStart_3126659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126659 prefixEnd_3126659 := by exact prefixLift 3126659
  have htrace : WordTrace (prefixWord ++ tailWord_3126659) baseStart_3126659 baseEnd_3126659 := by
    simpa [prefixWord, tailWord_3126659, baseEnd_3126659] using wordTrace_append hprefix tailTrace_3126659
  have hstable : (prefixWord ++ tailWord_3126659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126659).length < 2 ^ (prefixWord ++ tailWord_3126659).sum := by decide
  have hdescent : baseEnd_3126659 < baseStart_3126659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126670 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2]
def baseStart_3126670 : Nat := 118140960795 + 3126670 * 2 ^ 59
def prefixEnd_3126670 : Nat := 4983230072969 + 3 ^ 40 * 3126670 * 2
def baseEnd_3126670 : Nat := 1605484557993387122945713

theorem tailTrace_3126670 : CollatzResearch.WordTrace tailWord_3126670 prefixEnd_3126670 1605484557993387122945713 := by
  unfold tailWord_3126670
  simp only [CollatzResearch.WordTrace]
  refine ⟨14254877947827007195972183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76026015721744038378518309 14254877947827007195972183)
  ·
    refine ⟨21382316921740510793958275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14254877947827007195972183 21382316921740510793958275)
    ·
      refine ⟨32073475382610766190937413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21382316921740510793958275 32073475382610766190937413)
      ·
        refine ⟨6013776634239518660800765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32073475382610766190937413 6013776634239518660800765)
        ·
          refine ⟨2255166237839819497800287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6013776634239518660800765 2255166237839819497800287)
          ·
            refine ⟨3382749356759729246700431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255166237839819497800287 3382749356759729246700431)
            ·
              refine ⟨5074124035139593870050647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382749356759729246700431 5074124035139593870050647)
              ·
                refine ⟨7611186052709390805075971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074124035139593870050647 7611186052709390805075971)
                ·
                  refine ⟨11416779079064086207613957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7611186052709390805075971 11416779079064086207613957)
                  ·
                    refine ⟨2140646077324516163927617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11416779079064086207613957 2140646077324516163927617)
                    ·
                      refine ⟨1605484557993387122945713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140646077324516163927617 1605484557993387122945713)
                      ·
                        rfl

theorem cell23_3126670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_3126670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126670 prefixEnd_3126670 := by exact prefixLift 3126670
  have htrace : WordTrace (prefixWord ++ tailWord_3126670) baseStart_3126670 baseEnd_3126670 := by
    simpa [prefixWord, tailWord_3126670, baseEnd_3126670] using wordTrace_append hprefix tailTrace_3126670
  have hstable : (prefixWord ++ tailWord_3126670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126670).length < 2 ^ (prefixWord ++ tailWord_3126670).sum := by decide
  have hdescent : baseEnd_3126670 < baseStart_3126670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126709 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3126709 : Nat := 118140960795 + 3126709 * 2 ^ 59
def prefixEnd_3126709 : Nat := 4983230072969 + 3 ^ 40 * 3126709 * 2
def baseEnd_3126709 : Nat := 1605504583738912470358033

theorem tailTrace_3126709 : CollatzResearch.WordTrace tailWord_3126709 prefixEnd_3126709 1605504583738912470358033 := by
  unfold tailWord_3126709
  simp only [CollatzResearch.WordTrace]
  refine ⟨114040446029474767228447181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76026964019649844818964787 114040446029474767228447181)
  ·
    refine ⟨42765167261053037710667693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114040446029474767228447181 42765167261053037710667693)
    ·
      refine ⟨16036937722894889141500385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42765167261053037710667693 16036937722894889141500385)
      ·
        refine ⟨12027703292171166856125289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16036937722894889141500385 12027703292171166856125289)
        ·
          refine ⟨9020777469128375142093967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12027703292171166856125289 9020777469128375142093967)
          ·
            refine ⟨13531166203692562713140951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9020777469128375142093967 13531166203692562713140951)
            ·
              refine ⟨20296749305538844069711427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13531166203692562713140951 20296749305538844069711427)
              ·
                refine ⟨30445123958308266104567141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20296749305538844069711427 30445123958308266104567141)
                ·
                  refine ⟨5708460742182799894606339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30445123958308266104567141 5708460742182799894606339)
                  ·
                    refine ⟨8562691113274199841909509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5708460742182799894606339 8562691113274199841909509)
                    ·
                      refine ⟨1605504583738912470358033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8562691113274199841909509 1605504583738912470358033)
                      ·
                        rfl

theorem cell23_3126709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3126709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126709 prefixEnd_3126709 := by exact prefixLift 3126709
  have htrace : WordTrace (prefixWord ++ tailWord_3126709) baseStart_3126709 baseEnd_3126709 := by
    simpa [prefixWord, tailWord_3126709, baseEnd_3126709] using wordTrace_append hprefix tailTrace_3126709
  have hstable : (prefixWord ++ tailWord_3126709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126709).length < 2 ^ (prefixWord ++ tailWord_3126709).sum := by decide
  have hdescent : baseEnd_3126709 < baseStart_3126709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126746 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3]
def baseStart_3126746 : Nat := 118140960795 + 3126746 * 2 ^ 59
def prefixEnd_3126746 : Nat := 4983230072969 + 3 ^ 40 * 3126746 * 2
def baseEnd_3126746 : Nat := 1605523582523128825595363

theorem tailTrace_3126746 : CollatzResearch.WordTrace tailWord_3126746 prefixEnd_3126746 1605523582523128825595363 := by
  unfold tailWord_3126746
  simp only [CollatzResearch.WordTrace]
  refine ⟨28510448882585180636886023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76027863686893815031696061 28510448882585180636886023)
  ·
    refine ⟨42765673323877770955329035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28510448882585180636886023 42765673323877770955329035)
    ·
      refine ⟨64148509985816656432993553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42765673323877770955329035 64148509985816656432993553)
      ·
        refine ⟨48111382489362492324745165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64148509985816656432993553 48111382489362492324745165)
        ·
          refine ⟨18041768433510934621779437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48111382489362492324745165 18041768433510934621779437)
          ·
            refine ⟨6765663162566600483167289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18041768433510934621779437 6765663162566600483167289)
            ·
              refine ⟨5074247371924950362375467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6765663162566600483167289 5074247371924950362375467)
              ·
                refine ⟨7611371057887425543563201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074247371924950362375467 7611371057887425543563201)
                ·
                  refine ⟨5708528293415569157672401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7611371057887425543563201 5708528293415569157672401)
                  ·
                    refine ⟨4281396220061676868254301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5708528293415569157672401 4281396220061676868254301)
                    ·
                      refine ⟨1605523582523128825595363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4281396220061676868254301 1605523582523128825595363)
                      ·
                        rfl

theorem cell23_3126746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_3126746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126746 prefixEnd_3126746 := by exact prefixLift 3126746
  have htrace : WordTrace (prefixWord ++ tailWord_3126746) baseStart_3126746 baseEnd_3126746 := by
    simpa [prefixWord, tailWord_3126746, baseEnd_3126746] using wordTrace_append hprefix tailTrace_3126746
  have hstable : (prefixWord ++ tailWord_3126746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126746).length < 2 ^ (prefixWord ++ tailWord_3126746).sum := by decide
  have hdescent : baseEnd_3126746 < baseStart_3126746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126770 : List Nat := [3, 2, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_3126770 : Nat := 118140960795 + 3126770 * 2 ^ 59
def prefixEnd_3126770 : Nat := 4983230072969 + 3 ^ 40 * 3126770 * 2
def baseEnd_3126770 : Nat := 535178635352945577231751

theorem tailTrace_3126770 : CollatzResearch.WordTrace tailWord_3126770 prefixEnd_3126770 535178635352945577231751 := by
  unfold tailWord_3126770
  simp only [CollatzResearch.WordTrace]
  refine ⟨28510667720563443661604441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76028447254835849764278509 28510667720563443661604441)
  ·
    refine ⟨21383000790422582746203331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28510667720563443661604441 21383000790422582746203331)
    ·
      refine ⟨32074501185633874119304997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21383000790422582746203331 32074501185633874119304997)
      ·
        refine ⟨6013968972306351397369687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32074501185633874119304997 6013968972306351397369687)
        ·
          refine ⟨9020953458459527096054531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6013968972306351397369687 9020953458459527096054531)
          ·
            refine ⟨13531430187689290644081797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9020953458459527096054531 13531430187689290644081797)
            ·
              refine ⟨2537143160191741995765337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13531430187689290644081797 2537143160191741995765337)
              ·
                refine ⟨1902857370143806496824003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2537143160191741995765337 1902857370143806496824003)
                ·
                  refine ⟨2854286055215709745236005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1902857370143806496824003 2854286055215709745236005)
                  ·
                    refine ⟨535178635352945577231751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2854286055215709745236005 535178635352945577231751)
                    ·
                      rfl

theorem cell23_3126770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_3126770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126770 prefixEnd_3126770 := by exact prefixLift 3126770
  have htrace : WordTrace (prefixWord ++ tailWord_3126770) baseStart_3126770 baseEnd_3126770 := by
    simpa [prefixWord, tailWord_3126770, baseEnd_3126770] using wordTrace_append hprefix tailTrace_3126770
  have hstable : (prefixWord ++ tailWord_3126770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126770).length < 2 ^ (prefixWord ++ tailWord_3126770).sum := by decide
  have hdescent : baseEnd_3126770 < baseStart_3126770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126797 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3126797 : Nat := 118140960795 + 3126797 * 2 ^ 59
def prefixEnd_3126797 : Nat := 4983230072969 + 3 ^ 40 * 3126797 * 2
def baseEnd_3126797 : Nat := 1605549770036508126057629

theorem tailTrace_3126797 : CollatzResearch.WordTrace tailWord_3126797 prefixEnd_3126797 1605549770036508126057629 := by
  unfold tailWord_3126797
  simp only [CollatzResearch.WordTrace]
  refine ⟨114043655653155958257650645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76029103768770638838433763 114043655653155958257650645)
  ·
    refine ⟨2672898179370842771663687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 114043655653155958257650645 2672898179370842771663687)
    ·
      refine ⟨4009347269056264157495531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2672898179370842771663687 4009347269056264157495531)
      ·
        refine ⟨6014020903584396236243297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4009347269056264157495531 6014020903584396236243297)
        ·
          refine ⟨4510515677688297177182473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6014020903584396236243297 4510515677688297177182473)
          ·
            refine ⟨3382886758266222882886855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4510515677688297177182473 3382886758266222882886855)
            ·
              refine ⟨5074330137399334324330283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382886758266222882886855 5074330137399334324330283)
              ·
                refine ⟨7611495206099001486495425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074330137399334324330283 7611495206099001486495425)
                ·
                  refine ⟨5708621404574251114871569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7611495206099001486495425 5708621404574251114871569)
                  ·
                    refine ⟨4281466053430688336153677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5708621404574251114871569 4281466053430688336153677)
                    ·
                      refine ⟨1605549770036508126057629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4281466053430688336153677 1605549770036508126057629)
                      ·
                        rfl

theorem cell23_3126797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3126797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126797 prefixEnd_3126797 := by exact prefixLift 3126797
  have htrace : WordTrace (prefixWord ++ tailWord_3126797) baseStart_3126797 baseEnd_3126797 := by
    simpa [prefixWord, tailWord_3126797, baseEnd_3126797] using wordTrace_append hprefix tailTrace_3126797
  have hstable : (prefixWord ++ tailWord_3126797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126797).length < 2 ^ (prefixWord ++ tailWord_3126797).sum := by decide
  have hdescent : baseEnd_3126797 < baseStart_3126797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126803 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 2, 3, 2]
def baseStart_3126803 : Nat := 118140960795 + 3126803 * 2 ^ 59
def prefixEnd_3126803 : Nat := 4983230072969 + 3 ^ 40 * 3126803 * 2
def baseEnd_3126803 : Nat := 1605552850920435102582601

theorem tailTrace_3126803 : CollatzResearch.WordTrace tailWord_3126803 prefixEnd_3126803 1605552850920435102582601 := by
  unfold tailWord_3126803
  simp only [CollatzResearch.WordTrace]
  refine ⟨114043874491134221282369063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76029249660756147521579375 114043874491134221282369063)
  ·
    refine ⟨171065811736701331923553595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114043874491134221282369063 171065811736701331923553595)
    ·
      refine ⟨256598717605051997885330393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171065811736701331923553595 256598717605051997885330393)
      ·
        refine ⟨192449038203788998413997795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256598717605051997885330393 192449038203788998413997795)
        ·
          refine ⟨288673557305683497620996693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192449038203788998413997795 288673557305683497620996693)
          ·
            refine ⟨3382893249675978487746055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 288673557305683497620996693 3382893249675978487746055)
            ·
              refine ⟨5074339874513967731619083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382893249675978487746055 5074339874513967731619083)
              ·
                refine ⟨7611509811770951597428625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074339874513967731619083 7611509811770951597428625)
                ·
                  refine ⟨5708632358828213698071469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7611509811770951597428625 5708632358828213698071469)
                  ·
                    refine ⟨2140737134560580136776801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5708632358828213698071469 2140737134560580136776801)
                    ·
                      refine ⟨1605552850920435102582601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140737134560580136776801 1605552850920435102582601)
                      ·
                        rfl

theorem cell23_3126803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 3, 2].length) (baseStart_3126803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126803 prefixEnd_3126803 := by exact prefixLift 3126803
  have htrace : WordTrace (prefixWord ++ tailWord_3126803) baseStart_3126803 baseEnd_3126803 := by
    simpa [prefixWord, tailWord_3126803, baseEnd_3126803] using wordTrace_append hprefix tailTrace_3126803
  have hstable : (prefixWord ++ tailWord_3126803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126803).length < 2 ^ (prefixWord ++ tailWord_3126803).sum := by decide
  have hdescent : baseEnd_3126803 < baseStart_3126803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126826 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3126826 : Nat := 118140960795 + 3126826 * 2 ^ 59
def prefixEnd_3126826 : Nat := 4983230072969 + 3 ^ 40 * 3126826 * 2
def baseEnd_3126826 : Nat := 535188220325162837531665

theorem tailTrace_3126826 : CollatzResearch.WordTrace tailWord_3126826 prefixEnd_3126826 535188220325162837531665 := by
  unfold tailWord_3126826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28511178342512724052614083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76029808913367264140304221 28511178342512724052614083)
  ·
    refine ⟨42766767513769086078921125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28511178342512724052614083 42766767513769086078921125)
    ·
      refine ⟨8018768908831703639797711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42766767513769086078921125 8018768908831703639797711)
      ·
        refine ⟨12028153363247555459696567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8018768908831703639797711 12028153363247555459696567)
        ·
          refine ⟨18042230044871333189544851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12028153363247555459696567 18042230044871333189544851)
          ·
            refine ⟨27063345067306999784317277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18042230044871333189544851 27063345067306999784317277)
            ·
              refine ⟨10148754400240124919118979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27063345067306999784317277 10148754400240124919118979)
              ·
                refine ⟨15223131600360187378678469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10148754400240124919118979 15223131600360187378678469)
                ·
                  refine ⟨2854337175067535133502213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15223131600360187378678469 2854337175067535133502213)
                  ·
                    refine ⟨535188220325162837531665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2854337175067535133502213 535188220325162837531665)
                    ·
                      rfl

theorem cell23_3126826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3126826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126826 prefixEnd_3126826 := by exact prefixLift 3126826
  have htrace : WordTrace (prefixWord ++ tailWord_3126826) baseStart_3126826 baseEnd_3126826 := by
    simpa [prefixWord, tailWord_3126826, baseEnd_3126826] using wordTrace_append hprefix tailTrace_3126826
  have hstable : (prefixWord ++ tailWord_3126826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126826).length < 2 ^ (prefixWord ++ tailWord_3126826).sum := by decide
  have hdescent : baseEnd_3126826 < baseStart_3126826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126832 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_3126832 : Nat := 118140960795 + 3126832 * 2 ^ 59
def prefixEnd_3126832 : Nat := 4983230072969 + 3 ^ 40 * 3126832 * 2
def baseEnd_3126832 : Nat := 1605567741859415489119967

theorem tailTrace_3126832 : CollatzResearch.WordTrace tailWord_3126832 prefixEnd_3126832 1605567741859415489119967 := by
  unfold tailWord_3126832
  simp only [CollatzResearch.WordTrace]
  refine ⟨57022466104014579617587375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76029954805352772823449833 57022466104014579617587375)
  ·
    refine ⟨85533699156021869426381063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57022466104014579617587375 85533699156021869426381063)
    ·
      refine ⟨128300548734032804139571595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85533699156021869426381063 128300548734032804139571595)
      ·
        refine ⟨192450823101049206209357393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128300548734032804139571595 192450823101049206209357393)
        ·
          refine ⟨144338117325786904657018045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192450823101049206209357393 144338117325786904657018045)
          ·
            refine ⟨54126793997170089246381767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144338117325786904657018045 54126793997170089246381767)
            ·
              refine ⟨81190190995755133869572651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54126793997170089246381767 81190190995755133869572651)
              ·
                refine ⟨121785286493632700804358977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81190190995755133869572651 121785286493632700804358977)
                ·
                  refine ⟨91338964870224525603269233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121785286493632700804358977 91338964870224525603269233)
                  ·
                    refine ⟨68504223652668394202451925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91338964870224525603269233 68504223652668394202451925)
                    ·
                      refine ⟨1605567741859415489119967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68504223652668394202451925 1605567741859415489119967)
                      ·
                        rfl

theorem cell23_3126832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_3126832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126832 prefixEnd_3126832 := by exact prefixLift 3126832
  have htrace : WordTrace (prefixWord ++ tailWord_3126832) baseStart_3126832 baseEnd_3126832 := by
    simpa [prefixWord, tailWord_3126832, baseEnd_3126832] using wordTrace_append hprefix tailTrace_3126832
  have hstable : (prefixWord ++ tailWord_3126832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126832).length < 2 ^ (prefixWord ++ tailWord_3126832).sum := by decide
  have hdescent : baseEnd_3126832 < baseStart_3126832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126926 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3126926 : Nat := 118140960795 + 3126926 * 2 ^ 59
def prefixEnd_3126926 : Nat := 4983230072969 + 3 ^ 40 * 3126926 * 2
def baseEnd_3126926 : Nat := 1605616009040938121344535

theorem tailTrace_3126926 : CollatzResearch.WordTrace tailWord_3126926 prefixEnd_3126926 1605616009040938121344535 := by
  unfold tailWord_3126926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14256045083711076661137079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76032240446459075526064421 14256045083711076661137079)
  ·
    refine ⟨21384067625566614991705619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14256045083711076661137079 21384067625566614991705619)
    ·
      refine ⟨32076101438349922487558429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21384067625566614991705619 32076101438349922487558429)
      ·
        refine ⟨12028538039381220932834411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32076101438349922487558429 12028538039381220932834411)
        ·
          refine ⟨18042807059071831399251617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12028538039381220932834411 18042807059071831399251617)
          ·
            refine ⟨13532105294303873549438713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18042807059071831399251617 13532105294303873549438713)
            ·
              refine ⟨10149078970727905162079035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13532105294303873549438713 10149078970727905162079035)
              ·
                refine ⟨15223618456091857743118553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10149078970727905162079035 15223618456091857743118553)
                ·
                  refine ⟨11417713842068893307338915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15223618456091857743118553 11417713842068893307338915)
                  ·
                    refine ⟨17126570763103339961008373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11417713842068893307338915 17126570763103339961008373)
                    ·
                      refine ⟨1605616009040938121344535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17126570763103339961008373 1605616009040938121344535)
                      ·
                        rfl

theorem cell23_3126926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3126926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126926 prefixEnd_3126926 := by exact prefixLift 3126926
  have htrace : WordTrace (prefixWord ++ tailWord_3126926) baseStart_3126926 baseEnd_3126926 := by
    simpa [prefixWord, tailWord_3126926, baseEnd_3126926] using wordTrace_append hprefix tailTrace_3126926
  have hstable : (prefixWord ++ tailWord_3126926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126926).length < 2 ^ (prefixWord ++ tailWord_3126926).sum := by decide
  have hdescent : baseEnd_3126926 < baseStart_3126926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126959 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 1, 7]
def baseStart_3126959 : Nat := 118140960795 + 3126959 * 2 ^ 59
def prefixEnd_3126959 : Nat := 4983230072969 + 3 ^ 40 * 3126959 * 2
def baseEnd_3126959 : Nat := 535210984634178830743961

theorem tailTrace_3126959 : CollatzResearch.WordTrace tailWord_3126959 prefixEnd_3126959 535210984634178830743961 := by
  unfold tailWord_3126959
  simp only [CollatzResearch.WordTrace]
  refine ⟨114049564278569059925047931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76033042852379373283365287 114049564278569059925047931)
  ·
    refine ⟨171074346417853589887571897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114049564278569059925047931 171074346417853589887571897)
    ·
      refine ⟨128305759813390192415678923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171074346417853589887571897 128305759813390192415678923)
      ·
        refine ⟨192458639720085288623518385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128305759813390192415678923 192458639720085288623518385)
        ·
          refine ⟨144343979790063966467638789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192458639720085288623518385 144343979790063966467638789)
          ·
            refine ⟨27064496210636993712682273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144343979790063966467638789 27064496210636993712682273)
            ·
              refine ⟨20298372157977745284511705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27064496210636993712682273 20298372157977745284511705)
              ·
                refine ⟨15223779118483308963383779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20298372157977745284511705 15223779118483308963383779)
                ·
                  refine ⟨22835668677724963445075669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15223779118483308963383779 22835668677724963445075669)
                  ·
                    refine ⟨535210984634178830743961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22835668677724963445075669 535210984634178830743961)
                    ·
                      rfl

theorem cell23_3126959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_3126959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126959 prefixEnd_3126959 := by exact prefixLift 3126959
  have htrace : WordTrace (prefixWord ++ tailWord_3126959) baseStart_3126959 baseEnd_3126959 := by
    simpa [prefixWord, tailWord_3126959, baseEnd_3126959] using wordTrace_append hprefix tailTrace_3126959
  have hstable : (prefixWord ++ tailWord_3126959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126959).length < 2 ^ (prefixWord ++ tailWord_3126959).sum := by decide
  have hdescent : baseEnd_3126959 < baseStart_3126959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126969 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3126969 : Nat := 118140960795 + 3126969 * 2 ^ 59
def prefixEnd_3126969 : Nat := 4983230072969 + 3 ^ 40 * 3126969 * 2
def baseEnd_3126969 : Nat := 1605638088709081453106837

theorem tailTrace_3126969 : CollatzResearch.WordTrace tailWord_3126969 prefixEnd_3126969 1605638088709081453106837 := by
  unfold tailWord_3126969
  simp only [CollatzResearch.WordTrace]
  refine ⟨114049929008532831632911961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76033286005688554421941307 114049929008532831632911961)
  ·
    refine ⟨85537446756399623724683971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114049929008532831632911961 85537446756399623724683971)
    ·
      refine ⟨128306170134599435587025957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85537446756399623724683971 128306170134599435587025957)
      ·
        refine ⟨24057406900237394172567367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128306170134599435587025957 24057406900237394172567367)
        ·
          refine ⟨36086110350356091258851051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24057406900237394172567367 36086110350356091258851051)
          ·
            refine ⟨54129165525534136888276577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36086110350356091258851051 54129165525534136888276577)
            ·
              refine ⟨40596874144150602666207433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54129165525534136888276577 40596874144150602666207433)
              ·
                refine ⟨30447655608112951999655575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40596874144150602666207433 30447655608112951999655575)
                ·
                  refine ⟨45671483412169427999483363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30447655608112951999655575 45671483412169427999483363)
                  ·
                    refine ⟨68507225118254141999225045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45671483412169427999483363 68507225118254141999225045)
                    ·
                      refine ⟨1605638088709081453106837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68507225118254141999225045 1605638088709081453106837)
                      ·
                        rfl

theorem cell23_3126969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3126969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126969 prefixEnd_3126969 := by exact prefixLift 3126969
  have htrace : WordTrace (prefixWord ++ tailWord_3126969) baseStart_3126969 baseEnd_3126969 := by
    simpa [prefixWord, tailWord_3126969, baseEnd_3126969] using wordTrace_append hprefix tailTrace_3126969
  have hstable : (prefixWord ++ tailWord_3126969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126969).length < 2 ^ (prefixWord ++ tailWord_3126969).sum := by decide
  have hdescent : baseEnd_3126969 < baseStart_3126969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3126978 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_3126978 : Nat := 118140960795 + 3126978 * 2 ^ 59
def prefixEnd_3126978 : Nat := 4983230072969 + 3 ^ 40 * 3126978 * 2
def baseEnd_3126978 : Nat := 1605642710034971917894297

theorem tailTrace_3126978 : CollatzResearch.WordTrace tailWord_3126978 prefixEnd_3126978 1605642710034971917894297 := by
  unfold tailWord_3126978
  simp only [CollatzResearch.WordTrace]
  refine ⟨28512564316375056542497397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76033504843666817446659725 28512564316375056542497397)
  ·
    refine ⟨2673052904660161550859131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28512564316375056542497397 2673052904660161550859131)
    ·
      refine ⟨4009579356990242326288697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2673052904660161550859131 4009579356990242326288697)
      ·
        refine ⟨3007184517742681744716523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4009579356990242326288697 3007184517742681744716523)
        ·
          refine ⟨4510776776614022617074785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007184517742681744716523 4510776776614022617074785)
          ·
            refine ⟨3383082582460516962806089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4510776776614022617074785 3383082582460516962806089)
            ·
              refine ⟨2537311936845387722104567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3383082582460516962806089 2537311936845387722104567)
              ·
                refine ⟨3805967905268081583156851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537311936845387722104567 3805967905268081583156851)
                ·
                  refine ⟨5708951857902122374735277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3805967905268081583156851 5708951857902122374735277)
                  ·
                    refine ⟨2140856946713295890525729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5708951857902122374735277 2140856946713295890525729)
                    ·
                      refine ⟨1605642710034971917894297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140856946713295890525729 1605642710034971917894297)
                      ·
                        rfl

theorem cell23_3126978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_3126978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3126978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3126978 prefixEnd_3126978 := by exact prefixLift 3126978
  have htrace : WordTrace (prefixWord ++ tailWord_3126978) baseStart_3126978 baseEnd_3126978 := by
    simpa [prefixWord, tailWord_3126978, baseEnd_3126978] using wordTrace_append hprefix tailTrace_3126978
  have hstable : (prefixWord ++ tailWord_3126978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3126978).length < 2 ^ (prefixWord ++ tailWord_3126978).sum := by decide
  have hdescent : baseEnd_3126978 < baseStart_3126978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3126978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127013 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 2, 4, 2]
def baseStart_3127013 : Nat := 118140960795 + 3127013 * 2 ^ 59
def prefixEnd_3127013 : Nat := 4983230072969 + 3 ^ 40 * 3127013 * 2
def baseEnd_3127013 : Nat := 1605660681857879280956635

theorem tailTrace_3127013 : CollatzResearch.WordTrace tailWord_3127013 prefixEnd_3127013 1605660681857879280956635 := by
  unfold tailWord_3127013
  simp only [CollatzResearch.WordTrace]
  refine ⟨114051533820373427147513693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76034355880248951431675795 114051533820373427147513693)
  ·
    refine ⟨42769325182640035180317635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114051533820373427147513693 42769325182640035180317635)
    ·
      refine ⟨64153987773960052770476453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42769325182640035180317635 64153987773960052770476453)
      ·
        refine ⟨12028872707617509894464335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64153987773960052770476453 12028872707617509894464335)
        ·
          refine ⟨18043309061426264841696503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12028872707617509894464335 18043309061426264841696503)
          ·
            refine ⟨27064963592139397262544755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18043309061426264841696503 27064963592139397262544755)
            ·
              refine ⟨40597445388209095893817133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27064963592139397262544755 40597445388209095893817133)
              ·
                refine ⟨15224042020578410960181425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40597445388209095893817133 15224042020578410960181425)
                ·
                  refine ⟨11418031515433808220136069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15224042020578410960181425 11418031515433808220136069)
                  ·
                    refine ⟨2140880909143839041275513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11418031515433808220136069 2140880909143839041275513)
                    ·
                      refine ⟨1605660681857879280956635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140880909143839041275513 1605660681857879280956635)
                      ·
                        rfl

theorem cell23_3127013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_3127013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127013 prefixEnd_3127013 := by exact prefixLift 3127013
  have htrace : WordTrace (prefixWord ++ tailWord_3127013) baseStart_3127013 baseEnd_3127013 := by
    simpa [prefixWord, tailWord_3127013, baseEnd_3127013] using wordTrace_append hprefix tailTrace_3127013
  have hstable : (prefixWord ++ tailWord_3127013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127013).length < 2 ^ (prefixWord ++ tailWord_3127013).sum := by decide
  have hdescent : baseEnd_3127013 < baseStart_3127013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127026 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3127026 : Nat := 118140960795 + 3127026 * 2 ^ 59
def prefixEnd_3127026 : Nat := 4983230072969 + 3 ^ 40 * 3127026 * 2
def baseEnd_3127026 : Nat := 1605667357106387730094075

theorem tailTrace_3127026 : CollatzResearch.WordTrace tailWord_3127026 prefixEnd_3127026 1605667357106387730094075 := by
  unfold tailWord_3127026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28513001992331582591934233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76034671979550886911824621 28513001992331582591934233)
  ·
    refine ⟨21384751494248686943950675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28513001992331582591934233 21384751494248686943950675)
    ·
      refine ⟨32077127241373030415926013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21384751494248686943950675 32077127241373030415926013)
      ·
        refine ⟨12028922715514886405972255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32077127241373030415926013 12028922715514886405972255)
        ·
          refine ⟨18043384073272329608958383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12028922715514886405972255 18043384073272329608958383)
          ·
            refine ⟨27065076109908494413437575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18043384073272329608958383 27065076109908494413437575)
            ·
              refine ⟨40597614164862741620156363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27065076109908494413437575 40597614164862741620156363)
              ·
                refine ⟨60896421247294112430234545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40597614164862741620156363 60896421247294112430234545)
                ·
                  refine ⟨45672315935470584322675909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60896421247294112430234545 45672315935470584322675909)
                  ·
                    refine ⟨8563559237900734560501733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45672315935470584322675909 8563559237900734560501733)
                    ·
                      refine ⟨1605667357106387730094075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8563559237900734560501733 1605667357106387730094075)
                      ·
                        rfl

theorem cell23_3127026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3127026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127026 prefixEnd_3127026 := by exact prefixLift 3127026
  have htrace : WordTrace (prefixWord ++ tailWord_3127026) baseStart_3127026 baseEnd_3127026 := by
    simpa [prefixWord, tailWord_3127026, baseEnd_3127026] using wordTrace_append hprefix tailTrace_3127026
  have hstable : (prefixWord ++ tailWord_3127026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127026).length < 2 ^ (prefixWord ++ tailWord_3127026).sum := by decide
  have hdescent : baseEnd_3127026 < baseStart_3127026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127090 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2]
def baseStart_3127090 : Nat := 118140960795 + 3127090 * 2 ^ 59
def prefixEnd_3127090 : Nat := 4983230072969 + 3 ^ 40 * 3127090 * 2
def baseEnd_3127090 : Nat := 1605700219868275479693781

theorem tailTrace_3127090 : CollatzResearch.WordTrace tailWord_3127090 prefixEnd_3127090 1605700219868275479693781 := by
  unfold tailWord_3127090
  simp only [CollatzResearch.WordTrace]
  refine ⟨28513585560273617324516681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76036228160729646198711149 28513585560273617324516681)
  ·
    refine ⟨21385189170205212993387511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28513585560273617324516681 21385189170205212993387511)
    ·
      refine ⟨32077783755307819490081267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21385189170205212993387511 32077783755307819490081267)
      ·
        refine ⟨48116675632961729235121901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32077783755307819490081267 48116675632961729235121901)
        ·
          refine ⟨18043753362360648463170713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48116675632961729235121901 18043753362360648463170713)
          ·
            refine ⟨13532815021770486347378035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18043753362360648463170713 13532815021770486347378035)
            ·
              refine ⟨20299222532655729521067053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13532815021770486347378035 20299222532655729521067053)
              ·
                refine ⟨7612208449745898570400145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20299222532655729521067053 7612208449745898570400145)
                ·
                  refine ⟨5709156337309423927800109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7612208449745898570400145 5709156337309423927800109)
                  ·
                    refine ⟨2140933626491033972925041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5709156337309423927800109 2140933626491033972925041)
                    ·
                      refine ⟨1605700219868275479693781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140933626491033972925041 1605700219868275479693781)
                      ·
                        rfl

theorem cell23_3127090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_3127090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127090 prefixEnd_3127090 := by exact prefixLift 3127090
  have htrace : WordTrace (prefixWord ++ tailWord_3127090) baseStart_3127090 baseEnd_3127090 := by
    simpa [prefixWord, tailWord_3127090, baseEnd_3127090] using wordTrace_append hprefix tailTrace_3127090
  have hstable : (prefixWord ++ tailWord_3127090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127090).length < 2 ^ (prefixWord ++ tailWord_3127090).sum := by decide
  have hdescent : baseEnd_3127090 < baseStart_3127090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127096 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 3, 6]
def baseStart_3127096 : Nat := 118140960795 + 3127096 * 2 ^ 59
def prefixEnd_3127096 : Nat := 4983230072969 + 3 ^ 40 * 3127096 * 2
def baseEnd_3127096 : Nat := 535234433584067485406251

theorem tailTrace_3127096 : CollatzResearch.WordTrace tailWord_3127096 prefixEnd_3127096 535234433584067485406251 := by
  unfold tailWord_3127096
  simp only [CollatzResearch.WordTrace]
  refine ⟨57027280539536366161392571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76036374052715154881856761 57027280539536366161392571)
  ·
    refine ⟨85540920809304549242088857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57027280539536366161392571 85540920809304549242088857)
    ·
      refine ⟨64155690606978411931566643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85540920809304549242088857 64155690606978411931566643)
      ·
        refine ⟨96233535910467617897349965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64155690606978411931566643 96233535910467617897349965)
        ·
          refine ⟨36087575966425356711506237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96233535910467617897349965 36087575966425356711506237)
          ·
            refine ⟨13532840987409508766814839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36087575966425356711506237 13532840987409508766814839)
            ·
              refine ⟨20299261481114263150222259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13532840987409508766814839 20299261481114263150222259)
              ·
                refine ⟨30448892221671394725333389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20299261481114263150222259 30448892221671394725333389)
                ·
                  refine ⟨11418334583126773022000021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30448892221671394725333389 11418334583126773022000021)
                  ·
                    refine ⟨535234433584067485406251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11418334583126773022000021 535234433584067485406251)
                    ·
                      rfl

theorem cell23_3127096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_3127096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127096 prefixEnd_3127096 := by exact prefixLift 3127096
  have htrace : WordTrace (prefixWord ++ tailWord_3127096) baseStart_3127096 baseEnd_3127096 := by
    simpa [prefixWord, tailWord_3127096, baseEnd_3127096] using wordTrace_append hprefix tailTrace_3127096
  have hstable : (prefixWord ++ tailWord_3127096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127096).length < 2 ^ (prefixWord ++ tailWord_3127096).sum := by decide
  have hdescent : baseEnd_3127096 < baseStart_3127096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127120 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 3, 2, 2]
def baseStart_3127120 : Nat := 118140960795 + 3127120 * 2 ^ 59
def prefixEnd_3127120 : Nat := 4983230072969 + 3 ^ 40 * 3127120 * 2
def baseEnd_3127120 : Nat := 1605715624287910362318643

theorem tailTrace_3127120 : CollatzResearch.WordTrace tailWord_3127120 prefixEnd_3127120 1605715624287910362318643 := by
  unfold tailWord_3127120
  simp only [CollatzResearch.WordTrace]
  refine ⟨57027718215492892210829407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76036957620657189614439209 57027718215492892210829407)
  ·
    refine ⟨85541577323239338316244111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57027718215492892210829407 85541577323239338316244111)
    ·
      refine ⟨128312365984859007474366167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85541577323239338316244111 128312365984859007474366167)
      ·
        refine ⟨192468548977288511211549251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128312365984859007474366167 192468548977288511211549251)
        ·
          refine ⟨288702823465932766817323877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192468548977288511211549251 288702823465932766817323877)
          ·
            refine ⟨54131779399862393778248227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288702823465932766817323877 54131779399862393778248227)
            ·
              refine ⟨81197669099793590667372341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54131779399862393778248227 81197669099793590667372341)
              ·
                refine ⟨7612281478105649125066157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81197669099793590667372341 7612281478105649125066157)
                ·
                  refine ⟨2854605554289618421899809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7612281478105649125066157 2854605554289618421899809)
                  ·
                    refine ⟨2140954165717213816424857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2854605554289618421899809 2140954165717213816424857)
                    ·
                      refine ⟨1605715624287910362318643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2140954165717213816424857 1605715624287910362318643)
                      ·
                        rfl

theorem cell23_3127120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3, 2, 2].length) (baseStart_3127120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127120 prefixEnd_3127120 := by exact prefixLift 3127120
  have htrace : WordTrace (prefixWord ++ tailWord_3127120) baseStart_3127120 baseEnd_3127120 := by
    simpa [prefixWord, tailWord_3127120, baseEnd_3127120] using wordTrace_append hprefix tailTrace_3127120
  have hstable : (prefixWord ++ tailWord_3127120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127120).length < 2 ^ (prefixWord ++ tailWord_3127120).sum := by decide
  have hdescent : baseEnd_3127120 < baseStart_3127120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127143 : List Nat := [1, 1, 5, 1, 2, 1, 5, 7]
def baseStart_3127143 : Nat := 118140960795 + 3127143 * 2 ^ 59
def prefixEnd_3127143 : Nat := 4983230072969 + 3 ^ 40 * 3127143 * 2
def baseEnd_3127143 : Nat := 59471386457146806382631

theorem tailTrace_3127143 : CollatzResearch.WordTrace tailWord_3127143 prefixEnd_3127143 59471386457146806382631 := by
  unfold tailWord_3127143
  simp only [CollatzResearch.WordTrace]
  refine ⟨114056275309902459349746083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76037516873268306233164055 114056275309902459349746083)
  ·
    refine ⟨171084412964853689024619125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114056275309902459349746083 171084412964853689024619125)
    ·
      refine ⟨16039163715455033346058043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171084412964853689024619125 16039163715455033346058043)
      ·
        refine ⟨24058745573182550019087065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16039163715455033346058043 24058745573182550019087065)
        ·
          refine ⟨18044059179886912514315299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24058745573182550019087065 18044059179886912514315299)
          ·
            refine ⟨27066088769830368771472949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18044059179886912514315299 27066088769830368771472949)
            ·
              refine ⟨2537445822171597072325589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27066088769830368771472949 2537445822171597072325589)
              ·
                refine ⟨59471386457146806382631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2537445822171597072325589 59471386457146806382631)
                ·
                  rfl

theorem cell23_3127143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 7].length) (baseStart_3127143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127143 prefixEnd_3127143 := by exact prefixLift 3127143
  have htrace : WordTrace (prefixWord ++ tailWord_3127143) baseStart_3127143 baseEnd_3127143 := by
    simpa [prefixWord, tailWord_3127143, baseEnd_3127143] using wordTrace_append hprefix tailTrace_3127143
  have hstable : (prefixWord ++ tailWord_3127143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127143).length < 2 ^ (prefixWord ++ tailWord_3127143).sum := by decide
  have hdescent : baseEnd_3127143 < baseStart_3127143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127150 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3127150 : Nat := 118140960795 + 3127150 * 2 ^ 59
def prefixEnd_3127150 : Nat := 4983230072969 + 3 ^ 40 * 3127150 * 2
def baseEnd_3127150 : Nat := 1605731028707545244943505

theorem tailTrace_3127150 : CollatzResearch.WordTrace tailWord_3127150 prefixEnd_3127150 1605731028707545244943505 := by
  unfold tailWord_3127150
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257066327609637443156363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76037687080584733030167269 14257066327609637443156363)
  ·
    refine ⟨21385599491414456164734545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14257066327609637443156363 21385599491414456164734545)
    ·
      refine ⟨16039199618560842123550909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21385599491414456164734545 16039199618560842123550909)
      ·
        refine ⟨6014699856960315796331591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16039199618560842123550909 6014699856960315796331591)
        ·
          refine ⟨9022049785440473694497387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6014699856960315796331591 9022049785440473694497387)
          ·
            refine ⟨13533074678160710541746081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9022049785440473694497387 13533074678160710541746081)
            ·
              refine ⟨10149806008620532906309561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13533074678160710541746081 10149806008620532906309561)
              ·
                refine ⟨7612354506465399679732171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10149806008620532906309561 7612354506465399679732171)
                ·
                  refine ⟨11418531759698099519598257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7612354506465399679732171 11418531759698099519598257)
                  ·
                    refine ⟨8563898819773574639698693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11418531759698099519598257 8563898819773574639698693)
                    ·
                      refine ⟨1605731028707545244943505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8563898819773574639698693 1605731028707545244943505)
                      ·
                        rfl

theorem cell23_3127150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3127150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127150 prefixEnd_3127150 := by exact prefixLift 3127150
  have htrace : WordTrace (prefixWord ++ tailWord_3127150) baseStart_3127150 baseEnd_3127150 := by
    simpa [prefixWord, tailWord_3127150, baseEnd_3127150] using wordTrace_append hprefix tailTrace_3127150
  have hstable : (prefixWord ++ tailWord_3127150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127150).length < 2 ^ (prefixWord ++ tailWord_3127150).sum := by decide
  have hdescent : baseEnd_3127150 < baseStart_3127150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127153 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 1, 3, 3]
def baseStart_3127153 : Nat := 118140960795 + 3127153 * 2 ^ 59
def prefixEnd_3127153 : Nat := 4983230072969 + 3 ^ 40 * 3127153 * 2
def baseEnd_3127153 : Nat := 1605732569149508733205991

theorem tailTrace_3127153 : CollatzResearch.WordTrace tailWord_3127153 prefixEnd_3127153 1605732569149508733205991 := by
  unfold tailWord_3127153
  simp only [CollatzResearch.WordTrace]
  refine ⟨114056640039866231057610113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76037760026577487371740075 114056640039866231057610113)
  ·
    refine ⟨85542480029899673293207585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114056640039866231057610113 85542480029899673293207585)
    ·
      refine ⟨64156860022424754969905689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85542480029899673293207585 64156860022424754969905689)
      ·
        refine ⟨48117645016818566227429267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64156860022424754969905689 48117645016818566227429267)
        ·
          refine ⟨72176467525227849341143901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48117645016818566227429267 72176467525227849341143901)
          ·
            refine ⟨27066175321960443502928963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72176467525227849341143901 27066175321960443502928963)
            ·
              refine ⟨40599262982940665254393445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27066175321960443502928963 40599262982940665254393445)
              ·
                refine ⟨7612361809301374735198771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40599262982940665254393445 7612361809301374735198771)
                ·
                  refine ⟨11418542713952062102798157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7612361809301374735198771 11418542713952062102798157)
                  ·
                    refine ⟨4281953517732023288549309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11418542713952062102798157 4281953517732023288549309)
                    ·
                      refine ⟨1605732569149508733205991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4281953517732023288549309 1605732569149508733205991)
                      ·
                        rfl

theorem cell23_3127153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_3127153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127153 prefixEnd_3127153 := by exact prefixLift 3127153
  have htrace : WordTrace (prefixWord ++ tailWord_3127153) baseStart_3127153 baseEnd_3127153 := by
    simpa [prefixWord, tailWord_3127153, baseEnd_3127153] using wordTrace_append hprefix tailTrace_3127153
  have hstable : (prefixWord ++ tailWord_3127153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127153).length < 2 ^ (prefixWord ++ tailWord_3127153).sum := by decide
  have hdescent : baseEnd_3127153 < baseStart_3127153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127197 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_3127197 : Nat := 118140960795 + 3127197 * 2 ^ 59
def prefixEnd_3127197 : Nat := 4983230072969 + 3 ^ 40 * 3127197 * 2
def baseEnd_3127197 : Nat := 1605755162298306561055789

theorem tailTrace_3127197 : CollatzResearch.WordTrace tailWord_3127197 prefixEnd_3127197 1605755162298306561055789 := by
  unfold tailWord_3127197
  simp only [CollatzResearch.WordTrace]
  refine ⟨114058244851706826572211845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76038829901137884381474563 114058244851706826572211845)
  ·
    refine ⟨21385920909695029982289721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114058244851706826572211845 21385920909695029982289721)
    ·
      refine ⟨16039440682271272486717291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21385920909695029982289721 16039440682271272486717291)
      ·
        refine ⟨24059161023406908730075937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16039440682271272486717291 24059161023406908730075937)
        ·
          refine ⟨18044370767555181547556953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24059161023406908730075937 18044370767555181547556953)
          ·
            refine ⟨13533278075666386160667715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18044370767555181547556953 13533278075666386160667715)
            ·
              refine ⟨20299917113499579241001573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13533278075666386160667715 20299917113499579241001573)
              ·
                refine ⟨3806234458781171107687795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20299917113499579241001573 3806234458781171107687795)
                ·
                  refine ⟨5709351688171756661531693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806234458781171107687795 5709351688171756661531693)
                  ·
                    refine ⟨2141006883064408748074385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5709351688171756661531693 2141006883064408748074385)
                    ·
                      refine ⟨1605755162298306561055789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141006883064408748074385 1605755162298306561055789)
                      ·
                        rfl

theorem cell23_3127197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_3127197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127197 prefixEnd_3127197 := by exact prefixLift 3127197
  have htrace : WordTrace (prefixWord ++ tailWord_3127197) baseStart_3127197 baseEnd_3127197 := by
    simpa [prefixWord, tailWord_3127197, baseEnd_3127197] using wordTrace_append hprefix tailTrace_3127197
  have hstable : (prefixWord ++ tailWord_3127197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127197).length < 2 ^ (prefixWord ++ tailWord_3127197).sum := by decide
  have hdescent : baseEnd_3127197 < baseStart_3127197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127243 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 3]
def baseStart_3127243 : Nat := 118140960795 + 3127243 * 2 ^ 59
def prefixEnd_3127243 : Nat := 4983230072969 + 3 ^ 40 * 3127243 * 2
def baseEnd_3127243 : Nat := 1605778782408413381080577

theorem tailTrace_3127243 : CollatzResearch.WordTrace tailWord_3127243 prefixEnd_3127243 1605778782408413381080577 := by
  unfold tailWord_3127243
  simp only [CollatzResearch.WordTrace]
  refine ⟨114059922609540176428386383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76039948406360117618924255 114059922609540176428386383)
  ·
    refine ⟨171089883914310264642579575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114059922609540176428386383 171089883914310264642579575)
    ·
      refine ⟨256634825871465396963869363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171089883914310264642579575 256634825871465396963869363)
      ·
        refine ⟨384952238807198095445804045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256634825871465396963869363 384952238807198095445804045)
        ·
          refine ⟨144357089552699285792176517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384952238807198095445804045 144357089552699285792176517)
          ·
            refine ⟨27066954291131116086033097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144357089552699285792176517 27066954291131116086033097)
            ·
              refine ⟨20300215718348337064524823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27066954291131116086033097 20300215718348337064524823)
              ·
                refine ⟨30450323577522505596787235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20300215718348337064524823 30450323577522505596787235)
                ·
                  refine ⟨45675485366283758395180853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30450323577522505596787235 45675485366283758395180853)
                  ·
                    refine ⟨4282076753089102349548205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45675485366283758395180853 4282076753089102349548205)
                    ·
                      refine ⟨1605778782408413381080577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4282076753089102349548205 1605778782408413381080577)
                      ·
                        rfl

theorem cell23_3127243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 3].length) (baseStart_3127243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127243 prefixEnd_3127243 := by exact prefixLift 3127243
  have htrace : WordTrace (prefixWord ++ tailWord_3127243) baseStart_3127243 baseEnd_3127243 := by
    simpa [prefixWord, tailWord_3127243, baseEnd_3127243] using wordTrace_append hprefix tailTrace_3127243
  have hstable : (prefixWord ++ tailWord_3127243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127243).length < 2 ^ (prefixWord ++ tailWord_3127243).sum := by decide
  have hdescent : baseEnd_3127243 < baseStart_3127243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127244 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 2, 2, 2]
def baseStart_3127244 : Nat := 118140960795 + 3127244 * 2 ^ 59
def prefixEnd_3127244 : Nat := 4983230072969 + 3 ^ 40 * 3127244 * 2
def baseEnd_3127244 : Nat := 1605779295889067877168073

theorem tailTrace_3127244 : CollatzResearch.WordTrace tailWord_3127244 prefixEnd_3127244 1605779295889067877168073 := by
  unfold tailWord_3127244
  simp only [CollatzResearch.WordTrace]
  refine ⟨57029979541268276799586393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76039972721691035732781857 57029979541268276799586393)
  ·
    refine ⟨42772484655951207599689795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57029979541268276799586393 42772484655951207599689795)
    ·
      refine ⟨64158726983926811399534693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42772484655951207599689795 64158726983926811399534693)
      ·
        refine ⟨12029761309486277137412755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64158726983926811399534693 12029761309486277137412755)
        ·
          refine ⟨18044641964229415706119133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12029761309486277137412755 18044641964229415706119133)
          ·
            refine ⟨6766740736586030889794675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18044641964229415706119133 6766740736586030889794675)
            ·
              refine ⟨10150111104879046334692013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6766740736586030889794675 10150111104879046334692013)
              ·
                refine ⟨3806291664329642375509505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10150111104879046334692013 3806291664329642375509505)
                ·
                  refine ⟨2854718748247231781632129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3806291664329642375509505 2854718748247231781632129)
                  ·
                    refine ⟨2141039061185423836224097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2854718748247231781632129 2141039061185423836224097)
                    ·
                      refine ⟨1605779295889067877168073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141039061185423836224097 1605779295889067877168073)
                      ·
                        rfl

theorem cell23_3127244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_3127244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127244 prefixEnd_3127244 := by exact prefixLift 3127244
  have htrace : WordTrace (prefixWord ++ tailWord_3127244) baseStart_3127244 baseEnd_3127244 := by
    simpa [prefixWord, tailWord_3127244, baseEnd_3127244] using wordTrace_append hprefix tailTrace_3127244
  have hstable : (prefixWord ++ tailWord_3127244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127244).length < 2 ^ (prefixWord ++ tailWord_3127244).sum := by decide
  have hdescent : baseEnd_3127244 < baseStart_3127244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127320 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3127320 : Nat := 118140960795 + 3127320 * 2 ^ 59
def prefixEnd_3127320 : Nat := 4983230072969 + 3 ^ 40 * 3127320 * 2
def baseEnd_3127320 : Nat := 1605818320418809579817723

theorem tailTrace_3127320 : CollatzResearch.WordTrace tailWord_3127320 prefixEnd_3127320 1605818320418809579817723 := by
  unfold tailWord_3127320
  simp only [CollatzResearch.WordTrace]
  refine ⟨57031365515130609289469707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76041820686840812385959609 57031365515130609289469707)
  ·
    refine ⟨85547048272695913934204561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57031365515130609289469707 85547048272695913934204561)
    ·
      refine ⟨64160286204521935450653421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85547048272695913934204561 64160286204521935450653421)
      ·
        refine ⟨24060107326695725793995033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64160286204521935450653421 24060107326695725793995033)
        ·
          refine ⟨18045080495021794345496275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24060107326695725793995033 18045080495021794345496275)
          ·
            refine ⟨27067620742532691518244413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18045080495021794345496275 27067620742532691518244413)
            ·
              refine ⟨10150357778449759319341655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27067620742532691518244413 10150357778449759319341655)
              ·
                refine ⟨15225536667674638979012483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10150357778449759319341655 15225536667674638979012483)
                ·
                  refine ⟨22838305001511958468518725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15225536667674638979012483 22838305001511958468518725)
                  ·
                    refine ⟨4282182187783492212847261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22838305001511958468518725 4282182187783492212847261)
                    ·
                      refine ⟨1605818320418809579817723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4282182187783492212847261 1605818320418809579817723)
                      ·
                        rfl

theorem cell23_3127320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3127320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127320 prefixEnd_3127320 := by exact prefixLift 3127320
  have htrace : WordTrace (prefixWord ++ tailWord_3127320) baseStart_3127320 baseEnd_3127320 := by
    simpa [prefixWord, tailWord_3127320, baseEnd_3127320] using wordTrace_append hprefix tailTrace_3127320
  have hstable : (prefixWord ++ tailWord_3127320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127320).length < 2 ^ (prefixWord ++ tailWord_3127320).sum := by decide
  have hdescent : baseEnd_3127320 < baseStart_3127320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127357 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 6]
def baseStart_3127357 : Nat := 118140960795 + 3127357 * 2 ^ 59
def prefixEnd_3127357 : Nat := 4983230072969 + 3 ^ 40 * 3127357 * 2
def baseEnd_3127357 : Nat := 178426368800336215006117

theorem tailTrace_3127357 : CollatzResearch.WordTrace tailWord_3127357 prefixEnd_3127357 178426368800336215006117 := by
  unfold tailWord_3127357
  simp only [CollatzResearch.WordTrace]
  refine ⟨114064080531127173898036325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76042720354084782598690883 114064080531127173898036325)
  ·
    refine ⟨21387015099586345105881811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114064080531127173898036325 21387015099586345105881811)
    ·
      refine ⟨32080522649379517658822717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21387015099586345105881811 32080522649379517658822717)
      ·
        refine ⟨12030195993517319122058519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32080522649379517658822717 12030195993517319122058519)
        ·
          refine ⟨18045293990275978683087779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12030195993517319122058519 18045293990275978683087779)
          ·
            refine ⟨27067940985413968024631669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18045293990275978683087779 27067940985413968024631669)
            ·
              refine ⟨2537619467382559502309219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27067940985413968024631669 2537619467382559502309219)
              ·
                refine ⟨3806429201073839253463829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537619467382559502309219 3806429201073839253463829)
                ·
                  refine ⟨178426368800336215006117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3806429201073839253463829 178426368800336215006117)
                  ·
                    rfl

theorem cell23_3127357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_3127357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127357 prefixEnd_3127357 := by exact prefixLift 3127357
  have htrace : WordTrace (prefixWord ++ tailWord_3127357) baseStart_3127357 baseEnd_3127357 := by
    simpa [prefixWord, tailWord_3127357, baseEnd_3127357] using wordTrace_append hprefix tailTrace_3127357
  have hstable : (prefixWord ++ tailWord_3127357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127357).length < 2 ^ (prefixWord ++ tailWord_3127357).sum := by decide
  have hdescent : baseEnd_3127357 < baseStart_3127357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127367 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_3127367 : Nat := 118140960795 + 3127367 * 2 ^ 59
def prefixEnd_3127367 : Nat := 4983230072969 + 3 ^ 40 * 3127367 * 2
def baseEnd_3127367 : Nat := 1605842454009570895930007

theorem tailTrace_3127367 : CollatzResearch.WordTrace tailWord_3127367 prefixEnd_3127367 1605842454009570895930007 := by
  unfold tailWord_3127367
  simp only [CollatzResearch.WordTrace]
  refine ⟨114064445261090945605900355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76042963507393963737266903 114064445261090945605900355)
  ·
    refine ⟨171096667891636418408850533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114064445261090945605900355 171096667891636418408850533)
    ·
      refine ⟨32080625229681828451659475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171096667891636418408850533 32080625229681828451659475)
      ·
        refine ⟨48120937844522742677489213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32080625229681828451659475 48120937844522742677489213)
        ·
          refine ⟨18045351691696028504058455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48120937844522742677489213 18045351691696028504058455)
          ·
            refine ⟨27068027537544042756087683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18045351691696028504058455 27068027537544042756087683)
            ·
              refine ⟨40602041306316064134131525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27068027537544042756087683 40602041306316064134131525)
              ·
                refine ⟨7612882744934262025149661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40602041306316064134131525 7612882744934262025149661)
                ·
                  refine ⟨2854831029350348259431123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7612882744934262025149661 2854831029350348259431123)
                  ·
                    refine ⟨4282246544025522389146685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2854831029350348259431123 4282246544025522389146685)
                    ·
                      refine ⟨1605842454009570895930007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4282246544025522389146685 1605842454009570895930007)
                      ·
                        rfl

theorem cell23_3127367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_3127367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127367 prefixEnd_3127367 := by exact prefixLift 3127367
  have htrace : WordTrace (prefixWord ++ tailWord_3127367) baseStart_3127367 baseEnd_3127367 := by
    simpa [prefixWord, tailWord_3127367, baseEnd_3127367] using wordTrace_append hprefix tailTrace_3127367
  have hstable : (prefixWord ++ tailWord_3127367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127367).length < 2 ^ (prefixWord ++ tailWord_3127367).sum := by decide
  have hdescent : baseEnd_3127367 < baseStart_3127367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127377 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 2, 3, 2]
def baseStart_3127377 : Nat := 118140960795 + 3127377 * 2 ^ 59
def prefixEnd_3127377 : Nat := 4983230072969 + 3 ^ 40 * 3127377 * 2
def baseEnd_3127377 : Nat := 1605847588816115856804961

theorem tailTrace_3127377 : CollatzResearch.WordTrace tailWord_3127377 prefixEnd_3127377 1605847588816115856804961 := by
  unfold tailWord_3127377
  simp only [CollatzResearch.WordTrace]
  refine ⟨114064809991054717313764385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76043206660703144875842923 114064809991054717313764385)
  ·
    refine ⟨85548607493291037985323289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114064809991054717313764385 85548607493291037985323289)
    ·
      refine ⟨64161455619968278488992467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85548607493291037985323289 64161455619968278488992467)
      ·
        refine ⟨96242183429952417733488701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64161455619968278488992467 96242183429952417733488701)
        ·
          refine ⟨36090818786232156650058263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96242183429952417733488701 36090818786232156650058263)
          ·
            refine ⟨54136228179348234975087395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36090818786232156650058263 54136228179348234975087395)
            ·
              refine ⟨81204342269022352462631093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54136228179348234975087395 81204342269022352462631093)
              ·
                refine ⟨7612907087720845543371665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81204342269022352462631093 7612907087720845543371665)
                ·
                  refine ⟨5709680315790634157528749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7612907087720845543371665 5709680315790634157528749)
                  ·
                    refine ⟨2141130118421487809073281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5709680315790634157528749 2141130118421487809073281)
                    ·
                      refine ⟨1605847588816115856804961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141130118421487809073281 1605847588816115856804961)
                      ·
                        rfl

theorem cell23_3127377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_3127377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127377 prefixEnd_3127377 := by exact prefixLift 3127377
  have htrace : WordTrace (prefixWord ++ tailWord_3127377) baseStart_3127377 baseEnd_3127377 := by
    simpa [prefixWord, tailWord_3127377, baseEnd_3127377] using wordTrace_append hprefix tailTrace_3127377
  have hstable : (prefixWord ++ tailWord_3127377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127377).length < 2 ^ (prefixWord ++ tailWord_3127377).sum := by decide
  have hdescent : baseEnd_3127377 < baseStart_3127377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127378 : List Nat := [3, 2, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_3127378 : Nat := 118140960795 + 3127378 * 2 ^ 59
def prefixEnd_3127378 : Nat := 4983230072969 + 3 ^ 40 * 3127378 * 2
def baseEnd_3127378 : Nat := 535282700765590117630819

theorem tailTrace_3127378 : CollatzResearch.WordTrace tailWord_3127378 prefixEnd_3127378 535282700765590117630819 := by
  unfold tailWord_3127378
  simp only [CollatzResearch.WordTrace]
  refine ⟨28516211616012773621137697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76043230976034062989700525 28516211616012773621137697)
  ·
    refine ⟨21387158712009580215853273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28516211616012773621137697 21387158712009580215853273)
    ·
      refine ⟨16040369034007185161889955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21387158712009580215853273 16040369034007185161889955)
      ·
        refine ⟨24060553551010777742834933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16040369034007185161889955 24060553551010777742834933)
        ·
          refine ⟨2255676895407260413390775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24060553551010777742834933 2255676895407260413390775)
          ·
            refine ⟨3383515343110890620086163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255676895407260413390775 3383515343110890620086163)
            ·
              refine ⟨5075273014666335930129245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383515343110890620086163 5075273014666335930129245)
              ·
                refine ⟨1903227380499875973798467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5075273014666335930129245 1903227380499875973798467)
                ·
                  refine ⟨2854841070749813960697701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903227380499875973798467 2854841070749813960697701)
                  ·
                    refine ⟨535282700765590117630819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2854841070749813960697701 535282700765590117630819)
                    ·
                      rfl

theorem cell23_3127378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_3127378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127378 prefixEnd_3127378 := by exact prefixLift 3127378
  have htrace : WordTrace (prefixWord ++ tailWord_3127378) baseStart_3127378 baseEnd_3127378 := by
    simpa [prefixWord, tailWord_3127378, baseEnd_3127378] using wordTrace_append hprefix tailTrace_3127378
  have hstable : (prefixWord ++ tailWord_3127378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127378).length < 2 ^ (prefixWord ++ tailWord_3127378).sum := by decide
  have hdescent : baseEnd_3127378 < baseStart_3127378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127401 : List Nat := [1, 2, 1, 1, 1, 5, 5, 2, 1, 1, 3]
def baseStart_3127401 : Nat := 118140960795 + 3127401 * 2 ^ 59
def prefixEnd_3127401 : Nat := 4983230072969 + 3 ^ 40 * 3127401 * 2
def baseEnd_3127401 : Nat := 1605859912351823762904851

theorem tailTrace_3127401 : CollatzResearch.WordTrace tailWord_3127401 prefixEnd_3127401 1605859912351823762904851 := by
  unfold tailWord_3127401
  simp only [CollatzResearch.WordTrace]
  refine ⟨114065685342967769412638057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76043790228645179608425371 114065685342967769412638057)
  ·
    refine ⟨85549264007225827059478543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114065685342967769412638057 85549264007225827059478543)
    ·
      refine ⟨128323896010838740589217815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85549264007225827059478543 128323896010838740589217815)
      ·
        refine ⟨192485844016258110883826723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128323896010838740589217815 192485844016258110883826723)
        ·
          refine ⟨288728766024387166325740085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192485844016258110883826723 288728766024387166325740085)
          ·
            refine ⟨27068321814786296843038133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 288728766024387166325740085 27068321814786296843038133)
            ·
              refine ⟨2537655170136215329034825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27068321814786296843038133 2537655170136215329034825)
              ·
                refine ⟨1903241377602161496776119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2537655170136215329034825 1903241377602161496776119)
                ·
                  refine ⟨2854862066403242245164179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903241377602161496776119 2854862066403242245164179)
                  ·
                    refine ⟨4282293099604863367746269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2854862066403242245164179 4282293099604863367746269)
                    ·
                      refine ⟨1605859912351823762904851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4282293099604863367746269 1605859912351823762904851)
                      ·
                        rfl

theorem cell23_3127401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 1, 1, 3].length) (baseStart_3127401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127401 prefixEnd_3127401 := by exact prefixLift 3127401
  have htrace : WordTrace (prefixWord ++ tailWord_3127401) baseStart_3127401 baseEnd_3127401 := by
    simpa [prefixWord, tailWord_3127401, baseEnd_3127401] using wordTrace_append hprefix tailTrace_3127401
  have hstable : (prefixWord ++ tailWord_3127401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127401).length < 2 ^ (prefixWord ++ tailWord_3127401).sum := by decide
  have hdescent : baseEnd_3127401 < baseStart_3127401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127420 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_3127420 : Nat := 118140960795 + 3127420 * 2 ^ 59
def prefixEnd_3127420 : Nat := 4983230072969 + 3 ^ 40 * 3127420 * 2
def baseEnd_3127420 : Nat := 1605869668484259188567263

theorem tailTrace_3127420 : CollatzResearch.WordTrace tailWord_3127420 prefixEnd_3127420 1605869668484259188567263 := by
  unfold tailWord_3127420
  simp only [CollatzResearch.WordTrace]
  refine ⟨57033189164949467828789857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76044252219932623771719809 57033189164949467828789857)
  ·
    refine ⟨42774891873712100871592393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57033189164949467828789857 42774891873712100871592393)
    ·
      refine ⟨32081168905284075653694295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42774891873712100871592393 32081168905284075653694295)
      ·
        refine ⟨48121753357926113480541443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32081168905284075653694295 48121753357926113480541443)
        ·
          refine ⟨72182630036889170220812165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48121753357926113480541443 72182630036889170220812165)
          ·
            refine ⟨13534243131916719416402281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72182630036889170220812165 13534243131916719416402281)
            ·
              refine ⟨10150682348937539562301711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13534243131916719416402281 10150682348937539562301711)
              ·
                refine ⟨15226023523406309343452567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10150682348937539562301711 15226023523406309343452567)
                ·
                  refine ⟨22839035285109464015178851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15226023523406309343452567 22839035285109464015178851)
                  ·
                    refine ⟨34258552927664196022768277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22839035285109464015178851 34258552927664196022768277)
                    ·
                      refine ⟨1605869668484259188567263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34258552927664196022768277 1605869668484259188567263)
                      ·
                        rfl

theorem cell23_3127420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_3127420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127420 prefixEnd_3127420 := by exact prefixLift 3127420
  have htrace : WordTrace (prefixWord ++ tailWord_3127420) baseStart_3127420 baseEnd_3127420 := by
    simpa [prefixWord, tailWord_3127420, baseEnd_3127420] using wordTrace_append hprefix tailTrace_3127420
  have hstable : (prefixWord ++ tailWord_3127420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127420).length < 2 ^ (prefixWord ++ tailWord_3127420).sum := by decide
  have hdescent : baseEnd_3127420 < baseStart_3127420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127427 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 3]
def baseStart_3127427 : Nat := 118140960795 + 3127427 * 2 ^ 59
def prefixEnd_3127427 : Nat := 4983230072969 + 3 ^ 40 * 3127427 * 2
def baseEnd_3127427 : Nat := 1605873262848840661179731

theorem tailTrace_3127427 : CollatzResearch.WordTrace tailWord_3127427 prefixEnd_3127427 1605873262848840661179731 := by
  unfold tailWord_3127427
  simp only [CollatzResearch.WordTrace]
  refine ⟨114066633640873575853084535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76044422427249050568723023 114066633640873575853084535)
  ·
    refine ⟨171099950461310363779626803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114066633640873575853084535 171099950461310363779626803)
    ·
      refine ⟨256649925691965545669440205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171099950461310363779626803 256649925691965545669440205)
      ·
        refine ⟨96243722134487079626040077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256649925691965545669440205 96243722134487079626040077)
        ·
          refine ⟨36091395800432654859765029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96243722134487079626040077 36091395800432654859765029)
          ·
            refine ⟨6767136712581122786205943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36091395800432654859765029 6767136712581122786205943)
            ·
              refine ⟨10150705068871684179308915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6767136712581122786205943 10150705068871684179308915)
              ·
                refine ⟨15226057603307526268963373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10150705068871684179308915 15226057603307526268963373)
                ·
                  refine ⟨5709771601240322350861265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15226057603307526268963373 5709771601240322350861265)
                  ·
                    refine ⟨4282328700930241763145949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5709771601240322350861265 4282328700930241763145949)
                    ·
                      refine ⟨1605873262848840661179731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4282328700930241763145949 1605873262848840661179731)
                      ·
                        rfl

theorem cell23_3127427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_3127427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127427 prefixEnd_3127427 := by exact prefixLift 3127427
  have htrace : WordTrace (prefixWord ++ tailWord_3127427) baseStart_3127427 baseEnd_3127427 := by
    simpa [prefixWord, tailWord_3127427, baseEnd_3127427] using wordTrace_append hprefix tailTrace_3127427
  have hstable : (prefixWord ++ tailWord_3127427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127427).length < 2 ^ (prefixWord ++ tailWord_3127427).sum := by decide
  have hdescent : baseEnd_3127427 < baseStart_3127427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127446 : List Nat := [5, 3, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3127446 : Nat := 118140960795 + 3127446 * 2 ^ 59
def prefixEnd_3127446 : Nat := 4983230072969 + 3 ^ 40 * 3127446 * 2
def baseEnd_3127446 : Nat := 535294339660425362280715

theorem tailTrace_3127446 : CollatzResearch.WordTrace tailWord_3127446 prefixEnd_3127446 535294339660425362280715 := by
  unfold tailWord_3127446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7129207914237796381126637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76044884418536494732017461 7129207914237796381126637)
  ·
    refine ⟨2673452967839173642922489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7129207914237796381126637 2673452967839173642922489)
    ·
      refine ⟨2005089725879380232191867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2673452967839173642922489 2005089725879380232191867)
      ·
        refine ⟨3007634588819070348287801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005089725879380232191867 3007634588819070348287801)
        ·
          refine ⟨2255725941614302761215851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3007634588819070348287801 2255725941614302761215851)
          ·
            refine ⟨3383588912421454141823777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255725941614302761215851 3383588912421454141823777)
            ·
              refine ⟨2537691684316090606367833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3383588912421454141823777 2537691684316090606367833)
              ·
                refine ⟨1903268763237067954775875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2537691684316090606367833 1903268763237067954775875)
                ·
                  refine ⟨2854903144855601932163813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903268763237067954775875 2854903144855601932163813)
                  ·
                    refine ⟨535294339660425362280715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2854903144855601932163813 535294339660425362280715)
                    ·
                      rfl

theorem cell23_3127446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3127446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127446 prefixEnd_3127446 := by exact prefixLift 3127446
  have htrace : WordTrace (prefixWord ++ tailWord_3127446) baseStart_3127446 baseEnd_3127446 := by
    simpa [prefixWord, tailWord_3127446, baseEnd_3127446] using wordTrace_append hprefix tailTrace_3127446
  have hstable : (prefixWord ++ tailWord_3127446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127446).length < 2 ^ (prefixWord ++ tailWord_3127446).sum := by decide
  have hdescent : baseEnd_3127446 < baseStart_3127446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127474 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_3127474 : Nat := 118140960795 + 3127474 * 2 ^ 59
def prefixEnd_3127474 : Nat := 4983230072969 + 3 ^ 40 * 3127474 * 2
def baseEnd_3127474 : Nat := 1605897396439601977292015

theorem tailTrace_3127474 : CollatzResearch.WordTrace tailWord_3127474 prefixEnd_3127474 1605897396439601977292015 := by
  unfold tailWord_3127474
  simp only [CollatzResearch.WordTrace]
  refine ⟨28517086967925825720011369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76045565247802201920030317 28517086967925825720011369)
  ·
    refine ⟨21387815225944369290008527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28517086967925825720011369 21387815225944369290008527)
    ·
      refine ⟨32081722838916553935012791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21387815225944369290008527 32081722838916553935012791)
      ·
        refine ⟨48122584258374830902519187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32081722838916553935012791 48122584258374830902519187)
        ·
          refine ⟨72183876387562246353778781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48122584258374830902519187 72183876387562246353778781)
          ·
            refine ⟨27068953645335842382667043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72183876387562246353778781 27068953645335842382667043)
            ·
              refine ⟨40603430468003763574000565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27068953645335842382667043 40603430468003763574000565)
              ·
                refine ⟨3806571606375352835062553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40603430468003763574000565 3806571606375352835062553)
                ·
                  refine ⟨2854928704781514626296915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3806571606375352835062553 2854928704781514626296915)
                  ·
                    refine ⟨4282393057172271939445373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2854928704781514626296915 4282393057172271939445373)
                    ·
                      refine ⟨1605897396439601977292015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4282393057172271939445373 1605897396439601977292015)
                      ·
                        rfl

theorem cell23_3127474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_3127474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127474 prefixEnd_3127474 := by exact prefixLift 3127474
  have htrace : WordTrace (prefixWord ++ tailWord_3127474) baseStart_3127474 baseEnd_3127474 := by
    simpa [prefixWord, tailWord_3127474, baseEnd_3127474] using wordTrace_append hprefix tailTrace_3127474
  have hstable : (prefixWord ++ tailWord_3127474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127474).length < 2 ^ (prefixWord ++ tailWord_3127474).sum := by decide
  have hdescent : baseEnd_3127474 < baseStart_3127474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127480 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_3127480 : Nat := 118140960795 + 3127480 * 2 ^ 59
def prefixEnd_3127480 : Nat := 4983230072969 + 3 ^ 40 * 3127480 * 2
def baseEnd_3127480 : Nat := 1605900477323528953816987

theorem tailTrace_3127480 : CollatzResearch.WordTrace tailWord_3127480 prefixEnd_3127480 1605900477323528953816987 := by
  unfold tailWord_3127480
  simp only [CollatzResearch.WordTrace]
  refine ⟨57034283354840782952381947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76045711139787710603175929 57034283354840782952381947)
  ·
    refine ⟨85551425032261174428572921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57034283354840782952381947 85551425032261174428572921)
    ·
      refine ⟨64163568774195880821429691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85551425032261174428572921 64163568774195880821429691)
      ·
        refine ⟨96245353161293821232144537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64163568774195880821429691 96245353161293821232144537)
        ·
          refine ⟨72184014870970365924108403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96245353161293821232144537 72184014870970365924108403)
          ·
            refine ⟨108276022306455548886162605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72184014870970365924108403 108276022306455548886162605)
            ·
              refine ⟨40603508364920830832310977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108276022306455548886162605 40603508364920830832310977)
              ·
                refine ⟨30452631273690623124233233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40603508364920830832310977 30452631273690623124233233)
                ·
                  refine ⟨22839473455267967343174925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30452631273690623124233233 22839473455267967343174925)
                  ·
                    refine ⟨8564802545725487753690597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22839473455267967343174925 8564802545725487753690597)
                    ·
                      refine ⟨1605900477323528953816987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8564802545725487753690597 1605900477323528953816987)
                      ·
                        rfl

theorem cell23_3127480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_3127480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127480 prefixEnd_3127480 := by exact prefixLift 3127480
  have htrace : WordTrace (prefixWord ++ tailWord_3127480) baseStart_3127480 baseEnd_3127480 := by
    simpa [prefixWord, tailWord_3127480, baseEnd_3127480] using wordTrace_append hprefix tailTrace_3127480
  have hstable : (prefixWord ++ tailWord_3127480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127480).length < 2 ^ (prefixWord ++ tailWord_3127480).sum := by decide
  have hdescent : baseEnd_3127480 < baseStart_3127480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127497 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 3, 4, 2]
def baseStart_3127497 : Nat := 118140960795 + 3127497 * 2 ^ 59
def prefixEnd_3127497 : Nat := 4983230072969 + 3 ^ 40 * 3127497 * 2
def baseEnd_3127497 : Nat := 1605909206494655387304409

theorem tailTrace_3127497 : CollatzResearch.WordTrace tailWord_3127497 prefixEnd_3127497 1605909206494655387304409 := by
  unfold tailWord_3127497
  simp only [CollatzResearch.WordTrace]
  refine ⟨114069186750619977808132745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76046124500413318538755163 114069186750619977808132745)
  ·
    refine ⟨85551890062964983356099559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114069186750619977808132745 85551890062964983356099559)
    ·
      refine ⟨128327835094447475034149339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85551890062964983356099559 128327835094447475034149339)
      ·
        refine ⟨192491752641671212551224009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128327835094447475034149339 192491752641671212551224009)
        ·
          refine ⟨144368814481253409413418007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192491752641671212551224009 144368814481253409413418007)
          ·
            refine ⟨216553221721880114120127011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144368814481253409413418007 216553221721880114120127011)
            ·
              refine ⟨324829832582820171180190517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216553221721880114120127011 324829832582820171180190517)
              ·
                refine ⟨30452796804639391048142861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 324829832582820171180190517 30452796804639391048142861)
                ·
                  refine ⟨11419798801739771643053573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30452796804639391048142861 11419798801739771643053573)
                  ·
                    refine ⟨2141212275326207183072545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11419798801739771643053573 2141212275326207183072545)
                    ·
                      refine ⟨1605909206494655387304409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141212275326207183072545 1605909206494655387304409)
                      ·
                        rfl

theorem cell23_3127497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 4, 2].length) (baseStart_3127497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127497 prefixEnd_3127497 := by exact prefixLift 3127497
  have htrace : WordTrace (prefixWord ++ tailWord_3127497) baseStart_3127497 baseEnd_3127497 := by
    simpa [prefixWord, tailWord_3127497, baseEnd_3127497] using wordTrace_append hprefix tailTrace_3127497
  have hstable : (prefixWord ++ tailWord_3127497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127497).length < 2 ^ (prefixWord ++ tailWord_3127497).sum := by decide
  have hdescent : baseEnd_3127497 < baseStart_3127497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127582 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_3127582 : Nat := 118140960795 + 3127582 * 2 ^ 59
def prefixEnd_3127582 : Nat := 4983230072969 + 3 ^ 40 * 3127582 * 2
def baseEnd_3127582 : Nat := 1605952852350287554741519

theorem tailTrace_3127582 : CollatzResearch.WordTrace tailWord_3127582 prefixEnd_3127582 1605952852350287554741519 := by
  unfold tailWord_3127582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14259035869414004665622125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76048191303541358216651333 14259035869414004665622125)
  ·
    refine ⟨5347138451030251749608297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14259035869414004665622125 5347138451030251749608297)
    ·
      refine ⟨4010353838272688812206223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5347138451030251749608297 4010353838272688812206223)
      ·
        refine ⟨6015530757409033218309335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4010353838272688812206223 6015530757409033218309335)
        ·
          refine ⟨9023296136113549827464003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6015530757409033218309335 9023296136113549827464003)
          ·
            refine ⟨13534944204170324741196005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9023296136113549827464003 13534944204170324741196005)
            ·
              refine ⟨2537802038281935888974251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13534944204170324741196005 2537802038281935888974251)
              ·
                refine ⟨3806703057422903833461377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537802038281935888974251 3806703057422903833461377)
                ·
                  refine ⟨2855027293067177875096033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3806703057422903833461377 2855027293067177875096033)
                  ·
                    refine ⟨2141270469800383406322025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2855027293067177875096033 2141270469800383406322025)
                    ·
                      refine ⟨1605952852350287554741519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2141270469800383406322025 1605952852350287554741519)
                      ·
                        rfl

theorem cell23_3127582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_3127582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127582 prefixEnd_3127582 := by exact prefixLift 3127582
  have htrace : WordTrace (prefixWord ++ tailWord_3127582) baseStart_3127582 baseEnd_3127582 := by
    simpa [prefixWord, tailWord_3127582, baseEnd_3127582] using wordTrace_append hprefix tailTrace_3127582
  have hstable : (prefixWord ++ tailWord_3127582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127582).length < 2 ^ (prefixWord ++ tailWord_3127582).sum := by decide
  have hdescent : baseEnd_3127582 < baseStart_3127582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127587 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 4]
def baseStart_3127587 : Nat := 118140960795 + 3127587 * 2 ^ 59
def prefixEnd_3127587 : Nat := 4983230072969 + 3 ^ 40 * 3127587 * 2
def baseEnd_3127587 : Nat := 1605955419753560035178995

theorem tailTrace_3127587 : CollatzResearch.WordTrace tailWord_3127587 prefixEnd_3127587 1605955419753560035178995 := by
  unfold tailWord_3127587
  simp only [CollatzResearch.WordTrace]
  refine ⟨114072469320293923178909015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76048312880195948785939343 114072469320293923178909015)
  ·
    refine ⟨171108703980440884768363523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114072469320293923178909015 171108703980440884768363523)
    ·
      refine ⟨256663055970661327152545285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171108703980440884768363523 256663055970661327152545285)
      ·
        refine ⟨48124322994498998841102241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256663055970661327152545285 48124322994498998841102241)
        ·
          refine ⟨36093242245874249130826681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48124322994498998841102241 36093242245874249130826681)
          ·
            refine ⟨27069931684405686848120011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36093242245874249130826681 27069931684405686848120011)
            ·
              refine ⟨40604897526608530272180017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27069931684405686848120011 40604897526608530272180017)
              ·
                refine ⟨30453673144956397704135013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40604897526608530272180017 30453673144956397704135013)
                ·
                  refine ⟨5710063714679324569525315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30453673144956397704135013 5710063714679324569525315)
                  ·
                    refine ⟨8565095572018986854287973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5710063714679324569525315 8565095572018986854287973)
                    ·
                      refine ⟨1605955419753560035178995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8565095572018986854287973 1605955419753560035178995)
                      ·
                        rfl

theorem cell23_3127587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_3127587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127587 prefixEnd_3127587 := by exact prefixLift 3127587
  have htrace : WordTrace (prefixWord ++ tailWord_3127587) baseStart_3127587 baseEnd_3127587 := by
    simpa [prefixWord, tailWord_3127587, baseEnd_3127587] using wordTrace_append hprefix tailTrace_3127587
  have hstable : (prefixWord ++ tailWord_3127587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127587).length < 2 ^ (prefixWord ++ tailWord_3127587).sum := by decide
  have hdescent : baseEnd_3127587 < baseStart_3127587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127607 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 3]
def baseStart_3127607 : Nat := 118140960795 + 3127607 * 2 ^ 59
def prefixEnd_3127607 : Nat := 4983230072969 + 3 ^ 40 * 3127607 * 2
def baseEnd_3127607 : Nat := 1605965689366649956928903

theorem tailTrace_3127607 : CollatzResearch.WordTrace tailWord_3127607 prefixEnd_3127607 1605965689366649956928903 := by
  unfold tailWord_3127607
  simp only [CollatzResearch.WordTrace]
  refine ⟨114073198780221466594637075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76048799186814311063091383 114073198780221466594637075)
  ·
    refine ⟨171109798170332199891955613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114073198780221466594637075 171109798170332199891955613)
    ·
      refine ⟨64166174313874574959483355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171109798170332199891955613 64166174313874574959483355)
      ·
        refine ⟨96249261470811862439225033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64166174313874574959483355 96249261470811862439225033)
        ·
          refine ⟨72186946103108896829418775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96249261470811862439225033 72186946103108896829418775)
          ·
            refine ⟨108280419154663345244128163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72186946103108896829418775 108280419154663345244128163)
            ·
              refine ⟨162420628731995017866192245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108280419154663345244128163 162420628731995017866192245)
              ·
                refine ⟨15226933943624532924955523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162420628731995017866192245 15226933943624532924955523)
                ·
                  refine ⟨22840400915436799387433285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15226933943624532924955523 22840400915436799387433285)
                  ·
                    refine ⟨4282575171644399885143741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22840400915436799387433285 4282575171644399885143741)
                    ·
                      refine ⟨1605965689366649956928903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4282575171644399885143741 1605965689366649956928903)
                      ·
                        rfl

theorem cell23_3127607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_3127607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127607 prefixEnd_3127607 := by exact prefixLift 3127607
  have htrace : WordTrace (prefixWord ++ tailWord_3127607) baseStart_3127607 baseEnd_3127607 := by
    simpa [prefixWord, tailWord_3127607, baseEnd_3127607] using wordTrace_append hprefix tailTrace_3127607
  have hstable : (prefixWord ++ tailWord_3127607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127607).length < 2 ^ (prefixWord ++ tailWord_3127607).sum := by decide
  have hdescent : baseEnd_3127607 < baseStart_3127607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3127624 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_3127624 : Nat := 118140960795 + 3127624 * 2 ^ 59
def prefixEnd_3127624 : Nat := 4983230072969 + 3 ^ 40 * 3127624 * 2
def baseEnd_3127624 : Nat := 1605974418537776390416325

theorem tailTrace_3127624 : CollatzResearch.WordTrace tailWord_3127624 prefixEnd_3127624 1605974418537776390416325 := by
  unfold tailWord_3127624
  simp only [CollatzResearch.WordTrace]
  refine ⟨57036909410579939249002963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76049212547439918998670617 57036909410579939249002963)
  ·
    refine ⟨85555364115869908873504445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57036909410579939249002963 85555364115869908873504445)
    ·
      refine ⟨32083261543451215827564167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85555364115869908873504445 32083261543451215827564167)
      ·
        refine ⟨48124892315176823741346251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32083261543451215827564167 48124892315176823741346251)
        ·
          refine ⟨72187338472765235612019377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48124892315176823741346251 72187338472765235612019377)
          ·
            refine ⟨54140503854573926709014533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72187338472765235612019377 54140503854573926709014533)
            ·
              refine ⟨10151344472732611257940225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54140503854573926709014533 10151344472732611257940225)
              ·
                refine ⟨7613508354549458443455169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10151344472732611257940225 7613508354549458443455169)
                ·
                  refine ⟨5710131265912093832591377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7613508354549458443455169 5710131265912093832591377)
                  ·
                    refine ⟨4282598449434070374443533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5710131265912093832591377 4282598449434070374443533)
                    ·
                      refine ⟨1605974418537776390416325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4282598449434070374443533 1605974418537776390416325)
                      ·
                        rfl

theorem cell23_3127624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_3127624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3127624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3127624 prefixEnd_3127624 := by exact prefixLift 3127624
  have htrace : WordTrace (prefixWord ++ tailWord_3127624) baseStart_3127624 baseEnd_3127624 := by
    simpa [prefixWord, tailWord_3127624, baseEnd_3127624] using wordTrace_append hprefix tailTrace_3127624
  have hstable : (prefixWord ++ tailWord_3127624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3127624).length < 2 ^ (prefixWord ++ tailWord_3127624).sum := by decide
  have hdescent : baseEnd_3127624 < baseStart_3127624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3127624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
