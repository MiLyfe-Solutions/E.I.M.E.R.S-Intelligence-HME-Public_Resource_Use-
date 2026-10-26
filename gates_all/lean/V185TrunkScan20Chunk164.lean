import V185TrunkScan20Chunk163

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_997996 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_997996 : Nat := 118140960795 + 997996 * 2 ^ 59
def prefixEnd_997996 : Nat := 4983230072969 + 3 ^ 40 * 997996 * 2
def baseEnd_997996 : Nat := 455512568235184506453605

theorem tailTrace_997996 : CollatzResearch.WordTrace tailWord_997996 prefixEnd_997996 455512568235184506453605 := by
  unfold tailWord_997996
  simp only [CollatzResearch.WordTrace]
  refine ⟨18199952246219205496078921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24266602994958940661438561 18199952246219205496078921)
  ·
    refine ⟨13649964184664404122059191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18199952246219205496078921 13649964184664404122059191)
    ·
      refine ⟨20474946276996606183088787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13649964184664404122059191 20474946276996606183088787)
      ·
        refine ⟨30712419415494909274633181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20474946276996606183088787 30712419415494909274633181)
        ·
          refine ⟨11517157280810590977987443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30712419415494909274633181 11517157280810590977987443)
          ·
            refine ⟨17275735921215886466981165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11517157280810590977987443 17275735921215886466981165)
            ·
              refine ⟨6478400970455957425117937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17275735921215886466981165 6478400970455957425117937)
              ·
                refine ⟨4858800727841968068838453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6478400970455957425117937 4858800727841968068838453)
                ·
                  refine ⟨455512568235184506453605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4858800727841968068838453 455512568235184506453605)
                  ·
                    rfl

theorem cell20_997996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_997996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997996 prefixEnd_997996 := by exact prefixLift 997996
  have htrace : WordTrace (prefixWord ++ tailWord_997996) baseStart_997996 baseEnd_997996 := by
    simpa [prefixWord, tailWord_997996, baseEnd_997996] using wordTrace_append hprefix tailTrace_997996
  have hstable : (prefixWord ++ tailWord_997996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997996).length < 2 ^ (prefixWord ++ tailWord_997996).sum := by decide
  have hdescent : baseEnd_997996 < baseStart_997996 := by decide
  rcases family_descends (prefixWord ++ tailWord_997996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_997999 : List Nat := [1, 1, 2, 1, 3, 2, 5, 3, 2]
def baseStart_997999 : Nat := 118140960795 + 997999 * 2 ^ 59
def prefixEnd_997999 : Nat := 4983230072969 + 3 ^ 40 * 997999 * 2
def baseEnd_997999 : Nat := 455513937516929829353593

theorem tailTrace_997999 : CollatzResearch.WordTrace tailWord_997999 prefixEnd_997999 455513937516929829353593 := by
  unfold tailWord_997999
  simp only [CollatzResearch.WordTrace]
  refine ⟨36400013911427542504517051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24266675940951695003011367 36400013911427542504517051)
  ·
    refine ⟨54600020867141313756775577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36400013911427542504517051 54600020867141313756775577)
    ·
      refine ⟨40950015650355985317581683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54600020867141313756775577 40950015650355985317581683)
      ·
        refine ⟨61425023475533977976372525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40950015650355985317581683 61425023475533977976372525)
        ·
          refine ⟨23034383803325241741139697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61425023475533977976372525 23034383803325241741139697)
          ·
            refine ⟨17275787852493931305854773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23034383803325241741139697 17275787852493931305854773)
            ·
              refine ⟨1619605111171306059923885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17275787852493931305854773 1619605111171306059923885)
              ·
                refine ⟨607351916689239772471457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1619605111171306059923885 607351916689239772471457)
                ·
                  refine ⟨455513937516929829353593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607351916689239772471457 455513937516929829353593)
                  ·
                    rfl

theorem cell20_997999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 2].length) (baseStart_997999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_997999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_997999 prefixEnd_997999 := by exact prefixLift 997999
  have htrace : WordTrace (prefixWord ++ tailWord_997999) baseStart_997999 baseEnd_997999 := by
    simpa [prefixWord, tailWord_997999, baseEnd_997999] using wordTrace_append hprefix tailTrace_997999
  have hstable : (prefixWord ++ tailWord_997999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_997999).length < 2 ^ (prefixWord ++ tailWord_997999).sum := by decide
  have hdescent : baseEnd_997999 < baseStart_997999 := by decide
  rcases family_descends (prefixWord ++ tailWord_997999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998016 : List Nat := [2, 1, 1, 2, 1, 6, 3, 2, 2]
def baseStart_998016 : Nat := 118140960795 + 998016 * 2 ^ 59
def prefixEnd_998016 : Nat := 4983230072969 + 3 ^ 40 * 998016 * 2
def baseEnd_998016 : Nat := 455521696780153325786857

theorem tailTrace_998016 : CollatzResearch.WordTrace tailWord_998016 prefixEnd_998016 455521696780153325786857 := by
  unfold tailWord_998016
  simp only [CollatzResearch.WordTrace]
  refine ⟨18200316976182977203942951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24267089301577302938590601 18200316976182977203942951)
  ·
    refine ⟨27300475464274465805914427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18200316976182977203942951 27300475464274465805914427)
    ·
      refine ⟨40950713196411698708871641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27300475464274465805914427 40950713196411698708871641)
      ·
        refine ⟨30713034897308774031653731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40950713196411698708871641 30713034897308774031653731)
        ·
          refine ⟨46069552345963161047480597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30713034897308774031653731 46069552345963161047480597)
          ·
            refine ⟨2159510266217023174100653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46069552345963161047480597 2159510266217023174100653)
            ·
              refine ⟨809816349831383690287745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2159510266217023174100653 809816349831383690287745)
              ·
                refine ⟨607362262373537767715809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809816349831383690287745 607362262373537767715809)
                ·
                  refine ⟨455521696780153325786857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607362262373537767715809 455521696780153325786857)
                  ·
                    rfl

theorem cell20_998016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_998016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998016 prefixEnd_998016 := by exact prefixLift 998016
  have htrace : WordTrace (prefixWord ++ tailWord_998016) baseStart_998016 baseEnd_998016 := by
    simpa [prefixWord, tailWord_998016, baseEnd_998016] using wordTrace_append hprefix tailTrace_998016
  have hstable : (prefixWord ++ tailWord_998016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998016).length < 2 ^ (prefixWord ++ tailWord_998016).sum := by decide
  have hdescent : baseEnd_998016 < baseStart_998016 := by decide
  rcases family_descends (prefixWord ++ tailWord_998016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998026 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 3]
def baseStart_998026 : Nat := 118140960795 + 998026 * 2 ^ 59
def prefixEnd_998026 : Nat := 4983230072969 + 3 ^ 40 * 998026 * 2
def baseEnd_998026 : Nat := 455526261052637735453483

theorem tailTrace_998026 : CollatzResearch.WordTrace tailWord_998026 prefixEnd_998026 455526261052637735453483 := by
  unfold tailWord_998026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100249670582431528937483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24267332454886484077166621 9100249670582431528937483)
  ·
    refine ⟨13650374505873647293406225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9100249670582431528937483 13650374505873647293406225)
    ·
      refine ⟨10237780879405235470054669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13650374505873647293406225 10237780879405235470054669)
      ·
        refine ⟨3839167829776963301270501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10237780879405235470054669 3839167829776963301270501)
        ·
          refine ⟨719843968083180618988219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3839167829776963301270501 719843968083180618988219)
          ·
            refine ⟨1079765952124770928482329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719843968083180618988219 1079765952124770928482329)
            ·
              refine ⟨809824464093578196361747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079765952124770928482329 809824464093578196361747)
              ·
                refine ⟨1214736696140367294542621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809824464093578196361747 1214736696140367294542621)
                ·
                  refine ⟨455526261052637735453483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214736696140367294542621 455526261052637735453483)
                  ·
                    rfl

theorem cell20_998026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_998026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998026 prefixEnd_998026 := by exact prefixLift 998026
  have htrace : WordTrace (prefixWord ++ tailWord_998026) baseStart_998026 baseEnd_998026 := by
    simpa [prefixWord, tailWord_998026, baseEnd_998026] using wordTrace_append hprefix tailTrace_998026
  have hstable : (prefixWord ++ tailWord_998026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998026).length < 2 ^ (prefixWord ++ tailWord_998026).sum := by decide
  have hdescent : baseEnd_998026 < baseStart_998026 := by decide
  rcases family_descends (prefixWord ++ tailWord_998026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998041 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_998041 : Nat := 118140960795 + 998041 * 2 ^ 59
def prefixEnd_998041 : Nat := 4983230072969 + 3 ^ 40 * 998041 * 2
def baseEnd_998041 : Nat := 455533107461364349953421

theorem tailTrace_998041 : CollatzResearch.WordTrace tailWord_998041 prefixEnd_998041 455533107461364349953421 := by
  unfold tailWord_998041
  simp only [CollatzResearch.WordTrace]
  refine ⟨36401545777275383677545977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24267697184850255785030651 36401545777275383677545977)
  ·
    refine ⟨27301159332956537758159483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36401545777275383677545977 27301159332956537758159483)
    ·
      refine ⟨40951738999434806637239225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27301159332956537758159483 40951738999434806637239225)
      ·
        refine ⟨30713804249576104977929419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40951738999434806637239225 30713804249576104977929419)
        ·
          refine ⟨46070706374364157466894129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30713804249576104977929419 46070706374364157466894129)
          ·
            refine ⟨34553029780773118100170597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46070706374364157466894129 34553029780773118100170597)
            ·
              refine ⟨6478693083894959643781987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34553029780773118100170597 6478693083894959643781987)
              ·
                refine ⟨9718039625842439465672981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478693083894959643781987 9718039625842439465672981)
                ·
                  refine ⟨455533107461364349953421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9718039625842439465672981 455533107461364349953421)
                  ·
                    rfl

theorem cell20_998041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_998041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998041 prefixEnd_998041 := by exact prefixLift 998041
  have htrace : WordTrace (prefixWord ++ tailWord_998041) baseStart_998041 baseEnd_998041 := by
    simpa [prefixWord, tailWord_998041, baseEnd_998041] using wordTrace_append hprefix tailTrace_998041
  have hstable : (prefixWord ++ tailWord_998041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998041).length < 2 ^ (prefixWord ++ tailWord_998041).sum := by decide
  have hdescent : baseEnd_998041 < baseStart_998041 := by decide
  rcases family_descends (prefixWord ++ tailWord_998041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998065 : List Nat := [1, 2, 2, 6, 9]
def baseStart_998065 : Nat := 118140960795 + 998065 * 2 ^ 59
def prefixEnd_998065 : Nat := 4983230072969 + 3 ^ 40 * 998065 * 2
def baseEnd_998065 : Nat := 5624000761917616458683

theorem tailTrace_998065 : CollatzResearch.WordTrace tailWord_998065 prefixEnd_998065 5624000761917616458683 := by
  unfold tailWord_998065
  simp only [CollatzResearch.WordTrace]
  refine ⟨36402421129188435776419649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24268280752792290517613099 36402421129188435776419649)
  ·
    refine ⟨27301815846891326832314737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36402421129188435776419649 27301815846891326832314737)
    ·
      refine ⟨20476361885168495124236053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27301815846891326832314737 20476361885168495124236053)
      ·
        refine ⟨959829463367273208948565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20476361885168495124236053 959829463367273208948565)
        ·
          refine ⟨5624000761917616458683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 959829463367273208948565 5624000761917616458683)
          ·
            rfl

theorem cell20_998065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 9].length) (baseStart_998065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998065 prefixEnd_998065 := by exact prefixLift 998065
  have htrace : WordTrace (prefixWord ++ tailWord_998065) baseStart_998065 baseEnd_998065 := by
    simpa [prefixWord, tailWord_998065, baseEnd_998065] using wordTrace_append hprefix tailTrace_998065
  have hstable : (prefixWord ++ tailWord_998065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998065).length < 2 ^ (prefixWord ++ tailWord_998065).sum := by decide
  have hdescent : baseEnd_998065 < baseStart_998065 := by decide
  rcases family_descends (prefixWord ++ tailWord_998065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998071 : List Nat := [1, 1, 3, 1, 6, 2, 2, 2, 2]
def baseStart_998071 : Nat := 118140960795 + 998071 * 2 ^ 59
def prefixEnd_998071 : Nat := 4983230072969 + 3 ^ 40 * 998071 * 2
def baseEnd_998071 : Nat := 455546800278817578953299

theorem tailTrace_998071 : CollatzResearch.WordTrace tailWord_998071 prefixEnd_998071 455546800278817578953299 := by
  unfold tailWord_998071
  simp only [CollatzResearch.WordTrace]
  refine ⟨36402639967166698801138067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24268426644777799200758711 36402639967166698801138067)
  ·
    refine ⟨54603959950750048201707101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36402639967166698801138067 54603959950750048201707101)
    ·
      refine ⟨20476484981531268075640163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54603959950750048201707101 20476484981531268075640163)
      ·
        refine ⟨30714727472296902113460245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20476484981531268075640163 30714727472296902113460245)
        ·
          refine ⟨1439752850263917286568449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30714727472296902113460245 1439752850263917286568449)
          ·
            refine ⟨1079814637697937964926337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439752850263917286568449 1079814637697937964926337)
            ·
              refine ⟨809860978273453473694753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079814637697937964926337 809860978273453473694753)
              ·
                refine ⟨607395733705090105271065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809860978273453473694753 607395733705090105271065)
                ·
                  refine ⟨455546800278817578953299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607395733705090105271065 455546800278817578953299)
                  ·
                    rfl

theorem cell20_998071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 2].length) (baseStart_998071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998071 prefixEnd_998071 := by exact prefixLift 998071
  have htrace : WordTrace (prefixWord ++ tailWord_998071) baseStart_998071 baseEnd_998071 := by
    simpa [prefixWord, tailWord_998071, baseEnd_998071] using wordTrace_append hprefix tailTrace_998071
  have hstable : (prefixWord ++ tailWord_998071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998071).length < 2 ^ (prefixWord ++ tailWord_998071).sum := by decide
  have hdescent : baseEnd_998071 < baseStart_998071 := by decide
  rcases family_descends (prefixWord ++ tailWord_998071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998113 : List Nat := [1, 2, 3, 1, 4, 1, 1, 5, 2]
def baseStart_998113 : Nat := 118140960795 + 998113 * 2 ^ 59
def prefixEnd_998113 : Nat := 4983230072969 + 3 ^ 40 * 998113 * 2
def baseEnd_998113 : Nat := 455565970223252099553127

theorem tailTrace_998113 : CollatzResearch.WordTrace tailWord_998113 prefixEnd_998113 455565970223252099553127 := by
  unfold tailWord_998113
  simp only [CollatzResearch.WordTrace]
  refine ⟨36404171833014539974166993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24269447888676359982777995 36404171833014539974166993)
  ·
    refine ⟨27303128874760904980625245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36404171833014539974166993 27303128874760904980625245)
    ·
      refine ⟨10238673328035339367734467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27303128874760904980625245 10238673328035339367734467)
      ·
        refine ⟨15358009992053009051601701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10238673328035339367734467 15358009992053009051601701)
        ·
          refine ⟨2879626873509939197175319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15358009992053009051601701 2879626873509939197175319)
          ·
            refine ⟨4319440310264908795762979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879626873509939197175319 4319440310264908795762979)
            ·
              refine ⟨6479160465397363193644469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4319440310264908795762979 6479160465397363193644469)
              ·
                refine ⟨607421293631002799404169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6479160465397363193644469 607421293631002799404169)
                ·
                  refine ⟨455565970223252099553127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607421293631002799404169 455565970223252099553127)
                  ·
                    rfl

theorem cell20_998113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_998113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998113 prefixEnd_998113 := by exact prefixLift 998113
  have htrace : WordTrace (prefixWord ++ tailWord_998113) baseStart_998113 baseEnd_998113 := by
    simpa [prefixWord, tailWord_998113, baseEnd_998113] using wordTrace_append hprefix tailTrace_998113
  have hstable : (prefixWord ++ tailWord_998113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998113).length < 2 ^ (prefixWord ++ tailWord_998113).sum := by decide
  have hdescent : baseEnd_998113 < baseStart_998113 := by decide
  rcases family_descends (prefixWord ++ tailWord_998113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998127 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 3]
def baseStart_998127 : Nat := 118140960795 + 998127 * 2 ^ 59
def prefixEnd_998127 : Nat := 4983230072969 + 3 ^ 40 * 998127 * 2
def baseEnd_998127 : Nat := 455572360204730273086403

theorem tailTrace_998127 : CollatzResearch.WordTrace tailWord_998127 prefixEnd_998127 455572360204730273086403 := by
  unfold tailWord_998127
  simp only [CollatzResearch.WordTrace]
  refine ⟨36404682454963820365176635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24269788303309213576784423 36404682454963820365176635)
  ·
    refine ⟨54607023682445730547764953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36404682454963820365176635 54607023682445730547764953)
    ·
      refine ⟨40955267761834297910823715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54607023682445730547764953 40955267761834297910823715)
      ·
        refine ⟨61432901642751446866235573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40955267761834297910823715 61432901642751446866235573)
        ·
          refine ⟨5759334529007948143709585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61432901642751446866235573 5759334529007948143709585)
          ·
            refine ⟨4319500896755961107782189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5759334529007948143709585 4319500896755961107782189)
            ·
              refine ⟨1619812836283485415418321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4319500896755961107782189 1619812836283485415418321)
              ·
                refine ⟨1214859627212614061563741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1619812836283485415418321 1214859627212614061563741)
                ·
                  refine ⟨455572360204730273086403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214859627212614061563741 455572360204730273086403)
                  ·
                    rfl

theorem cell20_998127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 3].length) (baseStart_998127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998127 prefixEnd_998127 := by exact prefixLift 998127
  have htrace : WordTrace (prefixWord ++ tailWord_998127) baseStart_998127 baseEnd_998127 := by
    simpa [prefixWord, tailWord_998127, baseEnd_998127] using wordTrace_append hprefix tailTrace_998127
  have hstable : (prefixWord ++ tailWord_998127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998127).length < 2 ^ (prefixWord ++ tailWord_998127).sum := by decide
  have hdescent : baseEnd_998127 < baseStart_998127 := by decide
  rcases family_descends (prefixWord ++ tailWord_998127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998244 : List Nat := [2, 3, 1, 1, 4, 1, 4, 2, 2]
def baseStart_998244 : Nat := 118140960795 + 998244 * 2 ^ 59
def prefixEnd_998244 : Nat := 4983230072969 + 3 ^ 40 * 998244 * 2
def baseEnd_998244 : Nat := 455625762192797866185925

theorem tailTrace_998244 : CollatzResearch.WordTrace tailWord_998244 prefixEnd_998244 455625762192797866185925 := by
  unfold tailWord_998244
  simp only [CollatzResearch.WordTrace]
  refine ⟨18204474897769974673592893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24272633197026632898123857 18204474897769974673592893)
  ·
    refine ⟨6826678086663740502597335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18204474897769974673592893 6826678086663740502597335)
    ·
      refine ⟨10240017129995610753896003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6826678086663740502597335 10240017129995610753896003)
      ·
        refine ⟨15360025694993416130844005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10240017129995610753896003 15360025694993416130844005)
        ·
          refine ⟨2880004817811265524533251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15360025694993416130844005 2880004817811265524533251)
          ·
            refine ⟨4320007226716898286799877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880004817811265524533251 4320007226716898286799877)
            ·
              refine ⟨810001355009418428774977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4320007226716898286799877 810001355009418428774977)
              ·
                refine ⟨607501016257063821581233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810001355009418428774977 607501016257063821581233)
                ·
                  refine ⟨455625762192797866185925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607501016257063821581233 455625762192797866185925)
                  ·
                    rfl

theorem cell20_998244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_998244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998244 prefixEnd_998244 := by exact prefixLift 998244
  have htrace : WordTrace (prefixWord ++ tailWord_998244) baseStart_998244 baseEnd_998244 := by
    simpa [prefixWord, tailWord_998244, baseEnd_998244] using wordTrace_append hprefix tailTrace_998244
  have hstable : (prefixWord ++ tailWord_998244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998244).length < 2 ^ (prefixWord ++ tailWord_998244).sum := by decide
  have hdescent : baseEnd_998244 < baseStart_998244 := by decide
  rcases family_descends (prefixWord ++ tailWord_998244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998269 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_998269 : Nat := 118140960795 + 998269 * 2 ^ 59
def prefixEnd_998269 : Nat := 4983230072969 + 3 ^ 40 * 998269 * 2
def baseEnd_998269 : Nat := 455637172874008890352489

theorem tailTrace_998269 : CollatzResearch.WordTrace tailWord_998269 prefixEnd_998269 455637172874008890352489 := by
  unfold tailWord_998269
  simp only [CollatzResearch.WordTrace]
  refine ⟨36409861620449378616845861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24273241080299585744563907 36409861620449378616845861)
  ·
    refine ⟨6826849053834258490658599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36409861620449378616845861 6826849053834258490658599)
    ·
      refine ⟨10240273580751387735987899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6826849053834258490658599 10240273580751387735987899)
      ·
        refine ⟨15360410371127081603981849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10240273580751387735987899 15360410371127081603981849)
        ·
          refine ⟨11520307778345311202986387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15360410371127081603981849 11520307778345311202986387)
          ·
            refine ⟨17280461667517966804479581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11520307778345311202986387 17280461667517966804479581)
            ·
              refine ⟨6480173125319237551679843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17280461667517966804479581 6480173125319237551679843)
              ·
                refine ⟨9720259687978856327519765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480173125319237551679843 9720259687978856327519765)
                ·
                  refine ⟨455637172874008890352489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9720259687978856327519765 455637172874008890352489)
                  ·
                    rfl

theorem cell20_998269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_998269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998269 prefixEnd_998269 := by exact prefixLift 998269
  have htrace : WordTrace (prefixWord ++ tailWord_998269) baseStart_998269 baseEnd_998269 := by
    simpa [prefixWord, tailWord_998269, baseEnd_998269] using wordTrace_append hprefix tailTrace_998269
  have hstable : (prefixWord ++ tailWord_998269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998269).length < 2 ^ (prefixWord ++ tailWord_998269).sum := by decide
  have hdescent : baseEnd_998269 < baseStart_998269 := by decide
  rcases family_descends (prefixWord ++ tailWord_998269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998282 : List Nat := [3, 1, 2, 4, 1, 2, 2, 3, 2]
def baseStart_998282 : Nat := 118140960795 + 998282 * 2 ^ 59
def prefixEnd_998282 : Nat := 4983230072969 + 3 ^ 40 * 998282 * 2
def baseEnd_998282 : Nat := 455643106428238622919103

theorem tailTrace_998282 : CollatzResearch.WordTrace tailWord_998282 prefixEnd_998282 455643106428238622919103 := by
  unfold tailWord_998282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9102583942350570459267275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24273557179601521224712733 9102583942350570459267275)
  ·
    refine ⟨13653875913525855688900913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9102583942350570459267275 13653875913525855688900913)
    ·
      refine ⟨10240406935144391766675685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13653875913525855688900913 10240406935144391766675685)
      ·
        refine ⟨1920076300339573456251691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10240406935144391766675685 1920076300339573456251691)
        ·
          refine ⟨2880114450509360184377537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920076300339573456251691 2880114450509360184377537)
          ·
            refine ⟨2160085837882020138283153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2880114450509360184377537 2160085837882020138283153)
            ·
              refine ⟨1620064378411515103712365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2160085837882020138283153 1620064378411515103712365)
              ·
                refine ⟨607524141904318163892137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1620064378411515103712365 607524141904318163892137)
                ·
                  refine ⟨455643106428238622919103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607524141904318163892137 455643106428238622919103)
                  ·
                    rfl

theorem cell20_998282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_998282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998282 prefixEnd_998282 := by exact prefixLift 998282
  have htrace : WordTrace (prefixWord ++ tailWord_998282) baseStart_998282 baseEnd_998282 := by
    simpa [prefixWord, tailWord_998282, baseEnd_998282] using wordTrace_append hprefix tailTrace_998282
  have hstable : (prefixWord ++ tailWord_998282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998282).length < 2 ^ (prefixWord ++ tailWord_998282).sum := by decide
  have hdescent : baseEnd_998282 < baseStart_998282 := by decide
  rcases family_descends (prefixWord ++ tailWord_998282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998303 : List Nat := [1, 1, 2, 5, 2, 1, 2, 4, 2]
def baseStart_998303 : Nat := 118140960795 + 998303 * 2 ^ 59
def prefixEnd_998303 : Nat := 4983230072969 + 3 ^ 40 * 998303 * 2
def baseEnd_998303 : Nat := 455652691400455883219017

theorem tailTrace_998303 : CollatzResearch.WordTrace tailWord_998303 prefixEnd_998303 455652691400455883219017 := by
  unfold tailWord_998303
  simp only [CollatzResearch.WordTrace]
  refine ⟨36411101702326202423583563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24274067801550801615722375 36411101702326202423583563)
  ·
    refine ⟨54616652553489303635375345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36411101702326202423583563 54616652553489303635375345)
    ·
      refine ⟨40962489415116977726531509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54616652553489303635375345 40962489415116977726531509)
      ·
        refine ⟨3840233382667216661862329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40962489415116977726531509 3840233382667216661862329)
        ·
          refine ⟨2880175037000412496396747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3840233382667216661862329 2880175037000412496396747)
          ·
            refine ⟨4320262555500618744595121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880175037000412496396747 4320262555500618744595121)
            ·
              refine ⟨3240196916625464058446341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4320262555500618744595121 3240196916625464058446341)
              ·
                refine ⟨607536921867274510958689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3240196916625464058446341 607536921867274510958689)
                ·
                  refine ⟨455652691400455883219017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607536921867274510958689 455652691400455883219017)
                  ·
                    rfl

theorem cell20_998303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 2].length) (baseStart_998303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998303 prefixEnd_998303 := by exact prefixLift 998303
  have htrace : WordTrace (prefixWord ++ tailWord_998303) baseStart_998303 baseEnd_998303 := by
    simpa [prefixWord, tailWord_998303, baseEnd_998303] using wordTrace_append hprefix tailTrace_998303
  have hstable : (prefixWord ++ tailWord_998303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998303).length < 2 ^ (prefixWord ++ tailWord_998303).sum := by decide
  have hdescent : baseEnd_998303 < baseStart_998303 := by decide
  rcases family_descends (prefixWord ++ tailWord_998303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998307 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_998307 : Nat := 118140960795 + 998307 * 2 ^ 59
def prefixEnd_998307 : Nat := 4983230072969 + 3 ^ 40 * 998307 * 2
def baseEnd_998307 : Nat := 455654517109449647085667

theorem tailTrace_998307 : CollatzResearch.WordTrace tailWord_998307 prefixEnd_998307 455654517109449647085667 := by
  unfold tailWord_998307
  simp only [CollatzResearch.WordTrace]
  refine ⟨36411247594311711106729175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24274165062874474071152783 36411247594311711106729175)
  ·
    refine ⟨54616871391467566660093763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36411247594311711106729175 54616871391467566660093763)
    ·
      refine ⟨81925307087201349990140645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54616871391467566660093763 81925307087201349990140645)
      ·
        refine ⟨15360995078850253123151371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81925307087201349990140645 15360995078850253123151371)
        ·
          refine ⟨23041492618275379684727057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15360995078850253123151371 23041492618275379684727057)
          ·
            refine ⟨17281119463706534763545293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23041492618275379684727057 17281119463706534763545293)
            ·
              refine ⟨6480419798889950536329485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17281119463706534763545293 6480419798889950536329485)
              ·
                refine ⟨2430157424583731451123557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6480419798889950536329485 2430157424583731451123557)
                ·
                  refine ⟨455654517109449647085667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2430157424583731451123557 455654517109449647085667)
                  ·
                    rfl

theorem cell20_998307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_998307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998307 prefixEnd_998307 := by exact prefixLift 998307
  have htrace : WordTrace (prefixWord ++ tailWord_998307) baseStart_998307 baseEnd_998307 := by
    simpa [prefixWord, tailWord_998307, baseEnd_998307] using wordTrace_append hprefix tailTrace_998307
  have hstable : (prefixWord ++ tailWord_998307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998307).length < 2 ^ (prefixWord ++ tailWord_998307).sum := by decide
  have hdescent : baseEnd_998307 < baseStart_998307 := by decide
  rcases family_descends (prefixWord ++ tailWord_998307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998358 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_998358 : Nat := 118140960795 + 998358 * 2 ^ 59
def prefixEnd_998358 : Nat := 4983230072969 + 3 ^ 40 * 998358 * 2
def baseEnd_998358 : Nat := 455677794899120136385459

theorem tailTrace_998358 : CollatzResearch.WordTrace tailWord_998358 prefixEnd_998358 455677794899120136385459 := by
  unfold tailWord_998358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275819232320434176052233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24275405144751297877890485 2275819232320434176052233)
  ·
    refine ⟨1706864424240325632039175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2275819232320434176052233 1706864424240325632039175)
    ·
      refine ⟨2560296636360488448058763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706864424240325632039175 2560296636360488448058763)
      ·
        refine ⟨3840444954540732672088145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2560296636360488448058763 3840444954540732672088145)
        ·
          refine ⟨2880333715905549504066109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3840444954540732672088145 2880333715905549504066109)
          ·
            refine ⟨1080125143464581064024791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2880333715905549504066109 1080125143464581064024791)
            ·
              refine ⟨1620187715196871596037187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080125143464581064024791 1620187715196871596037187)
              ·
                refine ⟨2430281572795307394055781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620187715196871596037187 2430281572795307394055781)
                ·
                  refine ⟨455677794899120136385459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2430281572795307394055781 455677794899120136385459)
                  ·
                    rfl

theorem cell20_998358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_998358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998358 prefixEnd_998358 := by exact prefixLift 998358
  have htrace : WordTrace (prefixWord ++ tailWord_998358) baseStart_998358 baseEnd_998358 := by
    simpa [prefixWord, tailWord_998358, baseEnd_998358] using wordTrace_append hprefix tailTrace_998358
  have hstable : (prefixWord ++ tailWord_998358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998358).length < 2 ^ (prefixWord ++ tailWord_998358).sum := by decide
  have hdescent : baseEnd_998358 < baseStart_998358 := by decide
  rcases family_descends (prefixWord ++ tailWord_998358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998362 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_998362 : Nat := 118140960795 + 998362 * 2 ^ 59
def prefixEnd_998362 : Nat := 4983230072969 + 3 ^ 40 * 998362 * 2
def baseEnd_998362 : Nat := 455679620608113900252109

theorem tailTrace_998362 : CollatzResearch.WordTrace tailWord_998362 prefixEnd_998362 455679620608113900252109 := by
  unfold tailWord_998362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9103313402278113874995335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24275502406074970333320893 9103313402278113874995335)
  ·
    refine ⟨13654970103417170812493003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9103313402278113874995335 13654970103417170812493003)
    ·
      refine ⟨20482455155125756218739505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13654970103417170812493003 20482455155125756218739505)
      ·
        refine ⟨15361841366344317164054629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20482455155125756218739505 15361841366344317164054629)
        ·
          refine ⟨2880345256189559468260243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15361841366344317164054629 2880345256189559468260243)
          ·
            refine ⟨4320517884284339202390365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880345256189559468260243 4320517884284339202390365)
            ·
              refine ⟨1620194206606627200896387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4320517884284339202390365 1620194206606627200896387)
              ·
                refine ⟨2430291309909940801344581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620194206606627200896387 2430291309909940801344581)
                ·
                  refine ⟨455679620608113900252109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2430291309909940801344581 455679620608113900252109)
                  ·
                    rfl

theorem cell20_998362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_998362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998362 prefixEnd_998362 := by exact prefixLift 998362
  have htrace : WordTrace (prefixWord ++ tailWord_998362) baseStart_998362 baseEnd_998362 := by
    simpa [prefixWord, tailWord_998362, baseEnd_998362] using wordTrace_append hprefix tailTrace_998362
  have hstable : (prefixWord ++ tailWord_998362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998362).length < 2 ^ (prefixWord ++ tailWord_998362).sum := by decide
  have hdescent : baseEnd_998362 < baseStart_998362 := by decide
  rcases family_descends (prefixWord ++ tailWord_998362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998465 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 3]
def baseStart_998465 : Nat := 118140960795 + 998465 * 2 ^ 59
def prefixEnd_998465 : Nat := 4983230072969 + 3 ^ 40 * 998465 * 2
def baseEnd_998465 : Nat := 455726632614703319818355

theorem tailTrace_998465 : CollatzResearch.WordTrace tailWord_998465 prefixEnd_998465 455726632614703319818355 := by
  unfold tailWord_998465
  simp only [CollatzResearch.WordTrace]
  refine ⟨36417010327739304090980849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24278006885159536060653899 36417010327739304090980849)
  ·
    refine ⟨27312757745804478068235637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36417010327739304090980849 27312757745804478068235637)
    ·
      refine ⟨2560571038669169818897091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27312757745804478068235637 2560571038669169818897091)
      ·
        refine ⟨3840856558003754728345637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2560571038669169818897091 3840856558003754728345637)
        ·
          refine ⟨720160604625704011564807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3840856558003754728345637 720160604625704011564807)
          ·
            refine ⟨1080240906938556017347211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720160604625704011564807 1080240906938556017347211)
            ·
              refine ⟨1620361360407834026020817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080240906938556017347211 1620361360407834026020817)
              ·
                refine ⟨1215271020305875519515613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1620361360407834026020817 1215271020305875519515613)
                ·
                  refine ⟨455726632614703319818355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215271020305875519515613 455726632614703319818355)
                  ·
                    rfl

theorem cell20_998465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_998465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998465 prefixEnd_998465 := by exact prefixLift 998465
  have htrace : WordTrace (prefixWord ++ tailWord_998465) baseStart_998465 baseEnd_998465 := by
    simpa [prefixWord, tailWord_998465, baseEnd_998465] using wordTrace_append hprefix tailTrace_998465
  have hstable : (prefixWord ++ tailWord_998465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998465).length < 2 ^ (prefixWord ++ tailWord_998465).sum := by decide
  have hdescent : baseEnd_998465 < baseStart_998465 := by decide
  rcases family_descends (prefixWord ++ tailWord_998465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998497 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_998497 : Nat := 118140960795 + 998497 * 2 ^ 59
def prefixEnd_998497 : Nat := 4983230072969 + 3 ^ 40 * 998497 * 2
def baseEnd_998497 : Nat := 455741238286653430751557

theorem tailTrace_998497 : CollatzResearch.WordTrace tailWord_998497 prefixEnd_998497 455741238286653430751557 := by
  unfold tailWord_998497
  simp only [CollatzResearch.WordTrace]
  refine ⟨36418177463623373556145745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24278784975748915704097163 36418177463623373556145745)
  ·
    refine ⟨27313633097717530167109309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36418177463623373556145745 27313633097717530167109309)
    ·
      refine ⟨10242612411644073812665991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27313633097717530167109309 10242612411644073812665991)
      ·
        refine ⟨15363918617466110718998987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10242612411644073812665991 15363918617466110718998987)
        ·
          refine ⟨23045877926199166078498481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15363918617466110718998987 23045877926199166078498481)
          ·
            refine ⟨17284408444649374558873861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23045877926199166078498481 17284408444649374558873861)
            ·
              refine ⟨3240826583371757729788849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17284408444649374558873861 3240826583371757729788849)
              ·
                refine ⟨2430619937528818297341637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3240826583371757729788849 2430619937528818297341637)
                ·
                  refine ⟨455741238286653430751557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2430619937528818297341637 455741238286653430751557)
                  ·
                    rfl

theorem cell20_998497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_998497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998497 prefixEnd_998497 := by exact prefixLift 998497
  have htrace : WordTrace (prefixWord ++ tailWord_998497) baseStart_998497 baseEnd_998497 := by
    simpa [prefixWord, tailWord_998497, baseEnd_998497] using wordTrace_append hprefix tailTrace_998497
  have hstable : (prefixWord ++ tailWord_998497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998497).length < 2 ^ (prefixWord ++ tailWord_998497).sum := by decide
  have hdescent : baseEnd_998497 < baseStart_998497 := by decide
  rcases family_descends (prefixWord ++ tailWord_998497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998510 : List Nat := [4, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_998510 : Nat := 118140960795 + 998510 * 2 ^ 59
def prefixEnd_998510 : Nat := 4983230072969 + 3 ^ 40 * 998510 * 2
def baseEnd_998510 : Nat := 455747171840883163318171

theorem tailTrace_998510 : CollatzResearch.WordTrace tailWord_998510 prefixEnd_998510 455747171840883163318171 := by
  unfold tailWord_998510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552331451572034597046123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24279101075050851184245989 4552331451572034597046123)
  ·
    refine ⟨6828497177358051895569185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4552331451572034597046123 6828497177358051895569185)
    ·
      refine ⟨5121372883018538921676889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6828497177358051895569185 5121372883018538921676889)
      ·
        refine ⟨3841029662263904191257667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5121372883018538921676889 3841029662263904191257667)
        ·
          refine ⟨5761544493395856286886501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841029662263904191257667 5761544493395856286886501)
          ·
            refine ⟨1080289592511723053791219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5761544493395856286886501 1080289592511723053791219)
            ·
              refine ⟨1620434388767584580686829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080289592511723053791219 1620434388767584580686829)
              ·
                refine ⟨607662895787844217757561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1620434388767584580686829 607662895787844217757561)
                ·
                  refine ⟨455747171840883163318171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607662895787844217757561 455747171840883163318171)
                  ·
                    rfl

theorem cell20_998510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_998510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998510 prefixEnd_998510 := by exact prefixLift 998510
  have htrace : WordTrace (prefixWord ++ tailWord_998510) baseStart_998510 baseEnd_998510 := by
    simpa [prefixWord, tailWord_998510, baseEnd_998510] using wordTrace_append hprefix tailTrace_998510
  have hstable : (prefixWord ++ tailWord_998510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998510).length < 2 ^ (prefixWord ++ tailWord_998510).sum := by decide
  have hdescent : baseEnd_998510 < baseStart_998510 := by decide
  rcases family_descends (prefixWord ++ tailWord_998510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998511 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_998511 : Nat := 118140960795 + 998511 * 2 ^ 59
def prefixEnd_998511 : Nat := 4983230072969 + 3 ^ 40 * 998511 * 2
def baseEnd_998511 : Nat := 455747628268131604284833

theorem tailTrace_998511 : CollatzResearch.WordTrace tailWord_998511 prefixEnd_998511 455747628268131604284833 := by
  unfold tailWord_998511
  simp only [CollatzResearch.WordTrace]
  refine ⟨36418688085572653947155387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24279125390381769298103591 36418688085572653947155387)
  ·
    refine ⟨54628032128358980920733081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36418688085572653947155387 54628032128358980920733081)
    ·
      refine ⟨40971024096269235690549811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54628032128358980920733081 40971024096269235690549811)
      ·
        refine ⟨61456536144403853535824717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40971024096269235690549811 61456536144403853535824717)
        ·
          refine ⟨23046201054151445075934269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61456536144403853535824717 23046201054151445075934269)
          ·
            refine ⟨8642325395306791903475351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23046201054151445075934269 8642325395306791903475351)
            ·
              refine ⟨12963488092960187855213027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8642325395306791903475351 12963488092960187855213027)
              ·
                refine ⟨19445232139440281782819541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12963488092960187855213027 19445232139440281782819541)
                ·
                  refine ⟨455747628268131604284833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19445232139440281782819541 455747628268131604284833)
                  ·
                    rfl

theorem cell20_998511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_998511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998511 prefixEnd_998511 := by exact prefixLift 998511
  have htrace : WordTrace (prefixWord ++ tailWord_998511) baseStart_998511 baseEnd_998511 := by
    simpa [prefixWord, tailWord_998511, baseEnd_998511] using wordTrace_append hprefix tailTrace_998511
  have hstable : (prefixWord ++ tailWord_998511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998511).length < 2 ^ (prefixWord ++ tailWord_998511).sum := by decide
  have hdescent : baseEnd_998511 < baseStart_998511 := by decide
  rcases family_descends (prefixWord ++ tailWord_998511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998517 : List Nat := [1, 3, 4, 3, 2, 1, 6]
def baseStart_998517 : Nat := 118140960795 + 998517 * 2 ^ 59
def prefixEnd_998517 : Nat := 4983230072969 + 3 ^ 40 * 998517 * 2
def baseEnd_998517 : Nat := 50638929647958027787201

theorem tailTrace_998517 : CollatzResearch.WordTrace tailWord_998517 prefixEnd_998517 50638929647958027787201 := by
  unfold tailWord_998517
  simp only [CollatzResearch.WordTrace]
  refine ⟨36418906923550916971873805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24279271282367277981249203 36418906923550916971873805)
  ·
    refine ⟨13657090096331593864452677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36418906923550916971873805 13657090096331593864452677)
    ·
      refine ⟨2560704393062173849584877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13657090096331593864452677 2560704393062173849584877)
      ·
        refine ⟨960264147398315193594329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2560704393062173849584877 960264147398315193594329)
        ·
          refine ⟨720198110548736395195747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 960264147398315193594329 720198110548736395195747)
          ·
            refine ⟨1080297165823104592793621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720198110548736395195747 1080297165823104592793621)
            ·
              refine ⟨50638929647958027787201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1080297165823104592793621 50638929647958027787201)
              ·
                rfl

theorem cell20_998517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 6].length) (baseStart_998517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998517 prefixEnd_998517 := by exact prefixLift 998517
  have htrace : WordTrace (prefixWord ++ tailWord_998517) baseStart_998517 baseEnd_998517 := by
    simpa [prefixWord, tailWord_998517, baseEnd_998517] using wordTrace_append hprefix tailTrace_998517
  have hstable : (prefixWord ++ tailWord_998517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998517).length < 2 ^ (prefixWord ++ tailWord_998517).sum := by decide
  have hdescent : baseEnd_998517 < baseStart_998517 := by decide
  rcases family_descends (prefixWord ++ tailWord_998517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998521 : List Nat := [1, 2, 1, 3, 5, 2, 6]
def baseStart_998521 : Nat := 118140960795 + 998521 * 2 ^ 59
def prefixEnd_998521 : Nat := 4983230072969 + 3 ^ 40 * 998521 * 2
def baseEnd_998521 : Nat := 50639132504512890439051

theorem tailTrace_998521 : CollatzResearch.WordTrace tailWord_998521 prefixEnd_998521 50639132504512890439051 := by
  unfold tailWord_998521
  simp only [CollatzResearch.WordTrace]
  refine ⟨36419052815536425655019417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24279368543690950436679611 36419052815536425655019417)
  ·
    refine ⟨27314289611652319241264563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36419052815536425655019417 27314289611652319241264563)
    ·
      refine ⟨40971434417478478861896845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27314289611652319241264563 40971434417478478861896845)
      ·
        refine ⟨15364287906554429573211317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40971434417478478861896845 15364287906554429573211317)
        ·
          refine ⟨1440401991239477772488561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15364287906554429573211317 1440401991239477772488561)
          ·
            refine ⟨1080301493429608329366421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1440401991239477772488561 1080301493429608329366421)
            ·
              refine ⟨50639132504512890439051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1080301493429608329366421 50639132504512890439051)
              ·
                rfl

theorem cell20_998521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 6].length) (baseStart_998521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998521 prefixEnd_998521 := by exact prefixLift 998521
  have htrace : WordTrace (prefixWord ++ tailWord_998521) baseStart_998521 baseEnd_998521 := by
    simpa [prefixWord, tailWord_998521, baseEnd_998521] using wordTrace_append hprefix tailTrace_998521
  have hstable : (prefixWord ++ tailWord_998521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998521).length < 2 ^ (prefixWord ++ tailWord_998521).sum := by decide
  have hdescent : baseEnd_998521 < baseStart_998521 := by decide
  rcases family_descends (prefixWord ++ tailWord_998521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998531 : List Nat := [1, 1, 1, 3, 3, 2, 5, 2, 2]
def baseStart_998531 : Nat := 118140960795 + 998531 * 2 ^ 59
def prefixEnd_998531 : Nat := 4983230072969 + 3 ^ 40 * 998531 * 2
def baseEnd_998531 : Nat := 455756756813100423618085

theorem tailTrace_998531 : CollatzResearch.WordTrace tailWord_998531 prefixEnd_998531 455756756813100423618085 := by
  unfold tailWord_998531
  simp only [CollatzResearch.WordTrace]
  refine ⟨36419417545500197362883447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24279611697000131575255631 36419417545500197362883447)
  ·
    refine ⟨54629126318250296044325171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36419417545500197362883447 54629126318250296044325171)
    ·
      refine ⟨81943689477375444066487757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54629126318250296044325171 81943689477375444066487757)
      ·
        refine ⟨30728883554015791524932909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81943689477375444066487757 30728883554015791524932909)
        ·
          refine ⟨11523331332755921821849841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30728883554015791524932909 11523331332755921821849841)
          ·
            refine ⟨8642498499566941366387381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11523331332755921821849841 8642498499566941366387381)
            ·
              refine ⟨810234234334400753098817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8642498499566941366387381 810234234334400753098817)
              ·
                refine ⟨607675675750800564824113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810234234334400753098817 607675675750800564824113)
                ·
                  refine ⟨455756756813100423618085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607675675750800564824113 455756756813100423618085)
                  ·
                    rfl

theorem cell20_998531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 2].length) (baseStart_998531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998531 prefixEnd_998531 := by exact prefixLift 998531
  have htrace : WordTrace (prefixWord ++ tailWord_998531) baseStart_998531 baseEnd_998531 := by
    simpa [prefixWord, tailWord_998531, baseEnd_998531] using wordTrace_append hprefix tailTrace_998531
  have hstable : (prefixWord ++ tailWord_998531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998531).length < 2 ^ (prefixWord ++ tailWord_998531).sum := by decide
  have hdescent : baseEnd_998531 < baseStart_998531 := by decide
  rcases family_descends (prefixWord ++ tailWord_998531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998549 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_998549 : Nat := 118140960795 + 998549 * 2 ^ 59
def prefixEnd_998549 : Nat := 4983230072969 + 3 ^ 40 * 998549 * 2
def baseEnd_998549 : Nat := 455764972503572361018011

theorem tailTrace_998549 : CollatzResearch.WordTrace tailWord_998549 prefixEnd_998549 455764972503572361018011 := by
  unfold tailWord_998549
  simp only [CollatzResearch.WordTrace]
  refine ⟨36420074059434986437038701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24280049372956657624692467 36420074059434986437038701)
  ·
    refine ⟨13657527772288119913889513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36420074059434986437038701 13657527772288119913889513)
    ·
      refine ⟨10243145829216089935417135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13657527772288119913889513 10243145829216089935417135)
      ·
        refine ⟨15364718743824134903125703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10243145829216089935417135 15364718743824134903125703)
        ·
          refine ⟨23047078115736202354688555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15364718743824134903125703 23047078115736202354688555)
          ·
            refine ⟨34570617173604303532032833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23047078115736202354688555 34570617173604303532032833)
            ·
              refine ⟨25927962880203227649024625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34570617173604303532032833 25927962880203227649024625)
              ·
                refine ⟨19445972160152420736768469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25927962880203227649024625 19445972160152420736768469)
                ·
                  refine ⟨455764972503572361018011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19445972160152420736768469 455764972503572361018011)
                  ·
                    rfl

theorem cell20_998549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_998549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998549 prefixEnd_998549 := by exact prefixLift 998549
  have htrace : WordTrace (prefixWord ++ tailWord_998549) baseStart_998549 baseEnd_998549 := by
    simpa [prefixWord, tailWord_998549, baseEnd_998549] using wordTrace_append hprefix tailTrace_998549
  have hstable : (prefixWord ++ tailWord_998549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998549).length < 2 ^ (prefixWord ++ tailWord_998549).sum := by decide
  have hdescent : baseEnd_998549 < baseStart_998549 := by decide
  rcases family_descends (prefixWord ++ tailWord_998549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998628 : List Nat := [2, 3, 1, 1, 1, 2, 3, 5, 2]
def baseStart_998628 : Nat := 118140960795 + 998628 * 2 ^ 59
def prefixEnd_998628 : Nat := 4983230072969 + 3 ^ 40 * 998628 * 2
def baseEnd_998628 : Nat := 455801030256199197384355

theorem tailTrace_998628 : CollatzResearch.WordTrace tailWord_998628 prefixEnd_998628 455801030256199197384355 := by
  unfold tailWord_998628
  simp only [CollatzResearch.WordTrace]
  refine ⟨18211477713074391464582269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24281970284099188619443025 18211477713074391464582269)
  ·
    refine ⟨6829304142402896799218351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18211477713074391464582269 6829304142402896799218351)
    ·
      refine ⟨10243956213604345198827527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6829304142402896799218351 10243956213604345198827527)
      ·
        refine ⟨15365934320406517798241291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10243956213604345198827527 15365934320406517798241291)
        ·
          refine ⟨23048901480609776697361937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15365934320406517798241291 23048901480609776697361937)
          ·
            refine ⟨17286676110457332523021453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23048901480609776697361937 17286676110457332523021453)
            ·
              refine ⟨6482503541421499696133045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17286676110457332523021453 6482503541421499696133045)
              ·
                refine ⟨607734707008265596512473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6482503541421499696133045 607734707008265596512473)
                ·
                  refine ⟨455801030256199197384355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607734707008265596512473 455801030256199197384355)
                  ·
                    rfl

theorem cell20_998628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_998628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998628 prefixEnd_998628 := by exact prefixLift 998628
  have htrace : WordTrace (prefixWord ++ tailWord_998628) baseStart_998628 baseEnd_998628 := by
    simpa [prefixWord, tailWord_998628, baseEnd_998628] using wordTrace_append hprefix tailTrace_998628
  have hstable : (prefixWord ++ tailWord_998628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998628).length < 2 ^ (prefixWord ++ tailWord_998628).sum := by decide
  have hdescent : baseEnd_998628 < baseStart_998628 := by decide
  rcases family_descends (prefixWord ++ tailWord_998628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998649 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 4]
def baseStart_998649 : Nat := 118140960795 + 998649 * 2 ^ 59
def prefixEnd_998649 : Nat := 4983230072969 + 3 ^ 40 * 998649 * 2
def baseEnd_998649 : Nat := 455810615228416457684269

theorem tailTrace_998649 : CollatzResearch.WordTrace tailWord_998649 prefixEnd_998649 455810615228416457684269 := by
  unfold tailWord_998649
  simp only [CollatzResearch.WordTrace]
  refine ⟨36423721359072703515679001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24282480906048469010452667 36423721359072703515679001)
  ·
    refine ⟨27317791019304527636759251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36423721359072703515679001 27317791019304527636759251)
    ·
      refine ⟨40976686528956791455138877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27317791019304527636759251 40976686528956791455138877)
      ·
        refine ⟨15366257448358796795677079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40976686528956791455138877 15366257448358796795677079)
        ·
          refine ⟨23049386172538195193515619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15366257448358796795677079 23049386172538195193515619)
          ·
            refine ⟨34574079258807292790273429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23049386172538195193515619 34574079258807292790273429)
            ·
              refine ⟨1620659965256591849544067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34574079258807292790273429 1620659965256591849544067)
              ·
                refine ⟨2430989947884887774316101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620659965256591849544067 2430989947884887774316101)
                ·
                  refine ⟨455810615228416457684269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2430989947884887774316101 455810615228416457684269)
                  ·
                    rfl

theorem cell20_998649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_998649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998649 prefixEnd_998649 := by exact prefixLift 998649
  have htrace : WordTrace (prefixWord ++ tailWord_998649) baseStart_998649 baseEnd_998649 := by
    simpa [prefixWord, tailWord_998649, baseEnd_998649] using wordTrace_append hprefix tailTrace_998649
  have hstable : (prefixWord ++ tailWord_998649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998649).length < 2 ^ (prefixWord ++ tailWord_998649).sum := by decide
  have hdescent : baseEnd_998649 < baseStart_998649 := by decide
  rcases family_descends (prefixWord ++ tailWord_998649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998659 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 3]
def baseStart_998659 : Nat := 118140960795 + 998659 * 2 ^ 59
def prefixEnd_998659 : Nat := 4983230072969 + 3 ^ 40 * 998659 * 2
def baseEnd_998659 : Nat := 455815179500900867350895

theorem tailTrace_998659 : CollatzResearch.WordTrace tailWord_998659 prefixEnd_998659 455815179500900867350895 := by
  unfold tailWord_998659
  simp only [CollatzResearch.WordTrace]
  refine ⟨36424086089036475223543031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24282724059357650149028687 36424086089036475223543031)
  ·
    refine ⟨54636129133554712835314547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36424086089036475223543031 54636129133554712835314547)
    ·
      refine ⟨81954193700332069252971821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54636129133554712835314547 81954193700332069252971821)
      ·
        refine ⟨30732822637624525969864433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81954193700332069252971821 30732822637624525969864433)
        ·
          refine ⟨23049616978218394477398325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30732822637624525969864433 23049616978218394477398325)
          ·
            refine ⟨2160901591707974482256093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23049616978218394477398325 2160901591707974482256093)
            ·
              refine ⟨810338096890490430846035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2160901591707974482256093 810338096890490430846035)
              ·
                refine ⟨1215507145335735646269053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810338096890490430846035 1215507145335735646269053)
                ·
                  refine ⟨455815179500900867350895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215507145335735646269053 455815179500900867350895)
                  ·
                    rfl

theorem cell20_998659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 3].length) (baseStart_998659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998659 prefixEnd_998659 := by exact prefixLift 998659
  have htrace : WordTrace (prefixWord ++ tailWord_998659) baseStart_998659 baseEnd_998659 := by
    simpa [prefixWord, tailWord_998659, baseEnd_998659] using wordTrace_append hprefix tailTrace_998659
  have hstable : (prefixWord ++ tailWord_998659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998659).length < 2 ^ (prefixWord ++ tailWord_998659).sum := by decide
  have hdescent : baseEnd_998659 < baseStart_998659 := by decide
  rcases family_descends (prefixWord ++ tailWord_998659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998690 : List Nat := [3, 3, 1, 1, 5, 1, 6]
def baseStart_998690 : Nat := 118140960795 + 998690 * 2 ^ 59
def prefixEnd_998690 : Nat := 4983230072969 + 3 ^ 40 * 998690 * 2
def baseEnd_998690 : Nat := 50647703193955837479715

theorem tailTrace_998690 : CollatzResearch.WordTrace tailWord_998690 prefixEnd_998690 50647703193955837479715 := by
  unfold tailWord_998690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9106304187981041879480381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24283477834616111678614349 9106304187981041879480381)
  ·
    refine ⟨3414864070492890704805143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9106304187981041879480381 3414864070492890704805143)
    ·
      refine ⟨5122296105739336057207715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3414864070492890704805143 5122296105739336057207715)
      ·
        refine ⟨7683444158609004085811573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122296105739336057207715 7683444158609004085811573)
        ·
          refine ⟨720322889869594133044835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7683444158609004085811573 720322889869594133044835)
          ·
            refine ⟨1080484334804391199567253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720322889869594133044835 1080484334804391199567253)
            ·
              refine ⟨50647703193955837479715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1080484334804391199567253 50647703193955837479715)
              ·
                rfl

theorem cell20_998690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 6].length) (baseStart_998690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998690 prefixEnd_998690 := by exact prefixLift 998690
  have htrace : WordTrace (prefixWord ++ tailWord_998690) baseStart_998690 baseEnd_998690 := by
    simpa [prefixWord, tailWord_998690, baseEnd_998690] using wordTrace_append hprefix tailTrace_998690
  have hstable : (prefixWord ++ tailWord_998690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998690).length < 2 ^ (prefixWord ++ tailWord_998690).sum := by decide
  have hdescent : baseEnd_998690 < baseStart_998690 := by decide
  rcases family_descends (prefixWord ++ tailWord_998690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998710 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_998710 : Nat := 118140960795 + 998710 * 2 ^ 59
def prefixEnd_998710 : Nat := 4983230072969 + 3 ^ 40 * 998710 * 2
def baseEnd_998710 : Nat := 455838457290571356650687

theorem tailTrace_998710 : CollatzResearch.WordTrace tailWord_998710 prefixEnd_998710 455838457290571356650687 := by
  unfold tailWord_998710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2276621638240731933353099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24283964141234473955766389 2276621638240731933353099)
  ·
    refine ⟨3414932457361097900029649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2276621638240731933353099 3414932457361097900029649)
    ·
      refine ⟨2561199343020823425022237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3414932457361097900029649 2561199343020823425022237)
      ·
        refine ⟨960449753632808784383339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2561199343020823425022237 960449753632808784383339)
        ·
          refine ⟨1440674630449213176575009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960449753632808784383339 1440674630449213176575009)
          ·
            refine ⟨1080505972836909882431257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1440674630449213176575009 1080505972836909882431257)
            ·
              refine ⟨810379479627682411823443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1080505972836909882431257 810379479627682411823443)
              ·
                refine ⟨1215569219441523617735165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810379479627682411823443 1215569219441523617735165)
                ·
                  refine ⟨455838457290571356650687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215569219441523617735165 455838457290571356650687)
                  ·
                    rfl

theorem cell20_998710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_998710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998710 prefixEnd_998710 := by exact prefixLift 998710
  have htrace : WordTrace (prefixWord ++ tailWord_998710) baseStart_998710 baseEnd_998710 := by
    simpa [prefixWord, tailWord_998710, baseEnd_998710] using wordTrace_append hprefix tailTrace_998710
  have hstable : (prefixWord ++ tailWord_998710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998710).length < 2 ^ (prefixWord ++ tailWord_998710).sum := by decide
  have hdescent : baseEnd_998710 < baseStart_998710 := by decide
  rcases family_descends (prefixWord ++ tailWord_998710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998732 : List Nat := [2, 2, 1, 3, 2, 2, 2, 6]
def baseStart_998732 : Nat := 118140960795 + 998732 * 2 ^ 59
def prefixEnd_998732 : Nat := 4983230072969 + 3 ^ 40 * 998732 * 2
def baseEnd_998732 : Nat := 151949499563345685972421

theorem tailTrace_998732 : CollatzResearch.WordTrace tailWord_998732 prefixEnd_998732 151949499563345685972421 := by
  unfold tailWord_998732
  simp only [CollatzResearch.WordTrace]
  refine ⟨18213374308886004345475225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24284499078514672460633633 18213374308886004345475225)
  ·
    refine ⟨13660030731664503259106419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18213374308886004345475225 13660030731664503259106419)
    ·
      refine ⟨20490046097496754888659629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13660030731664503259106419 20490046097496754888659629)
      ·
        refine ⟨7683767286561283083247361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20490046097496754888659629 7683767286561283083247361)
        ·
          refine ⟨5762825464920962312435521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7683767286561283083247361 5762825464920962312435521)
          ·
            refine ⟨4322119098690721734326641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5762825464920962312435521 4322119098690721734326641)
            ·
              refine ⟨3241589324018041300744981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322119098690721734326641 3241589324018041300744981)
              ·
                refine ⟨151949499563345685972421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3241589324018041300744981 151949499563345685972421)
                ·
                  rfl

theorem cell20_998732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_998732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998732 prefixEnd_998732 := by exact prefixLift 998732
  have htrace : WordTrace (prefixWord ++ tailWord_998732) baseStart_998732 baseEnd_998732 := by
    simpa [prefixWord, tailWord_998732, baseEnd_998732] using wordTrace_append hprefix tailTrace_998732
  have hstable : (prefixWord ++ tailWord_998732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998732).length < 2 ^ (prefixWord ++ tailWord_998732).sum := by decide
  have hdescent : baseEnd_998732 < baseStart_998732 := by decide
  rcases family_descends (prefixWord ++ tailWord_998732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998756 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 3]
def baseStart_998756 : Nat := 118140960795 + 998756 * 2 ^ 59
def prefixEnd_998756 : Nat := 4983230072969 + 3 ^ 40 * 998756 * 2
def baseEnd_998756 : Nat := 455859452943999641117165

theorem tailTrace_998756 : CollatzResearch.WordTrace tailWord_998756 prefixEnd_998756 455859452943999641117165 := by
  unfold tailWord_998756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18213811984842530394912061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24285082646456707193216081 18213811984842530394912061)
  ·
    refine ⟨6830179494315948898092023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18213811984842530394912061 6830179494315948898092023)
    ·
      refine ⟨10245269241473923347138035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830179494315948898092023 10245269241473923347138035)
      ·
        refine ⟨15367903862210885020707053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245269241473923347138035 15367903862210885020707053)
        ·
          refine ⟨5762963948329081882765145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15367903862210885020707053 5762963948329081882765145)
          ·
            refine ⟨4322222961246811412073859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5762963948329081882765145 4322222961246811412073859)
            ·
              refine ⟨6483334441870217118110789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322222961246811412073859 6483334441870217118110789)
              ·
                refine ⟨1215625207850665709645773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6483334441870217118110789 1215625207850665709645773)
                ·
                  refine ⟨455859452943999641117165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215625207850665709645773 455859452943999641117165)
                  ·
                    rfl

theorem cell20_998756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_998756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998756 prefixEnd_998756 := by exact prefixLift 998756
  have htrace : WordTrace (prefixWord ++ tailWord_998756) baseStart_998756 baseEnd_998756 := by
    simpa [prefixWord, tailWord_998756, baseEnd_998756] using wordTrace_append hprefix tailTrace_998756
  have hstable : (prefixWord ++ tailWord_998756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998756).length < 2 ^ (prefixWord ++ tailWord_998756).sum := by decide
  have hdescent : baseEnd_998756 < baseStart_998756 := by decide
  rcases family_descends (prefixWord ++ tailWord_998756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998759 : List Nat := [1, 1, 5, 1, 4, 1, 1, 4, 2]
def baseStart_998759 : Nat := 118140960795 + 998759 * 2 ^ 59
def prefixEnd_998759 : Nat := 4983230072969 + 3 ^ 40 * 998759 * 2
def baseEnd_998759 : Nat := 455860822225744964017153

theorem tailTrace_998759 : CollatzResearch.WordTrace tailWord_998759 prefixEnd_998759 455860822225744964017153 := by
  unfold tailWord_998759
  simp only [CollatzResearch.WordTrace]
  refine ⟨36427733388674192302183331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24285155592449461534788887 36427733388674192302183331)
  ·
    refine ⟨54641600083011288453274997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36427733388674192302183331 54641600083011288453274997)
    ·
      refine ⟨5122650007782308292494531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54641600083011288453274997 5122650007782308292494531)
      ·
        refine ⟨7683975011673462438741797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122650007782308292494531 7683975011673462438741797)
        ·
          refine ⟨1440745314688774207264087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7683975011673462438741797 1440745314688774207264087)
          ·
            refine ⟨2161117972033161310896131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440745314688774207264087 2161117972033161310896131)
            ·
              refine ⟨3241676958049741966344197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161117972033161310896131 3241676958049741966344197)
              ·
                refine ⟨607814429634326618689537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3241676958049741966344197 607814429634326618689537)
                ·
                  refine ⟨455860822225744964017153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607814429634326618689537 455860822225744964017153)
                  ·
                    rfl

theorem cell20_998759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 2].length) (baseStart_998759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998759 prefixEnd_998759 := by exact prefixLift 998759
  have htrace : WordTrace (prefixWord ++ tailWord_998759) baseStart_998759 baseEnd_998759 := by
    simpa [prefixWord, tailWord_998759, baseEnd_998759] using wordTrace_append hprefix tailTrace_998759
  have hstable : (prefixWord ++ tailWord_998759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998759).length < 2 ^ (prefixWord ++ tailWord_998759).sum := by decide
  have hdescent : baseEnd_998759 < baseStart_998759 := by decide
  rcases family_descends (prefixWord ++ tailWord_998759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998787 : List Nat := [1, 1, 1, 3, 5, 2, 3, 4]
def baseStart_998787 : Nat := 118140960795 + 998787 * 2 ^ 59
def prefixEnd_998787 : Nat := 4983230072969 + 3 ^ 40 * 998787 * 2
def baseEnd_998787 : Nat := 151957867396233770361235

theorem tailTrace_998787 : CollatzResearch.WordTrace tailWord_998787 prefixEnd_998787 151957867396233770361235 := by
  unfold tailWord_998787
  simp only [CollatzResearch.WordTrace]
  refine ⟨36428754632572753084202615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24285836421715168722801743 36428754632572753084202615)
  ·
    refine ⟨54643131948859129626303923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36428754632572753084202615 54643131948859129626303923)
    ·
      refine ⟨81964697923288694439455885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54643131948859129626303923 81964697923288694439455885)
      ·
        refine ⟨30736761721233260414795957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81964697923288694439455885 30736761721233260414795957)
        ·
          refine ⟨2881571411365618163887121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30736761721233260414795957 2881571411365618163887121)
          ·
            refine ⟨2161178558524213622915341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2881571411365618163887121 2161178558524213622915341)
            ·
              refine ⟨810441959446580108593253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2161178558524213622915341 810441959446580108593253)
              ·
                refine ⟨151957867396233770361235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 810441959446580108593253 151957867396233770361235)
                ·
                  rfl

theorem cell20_998787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 4].length) (baseStart_998787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998787 prefixEnd_998787 := by exact prefixLift 998787
  have htrace : WordTrace (prefixWord ++ tailWord_998787) baseStart_998787 baseEnd_998787 := by
    simpa [prefixWord, tailWord_998787, baseEnd_998787] using wordTrace_append hprefix tailTrace_998787
  have hstable : (prefixWord ++ tailWord_998787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998787).length < 2 ^ (prefixWord ++ tailWord_998787).sum := by decide
  have hdescent : baseEnd_998787 < baseStart_998787 := by decide
  rcases family_descends (prefixWord ++ tailWord_998787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998818 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_998818 : Nat := 118140960795 + 998818 * 2 ^ 59
def prefixEnd_998818 : Nat := 4983230072969 + 3 ^ 40 * 998818 * 2
def baseEnd_998818 : Nat := 455887751433402981050245

theorem tailTrace_998818 : CollatzResearch.WordTrace tailWord_998818 prefixEnd_998818 455887751433402981050245 := by
  unfold tailWord_998818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9107471323865111344645277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24286590196973630252387405 9107471323865111344645277)
  ·
    refine ⟨3415301746449416754241979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9107471323865111344645277 3415301746449416754241979)
    ·
      refine ⟨5122952619674125131362969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3415301746449416754241979 5122952619674125131362969)
      ·
        refine ⟨3842214464755593848522227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5122952619674125131362969 3842214464755593848522227)
        ·
          refine ⟨5763321697133390772783341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842214464755593848522227 5763321697133390772783341)
          ·
            refine ⟨2161245636425021539793753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5763321697133390772783341 2161245636425021539793753)
            ·
              refine ⟨1620934227318766154845315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161245636425021539793753 1620934227318766154845315)
              ·
                refine ⟨2431401340978149232267973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620934227318766154845315 2431401340978149232267973)
                ·
                  refine ⟨455887751433402981050245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431401340978149232267973 455887751433402981050245)
                  ·
                    rfl

theorem cell20_998818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_998818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998818 prefixEnd_998818 := by exact prefixLift 998818
  have htrace : WordTrace (prefixWord ++ tailWord_998818) baseStart_998818 baseEnd_998818 := by
    simpa [prefixWord, tailWord_998818, baseEnd_998818] using wordTrace_append hprefix tailTrace_998818
  have hstable : (prefixWord ++ tailWord_998818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998818).length < 2 ^ (prefixWord ++ tailWord_998818).sum := by decide
  have hdescent : baseEnd_998818 < baseStart_998818 := by decide
  rcases family_descends (prefixWord ++ tailWord_998818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998852 : List Nat := [2, 3, 3, 2, 1, 3, 1, 3, 2]
def baseStart_998852 : Nat := 118140960795 + 998852 * 2 ^ 59
def prefixEnd_998852 : Nat := 4983230072969 + 3 ^ 40 * 998852 * 2
def baseEnd_998852 : Nat := 455903269959849973916773

theorem tailTrace_998852 : CollatzResearch.WordTrace tailWord_998852 prefixEnd_998852 455903269959849973916773 := by
  unfold tailWord_998852
  simp only [CollatzResearch.WordTrace]
  refine ⟨18215562688668634592659405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24287416918224846123545873 18215562688668634592659405)
  ·
    refine ⟨6830836008250737972247277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18215562688668634592659405 6830836008250737972247277)
    ·
      refine ⟨2561563503094026739592729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6830836008250737972247277 2561563503094026739592729)
      ·
        refine ⟨1921172627320520054694547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2561563503094026739592729 1921172627320520054694547)
        ·
          refine ⟨2881758940980780082041821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921172627320520054694547 2881758940980780082041821)
          ·
            refine ⟨1080659602867792530765683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2881758940980780082041821 1080659602867792530765683)
            ·
              refine ⟨1620989404301688796148525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080659602867792530765683 1620989404301688796148525)
              ·
                refine ⟨607871026613133298555697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1620989404301688796148525 607871026613133298555697)
                ·
                  refine ⟨455903269959849973916773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607871026613133298555697 455903269959849973916773)
                  ·
                    rfl

theorem cell20_998852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_998852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998852 prefixEnd_998852 := by exact prefixLift 998852
  have htrace : WordTrace (prefixWord ++ tailWord_998852) baseStart_998852 baseEnd_998852 := by
    simpa [prefixWord, tailWord_998852, baseEnd_998852] using wordTrace_append hprefix tailTrace_998852
  have hstable : (prefixWord ++ tailWord_998852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998852).length < 2 ^ (prefixWord ++ tailWord_998852).sum := by decide
  have hdescent : baseEnd_998852 < baseStart_998852 := by decide
  rcases family_descends (prefixWord ++ tailWord_998852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998873 : List Nat := [1, 2, 1, 2, 4, 3, 3, 2, 2]
def baseStart_998873 : Nat := 118140960795 + 998873 * 2 ^ 59
def prefixEnd_998873 : Nat := 4983230072969 + 3 ^ 40 * 998873 * 2
def baseEnd_998873 : Nat := 455912854932067234216687

theorem tailTrace_998873 : CollatzResearch.WordTrace tailWord_998873 prefixEnd_998873 455912854932067234216687 := by
  unfold tailWord_998873
  simp only [CollatzResearch.WordTrace]
  refine ⟨36431891310261189771833273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24287927540174126514555515 36431891310261189771833273)
  ·
    refine ⟨27323918482695892328874955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36431891310261189771833273 27323918482695892328874955)
    ·
      refine ⟨40985877724043838493312433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27323918482695892328874955 40985877724043838493312433)
      ·
        refine ⟨30739408293032878869984325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40985877724043838493312433 30739408293032878869984325)
        ·
          refine ⟨5763639054943664788122061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30739408293032878869984325 5763639054943664788122061)
          ·
            refine ⟨2161364645603874295545773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5763639054943664788122061 2161364645603874295545773)
            ·
              refine ⟨810511742101452860829665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2161364645603874295545773 810511742101452860829665)
              ·
                refine ⟨607883806576089645622249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810511742101452860829665 607883806576089645622249)
                ·
                  refine ⟨455912854932067234216687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607883806576089645622249 455912854932067234216687)
                  ·
                    rfl

theorem cell20_998873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_998873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998873 prefixEnd_998873 := by exact prefixLift 998873
  have htrace : WordTrace (prefixWord ++ tailWord_998873) baseStart_998873 baseEnd_998873 := by
    simpa [prefixWord, tailWord_998873, baseEnd_998873] using wordTrace_append hprefix tailTrace_998873
  have hstable : (prefixWord ++ tailWord_998873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998873).length < 2 ^ (prefixWord ++ tailWord_998873).sum := by decide
  have hdescent : baseEnd_998873 < baseStart_998873 := by decide
  rcases family_descends (prefixWord ++ tailWord_998873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998887 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 3]
def baseStart_998887 : Nat := 118140960795 + 998887 * 2 ^ 59
def prefixEnd_998887 : Nat := 4983230072969 + 3 ^ 40 * 998887 * 2
def baseEnd_998887 : Nat := 455919244913545407749963

theorem tailTrace_998887 : CollatzResearch.WordTrace tailWord_998887 prefixEnd_998887 455919244913545407749963 := by
  unfold tailWord_998887
  simp only [CollatzResearch.WordTrace]
  refine ⟨36432401932210470162842915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24288267954806980108561943 36432401932210470162842915)
  ·
    refine ⟨54648602898315705244264373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36432401932210470162842915 54648602898315705244264373)
    ·
      refine ⟨5123306521717097366649785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54648602898315705244264373 5123306521717097366649785)
      ·
        refine ⟨3842479891287823024987339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5123306521717097366649785 3842479891287823024987339)
        ·
          refine ⟨5763719836931734537481009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842479891287823024987339 5763719836931734537481009)
          ·
            refine ⟨4322789877698800903110757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5763719836931734537481009 4322789877698800903110757)
            ·
              refine ⟨810523102068525169333267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4322789877698800903110757 810523102068525169333267)
              ·
                refine ⟨1215784653102787753999901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810523102068525169333267 1215784653102787753999901)
                ·
                  refine ⟨455919244913545407749963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215784653102787753999901 455919244913545407749963)
                  ·
                    rfl

theorem cell20_998887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 3].length) (baseStart_998887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998887 prefixEnd_998887 := by exact prefixLift 998887
  have htrace : WordTrace (prefixWord ++ tailWord_998887) baseStart_998887 baseEnd_998887 := by
    simpa [prefixWord, tailWord_998887, baseEnd_998887] using wordTrace_append hprefix tailTrace_998887
  have hstable : (prefixWord ++ tailWord_998887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998887).length < 2 ^ (prefixWord ++ tailWord_998887).sum := by decide
  have hdescent : baseEnd_998887 < baseStart_998887 := by decide
  rcases family_descends (prefixWord ++ tailWord_998887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998901 : List Nat := [1, 3, 5, 1, 1, 1, 2, 6]
def baseStart_998901 : Nat := 118140960795 + 998901 * 2 ^ 59
def prefixEnd_998901 : Nat := 4983230072969 + 3 ^ 40 * 998901 * 2
def baseEnd_998901 : Nat := 151975211631674527094413

theorem tailTrace_998901 : CollatzResearch.WordTrace tailWord_998901 prefixEnd_998901 151975211631674527094413 := by
  unfold tailWord_998901
  simp only [CollatzResearch.WordTrace]
  refine ⟨36432912554159750553852557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24288608369439833702568371 36432912554159750553852557)
  ·
    refine ⟨13662342207809906457694709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36432912554159750553852557 13662342207809906457694709)
    ·
      refine ⟨1280844581982178730408879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13662342207809906457694709 1280844581982178730408879)
      ·
        refine ⟨1921266872973268095613319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1280844581982178730408879 1921266872973268095613319)
        ·
          refine ⟨2881900309459902143419979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921266872973268095613319 2881900309459902143419979)
          ·
            refine ⟨4322850464189853215129969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881900309459902143419979 4322850464189853215129969)
            ·
              refine ⟨3242137848142389911347477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322850464189853215129969 3242137848142389911347477)
              ·
                refine ⟨151975211631674527094413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3242137848142389911347477 151975211631674527094413)
                ·
                  rfl

theorem cell20_998901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 6].length) (baseStart_998901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998901 prefixEnd_998901 := by exact prefixLift 998901
  have htrace : WordTrace (prefixWord ++ tailWord_998901) baseStart_998901 baseEnd_998901 := by
    simpa [prefixWord, tailWord_998901, baseEnd_998901] using wordTrace_append hprefix tailTrace_998901
  have hstable : (prefixWord ++ tailWord_998901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998901).length < 2 ^ (prefixWord ++ tailWord_998901).sum := by decide
  have hdescent : baseEnd_998901 < baseStart_998901 := by decide
  rcases family_descends (prefixWord ++ tailWord_998901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998918 : List Nat := [6, 2, 1, 1, 10]
def baseStart_998918 : Nat := 118140960795 + 998918 * 2 ^ 59
def prefixEnd_998918 : Nat := 4983230072969 + 3 ^ 40 * 998918 * 2
def baseEnd_998918 : Nat := 5628807335287000959463

theorem tailTrace_998918 : CollatzResearch.WordTrace tailWord_998918 prefixEnd_998918 5628807335287000959463 := by
  unfold tailWord_998918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138547893596817576788169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24289021730065441638147605 1138547893596817576788169)
  ·
    refine ⟨853910920197613182591127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1138547893596817576788169 853910920197613182591127)
    ·
      refine ⟨1280866380296419773886691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 853910920197613182591127 1280866380296419773886691)
      ·
        refine ⟨1921299570444629660830037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1280866380296419773886691 1921299570444629660830037)
        ·
          refine ⟨5628807335287000959463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1921299570444629660830037 5628807335287000959463)
          ·
            rfl

theorem cell20_998918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 10].length) (baseStart_998918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998918 prefixEnd_998918 := by exact prefixLift 998918
  have htrace : WordTrace (prefixWord ++ tailWord_998918) baseStart_998918 baseEnd_998918 := by
    simpa [prefixWord, tailWord_998918, baseEnd_998918] using wordTrace_append hprefix tailTrace_998918
  have hstable : (prefixWord ++ tailWord_998918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998918).length < 2 ^ (prefixWord ++ tailWord_998918).sum := by decide
  have hdescent : baseEnd_998918 < baseStart_998918 := by decide
  rcases family_descends (prefixWord ++ tailWord_998918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998946 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_998946 : Nat := 118140960795 + 998946 * 2 ^ 59
def prefixEnd_998946 : Nat := 4983230072969 + 3 ^ 40 * 998946 * 2
def baseEnd_998946 : Nat := 455946174121203424783055

theorem tailTrace_998946 : CollatzResearch.WordTrace tailWord_998946 prefixEnd_998946 455946174121203424783055 := by
  unfold tailWord_998946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9108638459749180809810173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24289702559331148826160461 9108638459749180809810173)
  ·
    refine ⟨3415739422405942803678815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9108638459749180809810173 3415739422405942803678815)
    ·
      refine ⟨5123609133608914205518223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3415739422405942803678815 5123609133608914205518223)
      ·
        refine ⟨7685413700413371308277335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5123609133608914205518223 7685413700413371308277335)
        ·
          refine ⟨11528120550620056962416003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7685413700413371308277335 11528120550620056962416003)
          ·
            refine ⟨17292180825930085443624005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11528120550620056962416003 17292180825930085443624005)
            ·
              refine ⟨3242283904861891020679501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17292180825930085443624005 3242283904861891020679501)
              ·
                refine ⟨1215856464323209132754813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3242283904861891020679501 1215856464323209132754813)
                ·
                  refine ⟨455946174121203424783055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215856464323209132754813 455946174121203424783055)
                  ·
                    rfl

theorem cell20_998946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_998946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998946 prefixEnd_998946 := by exact prefixLift 998946
  have htrace : WordTrace (prefixWord ++ tailWord_998946) baseStart_998946 baseEnd_998946 := by
    simpa [prefixWord, tailWord_998946, baseEnd_998946] using wordTrace_append hprefix tailTrace_998946
  have hstable : (prefixWord ++ tailWord_998946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998946).length < 2 ^ (prefixWord ++ tailWord_998946).sum := by decide
  have hdescent : baseEnd_998946 < baseStart_998946 := by decide
  rcases family_descends (prefixWord ++ tailWord_998946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998966 : List Nat := [5, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_998966 : Nat := 118140960795 + 998966 * 2 ^ 59
def prefixEnd_998966 : Nat := 4983230072969 + 3 ^ 40 * 998966 * 2
def baseEnd_998966 : Nat := 455955302666172244116307

theorem tailTrace_998966 : CollatzResearch.WordTrace tailWord_998966 prefixEnd_998966 455955302666172244116307 := by
  unfold tailWord_998966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277205206182766665935547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24290188865949511103312501 2277205206182766665935547)
  ·
    refine ⟨3415807809274149998903321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2277205206182766665935547 3415807809274149998903321)
    ·
      refine ⟨2561855856955612499177491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3415807809274149998903321 2561855856955612499177491)
      ·
        refine ⟨3842783785433418748766237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561855856955612499177491 3842783785433418748766237)
        ·
          refine ⟨1441043919537532030787339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3842783785433418748766237 1441043919537532030787339)
          ·
            refine ⟨2161565879306298046181009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441043919537532030787339 2161565879306298046181009)
            ·
              refine ⟨1621174409479723534635757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161565879306298046181009 1621174409479723534635757)
              ·
                refine ⟨607940403554896325488409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1621174409479723534635757 607940403554896325488409)
                ·
                  refine ⟨455955302666172244116307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607940403554896325488409 455955302666172244116307)
                  ·
                    rfl

theorem cell20_998966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_998966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998966 prefixEnd_998966 := by exact prefixLift 998966
  have htrace : WordTrace (prefixWord ++ tailWord_998966) baseStart_998966 baseEnd_998966 := by
    simpa [prefixWord, tailWord_998966, baseEnd_998966] using wordTrace_append hprefix tailTrace_998966
  have hstable : (prefixWord ++ tailWord_998966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998966).length < 2 ^ (prefixWord ++ tailWord_998966).sum := by decide
  have hdescent : baseEnd_998966 < baseStart_998966 := by decide
  rcases family_descends (prefixWord ++ tailWord_998966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998970 : List Nat := [3, 1, 1, 1, 3, 2, 4, 3, 2]
def baseStart_998970 : Nat := 118140960795 + 998970 * 2 ^ 59
def prefixEnd_998970 : Nat := 4983230072969 + 3 ^ 40 * 998970 * 2
def baseEnd_998970 : Nat := 455957128375166007982957

theorem tailTrace_998970 : CollatzResearch.WordTrace tailWord_998970 prefixEnd_998970 455957128375166007982957 := by
  unfold tailWord_998970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9108857297727443834528591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24290286127273183558742909 9108857297727443834528591)
  ·
    refine ⟨13663285946591165751792887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9108857297727443834528591 13663285946591165751792887)
    ·
      refine ⟨20494928919886748627689331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13663285946591165751792887 20494928919886748627689331)
      ·
        refine ⟨30742393379830122941533997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20494928919886748627689331 30742393379830122941533997)
        ·
          refine ⟨11528397517436296103075249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30742393379830122941533997 11528397517436296103075249)
          ·
            refine ⟨8646298138077222077306437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11528397517436296103075249 8646298138077222077306437)
            ·
              refine ⟨1621180900889479139494957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8646298138077222077306437 1621180900889479139494957)
              ·
                refine ⟨607942837833554677310609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1621180900889479139494957 607942837833554677310609)
                ·
                  refine ⟨455957128375166007982957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607942837833554677310609 455957128375166007982957)
                  ·
                    rfl

theorem cell20_998970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_998970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998970 prefixEnd_998970 := by exact prefixLift 998970
  have htrace : WordTrace (prefixWord ++ tailWord_998970) baseStart_998970 baseEnd_998970 := by
    simpa [prefixWord, tailWord_998970, baseEnd_998970] using wordTrace_append hprefix tailTrace_998970
  have hstable : (prefixWord ++ tailWord_998970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998970).length < 2 ^ (prefixWord ++ tailWord_998970).sum := by decide
  have hdescent : baseEnd_998970 < baseStart_998970 := by decide
  rcases family_descends (prefixWord ++ tailWord_998970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998981 : List Nat := [1, 3, 1, 1, 1, 4, 9]
def baseStart_998981 : Nat := 118140960795 + 998981 * 2 ^ 59
def prefixEnd_998981 : Nat := 4983230072969 + 3 ^ 40 * 998981 * 2
def baseEnd_998981 : Nat := 50662461008322095401805

theorem tailTrace_998981 : CollatzResearch.WordTrace tailWord_998981 prefixEnd_998981 50662461008322095401805 := by
  unfold tailWord_998981
  simp only [CollatzResearch.WordTrace]
  refine ⟨36435830393869924216764797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24290553595913282811176531 36435830393869924216764797)
  ·
    refine ⟨13663436397701221581286799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36435830393869924216764797 13663436397701221581286799)
    ·
      refine ⟨20495154596551832371930199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13663436397701221581286799 20495154596551832371930199)
      ·
        refine ⟨30742731894827748557895299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20495154596551832371930199 30742731894827748557895299)
        ·
          refine ⟨46114097842241622836842949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30742731894827748557895299 46114097842241622836842949)
          ·
            refine ⟨8646393345420304281908053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46114097842241622836842949 8646393345420304281908053)
            ·
              refine ⟨50662461008322095401805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8646393345420304281908053 50662461008322095401805)
              ·
                rfl

theorem cell20_998981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 9].length) (baseStart_998981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_998981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_998981 prefixEnd_998981 := by exact prefixLift 998981
  have htrace : WordTrace (prefixWord ++ tailWord_998981) baseStart_998981 baseEnd_998981 := by
    simpa [prefixWord, tailWord_998981, baseEnd_998981] using wordTrace_append hprefix tailTrace_998981
  have hstable : (prefixWord ++ tailWord_998981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998981).length < 2 ^ (prefixWord ++ tailWord_998981).sum := by decide
  have hdescent : baseEnd_998981 < baseStart_998981 := by decide
  rcases family_descends (prefixWord ++ tailWord_998981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999043 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 3]
def baseStart_999043 : Nat := 118140960795 + 999043 * 2 ^ 59
def prefixEnd_999043 : Nat := 4983230072969 + 3 ^ 40 * 999043 * 2
def baseEnd_999043 : Nat := 455990447564302198549325

theorem tailTrace_999043 : CollatzResearch.WordTrace tailWord_999043 prefixEnd_999043 455990447564302198549325 := by
  unfold tailWord_999043
  simp only [CollatzResearch.WordTrace]
  refine ⟨36438091719645308805521783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24292061146430205870347855 36438091719645308805521783)
  ·
    refine ⟨54657137579467963208282675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36438091719645308805521783 54657137579467963208282675)
    ·
      refine ⟨81985706369201944812424013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54657137579467963208282675 81985706369201944812424013)
      ·
        refine ⟨30744639888450729304659005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81985706369201944812424013 30744639888450729304659005)
        ·
          refine ⟨11529239958169023489247127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30744639888450729304659005 11529239958169023489247127)
          ·
            refine ⟨17293859937253535233870691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529239958169023489247127 17293859937253535233870691)
            ·
              refine ⟨25940789905880302850806037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17293859937253535233870691 25940789905880302850806037)
              ·
                refine ⟨1215974526838139196131533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25940789905880302850806037 1215974526838139196131533)
                ·
                  refine ⟨455990447564302198549325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215974526838139196131533 455990447564302198549325)
                  ·
                    rfl

theorem cell20_999043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 3].length) (baseStart_999043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999043 prefixEnd_999043 := by exact prefixLift 999043
  have htrace : WordTrace (prefixWord ++ tailWord_999043) baseStart_999043 baseEnd_999043 := by
    simpa [prefixWord, tailWord_999043, baseEnd_999043] using wordTrace_append hprefix tailTrace_999043
  have hstable : (prefixWord ++ tailWord_999043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999043).length < 2 ^ (prefixWord ++ tailWord_999043).sum := by decide
  have hdescent : baseEnd_999043 < baseStart_999043 := by decide
  rcases family_descends (prefixWord ++ tailWord_999043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999094 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_999094 : Nat := 118140960795 + 999094 * 2 ^ 59
def prefixEnd_999094 : Nat := 4983230072969 + 3 ^ 40 * 999094 * 2
def baseEnd_999094 : Nat := 456013725353972687849117

theorem tailTrace_999094 : CollatzResearch.WordTrace tailWord_999094 prefixEnd_999094 456013725353972687849117 := by
  unfold tailWord_999094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277496990153784032226771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24293301228307029677085557 2277496990153784032226771)
  ·
    refine ⟨3416245485230676048340157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2277496990153784032226771 3416245485230676048340157)
    ·
      refine ⟨1281092056961503518127559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3416245485230676048340157 1281092056961503518127559)
      ·
        refine ⟨1921638085442255277191339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281092056961503518127559 1921638085442255277191339)
        ·
          refine ⟨2882457128163382915787009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921638085442255277191339 2882457128163382915787009)
          ·
            refine ⟨2161842846122537186840257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2882457128163382915787009 2161842846122537186840257)
            ·
              refine ⟨1621382134591902890130193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161842846122537186840257 1621382134591902890130193)
              ·
                refine ⟨1216036600943927167597645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1621382134591902890130193 1216036600943927167597645)
                ·
                  refine ⟨456013725353972687849117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216036600943927167597645 456013725353972687849117)
                  ·
                    rfl

theorem cell20_999094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_999094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999094 prefixEnd_999094 := by exact prefixLift 999094
  have htrace : WordTrace (prefixWord ++ tailWord_999094) baseStart_999094 baseEnd_999094 := by
    simpa [prefixWord, tailWord_999094, baseEnd_999094] using wordTrace_append hprefix tailTrace_999094
  have hstable : (prefixWord ++ tailWord_999094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999094).length < 2 ^ (prefixWord ++ tailWord_999094).sum := by decide
  have hdescent : baseEnd_999094 < baseStart_999094 := by decide
  rcases family_descends (prefixWord ++ tailWord_999094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999095 : List Nat := [1, 1, 3, 1, 5, 9]
def baseStart_999095 : Nat := 118140960795 + 999095 * 2 ^ 59
def prefixEnd_999095 : Nat := 4983230072969 + 3 ^ 40 * 999095 * 2
def baseEnd_999095 : Nat := 16889414140045226993177

theorem tailTrace_999095 : CollatzResearch.WordTrace tailWord_999095 prefixEnd_999095 16889414140045226993177 := by
  unfold tailWord_999095
  simp only [CollatzResearch.WordTrace]
  refine ⟨36439988315456921686414739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24293325543637947790943159 36439988315456921686414739)
  ·
    refine ⟨54659982473185382529622109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36439988315456921686414739 54659982473185382529622109)
    ·
      refine ⟨20497493427444518448608291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54659982473185382529622109 20497493427444518448608291)
      ·
        refine ⟨30746240141166777672912437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20497493427444518448608291 30746240141166777672912437)
        ·
          refine ⟨2882460013234385406835541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30746240141166777672912437 2882460013234385406835541)
          ·
            refine ⟨16889414140045226993177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2882460013234385406835541 16889414140045226993177)
            ·
              rfl

theorem cell20_999095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 9].length) (baseStart_999095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999095 prefixEnd_999095 := by exact prefixLift 999095
  have htrace : WordTrace (prefixWord ++ tailWord_999095) baseStart_999095 baseEnd_999095 := by
    simpa [prefixWord, tailWord_999095, baseEnd_999095] using wordTrace_append hprefix tailTrace_999095
  have hstable : (prefixWord ++ tailWord_999095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999095).length < 2 ^ (prefixWord ++ tailWord_999095).sum := by decide
  have hdescent : baseEnd_999095 < baseStart_999095 := by decide
  rcases family_descends (prefixWord ++ tailWord_999095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999098 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_999098 : Nat := 118140960795 + 999098 * 2 ^ 59
def prefixEnd_999098 : Nat := 4983230072969 + 3 ^ 40 * 999098 * 2
def baseEnd_999098 : Nat := 456015551062966451715767

theorem tailTrace_999098 : CollatzResearch.WordTrace tailWord_999098 prefixEnd_999098 456015551062966451715767 := by
  unfold tailWord_999098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110024433611513299693487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24293398489630702132515965 9110024433611513299693487)
  ·
    refine ⟨13665036650417269949540231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9110024433611513299693487 13665036650417269949540231)
    ·
      refine ⟨20497554975625904924310347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13665036650417269949540231 20497554975625904924310347)
      ·
        refine ⟨30746332463438857386465521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20497554975625904924310347 30746332463438857386465521)
        ·
          refine ⟨23059749347579143039849141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30746332463438857386465521 23059749347579143039849141)
          ·
            refine ⟨2161851501335544659985857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23059749347579143039849141 2161851501335544659985857)
            ·
              refine ⟨1621388626001658494989393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161851501335544659985857 1621388626001658494989393)
              ·
                refine ⟨1216041469501243871242045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1621388626001658494989393 1216041469501243871242045)
                ·
                  refine ⟨456015551062966451715767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216041469501243871242045 456015551062966451715767)
                  ·
                    rfl

theorem cell20_999098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_999098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999098 prefixEnd_999098 := by exact prefixLift 999098
  have htrace : WordTrace (prefixWord ++ tailWord_999098) baseStart_999098 baseEnd_999098 := by
    simpa [prefixWord, tailWord_999098, baseEnd_999098] using wordTrace_append hprefix tailTrace_999098
  have hstable : (prefixWord ++ tailWord_999098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999098).length < 2 ^ (prefixWord ++ tailWord_999098).sum := by decide
  have hdescent : baseEnd_999098 < baseStart_999098 := by decide
  rcases family_descends (prefixWord ++ tailWord_999098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999139 : List Nat := [1, 1, 1, 7, 2, 1, 2, 3, 2]
def baseStart_999139 : Nat := 118140960795 + 999139 * 2 ^ 59
def prefixEnd_999139 : Nat := 4983230072969 + 3 ^ 40 * 999139 * 2
def baseEnd_999139 : Nat := 456034264580152531348933

theorem tailTrace_999139 : CollatzResearch.WordTrace tailWord_999139 prefixEnd_999139 456034264580152531348933 := by
  unfold tailWord_999139
  simp only [CollatzResearch.WordTrace]
  refine ⟨36441593127297517201016471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24294395418198344800677647 36441593127297517201016471)
  ·
    refine ⟨54662389690946275801524707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36441593127297517201016471 54662389690946275801524707)
    ·
      refine ⟨81993584536419413702287061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54662389690946275801524707 81993584536419413702287061)
      ·
        refine ⟨1921724637572330008647353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 81993584536419413702287061 1921724637572330008647353)
        ·
          refine ⟨1441293478179247506485515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1921724637572330008647353 1441293478179247506485515)
          ·
            refine ⟨2161940217268871259728273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441293478179247506485515 2161940217268871259728273)
            ·
              refine ⟨1621455162951653444796205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161940217268871259728273 1621455162951653444796205)
              ·
                refine ⟨608045686106870041798577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1621455162951653444796205 608045686106870041798577)
                ·
                  refine ⟨456034264580152531348933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608045686106870041798577 456034264580152531348933)
                  ·
                    rfl

theorem cell20_999139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 2].length) (baseStart_999139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999139 prefixEnd_999139 := by exact prefixLift 999139
  have htrace : WordTrace (prefixWord ++ tailWord_999139) baseStart_999139 baseEnd_999139 := by
    simpa [prefixWord, tailWord_999139, baseEnd_999139] using wordTrace_append hprefix tailTrace_999139
  have hstable : (prefixWord ++ tailWord_999139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999139).length < 2 ^ (prefixWord ++ tailWord_999139).sum := by decide
  have hdescent : baseEnd_999139 < baseStart_999139 := by decide
  rcases family_descends (prefixWord ++ tailWord_999139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999156 : List Nat := [2, 6, 1, 1, 1, 1, 2, 4, 2]
def baseStart_999156 : Nat := 118140960795 + 999156 * 2 ^ 59
def prefixEnd_999156 : Nat := 4983230072969 + 3 ^ 40 * 999156 * 2
def baseEnd_999156 : Nat := 456042023843376027782197

theorem tailTrace_999156 : CollatzResearch.WordTrace tailWord_999156 prefixEnd_999156 456042023843376027782197 := by
  unfold tailWord_999156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18221106584117964552192661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24294808778823952736256881 18221106584117964552192661)
  ·
    refine ⟨854114371130529588384031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18221106584117964552192661 854114371130529588384031)
    ·
      refine ⟨1281171556695794382576047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854114371130529588384031 1281171556695794382576047)
      ·
        refine ⟨1921757335043691573864071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281171556695794382576047 1921757335043691573864071)
        ·
          refine ⟨2882636002565537360796107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921757335043691573864071 2882636002565537360796107)
          ·
            refine ⟨4323954003848306041194161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882636002565537360796107 4323954003848306041194161)
            ·
              refine ⟨3242965502886229530895621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4323954003848306041194161 3242965502886229530895621)
              ·
                refine ⟨608056031791168037042929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3242965502886229530895621 608056031791168037042929)
                ·
                  refine ⟨456042023843376027782197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608056031791168037042929 456042023843376027782197)
                  ·
                    rfl

theorem cell20_999156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_999156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999156 prefixEnd_999156 := by exact prefixLift 999156
  have htrace : WordTrace (prefixWord ++ tailWord_999156) baseStart_999156 baseEnd_999156 := by
    simpa [prefixWord, tailWord_999156, baseEnd_999156] using wordTrace_append hprefix tailTrace_999156
  have hstable : (prefixWord ++ tailWord_999156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999156).length < 2 ^ (prefixWord ++ tailWord_999156).sum := by decide
  have hdescent : baseEnd_999156 < baseStart_999156 := by decide
  rcases family_descends (prefixWord ++ tailWord_999156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999225 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 3]
def baseStart_999225 : Nat := 118140960795 + 999225 * 2 ^ 59
def prefixEnd_999225 : Nat := 4983230072969 + 3 ^ 40 * 999225 * 2
def baseEnd_999225 : Nat := 456073517323518454481915

theorem tailTrace_999225 : CollatzResearch.WordTrace tailWord_999225 prefixEnd_999225 456073517323518454481915 := by
  unfold tailWord_999225
  simp only [CollatzResearch.WordTrace]
  refine ⟨36444729804985953888647129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24296486536657302592431419 36444729804985953888647129)
  ·
    refine ⟨27333547353739465416485347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36444729804985953888647129 27333547353739465416485347)
    ·
      refine ⟨41000321030609198124728021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27333547353739465416485347 41000321030609198124728021)
      ·
        refine ⟨960945024154903081048313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41000321030609198124728021 960945024154903081048313)
        ·
          refine ⟨720708768116177310786235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 960945024154903081048313 720708768116177310786235)
          ·
            refine ⟨1081063152174265966179353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720708768116177310786235 1081063152174265966179353)
            ·
              refine ⟨810797364130699474634515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081063152174265966179353 810797364130699474634515)
              ·
                refine ⟨1216196046196049211951773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810797364130699474634515 1216196046196049211951773)
                ·
                  refine ⟨456073517323518454481915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216196046196049211951773 456073517323518454481915)
                  ·
                    rfl

theorem cell20_999225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_999225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999225 prefixEnd_999225 := by exact prefixLift 999225
  have htrace : WordTrace (prefixWord ++ tailWord_999225) baseStart_999225 baseEnd_999225 := by
    simpa [prefixWord, tailWord_999225, baseEnd_999225] using wordTrace_append hprefix tailTrace_999225
  have hstable : (prefixWord ++ tailWord_999225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999225).length < 2 ^ (prefixWord ++ tailWord_999225).sum := by decide
  have hdescent : baseEnd_999225 < baseStart_999225 := by decide
  rcases family_descends (prefixWord ++ tailWord_999225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999226 : List Nat := [3, 1, 1, 1, 5, 2, 2, 5]
def baseStart_999226 : Nat := 118140960795 + 999226 * 2 ^ 59
def prefixEnd_999226 : Nat := 4983230072969 + 3 ^ 40 * 999226 * 2
def baseEnd_999226 : Nat := 152024657916922298482859

theorem tailTrace_999226 : CollatzResearch.WordTrace tailWord_999226 prefixEnd_999226 152024657916922298482859 := by
  unfold tailWord_999226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9111191569495582764858383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24296510851988220706289021 9111191569495582764858383)
  ·
    refine ⟨13666787354243374147287575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9111191569495582764858383 13666787354243374147287575)
    ·
      refine ⟨20500181031365061220931363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13666787354243374147287575 20500181031365061220931363)
      ·
        refine ⟨30750271547047591831397045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20500181031365061220931363 30750271547047591831397045)
        ·
          refine ⟨2882837957535711734193473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30750271547047591831397045 2882837957535711734193473)
          ·
            refine ⟨2162128468151783800645105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2882837957535711734193473 2162128468151783800645105)
            ·
              refine ⟨1621596351113837850483829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2162128468151783800645105 1621596351113837850483829)
              ·
                refine ⟨152024657916922298482859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1621596351113837850483829 152024657916922298482859)
                ·
                  rfl

theorem cell20_999226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_999226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999226 prefixEnd_999226 := by exact prefixLift 999226
  have htrace : WordTrace (prefixWord ++ tailWord_999226) baseStart_999226 baseEnd_999226 := by
    simpa [prefixWord, tailWord_999226, baseEnd_999226] using wordTrace_append hprefix tailTrace_999226
  have hstable : (prefixWord ++ tailWord_999226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999226).length < 2 ^ (prefixWord ++ tailWord_999226).sum := by decide
  have hdescent : baseEnd_999226 < baseStart_999226 := by decide
  rcases family_descends (prefixWord ++ tailWord_999226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999229 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 3]
def baseStart_999229 : Nat := 118140960795 + 999229 * 2 ^ 59
def prefixEnd_999229 : Nat := 4983230072969 + 3 ^ 40 * 999229 * 2
def baseEnd_999229 : Nat := 456075343032512218348565

theorem tailTrace_999229 : CollatzResearch.WordTrace tailWord_999229 prefixEnd_999229 456075343032512218348565 := by
  unfold tailWord_999229
  simp only [CollatzResearch.WordTrace]
  refine ⟨36444875696971462571792741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24296583797980975047861827 36444875696971462571792741)
  ·
    refine ⟨6833414193182149232211139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36444875696971462571792741 6833414193182149232211139)
    ·
      refine ⟨10250121289773223848316709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6833414193182149232211139 10250121289773223848316709)
      ·
        refine ⟨1921897741832479471559383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10250121289773223848316709 1921897741832479471559383)
        ·
          refine ⟨2882846612748719207339075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921897741832479471559383 2882846612748719207339075)
          ·
            refine ⟨4324269919123078811008613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882846612748719207339075 4324269919123078811008613)
            ·
              refine ⟨810800609835577277064115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4324269919123078811008613 810800609835577277064115)
              ·
                refine ⟨1216200914753365915596173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810800609835577277064115 1216200914753365915596173)
                ·
                  refine ⟨456075343032512218348565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216200914753365915596173 456075343032512218348565)
                  ·
                    rfl

theorem cell20_999229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_999229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999229 prefixEnd_999229 := by exact prefixLift 999229
  have htrace : WordTrace (prefixWord ++ tailWord_999229) baseStart_999229 baseEnd_999229 := by
    simpa [prefixWord, tailWord_999229, baseEnd_999229] using wordTrace_append hprefix tailTrace_999229
  have hstable : (prefixWord ++ tailWord_999229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999229).length < 2 ^ (prefixWord ++ tailWord_999229).sum := by decide
  have hdescent : baseEnd_999229 < baseStart_999229 := by decide
  rcases family_descends (prefixWord ++ tailWord_999229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999257 : List Nat := [1, 2, 1, 2, 2, 3, 2, 5, 2]
def baseStart_999257 : Nat := 118140960795 + 999257 * 2 ^ 59
def prefixEnd_999257 : Nat := 4983230072969 + 3 ^ 40 * 999257 * 2
def baseEnd_999257 : Nat := 456088122995468565415117

theorem tailTrace_999257 : CollatzResearch.WordTrace tailWord_999257 prefixEnd_999257 456088122995468565415117 := by
  unfold tailWord_999257
  simp only [CollatzResearch.WordTrace]
  refine ⟨36445896940870023353812025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24297264627246682235874683 36445896940870023353812025)
  ·
    refine ⟨27334422705652517515359019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36445896940870023353812025 27334422705652517515359019)
    ·
      refine ⟨41001634058478776273038529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27334422705652517515359019 41001634058478776273038529)
      ·
        refine ⟨30751225543859082204778897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41001634058478776273038529 30751225543859082204778897)
        ·
          refine ⟨23063419157894311653584173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30751225543859082204778897 23063419157894311653584173)
          ·
            refine ⟨8648782184210366870094065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23063419157894311653584173 8648782184210366870094065)
            ·
              refine ⟨6486586638157775152570549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8648782184210366870094065 6486586638157775152570549)
              ·
                refine ⟨608117497327291420553489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6486586638157775152570549 608117497327291420553489)
                ·
                  refine ⟨456088122995468565415117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608117497327291420553489 456088122995468565415117)
                  ·
                    rfl

theorem cell20_999257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_999257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999257 prefixEnd_999257 := by exact prefixLift 999257
  have htrace : WordTrace (prefixWord ++ tailWord_999257) baseStart_999257 baseEnd_999257 := by
    simpa [prefixWord, tailWord_999257, baseEnd_999257] using wordTrace_append hprefix tailTrace_999257
  have hstable : (prefixWord ++ tailWord_999257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999257).length < 2 ^ (prefixWord ++ tailWord_999257).sum := by decide
  have hdescent : baseEnd_999257 < baseStart_999257 := by decide
  rcases family_descends (prefixWord ++ tailWord_999257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999292 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_999292 : Nat := 118140960795 + 999292 * 2 ^ 59
def prefixEnd_999292 : Nat := 4983230072969 + 3 ^ 40 * 999292 * 2
def baseEnd_999292 : Nat := 456104097949163999248307

theorem tailTrace_999292 : CollatzResearch.WordTrace tailWord_999292 prefixEnd_999292 456104097949163999248307 := by
  unfold tailWord_999292
  simp only [CollatzResearch.WordTrace]
  refine ⟨18223586747871612165668065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24298115663828816220890753 18223586747871612165668065)
  ·
    refine ⟨13667690060903709124251049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18223586747871612165668065 13667690060903709124251049)
    ·
      refine ⟨10250767545677781843188287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13667690060903709124251049 10250767545677781843188287)
      ·
        refine ⟨15376151318516672764782431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10250767545677781843188287 15376151318516672764782431)
        ·
          refine ⟨23064226977775009147173647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15376151318516672764782431 23064226977775009147173647)
          ·
            refine ⟨34596340466662513720760471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23064226977775009147173647 34596340466662513720760471)
            ·
              refine ⟨51894510699993770581140707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34596340466662513720760471 51894510699993770581140707)
              ·
                refine ⟨77841766049990655871711061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51894510699993770581140707 77841766049990655871711061)
                ·
                  refine ⟨456104097949163999248307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77841766049990655871711061 456104097949163999248307)
                  ·
                    rfl

theorem cell20_999292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_999292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999292 prefixEnd_999292 := by exact prefixLift 999292
  have htrace : WordTrace (prefixWord ++ tailWord_999292) baseStart_999292 baseEnd_999292 := by
    simpa [prefixWord, tailWord_999292, baseEnd_999292] using wordTrace_append hprefix tailTrace_999292
  have hstable : (prefixWord ++ tailWord_999292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999292).length < 2 ^ (prefixWord ++ tailWord_999292).sum := by decide
  have hdescent : baseEnd_999292 < baseStart_999292 := by decide
  rcases family_descends (prefixWord ++ tailWord_999292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999318 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_999318 : Nat := 118140960795 + 999318 * 2 ^ 59
def prefixEnd_999318 : Nat := 4983230072969 + 3 ^ 40 * 999318 * 2
def baseEnd_999318 : Nat := 456115965057623464381535

theorem tailTrace_999318 : CollatzResearch.WordTrace tailWord_999318 prefixEnd_999318 456115965057623464381535 := by
  unfold tailWord_999318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278007612103064423236413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24298747862432687181188405 2278007612103064423236413)
  ·
    refine ⟨854252854538649158713655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2278007612103064423236413 854252854538649158713655)
    ·
      refine ⟨1281379281807973738070483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854252854538649158713655 1281379281807973738070483)
      ·
        refine ⟨1922068922711960607105725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281379281807973738070483 1922068922711960607105725)
        ·
          refine ⟨720775846016985227664647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1922068922711960607105725 720775846016985227664647)
          ·
            refine ⟨1081163769025477841496971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720775846016985227664647 1081163769025477841496971)
            ·
              refine ⟨1621745653538216762245457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081163769025477841496971 1621745653538216762245457)
              ·
                refine ⟨1216309240153662571684093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1621745653538216762245457 1216309240153662571684093)
                ·
                  refine ⟨456115965057623464381535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216309240153662571684093 456115965057623464381535)
                  ·
                    rfl

theorem cell20_999318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_999318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999318 prefixEnd_999318 := by exact prefixLift 999318
  have htrace : WordTrace (prefixWord ++ tailWord_999318) baseStart_999318 baseEnd_999318 := by
    simpa [prefixWord, tailWord_999318, baseEnd_999318] using wordTrace_append hprefix tailTrace_999318
  have hstable : (prefixWord ++ tailWord_999318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999318).length < 2 ^ (prefixWord ++ tailWord_999318).sum := by decide
  have hdescent : baseEnd_999318 < baseStart_999318 := by decide
  rcases family_descends (prefixWord ++ tailWord_999318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999357 : List Nat := [1, 4, 1, 2, 3, 3, 2, 4]
def baseStart_999357 : Nat := 118140960795 + 999357 * 2 ^ 59
def prefixEnd_999357 : Nat := 4983230072969 + 3 ^ 40 * 999357 * 2
def baseEnd_999357 : Nat := 152044588573437554027125

theorem tailTrace_999357 : CollatzResearch.WordTrace tailWord_999357 prefixEnd_999357 152044588573437554027125 := by
  unfold tailWord_999357
  simp only [CollatzResearch.WordTrace]
  refine ⟨36449544240507740432452325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24299696160338493621634883 36449544240507740432452325)
  ·
    refine ⟨6834289545095201331084811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36449544240507740432452325 6834289545095201331084811)
    ·
      refine ⟨10251434317642801996627217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6834289545095201331084811 10251434317642801996627217)
      ·
        refine ⟨7688575738232101497470413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10251434317642801996627217 7688575738232101497470413)
        ·
          refine ⟨2883215901837038061551405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7688575738232101497470413 2883215901837038061551405)
          ·
            refine ⟨1081205963188889273081777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2883215901837038061551405 1081205963188889273081777)
            ·
              refine ⟨810904472391666954811333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081205963188889273081777 810904472391666954811333)
              ·
                refine ⟨152044588573437554027125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 810904472391666954811333 152044588573437554027125)
                ·
                  rfl

theorem cell20_999357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 4].length) (baseStart_999357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999357 prefixEnd_999357 := by exact prefixLift 999357
  have htrace : WordTrace (prefixWord ++ tailWord_999357) baseStart_999357 baseEnd_999357 := by
    simpa [prefixWord, tailWord_999357, baseEnd_999357] using wordTrace_append hprefix tailTrace_999357
  have hstable : (prefixWord ++ tailWord_999357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999357).length < 2 ^ (prefixWord ++ tailWord_999357).sum := by decide
  have hdescent : baseEnd_999357 < baseStart_999357 := by decide
  rcases family_descends (prefixWord ++ tailWord_999357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999461 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 3]
def baseStart_999461 : Nat := 118140960795 + 999461 * 2 ^ 59
def prefixEnd_999461 : Nat := 4983230072969 + 3 ^ 40 * 999461 * 2
def baseEnd_999461 : Nat := 456181234154150522614283

theorem tailTrace_999461 : CollatzResearch.WordTrace tailWord_999461 prefixEnd_999461 456181234154150522614283 := by
  unfold tailWord_999461
  simp only [CollatzResearch.WordTrace]
  refine ⟨36453337432130966194238237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24302224954753977462825491 36453337432130966194238237)
  ·
    refine ⟨13670001537049112322839339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36453337432130966194238237 13670001537049112322839339)
    ·
      refine ⟨20505002305573668484259009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13670001537049112322839339 20505002305573668484259009)
      ·
        refine ⟨15378751729180251363194257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20505002305573668484259009 15378751729180251363194257)
        ·
          refine ⟨11534063796885188522395693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15378751729180251363194257 11534063796885188522395693)
          ·
            refine ⟨4325273923831945695898385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11534063796885188522395693 4325273923831945695898385)
            ·
              refine ⟨3243955442873959271923789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4325273923831945695898385 3243955442873959271923789)
              ·
                refine ⟨1216483291077734726971421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3243955442873959271923789 1216483291077734726971421)
                ·
                  refine ⟨456181234154150522614283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216483291077734726971421 456181234154150522614283)
                  ·
                    rfl

theorem cell20_999461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_999461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999461 prefixEnd_999461 := by exact prefixLift 999461
  have htrace : WordTrace (prefixWord ++ tailWord_999461) baseStart_999461 baseEnd_999461 := by
    simpa [prefixWord, tailWord_999461, baseEnd_999461] using wordTrace_append hprefix tailTrace_999461
  have hstable : (prefixWord ++ tailWord_999461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999461).length < 2 ^ (prefixWord ++ tailWord_999461).sum := by decide
  have hdescent : baseEnd_999461 < baseStart_999461 := by decide
  rcases family_descends (prefixWord ++ tailWord_999461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999464 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 4]
def baseStart_999464 : Nat := 118140960795 + 999464 * 2 ^ 59
def prefixEnd_999464 : Nat := 4983230072969 + 3 ^ 40 * 999464 * 2
def baseEnd_999464 : Nat := 456182603435895845514271

theorem tailTrace_999464 : CollatzResearch.WordTrace tailWord_999464 prefixEnd_999464 456182603435895845514271 := by
  unfold tailWord_999464
  simp only [CollatzResearch.WordTrace]
  refine ⟨18226723425560048853298723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24302297900746731804398297 18226723425560048853298723)
  ·
    refine ⟨27340085138340073279948085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18226723425560048853298723 27340085138340073279948085)
    ·
      refine ⟨2563132981719381869995133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27340085138340073279948085 2563132981719381869995133)
      ·
        refine ⟨961174868144768201248175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2563132981719381869995133 961174868144768201248175)
        ·
          refine ⟨1441762302217152301872263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961174868144768201248175 1441762302217152301872263)
          ·
            refine ⟨2162643453325728452808395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441762302217152301872263 2162643453325728452808395)
            ·
              refine ⟨3243965179988592679212593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162643453325728452808395 3243965179988592679212593)
              ·
                refine ⟨2432973884991444509409445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3243965179988592679212593 2432973884991444509409445)
                ·
                  refine ⟨456182603435895845514271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2432973884991444509409445 456182603435895845514271)
                  ·
                    rfl

theorem cell20_999464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_999464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999464 prefixEnd_999464 := by exact prefixLift 999464
  have htrace : WordTrace (prefixWord ++ tailWord_999464) baseStart_999464 baseEnd_999464 := by
    simpa [prefixWord, tailWord_999464, baseEnd_999464] using wordTrace_append hprefix tailTrace_999464
  have hstable : (prefixWord ++ tailWord_999464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999464).length < 2 ^ (prefixWord ++ tailWord_999464).sum := by decide
  have hdescent : baseEnd_999464 < baseStart_999464 := by decide
  rcases family_descends (prefixWord ++ tailWord_999464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999482 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_999482 : Nat := 118140960795 + 999482 * 2 ^ 59
def prefixEnd_999482 : Nat := 4983230072969 + 3 ^ 40 * 999482 * 2
def baseEnd_999482 : Nat := 456190819126367782914197

theorem tailTrace_999482 : CollatzResearch.WordTrace tailWord_999482 prefixEnd_999482 456190819126367782914197 := by
  unfold tailWord_999482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113525841263721695188175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24302735576703257853835133 9113525841263721695188175)
  ·
    refine ⟨13670288761895582542782263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9113525841263721695188175 13670288761895582542782263)
    ·
      refine ⟨20505433142843373814173395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13670288761895582542782263 20505433142843373814173395)
      ·
        refine ⟨30758149714265060721260093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20505433142843373814173395 30758149714265060721260093)
        ·
          refine ⟨11534306142849397770472535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30758149714265060721260093 11534306142849397770472535)
          ·
            refine ⟨17301459214274096655708803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11534306142849397770472535 17301459214274096655708803)
            ·
              refine ⟨25952188821411144983563205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17301459214274096655708803 25952188821411144983563205)
              ·
                refine ⟨4866035404014589684418101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25952188821411144983563205 4866035404014589684418101)
                ·
                  refine ⟨456190819126367782914197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4866035404014589684418101 456190819126367782914197)
                  ·
                    rfl

theorem cell20_999482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_999482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999482 prefixEnd_999482 := by exact prefixLift 999482
  have htrace : WordTrace (prefixWord ++ tailWord_999482) baseStart_999482 baseEnd_999482 := by
    simpa [prefixWord, tailWord_999482, baseEnd_999482] using wordTrace_append hprefix tailTrace_999482
  have hstable : (prefixWord ++ tailWord_999482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999482).length < 2 ^ (prefixWord ++ tailWord_999482).sum := by decide
  have hdescent : baseEnd_999482 < baseStart_999482 := by decide
  rcases family_descends (prefixWord ++ tailWord_999482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999530 : List Nat := [3, 1, 3, 2, 3, 1, 1, 6]
def baseStart_999530 : Nat := 118140960795 + 999530 * 2 ^ 59
def prefixEnd_999530 : Nat := 4983230072969 + 3 ^ 40 * 999530 * 2
def baseEnd_999530 : Nat := 152070909211430983104667

theorem tailTrace_999530 : CollatzResearch.WordTrace tailWord_999530 prefixEnd_999530 152070909211430983104667 := by
  unfold tailWord_999530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113963517220247744625011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24303902712587327319000029 9113963517220247744625011)
  ·
    refine ⟨13670945275830371616937517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9113963517220247744625011 13670945275830371616937517)
    ·
      refine ⟨5126604478436389356351569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13670945275830371616937517 5126604478436389356351569)
      ·
        refine ⟨3844953358827292017263677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5126604478436389356351569 3844953358827292017263677)
        ·
          refine ⟨1441857509560234506473879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3844953358827292017263677 1441857509560234506473879)
          ·
            refine ⟨2162786264340351759710819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441857509560234506473879 2162786264340351759710819)
            ·
              refine ⟨3244179396510527639566229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162786264340351759710819 3244179396510527639566229)
              ·
                refine ⟨152070909211430983104667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3244179396510527639566229 152070909211430983104667)
                ·
                  rfl

theorem cell20_999530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_999530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999530 prefixEnd_999530 := by exact prefixLift 999530
  have htrace : WordTrace (prefixWord ++ tailWord_999530) baseStart_999530 baseEnd_999530 := by
    simpa [prefixWord, tailWord_999530, baseEnd_999530] using wordTrace_append hprefix tailTrace_999530
  have hstable : (prefixWord ++ tailWord_999530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999530).length < 2 ^ (prefixWord ++ tailWord_999530).sum := by decide
  have hdescent : baseEnd_999530 < baseStart_999530 := by decide
  rcases family_descends (prefixWord ++ tailWord_999530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999612 : List Nat := [2, 2, 2, 3, 4, 1, 2, 2, 2]
def baseStart_999612 : Nat := 118140960795 + 999612 * 2 ^ 59
def prefixEnd_999612 : Nat := 4983230072969 + 3 ^ 40 * 999612 * 2
def baseEnd_999612 : Nat := 456250154668665108580333

theorem tailTrace_999612 : CollatzResearch.WordTrace tailWord_999612 prefixEnd_999612 456250154668665108580333 := by
  unfold tailWord_999612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18229422427291959491492545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24305896569722612655323393 18229422427291959491492545)
  ·
    refine ⟨13672066820468969618619409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18229422427291959491492545 13672066820468969618619409)
    ·
      refine ⟨10254050115351727213964557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13672066820468969618619409 10254050115351727213964557)
      ·
        refine ⟨3845268793256897705236709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10254050115351727213964557 3845268793256897705236709)
        ·
          refine ⟨720987898735668319731883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3845268793256897705236709 720987898735668319731883)
          ·
            refine ⟨1081481848103502479597825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720987898735668319731883 1081481848103502479597825)
            ·
              refine ⟨811111386077626859698369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081481848103502479597825 811111386077626859698369)
              ·
                refine ⟨608333539558220144773777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811111386077626859698369 608333539558220144773777)
                ·
                  refine ⟨456250154668665108580333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608333539558220144773777 456250154668665108580333)
                  ·
                    rfl

theorem cell20_999612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_999612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999612 prefixEnd_999612 := by exact prefixLift 999612
  have htrace : WordTrace (prefixWord ++ tailWord_999612) baseStart_999612 baseEnd_999612 := by
    simpa [prefixWord, tailWord_999612, baseEnd_999612] using wordTrace_append hprefix tailTrace_999612
  have hstable : (prefixWord ++ tailWord_999612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999612).length < 2 ^ (prefixWord ++ tailWord_999612).sum := by decide
  have hdescent : baseEnd_999612 < baseStart_999612 := by decide
  rcases family_descends (prefixWord ++ tailWord_999612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999616 : List Nat := [2, 1, 1, 2, 5, 1, 4, 2, 2]
def baseStart_999616 : Nat := 118140960795 + 999616 * 2 ^ 59
def prefixEnd_999616 : Nat := 4983230072969 + 3 ^ 40 * 999616 * 2
def baseEnd_999616 : Nat := 456251980377658872446983

theorem tailTrace_999616 : CollatzResearch.WordTrace tailWord_999616 prefixEnd_999616 456251980377658872446983 := by
  unfold tailWord_999616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18229495373284713833065351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24305993831046285110753801 18229495373284713833065351)
  ·
    refine ⟨27344243059927070749598027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18229495373284713833065351 27344243059927070749598027)
    ·
      refine ⟨41016364589890606124397041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27344243059927070749598027 41016364589890606124397041)
      ·
        refine ⟨30762273442417954593297781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41016364589890606124397041 30762273442417954593297781)
        ·
          refine ⟨2883963135226683243121667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30762273442417954593297781 2883963135226683243121667)
          ·
            refine ⟨4325944702840024864682501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883963135226683243121667 4325944702840024864682501)
            ·
              refine ⟨811114631782504662127969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4325944702840024864682501 811114631782504662127969)
              ·
                refine ⟨608335973836878496595977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811114631782504662127969 608335973836878496595977)
                ·
                  refine ⟨456251980377658872446983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608335973836878496595977 456251980377658872446983)
                  ·
                    rfl

theorem cell20_999616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_999616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999616 prefixEnd_999616 := by exact prefixLift 999616
  have htrace : WordTrace (prefixWord ++ tailWord_999616) baseStart_999616 baseEnd_999616 := by
    simpa [prefixWord, tailWord_999616, baseEnd_999616] using wordTrace_append hprefix tailTrace_999616
  have hstable : (prefixWord ++ tailWord_999616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999616).length < 2 ^ (prefixWord ++ tailWord_999616).sum := by decide
  have hdescent : baseEnd_999616 < baseStart_999616 := by decide
  rcases family_descends (prefixWord ++ tailWord_999616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999637 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 4]
def baseStart_999637 : Nat := 118140960795 + 999637 * 2 ^ 59
def prefixEnd_999637 : Nat := 4983230072969 + 3 ^ 40 * 999637 * 2
def baseEnd_999637 : Nat := 456261565349876132746897

theorem tailTrace_999637 : CollatzResearch.WordTrace tailWord_999637 prefixEnd_999637 456261565349876132746897 := by
  unfold tailWord_999637
  simp only [CollatzResearch.WordTrace]
  refine ⟨36459756679493348252645165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24306504452995565501763443 36459756679493348252645165)
  ·
    refine ⟨13672408754810005594741937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36459756679493348252645165 13672408754810005594741937)
    ·
      refine ⟨10254306566107504196056453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13672408754810005594741937 10254306566107504196056453)
      ·
        refine ⟨1922682481145157036760585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10254306566107504196056453 1922682481145157036760585)
        ·
          refine ⟨1442011860858867777570439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1922682481145157036760585 1442011860858867777570439)
          ·
            refine ⟨2163017791288301666355659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442011860858867777570439 2163017791288301666355659)
            ·
              refine ⟨3244526686932452499533489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163017791288301666355659 3244526686932452499533489)
              ·
                refine ⟨2433395015199339374650117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3244526686932452499533489 2433395015199339374650117)
                ·
                  refine ⟨456261565349876132746897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433395015199339374650117 456261565349876132746897)
                  ·
                    rfl

theorem cell20_999637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_999637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999637 prefixEnd_999637 := by exact prefixLift 999637
  have htrace : WordTrace (prefixWord ++ tailWord_999637) baseStart_999637 baseEnd_999637 := by
    simpa [prefixWord, tailWord_999637, baseEnd_999637] using wordTrace_append hprefix tailTrace_999637
  have hstable : (prefixWord ++ tailWord_999637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999637).length < 2 ^ (prefixWord ++ tailWord_999637).sum := by decide
  have hdescent : baseEnd_999637 < baseStart_999637 := by decide
  rcases family_descends (prefixWord ++ tailWord_999637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999641 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_999641 : Nat := 118140960795 + 999641 * 2 ^ 59
def prefixEnd_999641 : Nat := 4983230072969 + 3 ^ 40 * 999641 * 2
def baseEnd_999641 : Nat := 456263391058869896613547

theorem tailTrace_999641 : CollatzResearch.WordTrace tailWord_999641 prefixEnd_999641 456263391058869896613547 := by
  unfold tailWord_999641
  simp only [CollatzResearch.WordTrace]
  refine ⟨36459902571478856935790777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24306601714319237957193851 36459902571478856935790777)
  ·
    refine ⟨27344926928609142701843083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36459902571478856935790777 27344926928609142701843083)
    ·
      refine ⟨41017390392913714052764625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27344926928609142701843083 41017390392913714052764625)
      ·
        refine ⟨30763042794685285539573469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41017390392913714052764625 30763042794685285539573469)
        ·
          refine ⟨11536141048006982077340051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30763042794685285539573469 11536141048006982077340051)
          ·
            refine ⟨17304211572010473116010077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11536141048006982077340051 17304211572010473116010077)
            ·
              refine ⟨6489079339503927418503779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17304211572010473116010077 6489079339503927418503779)
              ·
                refine ⟨9733619009255891127755669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6489079339503927418503779 9733619009255891127755669)
                ·
                  refine ⟨456263391058869896613547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9733619009255891127755669 456263391058869896613547)
                  ·
                    rfl

theorem cell20_999641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_999641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999641 prefixEnd_999641 := by exact prefixLift 999641
  have htrace : WordTrace (prefixWord ++ tailWord_999641) baseStart_999641 baseEnd_999641 := by
    simpa [prefixWord, tailWord_999641, baseEnd_999641] using wordTrace_append hprefix tailTrace_999641
  have hstable : (prefixWord ++ tailWord_999641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999641).length < 2 ^ (prefixWord ++ tailWord_999641).sum := by decide
  have hdescent : baseEnd_999641 < baseStart_999641 := by decide
  rcases family_descends (prefixWord ++ tailWord_999641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999703 : List Nat := [1, 1, 3, 4, 1, 3, 1, 6]
def baseStart_999703 : Nat := 118140960795 + 999703 * 2 ^ 59
def prefixEnd_999703 : Nat := 4983230072969 + 3 ^ 40 * 999703 * 2
def baseEnd_999703 : Nat := 152097229849424412182209

theorem tailTrace_999703 : CollatzResearch.WordTrace tailWord_999703 prefixEnd_999703 152097229849424412182209 := by
  unfold tailWord_999703
  simp only [CollatzResearch.WordTrace]
  refine ⟨36462163897254241524547763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24308109264836161016365175 36462163897254241524547763)
  ·
    refine ⟨54693245845881362286821645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36462163897254241524547763 54693245845881362286821645)
    ·
      refine ⟨20509967192205510857558117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54693245845881362286821645 20509967192205510857558117)
      ·
        refine ⟨3845618848538533285792147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20509967192205510857558117 3845618848538533285792147)
        ·
          refine ⟨5768428272807799928688221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3845618848538533285792147 5768428272807799928688221)
          ·
            refine ⟨2163160602302924973258083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5768428272807799928688221 2163160602302924973258083)
            ·
              refine ⟨3244740903454387459887125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163160602302924973258083 3244740903454387459887125)
              ·
                refine ⟨152097229849424412182209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3244740903454387459887125 152097229849424412182209)
                ·
                  rfl

theorem cell20_999703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_999703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999703 prefixEnd_999703 := by exact prefixLift 999703
  have htrace : WordTrace (prefixWord ++ tailWord_999703) baseStart_999703 baseEnd_999703 := by
    simpa [prefixWord, tailWord_999703, baseEnd_999703] using wordTrace_append hprefix tailTrace_999703
  have hstable : (prefixWord ++ tailWord_999703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999703).length < 2 ^ (prefixWord ++ tailWord_999703).sum := by decide
  have hdescent : baseEnd_999703 < baseStart_999703 := by decide
  rcases family_descends (prefixWord ++ tailWord_999703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999709 : List Nat := [1, 4, 2, 3, 2, 2, 1, 3, 2]
def baseStart_999709 : Nat := 118140960795 + 999709 * 2 ^ 59
def prefixEnd_999709 : Nat := 4983230072969 + 3 ^ 40 * 999709 * 2
def baseEnd_999709 : Nat := 456294428111763882346603

theorem tailTrace_999709 : CollatzResearch.WordTrace tailWord_999709 prefixEnd_999709 456294428111763882346603 := by
  unfold tailWord_999709
  simp only [CollatzResearch.WordTrace]
  refine ⟨36462382735232504549266181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24308255156821669699510787 36462382735232504549266181)
  ·
    refine ⟨6836696762856094602987409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36462382735232504549266181 6836696762856094602987409)
    ·
      refine ⟨5127522572142070952240557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6836696762856094602987409 5127522572142070952240557)
      ·
        refine ⟨1922820964553276607090209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5127522572142070952240557 1922820964553276607090209)
        ·
          refine ⟨1442115723414957455317657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1922820964553276607090209 1442115723414957455317657)
          ·
            refine ⟨1081586792561218091488243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1442115723414957455317657 1081586792561218091488243)
            ·
              refine ⟨1622380188841827137232365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081586792561218091488243 1622380188841827137232365)
              ·
                refine ⟨608392570815685176462137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1622380188841827137232365 608392570815685176462137)
                ·
                  refine ⟨456294428111763882346603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608392570815685176462137 456294428111763882346603)
                  ·
                    rfl

theorem cell20_999709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_999709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999709 prefixEnd_999709 := by exact prefixLift 999709
  have htrace : WordTrace (prefixWord ++ tailWord_999709) baseStart_999709 baseEnd_999709 := by
    simpa [prefixWord, tailWord_999709, baseEnd_999709] using wordTrace_append hprefix tailTrace_999709
  have hstable : (prefixWord ++ tailWord_999709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999709).length < 2 ^ (prefixWord ++ tailWord_999709).sum := by decide
  have hdescent : baseEnd_999709 < baseStart_999709 := by decide
  rcases family_descends (prefixWord ++ tailWord_999709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999713 : List Nat := [1, 2, 3, 2, 1, 1, 5, 3, 2]
def baseStart_999713 : Nat := 118140960795 + 999713 * 2 ^ 59
def prefixEnd_999713 : Nat := 4983230072969 + 3 ^ 40 * 999713 * 2
def baseEnd_999713 : Nat := 456296253820757646213253

theorem tailTrace_999713 : CollatzResearch.WordTrace tailWord_999713 prefixEnd_999713 456296253820757646213253 := by
  unfold tailWord_999713
  simp only [CollatzResearch.WordTrace]
  refine ⟨36462528627218013232411793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24308352418145342154941195 36462528627218013232411793)
  ·
    refine ⟨27346896470413509924308845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36462528627218013232411793 27346896470413509924308845)
    ·
      refine ⟨10255086176405066221615817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27346896470413509924308845 10255086176405066221615817)
      ·
        refine ⟨7691314632303799666211863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10255086176405066221615817 7691314632303799666211863)
        ·
          refine ⟨11536971948455699499317795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7691314632303799666211863 11536971948455699499317795)
          ·
            refine ⟨17305457922683549248976693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11536971948455699499317795 17305457922683549248976693)
            ·
              refine ⟨1622386680251582742091565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17305457922683549248976693 1622386680251582742091565)
              ·
                refine ⟨608395005094343528284337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1622386680251582742091565 608395005094343528284337)
                ·
                  refine ⟨456296253820757646213253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608395005094343528284337 456296253820757646213253)
                  ·
                    rfl

theorem cell20_999713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_999713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999713 prefixEnd_999713 := by exact prefixLift 999713
  have htrace : WordTrace (prefixWord ++ tailWord_999713) baseStart_999713 baseEnd_999713 := by
    simpa [prefixWord, tailWord_999713, baseEnd_999713] using wordTrace_append hprefix tailTrace_999713
  have hstable : (prefixWord ++ tailWord_999713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999713).length < 2 ^ (prefixWord ++ tailWord_999713).sum := by decide
  have hdescent : baseEnd_999713 < baseStart_999713 := by decide
  rcases family_descends (prefixWord ++ tailWord_999713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999720 : List Nat := [2, 1, 5, 1, 3, 2, 6]
def baseStart_999720 : Nat := 118140960795 + 999720 * 2 ^ 59
def prefixEnd_999720 : Nat := 4983230072969 + 3 ^ 40 * 999720 * 2
def baseEnd_999720 : Nat := 50699938756832970331099

theorem tailTrace_999720 : CollatzResearch.WordTrace tailWord_999720 prefixEnd_999720 50699938756832970331099 := by
  unfold tailWord_999720
  simp only [CollatzResearch.WordTrace]
  refine ⟨18231391969096326713958307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24308522625461768951944409 18231391969096326713958307)
  ·
    refine ⟨27347087953644490070937461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18231391969096326713958307 27347087953644490070937461)
    ·
      refine ⟨2563789495654170944150387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27347087953644490070937461 2563789495654170944150387)
      ·
        refine ⟨3845684243481256416225581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2563789495654170944150387 3845684243481256416225581)
        ·
          refine ⟨1442131591305471156084593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3845684243481256416225581 1442131591305471156084593)
          ·
            refine ⟨1081598693479103367063445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1442131591305471156084593 1081598693479103367063445)
            ·
              refine ⟨50699938756832970331099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1081598693479103367063445 50699938756832970331099)
              ·
                rfl

theorem cell20_999720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 6].length) (baseStart_999720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999720 prefixEnd_999720 := by exact prefixLift 999720
  have htrace : WordTrace (prefixWord ++ tailWord_999720) baseStart_999720 baseEnd_999720 := by
    simpa [prefixWord, tailWord_999720, baseEnd_999720] using wordTrace_append hprefix tailTrace_999720
  have hstable : (prefixWord ++ tailWord_999720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999720).length < 2 ^ (prefixWord ++ tailWord_999720).sum := by decide
  have hdescent : baseEnd_999720 < baseStart_999720 := by decide
  rcases family_descends (prefixWord ++ tailWord_999720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999724 : List Nat := [2, 2, 1, 1, 1, 3, 10]
def baseStart_999724 : Nat := 118140960795 + 999724 * 2 ^ 59
def prefixEnd_999724 : Nat := 4983230072969 + 3 ^ 40 * 999724 * 2
def baseEnd_999724 : Nat := 50700141613387832982949

theorem tailTrace_999724 : CollatzResearch.WordTrace tailWord_999724 prefixEnd_999724 50700141613387832982949 := by
  unfold tailWord_999724
  simp only [CollatzResearch.WordTrace]
  refine ⟨18231464915089081055531113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24308619886785441407374817 18231464915089081055531113)
  ·
    refine ⟨13673598686316810791648335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18231464915089081055531113 13673598686316810791648335)
    ·
      refine ⟨20510398029475216187472503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13673598686316810791648335 20510398029475216187472503)
      ·
        refine ⟨30765597044212824281208755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20510398029475216187472503 30765597044212824281208755)
        ·
          refine ⟨46148395566319236421813133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30765597044212824281208755 46148395566319236421813133)
          ·
            refine ⟨17305648337369713658179925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46148395566319236421813133 17305648337369713658179925)
            ·
              refine ⟨50700141613387832982949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17305648337369713658179925 50700141613387832982949)
              ·
                rfl

theorem cell20_999724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 10].length) (baseStart_999724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999724 prefixEnd_999724 := by exact prefixLift 999724
  have htrace : WordTrace (prefixWord ++ tailWord_999724) baseStart_999724 baseEnd_999724 := by
    simpa [prefixWord, tailWord_999724, baseEnd_999724] using wordTrace_append hprefix tailTrace_999724
  have hstable : (prefixWord ++ tailWord_999724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999724).length < 2 ^ (prefixWord ++ tailWord_999724).sum := by decide
  have hdescent : baseEnd_999724 < baseStart_999724 := by decide
  rcases family_descends (prefixWord ++ tailWord_999724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999726 : List Nat := [4, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_999726 : Nat := 118140960795 + 999726 * 2 ^ 59
def prefixEnd_999726 : Nat := 4983230072969 + 3 ^ 40 * 999726 * 2
def baseEnd_999726 : Nat := 456302187374987378779867

theorem tailTrace_999726 : CollatzResearch.WordTrace tailWord_999726 prefixEnd_999726 456302187374987378779867 := by
  unfold tailWord_999726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4557875347021364556579379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24308668517447277635090021 4557875347021364556579379)
  ·
    refine ⟨6836813020532046834869069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4557875347021364556579379 6836813020532046834869069)
    ·
      refine ⟨2563804882699517563075901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6836813020532046834869069 2563804882699517563075901)
      ·
        refine ⟨961426831012319086153463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2563804882699517563075901 961426831012319086153463)
        ·
          refine ⟨1442140246518478629230195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961426831012319086153463 1442140246518478629230195)
          ·
            refine ⟨2163210369777717943845293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442140246518478629230195 2163210369777717943845293)
            ·
              refine ⟨811203888666644228941985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2163210369777717943845293 811203888666644228941985)
              ·
                refine ⟨608402916499983171706489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811203888666644228941985 608402916499983171706489)
                ·
                  refine ⟨456302187374987378779867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608402916499983171706489 456302187374987378779867)
                  ·
                    rfl

theorem cell20_999726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_999726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999726 prefixEnd_999726 := by exact prefixLift 999726
  have htrace : WordTrace (prefixWord ++ tailWord_999726) baseStart_999726 baseEnd_999726 := by
    simpa [prefixWord, tailWord_999726, baseEnd_999726] using wordTrace_append hprefix tailTrace_999726
  have hstable : (prefixWord ++ tailWord_999726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999726).length < 2 ^ (prefixWord ++ tailWord_999726).sum := by decide
  have hdescent : baseEnd_999726 < baseStart_999726 := by decide
  rcases family_descends (prefixWord ++ tailWord_999726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999730 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 4]
def baseStart_999730 : Nat := 118140960795 + 999730 * 2 ^ 59
def prefixEnd_999730 : Nat := 4983230072969 + 3 ^ 40 * 999730 * 2
def baseEnd_999730 : Nat := 456304013083981142646517

theorem tailTrace_999730 : CollatzResearch.WordTrace tailWord_999730 prefixEnd_999730 456304013083981142646517 := by
  unfold tailWord_999730
  simp only [CollatzResearch.WordTrace]
  refine ⟨9115787167039106283945161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24308765778770950090520429 9115787167039106283945161)
  ·
    refine ⟨6836840375279329712958871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9115787167039106283945161 6836840375279329712958871)
    ·
      refine ⟨10255260562918994569438307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6836840375279329712958871 10255260562918994569438307)
      ·
        refine ⟨15382890844378491854157461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10255260562918994569438307 15382890844378491854157461)
        ·
          refine ⟨721073008330241805663631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15382890844378491854157461 721073008330241805663631)
          ·
            refine ⟨1081609512495362708495447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721073008330241805663631 1081609512495362708495447)
            ·
              refine ⟨1622414268743044062743171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081609512495362708495447 1622414268743044062743171)
              ·
                refine ⟨2433621403114566094114757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622414268743044062743171 2433621403114566094114757)
                ·
                  refine ⟨456304013083981142646517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433621403114566094114757 456304013083981142646517)
                  ·
                    rfl

theorem cell20_999730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_999730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999730 prefixEnd_999730 := by exact prefixLift 999730
  have htrace : WordTrace (prefixWord ++ tailWord_999730) baseStart_999730 baseEnd_999730 := by
    simpa [prefixWord, tailWord_999730, baseEnd_999730] using wordTrace_append hprefix tailTrace_999730
  have hstable : (prefixWord ++ tailWord_999730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999730).length < 2 ^ (prefixWord ++ tailWord_999730).sum := by decide
  have hdescent : baseEnd_999730 < baseStart_999730 := by decide
  rcases family_descends (prefixWord ++ tailWord_999730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999789 : List Nat := [1, 5, 1, 1, 1, 2, 3, 4, 2]
def baseStart_999789 : Nat := 118140960795 + 999789 * 2 ^ 59
def prefixEnd_999789 : Nat := 4983230072969 + 3 ^ 40 * 999789 * 2
def baseEnd_999789 : Nat := 456330942291639159679609

theorem tailTrace_999789 : CollatzResearch.WordTrace tailWord_999789 prefixEnd_999789 456330942291639159679609 := by
  unfold tailWord_999789
  simp only [CollatzResearch.WordTrace]
  refine ⟨36465300574942678212178421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24310200383295118808118947 36465300574942678212178421)
  ·
    refine ⟨3418621928900876082391727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36465300574942678212178421 3418621928900876082391727)
    ·
      refine ⟨5127932893351314123587591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3418621928900876082391727 5127932893351314123587591)
      ·
        refine ⟨7691899340026971185381387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5127932893351314123587591 7691899340026971185381387)
        ·
          refine ⟨11537849010040456778072081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7691899340026971185381387 11537849010040456778072081)
          ·
            refine ⟨8653386757530342583554061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11537849010040456778072081 8653386757530342583554061)
            ·
              refine ⟨3245020034073878468832773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8653386757530342583554061 3245020034073878468832773)
              ·
                refine ⟨608441256388852212906145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3245020034073878468832773 608441256388852212906145)
                ·
                  refine ⟨456330942291639159679609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608441256388852212906145 456330942291639159679609)
                  ·
                    rfl

theorem cell20_999789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_999789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999789 prefixEnd_999789 := by exact prefixLift 999789
  have htrace : WordTrace (prefixWord ++ tailWord_999789) baseStart_999789 baseEnd_999789 := by
    simpa [prefixWord, tailWord_999789, baseEnd_999789] using wordTrace_append hprefix tailTrace_999789
  have hstable : (prefixWord ++ tailWord_999789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999789).length < 2 ^ (prefixWord ++ tailWord_999789).sum := by decide
  have hdescent : baseEnd_999789 < baseStart_999789 := by decide
  rcases family_descends (prefixWord ++ tailWord_999789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999793 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_999793 : Nat := 118140960795 + 999793 * 2 ^ 59
def prefixEnd_999793 : Nat := 4983230072969 + 3 ^ 40 * 999793 * 2
def baseEnd_999793 : Nat := 456332768000632923546259

theorem tailTrace_999793 : CollatzResearch.WordTrace tailWord_999793 prefixEnd_999793 456332768000632923546259 := by
  unfold tailWord_999793
  simp only [CollatzResearch.WordTrace]
  refine ⟨36465446466928186895324033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24310297644618791263549355 36465446466928186895324033)
  ·
    refine ⟨27349084850196140171493025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36465446466928186895324033 27349084850196140171493025)
    ·
      refine ⟨20511813637647105128619769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27349084850196140171493025 20511813637647105128619769)
      ·
        refine ⟨15383860228235328846464827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20511813637647105128619769 15383860228235328846464827)
        ·
          refine ⟨23075790342352993269697241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15383860228235328846464827 23075790342352993269697241)
          ·
            refine ⟨17306842756764744952272931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23075790342352993269697241 17306842756764744952272931)
            ·
              refine ⟨25960264135147117428409397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17306842756764744952272931 25960264135147117428409397)
              ·
                refine ⟨2433774762670042258913381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25960264135147117428409397 2433774762670042258913381)
                ·
                  refine ⟨456332768000632923546259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433774762670042258913381 456332768000632923546259)
                  ·
                    rfl

theorem cell20_999793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_999793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999793 prefixEnd_999793 := by exact prefixLift 999793
  have htrace : WordTrace (prefixWord ++ tailWord_999793) baseStart_999793 baseEnd_999793 := by
    simpa [prefixWord, tailWord_999793, baseEnd_999793] using wordTrace_append hprefix tailTrace_999793
  have hstable : (prefixWord ++ tailWord_999793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999793).length < 2 ^ (prefixWord ++ tailWord_999793).sum := by decide
  have hdescent : baseEnd_999793 < baseStart_999793 := by decide
  rcases family_descends (prefixWord ++ tailWord_999793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999830 : List Nat := [5, 3, 1, 2, 1, 1, 7]
def baseStart_999830 : Nat := 118140960795 + 999830 * 2 ^ 59
def prefixEnd_999830 : Nat := 4983230072969 + 3 ^ 40 * 999830 * 2
def baseEnd_999830 : Nat := 50705517312091693256975

theorem tailTrace_999830 : CollatzResearch.WordTrace tailWord_999830 prefixEnd_999830 50705517312091693256975 := by
  unfold tailWord_999830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2279174747987133888401309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24311197311862761476280629 2279174747987133888401309)
  ·
    refine ⟨854690530495175208150491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2279174747987133888401309 854690530495175208150491)
    ·
      refine ⟨1282035795742762812225737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854690530495175208150491 1282035795742762812225737)
      ·
        refine ⟨961526846807072109169303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1282035795742762812225737 961526846807072109169303)
        ·
          refine ⟨1442290270210608163753955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961526846807072109169303 1442290270210608163753955)
          ·
            refine ⟨2163435405315912245630933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442290270210608163753955 2163435405315912245630933)
            ·
              refine ⟨50705517312091693256975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2163435405315912245630933 50705517312091693256975)
              ·
                rfl

theorem cell20_999830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 7].length) (baseStart_999830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999830 prefixEnd_999830 := by exact prefixLift 999830
  have htrace : WordTrace (prefixWord ++ tailWord_999830) baseStart_999830 baseEnd_999830 := by
    simpa [prefixWord, tailWord_999830, baseEnd_999830] using wordTrace_append hprefix tailTrace_999830
  have hstable : (prefixWord ++ tailWord_999830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999830).length < 2 ^ (prefixWord ++ tailWord_999830).sum := by decide
  have hdescent : baseEnd_999830 < baseStart_999830 := by decide
  rcases family_descends (prefixWord ++ tailWord_999830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999837 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 3]
def baseStart_999837 : Nat := 118140960795 + 999837 * 2 ^ 59
def prefixEnd_999837 : Nat := 4983230072969 + 3 ^ 40 * 999837 * 2
def baseEnd_999837 : Nat := 456352850799564326079413

theorem tailTrace_999837 : CollatzResearch.WordTrace tailWord_999837 prefixEnd_999837 456352850799564326079413 := by
  unfold tailWord_999837
  simp only [CollatzResearch.WordTrace]
  refine ⟨36467051278768782409925765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24311367519179188273283843 36467051278768782409925765)
  ·
    refine ⟨6837572114769146701861081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36467051278768782409925765 6837572114769146701861081)
    ·
      refine ⟨5128179086076860026395811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6837572114769146701861081 5128179086076860026395811)
      ·
        refine ⟨7692268629115290039593717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5128179086076860026395811 7692268629115290039593717)
        ·
          refine ⟨721150183979558441211911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7692268629115290039593717 721150183979558441211911)
          ·
            refine ⟨1081725275969337661817867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721150183979558441211911 1081725275969337661817867)
            ·
              refine ⟨1622587913954006492726801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081725275969337661817867 1622587913954006492726801)
              ·
                refine ⟨1216940935465504869545101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622587913954006492726801 1216940935465504869545101)
                ·
                  refine ⟨456352850799564326079413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216940935465504869545101 456352850799564326079413)
                  ·
                    rfl

theorem cell20_999837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_999837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999837 prefixEnd_999837 := by exact prefixLift 999837
  have htrace : WordTrace (prefixWord ++ tailWord_999837) baseStart_999837 baseEnd_999837 := by
    simpa [prefixWord, tailWord_999837, baseEnd_999837] using wordTrace_append hprefix tailTrace_999837
  have hstable : (prefixWord ++ tailWord_999837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999837).length < 2 ^ (prefixWord ++ tailWord_999837).sum := by decide
  have hdescent : baseEnd_999837 < baseStart_999837 := by decide
  rcases family_descends (prefixWord ++ tailWord_999837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999893 : List Nat := [1, 3, 2, 3, 1, 4, 6]
def baseStart_999893 : Nat := 118140960795 + 999893 * 2 ^ 59
def prefixEnd_999893 : Nat := 4983230072969 + 3 ^ 40 * 999893 * 2
def baseEnd_999893 : Nat := 50708712302830780023613

theorem tailTrace_999893 : CollatzResearch.WordTrace tailWord_999893 prefixEnd_999893 50708712302830780023613 := by
  unfold tailWord_999893
  simp only [CollatzResearch.WordTrace]
  refine ⟨36469093766565903973964333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24312729177710602649309555 36469093766565903973964333)
  ·
    refine ⟨13675910162462213990236625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36469093766565903973964333 13675910162462213990236625)
    ·
      refine ⟨10256932621846660492677469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13675910162462213990236625 10256932621846660492677469)
      ·
        refine ⟨3846349733192497684754051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10256932621846660492677469 3846349733192497684754051)
        ·
          refine ⟨5769524599788746527131077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846349733192497684754051 5769524599788746527131077)
          ·
            refine ⟨1081785862460389973837077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5769524599788746527131077 1081785862460389973837077)
            ·
              refine ⟨50708712302830780023613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1081785862460389973837077 50708712302830780023613)
              ·
                rfl

theorem cell20_999893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 6].length) (baseStart_999893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_999893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_999893 prefixEnd_999893 := by exact prefixLift 999893
  have htrace : WordTrace (prefixWord ++ tailWord_999893) baseStart_999893 baseEnd_999893 := by
    simpa [prefixWord, tailWord_999893, baseEnd_999893] using wordTrace_append hprefix tailTrace_999893
  have hstable : (prefixWord ++ tailWord_999893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999893).length < 2 ^ (prefixWord ++ tailWord_999893).sum := by decide
  have hdescent : baseEnd_999893 < baseStart_999893 := by decide
  rcases family_descends (prefixWord ++ tailWord_999893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000000 : List Nat := [2, 1, 1, 2, 2, 2, 3, 5, 2]
def baseStart_1000000 : Nat := 118140960795 + 1000000 * 2 ^ 59
def prefixEnd_1000000 : Nat := 4983230072969 + 3 ^ 40 * 1000000 * 2
def baseEnd_1000000 : Nat := 456427248441060203645413

theorem tailTrace_1000000 : CollatzResearch.WordTrace tailWord_1000000 prefixEnd_1000000 456427248441060203645413 := by
  unfold tailWord_1000000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18236498188589130624054727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24315330918118840832072969 18236498188589130624054727)
  ·
    refine ⟨27354747282883695936082091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18236498188589130624054727 27354747282883695936082091)
    ·
      refine ⟨41032120924325543904123137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27354747282883695936082091 41032120924325543904123137)
      ·
        refine ⟨30774090693244157928092353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41032120924325543904123137 30774090693244157928092353)
        ·
          refine ⟨23080568019933118446069265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30774090693244157928092353 23080568019933118446069265)
          ·
            refine ⟨17310426014949838834551949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23080568019933118446069265 17310426014949838834551949)
            ·
              refine ⟨6491409755606189562956981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17310426014949838834551949 6491409755606189562956981)
              ·
                refine ⟨608569664588080271527217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6491409755606189562956981 608569664588080271527217)
                ·
                  refine ⟨456427248441060203645413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608569664588080271527217 456427248441060203645413)
                  ·
                    rfl

theorem cell20_1000000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_1000000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000000 prefixEnd_1000000 := by exact prefixLift 1000000
  have htrace : WordTrace (prefixWord ++ tailWord_1000000) baseStart_1000000 baseEnd_1000000 := by
    simpa [prefixWord, tailWord_1000000, baseEnd_1000000] using wordTrace_append hprefix tailTrace_1000000
  have hstable : (prefixWord ++ tailWord_1000000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000000).length < 2 ^ (prefixWord ++ tailWord_1000000).sum := by decide
  have hdescent : baseEnd_1000000 < baseStart_1000000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000021 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_1000021 : Nat := 118140960795 + 1000021 * 2 ^ 59
def prefixEnd_1000021 : Nat := 4983230072969 + 3 ^ 40 * 1000021 * 2
def baseEnd_1000021 : Nat := 456436833413277463945327

theorem tailTrace_1000021 : CollatzResearch.WordTrace tailWord_1000021 prefixEnd_1000021 456436833413277463945327 := by
  unfold tailWord_1000021
  simp only [CollatzResearch.WordTrace]
  refine ⟨36473762310102181834623917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24315841540068121223082611 36473762310102181834623917)
  ·
    refine ⟨13677660866288318187983969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36473762310102181834623917 13677660866288318187983969)
    ·
      refine ⟨10258245649716238640987977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13677660866288318187983969 10258245649716238640987977)
      ·
        refine ⟨7693684237287178980740983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10258245649716238640987977 7693684237287178980740983)
        ·
          refine ⟨11540526355930768471111475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7693684237287178980740983 11540526355930768471111475)
          ·
            refine ⟨17310789533896152706667213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11540526355930768471111475 17310789533896152706667213)
            ·
              refine ⟨6491546075211057265000205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17310789533896152706667213 6491546075211057265000205)
              ·
                refine ⟨2434329778204146474375077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6491546075211057265000205 2434329778204146474375077)
                ·
                  refine ⟨456436833413277463945327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2434329778204146474375077 456436833413277463945327)
                  ·
                    rfl

theorem cell20_1000021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_1000021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000021 prefixEnd_1000021 := by exact prefixLift 1000021
  have htrace : WordTrace (prefixWord ++ tailWord_1000021) baseStart_1000021 baseEnd_1000021 := by
    simpa [prefixWord, tailWord_1000021, baseEnd_1000021] using wordTrace_append hprefix tailTrace_1000021
  have hstable : (prefixWord ++ tailWord_1000021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000021).length < 2 ^ (prefixWord ++ tailWord_1000021).sum := by decide
  have hdescent : baseEnd_1000021 < baseStart_1000021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000045 : List Nat := [1, 5, 1, 1, 3, 2, 1, 6]
def baseStart_1000045 : Nat := 118140960795 + 1000045 * 2 ^ 59
def prefixEnd_1000045 : Nat := 4983230072969 + 3 ^ 40 * 1000045 * 2
def baseEnd_1000045 : Nat := 152149262555746682381743

theorem tailTrace_1000045 : CollatzResearch.WordTrace tailWord_1000045 prefixEnd_1000045 152149262555746682381743 := by
  unfold tailWord_1000045
  simp only [CollatzResearch.WordTrace]
  refine ⟨36474637662015233933497589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24316425108010155955665059 36474637662015233933497589)
  ·
    refine ⟨3419497280813928181265399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36474637662015233933497589 3419497280813928181265399)
    ·
      refine ⟨5129245921220892271898099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3419497280813928181265399 5129245921220892271898099)
      ·
        refine ⟨7693868881831338407847149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129245921220892271898099 7693868881831338407847149)
        ·
          refine ⟨2885200830686751902942681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7693868881831338407847149 2885200830686751902942681)
          ·
            refine ⟨2163900623015063927207011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2885200830686751902942681 2163900623015063927207011)
            ·
              refine ⟨3245850934522595890810517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163900623015063927207011 3245850934522595890810517)
              ·
                refine ⟨152149262555746682381743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3245850934522595890810517 152149262555746682381743)
                ·
                  rfl

theorem cell20_1000045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_1000045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000045 prefixEnd_1000045 := by exact prefixLift 1000045
  have htrace : WordTrace (prefixWord ++ tailWord_1000045) baseStart_1000045 baseEnd_1000045 := by
    simpa [prefixWord, tailWord_1000045, baseEnd_1000045] using wordTrace_append hprefix tailTrace_1000045
  have hstable : (prefixWord ++ tailWord_1000045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000045).length < 2 ^ (prefixWord ++ tailWord_1000045).sum := by decide
  have hdescent : baseEnd_1000045 < baseStart_1000045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000114 : List Nat := [3, 2, 1, 1, 1, 2, 1, 7, 2]
def baseStart_1000114 : Nat := 118140960795 + 1000114 * 2 ^ 59
def prefixEnd_1000114 : Nat := 4983230072969 + 3 ^ 40 * 1000114 * 2
def baseEnd_1000114 : Nat := 456479281147382473844947

theorem tailTrace_1000114 : CollatzResearch.WordTrace tailWord_1000114 prefixEnd_1000114 456479281147382473844947 := by
  unfold tailWord_1000114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9119288574691314679439849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24318102865843505811839597 9119288574691314679439849)
  ·
    refine ⟨6839466431018486009579887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9119288574691314679439849 6839466431018486009579887)
    ·
      refine ⟨10259199646527729014369831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6839466431018486009579887 10259199646527729014369831)
      ·
        refine ⟨15388799469791593521554747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10259199646527729014369831 15388799469791593521554747)
        ·
          refine ⟨23083199204687390282332121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15388799469791593521554747 23083199204687390282332121)
          ·
            refine ⟨17312399403515542711749091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23083199204687390282332121 17312399403515542711749091)
            ·
              refine ⟨25968599105273314067623637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17312399403515542711749091 25968599105273314067623637)
              ·
                refine ⟨608639041529843298459929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25968599105273314067623637 608639041529843298459929)
                ·
                  refine ⟨456479281147382473844947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608639041529843298459929 456479281147382473844947)
                  ·
                    rfl

theorem cell20_1000114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_1000114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000114 prefixEnd_1000114 := by exact prefixLift 1000114
  have htrace : WordTrace (prefixWord ++ tailWord_1000114) baseStart_1000114 baseEnd_1000114 := by
    simpa [prefixWord, tailWord_1000114, baseEnd_1000114] using wordTrace_append hprefix tailTrace_1000114
  have hstable : (prefixWord ++ tailWord_1000114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000114).length < 2 ^ (prefixWord ++ tailWord_1000114).sum := by decide
  have hdescent : baseEnd_1000114 < baseStart_1000114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000128 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 3]
def baseStart_1000128 : Nat := 118140960795 + 1000128 * 2 ^ 59
def prefixEnd_1000128 : Nat := 4983230072969 + 3 ^ 40 * 1000128 * 2
def baseEnd_1000128 : Nat := 456485671128860647378223

theorem tailTrace_1000128 : CollatzResearch.WordTrace tailWord_1000128 prefixEnd_1000128 456485671128860647378223 := by
  unfold tailWord_1000128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18238832460357269554384519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24318443280476359405846025 18238832460357269554384519)
  ·
    refine ⟨27358248690535904331576779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18238832460357269554384519 27358248690535904331576779)
    ·
      refine ⟨41037373035803856497365169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27358248690535904331576779 41037373035803856497365169)
      ·
        refine ⟨30778029776852892373023877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41037373035803856497365169 30778029776852892373023877)
        ·
          refine ⟨5770880583159917319941977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30778029776852892373023877 5770880583159917319941977)
          ·
            refine ⟨4328160437369937989956483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5770880583159917319941977 4328160437369937989956483)
            ·
              refine ⟨6492240656054906984934725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328160437369937989956483 6492240656054906984934725)
              ·
                refine ⟨1217295123010295059675261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6492240656054906984934725 1217295123010295059675261)
                ·
                  refine ⟨456485671128860647378223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217295123010295059675261 456485671128860647378223)
                  ·
                    rfl

theorem cell20_1000128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_1000128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000128 prefixEnd_1000128 := by exact prefixLift 1000128
  have htrace : WordTrace (prefixWord ++ tailWord_1000128) baseStart_1000128 baseEnd_1000128 := by
    simpa [prefixWord, tailWord_1000128, baseEnd_1000128] using wordTrace_append hprefix tailTrace_1000128
  have hstable : (prefixWord ++ tailWord_1000128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000128).length < 2 ^ (prefixWord ++ tailWord_1000128).sum := by decide
  have hdescent : baseEnd_1000128 < baseStart_1000128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000134 : List Nat := [6, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1000134 : Nat := 118140960795 + 1000134 * 2 ^ 59
def prefixEnd_1000134 : Nat := 4983230072969 + 3 ^ 40 * 1000134 * 2
def baseEnd_1000134 : Nat := 152162803230783764392733

theorem tailTrace_1000134 : CollatzResearch.WordTrace tailWord_1000134 prefixEnd_1000134 152162803230783764392733 := by
  unfold tailWord_1000134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139933867459150066671483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24318589172461868088991637 1139933867459150066671483)
  ·
    refine ⟨1709900801188725100007225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139933867459150066671483 1709900801188725100007225)
    ·
      refine ⟨1282425600891543825005419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1709900801188725100007225 1282425600891543825005419)
      ·
        refine ⟨1923638401337315737508129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282425600891543825005419 1923638401337315737508129)
        ·
          refine ⟨1442728801002986803131097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1923638401337315737508129 1442728801002986803131097)
          ·
            refine ⟨1082046600752240102348323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1442728801002986803131097 1082046600752240102348323)
            ·
              refine ⟨1623069901128360153522485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082046600752240102348323 1623069901128360153522485)
              ·
                refine ⟨152162803230783764392733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1623069901128360153522485 152162803230783764392733)
                ·
                  rfl

theorem cell20_1000134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1000134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000134 prefixEnd_1000134 := by exact prefixLift 1000134
  have htrace : WordTrace (prefixWord ++ tailWord_1000134) baseStart_1000134 baseEnd_1000134 := by
    simpa [prefixWord, tailWord_1000134, baseEnd_1000134] using wordTrace_append hprefix tailTrace_1000134
  have hstable : (prefixWord ++ tailWord_1000134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000134).length < 2 ^ (prefixWord ++ tailWord_1000134).sum := by decide
  have hdescent : baseEnd_1000134 < baseStart_1000134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000159 : List Nat := [1, 1, 2, 3, 2, 4, 3, 4]
def baseStart_1000159 : Nat := 118140960795 + 1000159 * 2 ^ 59
def prefixEnd_1000159 : Nat := 4983230072969 + 3 ^ 40 * 1000159 * 2
def baseEnd_1000159 : Nat := 152166606791187439114921

theorem tailTrace_1000159 : CollatzResearch.WordTrace tailWord_1000159 prefixEnd_1000159 152166606791187439114921 := by
  unfold tailWord_1000159
  simp only [CollatzResearch.WordTrace]
  refine ⟨36478795583602231403147531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24319197055734820935431687 36478795583602231403147531)
  ·
    refine ⟨54718193375403347104721297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36478795583602231403147531 54718193375403347104721297)
    ·
      refine ⟨41038645031552510328540973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54718193375403347104721297 41038645031552510328540973)
      ·
        refine ⟨15389491886832191373202865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41038645031552510328540973 15389491886832191373202865)
        ·
          refine ⟨11542118915124143529902149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15389491886832191373202865 11542118915124143529902149)
          ·
            refine ⟨2164147296585776911856653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11542118915124143529902149 2164147296585776911856653)
            ·
              refine ⟨811555236219666341946245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2164147296585776911856653 811555236219666341946245)
              ·
                refine ⟨152166606791187439114921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 811555236219666341946245 152166606791187439114921)
                ·
                  rfl

theorem cell20_1000159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 4].length) (baseStart_1000159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000159 prefixEnd_1000159 := by exact prefixLift 1000159
  have htrace : WordTrace (prefixWord ++ tailWord_1000159) baseStart_1000159 baseEnd_1000159 := by
    simpa [prefixWord, tailWord_1000159, baseEnd_1000159] using wordTrace_append hprefix tailTrace_1000159
  have hstable : (prefixWord ++ tailWord_1000159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000159).length < 2 ^ (prefixWord ++ tailWord_1000159).sum := by decide
  have hdescent : baseEnd_1000159 < baseStart_1000159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000173 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1000173 : Nat := 118140960795 + 1000173 * 2 ^ 59
def prefixEnd_1000173 : Nat := 4983230072969 + 3 ^ 40 * 1000173 * 2
def baseEnd_1000173 : Nat := 456506210355040490878039

theorem tailTrace_1000173 : CollatzResearch.WordTrace tailWord_1000173 prefixEnd_1000173 456506210355040490878039 := by
  unfold tailWord_1000173
  simp only [CollatzResearch.WordTrace]
  refine ⟨36479306205551511794157173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24319537470367674529438115 36479306205551511794157173)
  ·
    refine ⟨3419934956770454230702235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36479306205551511794157173 3419934956770454230702235)
    ·
      refine ⟨5129902435155681346053353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3419934956770454230702235 5129902435155681346053353)
      ·
        refine ⟨3847426826366761009540015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5129902435155681346053353 3847426826366761009540015)
        ·
          refine ⟨5771140239550141514310023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847426826366761009540015 5771140239550141514310023)
          ·
            refine ⟨8656710359325212271465035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771140239550141514310023 8656710359325212271465035)
            ·
              refine ⟨12985065538987818407197553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656710359325212271465035 12985065538987818407197553)
              ·
                refine ⟨9738799154240863805398165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12985065538987818407197553 9738799154240863805398165)
                ·
                  refine ⟨456506210355040490878039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9738799154240863805398165 456506210355040490878039)
                  ·
                    rfl

theorem cell20_1000173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1000173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000173 prefixEnd_1000173 := by exact prefixLift 1000173
  have htrace : WordTrace (prefixWord ++ tailWord_1000173) baseStart_1000173 baseEnd_1000173 := by
    simpa [prefixWord, tailWord_1000173, baseEnd_1000173] using wordTrace_append hprefix tailTrace_1000173
  have hstable : (prefixWord ++ tailWord_1000173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000173).length < 2 ^ (prefixWord ++ tailWord_1000173).sum := by decide
  have hdescent : baseEnd_1000173 < baseStart_1000173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000190 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1000190 : Nat := 118140960795 + 1000190 * 2 ^ 59
def prefixEnd_1000190 : Nat := 4983230072969 + 3 ^ 40 * 1000190 * 2
def baseEnd_1000190 : Nat := 456513969618263987311303

theorem tailTrace_1000190 : CollatzResearch.WordTrace tailWord_1000190 prefixEnd_1000190 456513969618263987311303 := by
  unfold tailWord_1000190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559990780811240462190753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24319950830993282465017349 4559990780811240462190753)
  ·
    refine ⟨3419993085608430346643065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4559990780811240462190753 3419993085608430346643065)
    ·
      refine ⟨2564994814206322759982299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3419993085608430346643065 2564994814206322759982299)
      ·
        refine ⟨3847492221309484139973449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564994814206322759982299 3847492221309484139973449)
        ·
          refine ⟨2885619165982113104980087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3847492221309484139973449 2885619165982113104980087)
          ·
            refine ⟨4328428748973169657470131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885619165982113104980087 4328428748973169657470131)
            ·
              refine ⟨6492643123459754486205197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328428748973169657470131 6492643123459754486205197)
              ·
                refine ⟨2434741171297407932326949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6492643123459754486205197 2434741171297407932326949)
                ·
                  refine ⟨456513969618263987311303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2434741171297407932326949 456513969618263987311303)
                  ·
                    rfl

theorem cell20_1000190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1000190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000190 prefixEnd_1000190 := by exact prefixLift 1000190
  have htrace : WordTrace (prefixWord ++ tailWord_1000190) baseStart_1000190 baseEnd_1000190 := by
    simpa [prefixWord, tailWord_1000190, baseEnd_1000190] using wordTrace_append hprefix tailTrace_1000190
  have hstable : (prefixWord ++ tailWord_1000190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000190).length < 2 ^ (prefixWord ++ tailWord_1000190).sum := by decide
  have hdescent : baseEnd_1000190 < baseStart_1000190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000210 : List Nat := [3, 2, 4, 1, 3, 1, 2, 4]
def baseStart_1000210 : Nat := 118140960795 + 1000210 * 2 ^ 59
def prefixEnd_1000210 : Nat := 4983230072969 + 3 ^ 40 * 1000210 * 2
def baseEnd_1000210 : Nat := 152174366054410935548185

theorem tailTrace_1000210 : CollatzResearch.WordTrace tailWord_1000210 prefixEnd_1000210 152174366054410935548185 := by
  unfold tailWord_1000210
  simp only [CollatzResearch.WordTrace]
  refine ⟨9120163926604366778313521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24320437137611644742169389 9120163926604366778313521)
  ·
    refine ⟨6840122944953275083735141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9120163926604366778313521 6840122944953275083735141)
    ·
      refine ⟨1282523052178739078200339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6840122944953275083735141 1282523052178739078200339)
      ·
        refine ⟨1923784578268108617300509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282523052178739078200339 1923784578268108617300509)
        ·
          refine ⟨721419216850540731487691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1923784578268108617300509 721419216850540731487691)
          ·
            refine ⟨1082128825275811097231537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721419216850540731487691 1082128825275811097231537)
            ·
              refine ⟨811596618956858322923653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082128825275811097231537 811596618956858322923653)
              ·
                refine ⟨152174366054410935548185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 811596618956858322923653 152174366054410935548185)
                ·
                  rfl

theorem cell20_1000210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_1000210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000210 prefixEnd_1000210 := by exact prefixLift 1000210
  have htrace : WordTrace (prefixWord ++ tailWord_1000210) baseStart_1000210 baseEnd_1000210 := by
    simpa [prefixWord, tailWord_1000210, baseEnd_1000210] using wordTrace_append hprefix tailTrace_1000210
  have hstable : (prefixWord ++ tailWord_1000210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000210).length < 2 ^ (prefixWord ++ tailWord_1000210).sum := by decide
  have hdescent : baseEnd_1000210 < baseStart_1000210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000218 : List Nat := [3, 1, 1, 3, 2, 1, 3, 6]
def baseStart_1000218 : Nat := 118140960795 + 1000218 * 2 ^ 59
def prefixEnd_1000218 : Nat := 4983230072969 + 3 ^ 40 * 1000218 * 2
def baseEnd_1000218 : Nat := 152175583193740111459285

theorem tailTrace_1000218 : CollatzResearch.WordTrace tailWord_1000218 prefixEnd_1000218 152175583193740111459285 := by
  unfold tailWord_1000218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9120236872597121119886327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24320631660258989653030205 9120236872597121119886327)
  ·
    refine ⟨13680355308895681679829491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9120236872597121119886327 13680355308895681679829491)
    ·
      refine ⟨20520532963343522519744237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13680355308895681679829491 20520532963343522519744237)
      ·
        refine ⟨7695199861253820944904089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20520532963343522519744237 7695199861253820944904089)
        ·
          refine ⟨5771399895940365708678067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7695199861253820944904089 5771399895940365708678067)
          ·
            refine ⟨8657099843910548563017101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771399895940365708678067 8657099843910548563017101)
            ·
              refine ⟨3246412441466455711131413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8657099843910548563017101 3246412441466455711131413)
              ·
                refine ⟨152175583193740111459285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3246412441466455711131413 152175583193740111459285)
                ·
                  rfl

theorem cell20_1000218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_1000218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000218 prefixEnd_1000218 := by exact prefixLift 1000218
  have htrace : WordTrace (prefixWord ++ tailWord_1000218) baseStart_1000218 baseEnd_1000218 := by
    simpa [prefixWord, tailWord_1000218, baseEnd_1000218] using wordTrace_append hprefix tailTrace_1000218
  have hstable : (prefixWord ++ tailWord_1000218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000218).length < 2 ^ (prefixWord ++ tailWord_1000218).sum := by decide
  have hdescent : baseEnd_1000218 < baseStart_1000218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000225 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_1000225 : Nat := 118140960795 + 1000225 * 2 ^ 59
def prefixEnd_1000225 : Nat := 4983230072969 + 3 ^ 40 * 1000225 * 2
def baseEnd_1000225 : Nat := 456529944571959421144493

theorem tailTrace_1000225 : CollatzResearch.WordTrace tailWord_1000225 prefixEnd_1000225 456529944571959421144493 := by
  unfold tailWord_1000225
  simp only [CollatzResearch.WordTrace]
  refine ⟨36481202801363124675050129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24320801867575416450033419 36481202801363124675050129)
  ·
    refine ⟨27360902101022343506287597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36481202801363124675050129 27360902101022343506287597)
    ·
      refine ⟨10260338287883378814857849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27360902101022343506287597 10260338287883378814857849)
      ·
        refine ⟨7695253715912534111143387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10260338287883378814857849 7695253715912534111143387)
        ·
          refine ⟨11542880573868801166715081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695253715912534111143387 11542880573868801166715081)
          ·
            refine ⟨8657160430401600875036311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11542880573868801166715081 8657160430401600875036311)
            ·
              refine ⟨12985740645602401312554467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8657160430401600875036311 12985740645602401312554467)
              ·
                refine ⟨19478610968403601968831701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12985740645602401312554467 19478610968403601968831701)
                ·
                  refine ⟨456529944571959421144493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19478610968403601968831701 456529944571959421144493)
                  ·
                    rfl

theorem cell20_1000225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_1000225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000225 prefixEnd_1000225 := by exact prefixLift 1000225
  have htrace : WordTrace (prefixWord ++ tailWord_1000225) baseStart_1000225 baseEnd_1000225 := by
    simpa [prefixWord, tailWord_1000225, baseEnd_1000225] using wordTrace_append hprefix tailTrace_1000225
  have hstable : (prefixWord ++ tailWord_1000225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000225).length < 2 ^ (prefixWord ++ tailWord_1000225).sum := by decide
  have hdescent : baseEnd_1000225 < baseStart_1000225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000242 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_1000242 : Nat := 118140960795 + 1000242 * 2 ^ 59
def prefixEnd_1000242 : Nat := 4983230072969 + 3 ^ 40 * 1000242 * 2
def baseEnd_1000242 : Nat := 456537703835182917577757

theorem tailTrace_1000242 : CollatzResearch.WordTrace tailWord_1000242 prefixEnd_1000242 456537703835182917577757 := by
  unfold tailWord_1000242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9120455710575384144604745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24321215228201024385612653 9120455710575384144604745)
  ·
    refine ⟨6840341782931538108453559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9120455710575384144604745 6840341782931538108453559)
    ·
      refine ⟨10260512674397307162680339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6840341782931538108453559 10260512674397307162680339)
      ·
        refine ⟨15390769011595960744020509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260512674397307162680339 15390769011595960744020509)
        ·
          refine ⟨5771538379348485279007691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15390769011595960744020509 5771538379348485279007691)
          ·
            refine ⟨8657307569022727918511537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771538379348485279007691 8657307569022727918511537)
            ·
              refine ⟨6492980676767045938883653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8657307569022727918511537 6492980676767045938883653)
              ·
                refine ⟨1217433876893821113540685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6492980676767045938883653 1217433876893821113540685)
                ·
                  refine ⟨456537703835182917577757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217433876893821113540685 456537703835182917577757)
                  ·
                    rfl

theorem cell20_1000242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_1000242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000242 prefixEnd_1000242 := by exact prefixLift 1000242
  have htrace : WordTrace (prefixWord ++ tailWord_1000242) baseStart_1000242 baseEnd_1000242 := by
    simpa [prefixWord, tailWord_1000242, baseEnd_1000242] using wordTrace_append hprefix tailTrace_1000242
  have hstable : (prefixWord ++ tailWord_1000242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000242).length < 2 ^ (prefixWord ++ tailWord_1000242).sum := by decide
  have hdescent : baseEnd_1000242 < baseStart_1000242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000325 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1000325 : Nat := 118140960795 + 1000325 * 2 ^ 59
def prefixEnd_1000325 : Nat := 4983230072969 + 3 ^ 40 * 1000325 * 2
def baseEnd_1000325 : Nat := 456575587296803517810751

theorem tailTrace_1000325 : CollatzResearch.WordTrace tailWord_1000325 prefixEnd_1000325 456575587296803517810751 := by
  unfold tailWord_1000325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36484850101000841753690429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24323233400667227835793619 36484850101000841753690429)
  ·
    refine ⟨13681818787875315657633911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36484850101000841753690429 13681818787875315657633911)
    ·
      refine ⟨20522728181812973486450867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13681818787875315657633911 20522728181812973486450867)
      ·
        refine ⟨30784092272719460229676301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20522728181812973486450867 30784092272719460229676301)
        ·
          refine ⟨11544034602269797586128613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30784092272719460229676301 11544034602269797586128613)
          ·
            refine ⟨2164506487925587047399115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11544034602269797586128613 2164506487925587047399115)
            ·
              refine ⟨3246759731888380571098673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164506487925587047399115 3246759731888380571098673)
              ·
                refine ⟨2435069798916285428324005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246759731888380571098673 2435069798916285428324005)
                ·
                  refine ⟨456575587296803517810751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2435069798916285428324005 456575587296803517810751)
                  ·
                    rfl

theorem cell20_1000325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1000325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000325 prefixEnd_1000325 := by exact prefixLift 1000325
  have htrace : WordTrace (prefixWord ++ tailWord_1000325) baseStart_1000325 baseEnd_1000325 := by
    simpa [prefixWord, tailWord_1000325, baseEnd_1000325] using wordTrace_append hprefix tailTrace_1000325
  have hstable : (prefixWord ++ tailWord_1000325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000325).length < 2 ^ (prefixWord ++ tailWord_1000325).sum := by decide
  have hdescent : baseEnd_1000325 < baseStart_1000325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000338 : List Nat := [3, 2, 3, 2, 2, 1, 2, 3, 2]
def baseStart_1000338 : Nat := 118140960795 + 1000338 * 2 ^ 59
def prefixEnd_1000338 : Nat := 4983230072969 + 3 ^ 40 * 1000338 * 2
def baseEnd_1000338 : Nat := 456581520851033250377365

theorem tailTrace_1000338 : CollatzResearch.WordTrace tailWord_1000338 prefixEnd_1000338 456581520851033250377365 := by
  unfold tailWord_1000338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9121331062488436243478417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24323549499969163315942445 9121331062488436243478417)
  ·
    refine ⟨6840998296866327182608813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9121331062488436243478417 6840998296866327182608813)
    ·
      refine ⟨2565374361324872693478305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6840998296866327182608813 2565374361324872693478305)
      ·
        refine ⟨1924030770993654520108729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2565374361324872693478305 1924030770993654520108729)
        ·
          refine ⟨1443023078245240890081547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1924030770993654520108729 1443023078245240890081547)
          ·
            refine ⟨2164534617367861335122321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443023078245240890081547 2164534617367861335122321)
            ·
              refine ⟨1623400963025896001341741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164534617367861335122321 1623400963025896001341741)
              ·
                refine ⟨608775361134711000503153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1623400963025896001341741 608775361134711000503153)
                ·
                  refine ⟨456581520851033250377365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608775361134711000503153 456581520851033250377365)
                  ·
                    rfl

theorem cell20_1000338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_1000338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000338 prefixEnd_1000338 := by exact prefixLift 1000338
  have htrace : WordTrace (prefixWord ++ tailWord_1000338) baseStart_1000338 baseEnd_1000338 := by
    simpa [prefixWord, tailWord_1000338, baseEnd_1000338] using wordTrace_append hprefix tailTrace_1000338
  have hstable : (prefixWord ++ tailWord_1000338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000338).length < 2 ^ (prefixWord ++ tailWord_1000338).sum := by decide
  have hdescent : baseEnd_1000338 < baseStart_1000338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000373 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 3]
def baseStart_1000373 : Nat := 118140960795 + 1000373 * 2 ^ 59
def prefixEnd_1000373 : Nat := 4983230072969 + 3 ^ 40 * 1000373 * 2
def baseEnd_1000373 : Nat := 456597495804728684210555

theorem tailTrace_1000373 : CollatzResearch.WordTrace tailWord_1000373 prefixEnd_1000373 456597495804728684210555 := by
  unfold tailWord_1000373
  simp only [CollatzResearch.WordTrace]
  refine ⟨36486600804826945951437773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24324400536551297300958515 36486600804826945951437773)
  ·
    refine ⟨13682475301810104731789165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36486600804826945951437773 13682475301810104731789165)
    ·
      refine ⟨5130928238178789274420937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13682475301810104731789165 5130928238178789274420937)
      ·
        refine ⟨3848196178634091955815703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5130928238178789274420937 3848196178634091955815703)
        ·
          refine ⟨5772294267951137933723555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848196178634091955815703 5772294267951137933723555)
          ·
            refine ⟨8658441401926706900585333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772294267951137933723555 8658441401926706900585333)
            ·
              refine ⟨811728881430628771929875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8658441401926706900585333 811728881430628771929875)
              ·
                refine ⟨1217593322145943157894813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811728881430628771929875 1217593322145943157894813)
                ·
                  refine ⟨456597495804728684210555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217593322145943157894813 456597495804728684210555)
                  ·
                    rfl

theorem cell20_1000373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_1000373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000373 prefixEnd_1000373 := by exact prefixLift 1000373
  have htrace : WordTrace (prefixWord ++ tailWord_1000373) baseStart_1000373 baseEnd_1000373 := by
    simpa [prefixWord, tailWord_1000373, baseEnd_1000373] using wordTrace_append hprefix tailTrace_1000373
  have hstable : (prefixWord ++ tailWord_1000373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000373).length < 2 ^ (prefixWord ++ tailWord_1000373).sum := by decide
  have hdescent : baseEnd_1000373 < baseStart_1000373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000408 : List Nat := [2, 1, 2, 2, 2, 5, 6]
def baseStart_1000408 : Nat := 118140960795 + 1000408 * 2 ^ 59
def prefixEnd_1000408 : Nat := 4983230072969 + 3 ^ 40 * 1000408 * 2
def baseEnd_1000408 : Nat := 50734830084269346449305

theorem tailTrace_1000408 : CollatzResearch.WordTrace tailWord_1000408 prefixEnd_1000408 50734830084269346449305 := by
  unfold tailWord_1000408
  simp only [CollatzResearch.WordTrace]
  refine ⟨18243938679850073464480939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24325251573133431285974585 18243938679850073464480939)
  ·
    refine ⟨27365908019775110196721409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18243938679850073464480939 27365908019775110196721409)
    ·
      refine ⟨20524431014831332647541057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27365908019775110196721409 20524431014831332647541057)
      ·
        refine ⟨15393323261123499485655793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20524431014831332647541057 15393323261123499485655793)
        ·
          refine ⟨11544992445842624614241845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15393323261123499485655793 11544992445842624614241845)
          ·
            refine ⟨1082343041797746057585173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11544992445842624614241845 1082343041797746057585173)
            ·
              refine ⟨50734830084269346449305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1082343041797746057585173 50734830084269346449305)
              ·
                rfl

theorem cell20_1000408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 6].length) (baseStart_1000408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000408 prefixEnd_1000408 := by exact prefixLift 1000408
  have htrace : WordTrace (prefixWord ++ tailWord_1000408) baseStart_1000408 baseEnd_1000408 := by
    simpa [prefixWord, tailWord_1000408, baseEnd_1000408] using wordTrace_append hprefix tailTrace_1000408
  have hstable : (prefixWord ++ tailWord_1000408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000408).length < 2 ^ (prefixWord ++ tailWord_1000408).sum := by decide
  have hdescent : baseEnd_1000408 < baseStart_1000408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000480 : List Nat := [2, 1, 1, 7, 1, 2, 1, 5]
def baseStart_1000480 : Nat := 118140960795 + 1000480 * 2 ^ 59
def prefixEnd_1000480 : Nat := 4983230072969 + 3 ^ 40 * 1000480 * 2
def baseEnd_1000480 : Nat := 152215444506770622547817

theorem tailTrace_1000480 : CollatzResearch.WordTrace tailWord_1000480 prefixEnd_1000480 152215444506770622547817 := by
  unfold tailWord_1000480
  simp only [CollatzResearch.WordTrace]
  refine ⟨18245251707719651612791447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24327002276959535483721929 18245251707719651612791447)
  ·
    refine ⟨27367877561579477419187171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18245251707719651612791447 27367877561579477419187171)
    ·
      refine ⟨41051816342369216128780757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27367877561579477419187171 41051816342369216128780757)
      ·
        refine ⟨962151945524278503018299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41051816342369216128780757 962151945524278503018299)
        ·
          refine ⟨1443227918286417754527449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962151945524278503018299 1443227918286417754527449)
          ·
            refine ⟨1082420938714813315895587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1443227918286417754527449 1082420938714813315895587)
            ·
              refine ⟨1623631408072219973843381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082420938714813315895587 1623631408072219973843381)
              ·
                refine ⟨152215444506770622547817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1623631408072219973843381 152215444506770622547817)
                ·
                  rfl

theorem cell20_1000480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_1000480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000480 prefixEnd_1000480 := by exact prefixLift 1000480
  have htrace : WordTrace (prefixWord ++ tailWord_1000480) baseStart_1000480 baseEnd_1000480 := by
    simpa [prefixWord, tailWord_1000480, baseEnd_1000480] using wordTrace_append hprefix tailTrace_1000480
  have hstable : (prefixWord ++ tailWord_1000480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000480).length < 2 ^ (prefixWord ++ tailWord_1000480).sum := by decide
  have hdescent : baseEnd_1000480 < baseStart_1000480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000487 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 3]
def baseStart_1000487 : Nat := 118140960795 + 1000487 * 2 ^ 59
def prefixEnd_1000487 : Nat := 4983230072969 + 3 ^ 40 * 1000487 * 2
def baseEnd_1000487 : Nat := 456649528511050954410089

theorem tailTrace_1000487 : CollatzResearch.WordTrace tailWord_1000487 prefixEnd_1000487 456649528511050954410089 := by
  unfold tailWord_1000487
  simp only [CollatzResearch.WordTrace]
  refine ⟨36490758726413943421087715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24327172484275962280725143 36490758726413943421087715)
  ·
    refine ⟨54736138089620915131631573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36490758726413943421087715 54736138089620915131631573)
    ·
      refine ⟨1282878236475490198397615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 54736138089620915131631573 1282878236475490198397615)
      ·
        refine ⟨1924317354713235297596423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282878236475490198397615 1924317354713235297596423)
        ·
          refine ⟨2886476032069852946394635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924317354713235297596423 2886476032069852946394635)
          ·
            refine ⟨4329714048104779419591953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886476032069852946394635 4329714048104779419591953)
            ·
              refine ⟨3247285536078584564693965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4329714048104779419591953 3247285536078584564693965)
              ·
                refine ⟨1217732076029469211760237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3247285536078584564693965 1217732076029469211760237)
                ·
                  refine ⟨456649528511050954410089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217732076029469211760237 456649528511050954410089)
                  ·
                    rfl

theorem cell20_1000487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 3].length) (baseStart_1000487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000487 prefixEnd_1000487 := by exact prefixLift 1000487
  have htrace : WordTrace (prefixWord ++ tailWord_1000487) baseStart_1000487 baseEnd_1000487 := by
    simpa [prefixWord, tailWord_1000487, baseEnd_1000487] using wordTrace_append hprefix tailTrace_1000487
  have hstable : (prefixWord ++ tailWord_1000487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000487).length < 2 ^ (prefixWord ++ tailWord_1000487).sum := by decide
  have hdescent : baseEnd_1000487 < baseStart_1000487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000491 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 3]
def baseStart_1000491 : Nat := 118140960795 + 1000491 * 2 ^ 59
def prefixEnd_1000491 : Nat := 4983230072969 + 3 ^ 40 * 1000491 * 2
def baseEnd_1000491 : Nat := 456651354220044718276739

theorem tailTrace_1000491 : CollatzResearch.WordTrace tailWord_1000491 prefixEnd_1000491 456651354220044718276739 := by
  unfold tailWord_1000491
  simp only [CollatzResearch.WordTrace]
  refine ⟨36490904618399452104233327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24327269745599634736155551 36490904618399452104233327)
  ·
    refine ⟨54736356927599178156349991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36490904618399452104233327 54736356927599178156349991)
    ·
      refine ⟨82104535391398767234524987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54736356927599178156349991 82104535391398767234524987)
      ·
        refine ⟨123156803087098150851787481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82104535391398767234524987 123156803087098150851787481)
        ·
          refine ⟨92367602315323613138840611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123156803087098150851787481 92367602315323613138840611)
          ·
            refine ⟨138551403472985419708260917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92367602315323613138840611 138551403472985419708260917)
            ·
              refine ⟨12989194075592383097649461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138551403472985419708260917 12989194075592383097649461)
              ·
                refine ⟨1217736944586785915404637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12989194075592383097649461 1217736944586785915404637)
                ·
                  refine ⟨456651354220044718276739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217736944586785915404637 456651354220044718276739)
                  ·
                    rfl

theorem cell20_1000491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 3].length) (baseStart_1000491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000491 prefixEnd_1000491 := by exact prefixLift 1000491
  have htrace : WordTrace (prefixWord ++ tailWord_1000491) baseStart_1000491 baseEnd_1000491 := by
    simpa [prefixWord, tailWord_1000491, baseEnd_1000491] using wordTrace_append hprefix tailTrace_1000491
  have hstable : (prefixWord ++ tailWord_1000491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000491).length < 2 ^ (prefixWord ++ tailWord_1000491).sum := by decide
  have hdescent : baseEnd_1000491 < baseStart_1000491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000525 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1000525 : Nat := 118140960795 + 1000525 * 2 ^ 59
def prefixEnd_1000525 : Nat := 4983230072969 + 3 ^ 40 * 1000525 * 2
def baseEnd_1000525 : Nat := 456666872746491711143267

theorem tailTrace_1000525 : CollatzResearch.WordTrace tailWord_1000525 prefixEnd_1000525 456666872746491711143267 := by
  unfold tailWord_1000525
  simp only [CollatzResearch.WordTrace]
  refine ⟨36492144700276275910971029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24328096466850850607314019 36492144700276275910971029)
  ·
    refine ⟨1710569282825450433326767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36492144700276275910971029 1710569282825450433326767)
    ·
      refine ⟨2565853924238175649990151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710569282825450433326767 2565853924238175649990151)
      ·
        refine ⟨3848780886357263474985227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565853924238175649990151 3848780886357263474985227)
        ·
          refine ⟨5773171329535895212477841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848780886357263474985227 5773171329535895212477841)
          ·
            refine ⟨4329878497151921409358381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5773171329535895212477841 4329878497151921409358381)
            ·
              refine ⟨1623704436431970528509393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4329878497151921409358381 1623704436431970528509393)
              ·
                refine ⟨1217778327323977896382045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1623704436431970528509393 1217778327323977896382045)
                ·
                  refine ⟨456666872746491711143267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217778327323977896382045 456666872746491711143267)
                  ·
                    rfl

theorem cell20_1000525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1000525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000525 prefixEnd_1000525 := by exact prefixLift 1000525
  have htrace : WordTrace (prefixWord ++ tailWord_1000525) baseStart_1000525 baseEnd_1000525 := by
    simpa [prefixWord, tailWord_1000525, baseEnd_1000525] using wordTrace_append hprefix tailTrace_1000525
  have hstable : (prefixWord ++ tailWord_1000525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000525).length < 2 ^ (prefixWord ++ tailWord_1000525).sum := by decide
  have hdescent : baseEnd_1000525 < baseStart_1000525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000532 : List Nat := [2, 4, 1, 1, 1, 1, 4, 4, 2]
def baseStart_1000532 : Nat := 118140960795 + 1000532 * 2 ^ 59
def prefixEnd_1000532 : Nat := 4983230072969 + 3 ^ 40 * 1000532 * 2
def baseEnd_1000532 : Nat := 456670067737230797909905

theorem tailTrace_1000532 : CollatzResearch.WordTrace tailWord_1000532 prefixEnd_1000532 456670067737230797909905 := by
  unfold tailWord_1000532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18246200005625458053237925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24328266674167277404317233 18246200005625458053237925)
  ·
    refine ⟨3421162501054773384982111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18246200005625458053237925 3421162501054773384982111)
    ·
      refine ⟨5131743751582160077473167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421162501054773384982111 5131743751582160077473167)
      ·
        refine ⟨7697615627373240116209751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131743751582160077473167 7697615627373240116209751)
        ·
          refine ⟨11546423441059860174314627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7697615627373240116209751 11546423441059860174314627)
          ·
            refine ⟨17319635161589790261471941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11546423441059860174314627 17319635161589790261471941)
            ·
              refine ⟨3247431592798085674025989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17319635161589790261471941 3247431592798085674025989)
              ·
                refine ⟨608893423649641063879873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3247431592798085674025989 608893423649641063879873)
                ·
                  refine ⟨456670067737230797909905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608893423649641063879873 456670067737230797909905)
                  ·
                    rfl

theorem cell20_1000532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_1000532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000532 prefixEnd_1000532 := by exact prefixLift 1000532
  have htrace : WordTrace (prefixWord ++ tailWord_1000532) baseStart_1000532 baseEnd_1000532 := by
    simpa [prefixWord, tailWord_1000532, baseEnd_1000532] using wordTrace_append hprefix tailTrace_1000532
  have hstable : (prefixWord ++ tailWord_1000532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000532).length < 2 ^ (prefixWord ++ tailWord_1000532).sum := by decide
  have hdescent : baseEnd_1000532 < baseStart_1000532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000543 : List Nat := [1, 1, 2, 3, 1, 1, 4, 7]
def baseStart_1000543 : Nat := 118140960795 + 1000543 * 2 ^ 59
def prefixEnd_1000543 : Nat := 4983230072969 + 3 ^ 40 * 1000543 * 2
def baseEnd_1000543 : Nat := 152225029478987882847731

theorem tailTrace_1000543 : CollatzResearch.WordTrace tailWord_1000543 prefixEnd_1000543 152225029478987882847731 := by
  unfold tailWord_1000543
  simp only [CollatzResearch.WordTrace]
  refine ⟨36492801214211064985126283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24328534142807376656750855 36492801214211064985126283)
  ·
    refine ⟨54739201821316597477689425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36492801214211064985126283 54739201821316597477689425)
    ·
      refine ⟨41054401365987448108267069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54739201821316597477689425 41054401365987448108267069)
      ·
        refine ⟨15395400512245293040600151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41054401365987448108267069 15395400512245293040600151)
        ·
          refine ⟨23093100768367939560900227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15395400512245293040600151 23093100768367939560900227)
          ·
            refine ⟨34639651152551909341350341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23093100768367939560900227 34639651152551909341350341)
            ·
              refine ⟨6494934591103483001503189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34639651152551909341350341 6494934591103483001503189)
              ·
                refine ⟨152225029478987882847731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6494934591103483001503189 152225029478987882847731)
                ·
                  rfl

theorem cell20_1000543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_1000543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000543 prefixEnd_1000543 := by exact prefixLift 1000543
  have htrace : WordTrace (prefixWord ++ tailWord_1000543) baseStart_1000543 baseEnd_1000543 := by
    simpa [prefixWord, tailWord_1000543, baseEnd_1000543] using wordTrace_append hprefix tailTrace_1000543
  have hstable : (prefixWord ++ tailWord_1000543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000543).length < 2 ^ (prefixWord ++ tailWord_1000543).sum := by decide
  have hdescent : baseEnd_1000543 < baseStart_1000543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000684 : List Nat := [2, 2, 1, 1, 2, 5, 2, 3, 2]
def baseStart_1000684 : Nat := 118140960795 + 1000684 * 2 ^ 59
def prefixEnd_1000684 : Nat := 4983230072969 + 3 ^ 40 * 1000684 * 2
def baseEnd_1000684 : Nat := 456739444678993824842617

theorem tailTrace_1000684 : CollatzResearch.WordTrace tailWord_1000684 prefixEnd_1000684 456739444678993824842617 := by
  unfold tailWord_1000684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18248971953350123033004553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24331962604466830710672737 18248971953350123033004553)
  ·
    refine ⟨13686728965012592274753415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18248971953350123033004553 13686728965012592274753415)
    ·
      refine ⟨20530093447518888412130123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13686728965012592274753415 20530093447518888412130123)
      ·
        refine ⟨30795140171278332618195185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20530093447518888412130123 30795140171278332618195185)
        ·
          refine ⟨23096355128458749463646389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30795140171278332618195185 23096355128458749463646389)
          ·
            refine ⟨2165283293293007762216849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23096355128458749463646389 2165283293293007762216849)
            ·
              refine ⟨1623962469969755821662637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165283293293007762216849 1623962469969755821662637)
              ·
                refine ⟨608985926238658433123489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1623962469969755821662637 608985926238658433123489)
                ·
                  refine ⟨456739444678993824842617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608985926238658433123489 456739444678993824842617)
                  ·
                    rfl

theorem cell20_1000684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_1000684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000684 prefixEnd_1000684 := by exact prefixLift 1000684
  have htrace : WordTrace (prefixWord ++ tailWord_1000684) baseStart_1000684 baseEnd_1000684 := by
    simpa [prefixWord, tailWord_1000684, baseEnd_1000684] using wordTrace_append hprefix tailTrace_1000684
  have hstable : (prefixWord ++ tailWord_1000684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000684).length < 2 ^ (prefixWord ++ tailWord_1000684).sum := by decide
  have hdescent : baseEnd_1000684 < baseStart_1000684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000705 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 4]
def baseStart_1000705 : Nat := 118140960795 + 1000705 * 2 ^ 59
def prefixEnd_1000705 : Nat := 4983230072969 + 3 ^ 40 * 1000705 * 2
def baseEnd_1000705 : Nat := 456749029651211085142531

theorem tailTrace_1000705 : CollatzResearch.WordTrace tailWord_1000705 prefixEnd_1000705 456749029651211085142531 := by
  unfold tailWord_1000705
  simp only [CollatzResearch.WordTrace]
  refine ⟨36498709839624166652523569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24332473226416111101682379 36498709839624166652523569)
  ·
    refine ⟨27374032379718124989392677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36498709839624166652523569 27374032379718124989392677)
    ·
      refine ⟨5132631071197148435511127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27374032379718124989392677 5132631071197148435511127)
      ·
        refine ⟨7698946606795722653266691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132631071197148435511127 7698946606795722653266691)
        ·
          refine ⟨11548419910193583979900037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7698946606795722653266691 11548419910193583979900037)
          ·
            refine ⟨2165328733161296996231257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11548419910193583979900037 2165328733161296996231257)
            ·
              refine ⟨1623996549870972747173443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165328733161296996231257 1623996549870972747173443)
              ·
                refine ⟨2435994824806459120760165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623996549870972747173443 2435994824806459120760165)
                ·
                  refine ⟨456749029651211085142531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2435994824806459120760165 456749029651211085142531)
                  ·
                    rfl

theorem cell20_1000705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_1000705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000705 prefixEnd_1000705 := by exact prefixLift 1000705
  have htrace : WordTrace (prefixWord ++ tailWord_1000705) baseStart_1000705 baseEnd_1000705 := by
    simpa [prefixWord, tailWord_1000705, baseEnd_1000705] using wordTrace_append hprefix tailTrace_1000705
  have hstable : (prefixWord ++ tailWord_1000705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000705).length < 2 ^ (prefixWord ++ tailWord_1000705).sum := by decide
  have hdescent : baseEnd_1000705 < baseStart_1000705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000757 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1000757 : Nat := 118140960795 + 1000757 * 2 ^ 59
def prefixEnd_1000757 : Nat := 4983230072969 + 3 ^ 40 * 1000757 * 2
def baseEnd_1000757 : Nat := 456772763868130015408985

theorem tailTrace_1000757 : CollatzResearch.WordTrace tailWord_1000757 prefixEnd_1000757 456772763868130015408985 := by
  unfold tailWord_1000757
  simp only [CollatzResearch.WordTrace]
  refine ⟨36500606435435779533416525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24333737623623853022277683 36500606435435779533416525)
  ·
    refine ⟨13687727413288417325031197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36500606435435779533416525 13687727413288417325031197)
    ·
      refine ⟨5132897779983156496886699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13687727413288417325031197 5132897779983156496886699)
      ·
        refine ⟨7699346669974734745330049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132897779983156496886699 7699346669974734745330049)
        ·
          refine ⟨5774510002481051058997537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7699346669974734745330049 5774510002481051058997537)
          ·
            refine ⟨4330882501860788294248153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5774510002481051058997537 4330882501860788294248153)
            ·
              refine ⟨3248161876395591220686115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4330882501860788294248153 3248161876395591220686115)
              ·
                refine ⟨4872242814593386831029173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248161876395591220686115 4872242814593386831029173)
                ·
                  refine ⟨456772763868130015408985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4872242814593386831029173 456772763868130015408985)
                  ·
                    rfl

theorem cell20_1000757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1000757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000757 prefixEnd_1000757 := by exact prefixLift 1000757
  have htrace : WordTrace (prefixWord ++ tailWord_1000757) baseStart_1000757 baseEnd_1000757 := by
    simpa [prefixWord, tailWord_1000757, baseEnd_1000757] using wordTrace_append hprefix tailTrace_1000757
  have hstable : (prefixWord ++ tailWord_1000757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000757).length < 2 ^ (prefixWord ++ tailWord_1000757).sum := by decide
  have hdescent : baseEnd_1000757 < baseStart_1000757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000812 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 3]
def baseStart_1000812 : Nat := 118140960795 + 1000812 * 2 ^ 59
def prefixEnd_1000812 : Nat := 4983230072969 + 3 ^ 40 * 1000812 * 2
def baseEnd_1000812 : Nat := 456797867366794268575427

theorem tailTrace_1000812 : CollatzResearch.WordTrace tailWord_1000812 prefixEnd_1000812 456797867366794268575427 := by
  unfold tailWord_1000812
  simp only [CollatzResearch.WordTrace]
  refine ⟨18251306225118261963334345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24335074966824349284445793 18251306225118261963334345)
  ·
    refine ⟨13688479668838696472500759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18251306225118261963334345 13688479668838696472500759)
    ·
      refine ⟨20532719503258044708751139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13688479668838696472500759 20532719503258044708751139)
      ·
        refine ⟨30799079254887067063126709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20532719503258044708751139 30799079254887067063126709)
        ·
          refine ⟨2887413680145662537168129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30799079254887067063126709 2887413680145662537168129)
          ·
            refine ⟨2165560260109246902876097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2887413680145662537168129 2165560260109246902876097)
            ·
              refine ⟨1624170195081935177157073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165560260109246902876097 1624170195081935177157073)
              ·
                refine ⟨1218127646311451382867805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624170195081935177157073 1218127646311451382867805)
                ·
                  refine ⟨456797867366794268575427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218127646311451382867805 456797867366794268575427)
                  ·
                    rfl

theorem cell20_1000812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_1000812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000812 prefixEnd_1000812 := by exact prefixLift 1000812
  have htrace : WordTrace (prefixWord ++ tailWord_1000812) baseStart_1000812 baseEnd_1000812 := by
    simpa [prefixWord, tailWord_1000812, baseEnd_1000812] using wordTrace_append hprefix tailTrace_1000812
  have hstable : (prefixWord ++ tailWord_1000812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000812).length < 2 ^ (prefixWord ++ tailWord_1000812).sum := by decide
  have hdescent : baseEnd_1000812 < baseStart_1000812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000840 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_1000840 : Nat := 118140960795 + 1000840 * 2 ^ 59
def prefixEnd_1000840 : Nat := 4983230072969 + 3 ^ 40 * 1000840 * 2
def baseEnd_1000840 : Nat := 456810647329750615641979

theorem tailTrace_1000840 : CollatzResearch.WordTrace tailWord_1000840 prefixEnd_1000840 456810647329750615641979 := by
  unfold tailWord_1000840
  simp only [CollatzResearch.WordTrace]
  refine ⟨18251816847067542354343987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24335755796090056472458649 18251816847067542354343987)
  ·
    refine ⟨27377725270601313531515981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18251816847067542354343987 27377725270601313531515981)
    ·
      refine ⟨10266646976475492574318493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27377725270601313531515981 10266646976475492574318493)
      ·
        refine ⟨3849992616178309715369435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10266646976475492574318493 3849992616178309715369435)
        ·
          refine ⟨5774988924267464573054153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3849992616178309715369435 5774988924267464573054153)
          ·
            refine ⟨4331241693200598429790615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5774988924267464573054153 4331241693200598429790615)
            ·
              refine ⟨6496862539800897644685923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331241693200598429790615 6496862539800897644685923)
              ·
                refine ⟨9745293809701346467028885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6496862539800897644685923 9745293809701346467028885)
                ·
                  refine ⟨456810647329750615641979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9745293809701346467028885 456810647329750615641979)
                  ·
                    rfl

theorem cell20_1000840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_1000840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000840 prefixEnd_1000840 := by exact prefixLift 1000840
  have htrace : WordTrace (prefixWord ++ tailWord_1000840) baseStart_1000840 baseEnd_1000840 := by
    simpa [prefixWord, tailWord_1000840, baseEnd_1000840] using wordTrace_append hprefix tailTrace_1000840
  have hstable : (prefixWord ++ tailWord_1000840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000840).length < 2 ^ (prefixWord ++ tailWord_1000840).sum := by decide
  have hdescent : baseEnd_1000840 < baseStart_1000840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000857 : List Nat := [1, 2, 1, 2, 1, 5, 1, 5, 2]
def baseStart_1000857 : Nat := 118140960795 + 1000857 * 2 ^ 59
def prefixEnd_1000857 : Nat := 4983230072969 + 3 ^ 40 * 1000857 * 2
def baseEnd_1000857 : Nat := 456818406592974112075243

theorem tailTrace_1000857 : CollatzResearch.WordTrace tailWord_1000857 prefixEnd_1000857 456818406592974112075243 := by
  unfold tailWord_1000857
  simp only [CollatzResearch.WordTrace]
  refine ⟨36504253735073496612056825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24336169156715664408037883 36504253735073496612056825)
  ·
    refine ⟨27378190301305122459042619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36504253735073496612056825 27378190301305122459042619)
    ·
      refine ⟨41067285451957683688563929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27378190301305122459042619 41067285451957683688563929)
      ·
        refine ⟨30800464088968262766422947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41067285451957683688563929 30800464088968262766422947)
        ·
          refine ⟨46200696133452394149634421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30800464088968262766422947 46200696133452394149634421)
          ·
            refine ⟨4331315262511161951528227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46200696133452394149634421 4331315262511161951528227)
            ·
              refine ⟨6496972893766742927292341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331315262511161951528227 6496972893766742927292341)
              ·
                refine ⟨609091208790632149433657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6496972893766742927292341 609091208790632149433657)
                ·
                  refine ⟨456818406592974112075243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609091208790632149433657 456818406592974112075243)
                  ·
                    rfl

theorem cell20_1000857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_1000857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000857 prefixEnd_1000857 := by exact prefixLift 1000857
  have htrace : WordTrace (prefixWord ++ tailWord_1000857) baseStart_1000857 baseEnd_1000857 := by
    simpa [prefixWord, tailWord_1000857, baseEnd_1000857] using wordTrace_append hprefix tailTrace_1000857
  have hstable : (prefixWord ++ tailWord_1000857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000857).length < 2 ^ (prefixWord ++ tailWord_1000857).sum := by decide
  have hdescent : baseEnd_1000857 < baseStart_1000857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000871 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_1000871 : Nat := 118140960795 + 1000871 * 2 ^ 59
def prefixEnd_1000871 : Nat := 4983230072969 + 3 ^ 40 * 1000871 * 2
def baseEnd_1000871 : Nat := 456824796574452285608519

theorem tailTrace_1000871 : CollatzResearch.WordTrace tailWord_1000871 prefixEnd_1000871 456824796574452285608519 := by
  unfold tailWord_1000871
  simp only [CollatzResearch.WordTrace]
  refine ⟨36504764357022777003066467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24336509571348518002044311 36504764357022777003066467)
  ·
    refine ⟨54757146535534165504599701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36504764357022777003066467 54757146535534165504599701)
    ·
      refine ⟨2566741243853164008028111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54757146535534165504599701 2566741243853164008028111)
      ·
        refine ⟨3850111865779746012042167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566741243853164008028111 3850111865779746012042167)
        ·
          refine ⟨5775167798669619018063251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850111865779746012042167 5775167798669619018063251)
          ·
            refine ⟨8662751698004428527094877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5775167798669619018063251 8662751698004428527094877)
            ·
              refine ⟨3248531886751660697660579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8662751698004428527094877 3248531886751660697660579)
              ·
                refine ⟨4872797830127491046490869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248531886751660697660579 4872797830127491046490869)
                ·
                  refine ⟨456824796574452285608519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4872797830127491046490869 456824796574452285608519)
                  ·
                    rfl

theorem cell20_1000871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_1000871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000871 prefixEnd_1000871 := by exact prefixLift 1000871
  have htrace : WordTrace (prefixWord ++ tailWord_1000871) baseStart_1000871 baseEnd_1000871 := by
    simpa [prefixWord, tailWord_1000871, baseEnd_1000871] using wordTrace_append hprefix tailTrace_1000871
  have hstable : (prefixWord ++ tailWord_1000871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000871).length < 2 ^ (prefixWord ++ tailWord_1000871).sum := by decide
  have hdescent : baseEnd_1000871 < baseStart_1000871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000933 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 4]
def baseStart_1000933 : Nat := 118140960795 + 1000933 * 2 ^ 59
def prefixEnd_1000933 : Nat := 4983230072969 + 3 ^ 40 * 1000933 * 2
def baseEnd_1000933 : Nat := 456853095063855625541599

theorem tailTrace_1000933 : CollatzResearch.WordTrace tailWord_1000933 prefixEnd_1000933 456853095063855625541599 := by
  unfold tailWord_1000933
  simp only [CollatzResearch.WordTrace]
  refine ⟨36507025682798161591823453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24338017121865441061215635 36507025682798161591823453)
  ·
    refine ⟨13690134631049310596933795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36507025682798161591823453 13690134631049310596933795)
    ·
      refine ⟨20535201946573965895400693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13690134631049310596933795 20535201946573965895400693)
      ·
        refine ⟨1925175182491309302693815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20535201946573965895400693 1925175182491309302693815)
        ·
          refine ⟨2887762773736963954040723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925175182491309302693815 2887762773736963954040723)
          ·
            refine ⟨4331644160605445931061085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887762773736963954040723 4331644160605445931061085)
            ·
              refine ⟨1624366560227042224147907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4331644160605445931061085 1624366560227042224147907)
              ·
                refine ⟨2436549840340563336221861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624366560227042224147907 2436549840340563336221861)
                ·
                  refine ⟨456853095063855625541599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2436549840340563336221861 456853095063855625541599)
                  ·
                    rfl

theorem cell20_1000933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_1000933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000933 prefixEnd_1000933 := by exact prefixLift 1000933
  have htrace : WordTrace (prefixWord ++ tailWord_1000933) baseStart_1000933 baseEnd_1000933 := by
    simpa [prefixWord, tailWord_1000933, baseEnd_1000933] using wordTrace_append hprefix tailTrace_1000933
  have hstable : (prefixWord ++ tailWord_1000933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000933).length < 2 ^ (prefixWord ++ tailWord_1000933).sum := by decide
  have hdescent : baseEnd_1000933 < baseStart_1000933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000968 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_1000968 : Nat := 118140960795 + 1000968 * 2 ^ 59
def prefixEnd_1000968 : Nat := 4983230072969 + 3 ^ 40 * 1000968 * 2
def baseEnd_1000968 : Nat := 456869070017551059374789

theorem tailTrace_1000968 : CollatzResearch.WordTrace tailWord_1000968 prefixEnd_1000968 456869070017551059374789 := by
  unfold tailWord_1000968
  simp only [CollatzResearch.WordTrace]
  refine ⟨18254151118835681284673779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24338868158447575046231705 18254151118835681284673779)
  ·
    refine ⟨27381226678253521927010669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18254151118835681284673779 27381226678253521927010669)
    ·
      refine ⟨10267960004345070722629001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27381226678253521927010669 10267960004345070722629001)
      ·
        refine ⟨7700970003258803041971751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10267960004345070722629001 7700970003258803041971751)
        ·
          refine ⟨11551455004888204562957627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700970003258803041971751 11551455004888204562957627)
          ·
            refine ⟨17327182507332306844436441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11551455004888204562957627 17327182507332306844436441)
            ·
              refine ⟨12995386880499230133327331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17327182507332306844436441 12995386880499230133327331)
              ·
                refine ⟨19493080320748845199990997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12995386880499230133327331 19493080320748845199990997)
                ·
                  refine ⟨456869070017551059374789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19493080320748845199990997 456869070017551059374789)
                  ·
                    rfl

theorem cell20_1000968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_1000968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000968 prefixEnd_1000968 := by exact prefixLift 1000968
  have htrace : WordTrace (prefixWord ++ tailWord_1000968) baseStart_1000968 baseEnd_1000968 := by
    simpa [prefixWord, tailWord_1000968, baseEnd_1000968] using wordTrace_append hprefix tailTrace_1000968
  have hstable : (prefixWord ++ tailWord_1000968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000968).length < 2 ^ (prefixWord ++ tailWord_1000968).sum := by decide
  have hdescent : baseEnd_1000968 < baseStart_1000968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000984 : List Nat := [2, 1, 2, 3, 5, 1, 2, 2, 2]
def baseStart_1000984 : Nat := 118140960795 + 1000984 * 2 ^ 59
def prefixEnd_1000984 : Nat := 4983230072969 + 3 ^ 40 * 1000984 * 2
def baseEnd_1000984 : Nat := 456876372853526114841391

theorem tailTrace_1000984 : CollatzResearch.WordTrace tailWord_1000984 prefixEnd_1000984 456876372853526114841391 := by
  unfold tailWord_1000984
  simp only [CollatzResearch.WordTrace]
  refine ⟨18254442902806698650965003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24339257203742264867953337 18254442902806698650965003)
  ·
    refine ⟨27381664354210047976447505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18254442902806698650965003 27381664354210047976447505)
    ·
      refine ⟨20536248265657535982335629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27381664354210047976447505 20536248265657535982335629)
      ·
        refine ⟨7701093099621575993375861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20536248265657535982335629 7701093099621575993375861)
        ·
          refine ⟨721977478089522749378987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7701093099621575993375861 721977478089522749378987)
          ·
            refine ⟨1082966217134284124068481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721977478089522749378987 1082966217134284124068481)
            ·
              refine ⟨812224662850713093051361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082966217134284124068481 812224662850713093051361)
              ·
                refine ⟨609168497138034819788521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812224662850713093051361 609168497138034819788521)
                ·
                  refine ⟨456876372853526114841391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609168497138034819788521 456876372853526114841391)
                  ·
                    rfl

theorem cell20_1000984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_1000984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000984 prefixEnd_1000984 := by exact prefixLift 1000984
  have htrace : WordTrace (prefixWord ++ tailWord_1000984) baseStart_1000984 baseEnd_1000984 := by
    simpa [prefixWord, tailWord_1000984, baseEnd_1000984] using wordTrace_append hprefix tailTrace_1000984
  have hstable : (prefixWord ++ tailWord_1000984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000984).length < 2 ^ (prefixWord ++ tailWord_1000984).sum := by decide
  have hdescent : baseEnd_1000984 < baseStart_1000984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000995 : List Nat := [1, 1, 1, 4, 6, 1, 1, 5]
def baseStart_1000995 : Nat := 118140960795 + 1000995 * 2 ^ 59
def prefixEnd_1000995 : Nat := 4983230072969 + 3 ^ 40 * 1000995 * 2
def baseEnd_1000995 : Nat := 152293797851086321824893

theorem tailTrace_1000995 : CollatzResearch.WordTrace tailWord_1000995 prefixEnd_1000995 152293797851086321824893 := by
  unfold tailWord_1000995
  simp only [CollatzResearch.WordTrace]
  refine ⟨36509287008573546180580439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24339524672382364120386959 36509287008573546180580439)
  ·
    refine ⟨54763930512860319270870659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36509287008573546180580439 54763930512860319270870659)
    ·
      refine ⟨82145895769290478906305989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54763930512860319270870659 82145895769290478906305989)
      ·
        refine ⟨15402355456741964794932373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82145895769290478906305989 15402355456741964794932373)
        ·
          refine ⟨721985412034779599762455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15402355456741964794932373 721985412034779599762455)
          ·
            refine ⟨1082978118052169399643683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721985412034779599762455 1082978118052169399643683)
            ·
              refine ⟨1624467177078254099465525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082978118052169399643683 1624467177078254099465525)
              ·
                refine ⟨152293797851086321824893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1624467177078254099465525 152293797851086321824893)
                ·
                  rfl

theorem cell20_1000995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 5].length) (baseStart_1000995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1000995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1000995 prefixEnd_1000995 := by exact prefixLift 1000995
  have htrace : WordTrace (prefixWord ++ tailWord_1000995) baseStart_1000995 baseEnd_1000995 := by
    simpa [prefixWord, tailWord_1000995, baseEnd_1000995] using wordTrace_append hprefix tailTrace_1000995
  have hstable : (prefixWord ++ tailWord_1000995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000995).length < 2 ^ (prefixWord ++ tailWord_1000995).sum := by decide
  have hdescent : baseEnd_1000995 < baseStart_1000995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001016 : List Nat := [2, 1, 2, 1, 4, 3, 3, 4]
def baseStart_1001016 : Nat := 118140960795 + 1001016 * 2 ^ 59
def prefixEnd_1001016 : Nat := 4983230072969 + 3 ^ 40 * 1001016 * 2
def baseEnd_1001016 : Nat := 152296992841825408591531

theorem tailTrace_1001016 : CollatzResearch.WordTrace tailWord_1001016 prefixEnd_1001016 152296992841825408591531 := by
  unfold tailWord_1001016
  simp only [CollatzResearch.WordTrace]
  refine ⟨18255026470748733383547451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24340035294331644511396601 18255026470748733383547451)
  ·
    refine ⟨27382539706123100075321177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18255026470748733383547451 27382539706123100075321177)
    ·
      refine ⟨20536904779592325056490883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27382539706123100075321177 20536904779592325056490883)
      ·
        refine ⟨30805357169388487584736325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20536904779592325056490883 30805357169388487584736325)
        ·
          refine ⟨5776004469260341422138061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30805357169388487584736325 5776004469260341422138061)
          ·
            refine ⟨2166001675972628033301773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5776004469260341422138061 2166001675972628033301773)
            ·
              refine ⟨812250628489735512488165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2166001675972628033301773 812250628489735512488165)
              ·
                refine ⟨152296992841825408591531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 812250628489735512488165 152296992841825408591531)
                ·
                  rfl

theorem cell20_1001016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_1001016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001016 prefixEnd_1001016 := by exact prefixLift 1001016
  have htrace : WordTrace (prefixWord ++ tailWord_1001016) baseStart_1001016 baseEnd_1001016 := by
    simpa [prefixWord, tailWord_1001016, baseEnd_1001016] using wordTrace_append hprefix tailTrace_1001016
  have hstable : (prefixWord ++ tailWord_1001016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001016).length < 2 ^ (prefixWord ++ tailWord_1001016).sum := by decide
  have hdescent : baseEnd_1001016 < baseStart_1001016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001047 : List Nat := [1, 1, 3, 2, 2, 3, 2, 4, 2]
def baseStart_1001047 : Nat := 118140960795 + 1001047 * 2 ^ 59
def prefixEnd_1001047 : Nat := 4983230072969 + 3 ^ 40 * 1001047 * 2
def baseEnd_1001047 : Nat := 456905127770177895741133

theorem tailTrace_1001047 : CollatzResearch.WordTrace tailWord_1001047 prefixEnd_1001047 456905127770177895741133 := by
  unfold tailWord_1001047
  simp only [CollatzResearch.WordTrace]
  refine ⟨36511183604385159061473395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24340789069590106040982263 36511183604385159061473395)
  ·
    refine ⟨54766775406577738592210093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36511183604385159061473395 54766775406577738592210093)
    ·
      refine ⟨20537540777466651972078785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54766775406577738592210093 20537540777466651972078785)
      ·
        refine ⟨15403155583099988979059089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20537540777466651972078785 15403155583099988979059089)
        ·
          refine ⟨11552366687324991734294317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15403155583099988979059089 11552366687324991734294317)
          ·
            refine ⟨4332137507746871900360369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11552366687324991734294317 4332137507746871900360369)
            ·
              refine ⟨3249103130810153925270277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4332137507746871900360369 3249103130810153925270277)
              ·
                refine ⟨609206837026903860988177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3249103130810153925270277 609206837026903860988177)
                ·
                  refine ⟨456905127770177895741133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609206837026903860988177 456905127770177895741133)
                  ·
                    rfl

theorem cell20_1001047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 2].length) (baseStart_1001047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001047 prefixEnd_1001047 := by exact prefixLift 1001047
  have htrace : WordTrace (prefixWord ++ tailWord_1001047) baseStart_1001047 baseEnd_1001047 := by
    simpa [prefixWord, tailWord_1001047, baseEnd_1001047] using wordTrace_append hprefix tailTrace_1001047
  have hstable : (prefixWord ++ tailWord_1001047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001047).length < 2 ^ (prefixWord ++ tailWord_1001047).sum := by decide
  have hdescent : baseEnd_1001047 < baseStart_1001047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001092 : List Nat := [2, 3, 2, 1, 4, 2, 6]
def baseStart_1001092 : Nat := 118140960795 + 1001092 * 2 ^ 59
def prefixEnd_1001092 : Nat := 4983230072969 + 3 ^ 40 * 1001092 * 2
def baseEnd_1001092 : Nat := 50769518555150859915661

theorem tailTrace_1001092 : CollatzResearch.WordTrace tailWord_1001092 prefixEnd_1001092 50769518555150859915661 := by
  unfold tailWord_1001092
  simp only [CollatzResearch.WordTrace]
  refine ⟨18256412444611065873430765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24341883259481421164574353 18256412444611065873430765)
  ·
    refine ⟨6846154666729149702536537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18256412444611065873430765 6846154666729149702536537)
    ·
      refine ⟨5134616000046862276902403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6846154666729149702536537 5134616000046862276902403)
      ·
        refine ⟨7701924000070293415353605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5134616000046862276902403 7701924000070293415353605)
        ·
          refine ⟨1444110750013180015378801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7701924000070293415353605 1444110750013180015378801)
          ·
            refine ⟨1083083062509885011534101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1444110750013180015378801 1083083062509885011534101)
            ·
              refine ⟨50769518555150859915661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1083083062509885011534101 50769518555150859915661)
              ·
                rfl

theorem cell20_1001092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 6].length) (baseStart_1001092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001092 prefixEnd_1001092 := by exact prefixLift 1001092
  have htrace : WordTrace (prefixWord ++ tailWord_1001092) baseStart_1001092 baseEnd_1001092 := by
    simpa [prefixWord, tailWord_1001092, baseEnd_1001092] using wordTrace_append hprefix tailTrace_1001092
  have hstable : (prefixWord ++ tailWord_1001092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001092).length < 2 ^ (prefixWord ++ tailWord_1001092).sum := by decide
  have hdescent : baseEnd_1001092 < baseStart_1001092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001116 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 3]
def baseStart_1001116 : Nat := 118140960795 + 1001116 * 2 ^ 59
def prefixEnd_1001116 : Nat := 4983230072969 + 3 ^ 40 * 1001116 * 2
def baseEnd_1001116 : Nat := 456936621250320322440851

theorem tailTrace_1001116 : CollatzResearch.WordTrace tailWord_1001116 prefixEnd_1001116 456936621250320322440851 := by
  unfold tailWord_1001116
  simp only [CollatzResearch.WordTrace]
  refine ⟨18256850120567591922867601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24342466827423455897156801 18256850120567591922867601)
  ·
    refine ⟨13692637590425693942150701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18256850120567591922867601 13692637590425693942150701)
    ·
      refine ⟨5134739096409635228306513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13692637590425693942150701 5134739096409635228306513)
      ·
        refine ⟨3851054322307226421229885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5134739096409635228306513 3851054322307226421229885)
        ·
          refine ⟨1444145370865209907961207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3851054322307226421229885 1444145370865209907961207)
          ·
            refine ⟨2166218056297814861941811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444145370865209907961207 2166218056297814861941811)
            ·
              refine ⟨3249327084446722292912717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166218056297814861941811 3249327084446722292912717)
              ·
                refine ⟨1218497656667520859842269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3249327084446722292912717 1218497656667520859842269)
                ·
                  refine ⟨456936621250320322440851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218497656667520859842269 456936621250320322440851)
                  ·
                    rfl

theorem cell20_1001116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_1001116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001116 prefixEnd_1001116 := by exact prefixLift 1001116
  have htrace : WordTrace (prefixWord ++ tailWord_1001116) baseStart_1001116 baseEnd_1001116 := by
    simpa [prefixWord, tailWord_1001116, baseEnd_1001116] using wordTrace_append hprefix tailTrace_1001116
  have hstable : (prefixWord ++ tailWord_1001116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001116).length < 2 ^ (prefixWord ++ tailWord_1001116).sum := by decide
  have hdescent : baseEnd_1001116 < baseStart_1001116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001199 : List Nat := [1, 1, 2, 1, 5, 1, 4, 3, 2]
def baseStart_1001199 : Nat := 118140960795 + 1001199 * 2 ^ 59
def prefixEnd_1001199 : Nat := 4983230072969 + 3 ^ 40 * 1001199 * 2
def baseEnd_1001199 : Nat := 456974504711940922673845

theorem tailTrace_1001199 : CollatzResearch.WordTrace tailWord_1001199 prefixEnd_1001199 456974504711940922673845 := by
  unfold tailWord_1001199
  simp only [CollatzResearch.WordTrace]
  refine ⟨36516727499834489021006651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24344484999889659347337767 36516727499834489021006651)
  ·
    refine ⟨54775091249751733531509977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36516727499834489021006651 54775091249751733531509977)
    ·
      refine ⟨41081318437313800148632483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54775091249751733531509977 41081318437313800148632483)
      ·
        refine ⟨61621977655970700222948725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41081318437313800148632483 61621977655970700222948725)
        ·
          refine ⟨5777060405247253145901443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61621977655970700222948725 5777060405247253145901443)
          ·
            refine ⟨8665590607870879718852165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5777060405247253145901443 8665590607870879718852165)
            ·
              refine ⟨1624798238975789947284781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8665590607870879718852165 1624798238975789947284781)
              ·
                refine ⟨609299339615921230231793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1624798238975789947284781 609299339615921230231793)
                ·
                  refine ⟨456974504711940922673845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609299339615921230231793 456974504711940922673845)
                  ·
                    rfl

theorem cell20_1001199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 2].length) (baseStart_1001199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001199 prefixEnd_1001199 := by exact prefixLift 1001199
  have htrace : WordTrace (prefixWord ++ tailWord_1001199) baseStart_1001199 baseEnd_1001199 := by
    simpa [prefixWord, tailWord_1001199, baseEnd_1001199] using wordTrace_append hprefix tailTrace_1001199
  have hstable : (prefixWord ++ tailWord_1001199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001199).length < 2 ^ (prefixWord ++ tailWord_1001199).sum := by decide
  have hdescent : baseEnd_1001199 < baseStart_1001199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001220 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1001220 : Nat := 118140960795 + 1001220 * 2 ^ 59
def prefixEnd_1001220 : Nat := 4983230072969 + 3 ^ 40 * 1001220 * 2
def baseEnd_1001220 : Nat := 456984089684158182973759

theorem tailTrace_1001220 : CollatzResearch.WordTrace tailWord_1001220 prefixEnd_1001220 456984089684158182973759 := by
  unfold tailWord_1001220
  simp only [CollatzResearch.WordTrace]
  refine ⟨18258746716379204803760557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24344995621838939738347409 18258746716379204803760557)
  ·
    refine ⟨6847030018642201801410209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18258746716379204803760557 6847030018642201801410209)
    ·
      refine ⟨5135272513981651351057657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6847030018642201801410209 5135272513981651351057657)
      ·
        refine ⟨3851454385486238513293243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5135272513981651351057657 3851454385486238513293243)
        ·
          refine ⟨5777181578229357769939865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851454385486238513293243 5777181578229357769939865)
          ·
            refine ⟨4332886183672018327454899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5777181578229357769939865 4332886183672018327454899)
            ·
              refine ⟨6499329275508027491182349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332886183672018327454899 6499329275508027491182349)
              ·
                refine ⟨2437248478315510309193381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6499329275508027491182349 2437248478315510309193381)
                ·
                  refine ⟨456984089684158182973759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2437248478315510309193381 456984089684158182973759)
                  ·
                    rfl

theorem cell20_1001220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1001220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001220 prefixEnd_1001220 := by exact prefixLift 1001220
  have htrace : WordTrace (prefixWord ++ tailWord_1001220) baseStart_1001220 baseEnd_1001220 := by
    simpa [prefixWord, tailWord_1001220, baseEnd_1001220] using wordTrace_append hprefix tailTrace_1001220
  have hstable : (prefixWord ++ tailWord_1001220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001220).length < 2 ^ (prefixWord ++ tailWord_1001220).sum := by decide
  have hdescent : baseEnd_1001220 < baseStart_1001220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001236 : List Nat := [2, 4, 4, 1, 2, 1, 2, 4]
def baseStart_1001236 : Nat := 118140960795 + 1001236 * 2 ^ 59
def prefixEnd_1001236 : Nat := 4983230072969 + 3 ^ 40 * 1001236 * 2
def baseEnd_1001236 : Nat := 152330464173377746146787

theorem tailTrace_1001236 : CollatzResearch.WordTrace tailWord_1001236 prefixEnd_1001236 152330464173377746146787 := by
  unfold tailWord_1001236
  simp only [CollatzResearch.WordTrace]
  refine ⟨18259038500350222170051781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24345384667133629560069041 18259038500350222170051781)
  ·
    refine ⟨3423569718815666656884709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18259038500350222170051781 3423569718815666656884709)
    ·
      refine ⟨641919322277937498165883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3423569718815666656884709 641919322277937498165883)
      ·
        refine ⟨962878983416906247248825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641919322277937498165883 962878983416906247248825)
        ·
          refine ⟨722159237562679685436619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962878983416906247248825 722159237562679685436619)
          ·
            refine ⟨1083238856344019528154929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722159237562679685436619 1083238856344019528154929)
            ·
              refine ⟨812429142258014646116197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083238856344019528154929 812429142258014646116197)
              ·
                refine ⟨152330464173377746146787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 812429142258014646116197 152330464173377746146787)
                ·
                  rfl

theorem cell20_1001236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_1001236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001236 prefixEnd_1001236 := by exact prefixLift 1001236
  have htrace : WordTrace (prefixWord ++ tailWord_1001236) baseStart_1001236 baseEnd_1001236 := by
    simpa [prefixWord, tailWord_1001236, baseEnd_1001236] using wordTrace_append hprefix tailTrace_1001236
  have hstable : (prefixWord ++ tailWord_1001236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001236).length < 2 ^ (prefixWord ++ tailWord_1001236).sum := by decide
  have hdescent : baseEnd_1001236 < baseStart_1001236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001265 : List Nat := [1, 2, 2, 3, 2, 4, 6]
def baseStart_1001265 : Nat := 118140960795 + 1001265 * 2 ^ 59
def prefixEnd_1001265 : Nat := 4983230072969 + 3 ^ 40 * 1001265 * 2
def baseEnd_1001265 : Nat := 50778292101148669608175

theorem tailTrace_1001265 : CollatzResearch.WordTrace tailWord_1001265 prefixEnd_1001265 50778292101148669608175 := by
  unfold tailWord_1001265
  simp only [CollatzResearch.WordTrace]
  refine ⟨36519134717595382292909249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24346089811730254861939499 36519134717595382292909249)
  ·
    refine ⟨27389351038196536719681937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36519134717595382292909249 27389351038196536719681937)
    ·
      refine ⟨20542013278647402539761453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27389351038196536719681937 20542013278647402539761453)
      ·
        refine ⟨7703254979492775952410545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20542013278647402539761453 7703254979492775952410545)
        ·
          refine ⟨5777441234619581964307909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7703254979492775952410545 5777441234619581964307909)
          ·
            refine ⟨1083270231491171618307733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5777441234619581964307909 1083270231491171618307733)
            ·
              refine ⟨50778292101148669608175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1083270231491171618307733 50778292101148669608175)
              ·
                rfl

theorem cell20_1001265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 6].length) (baseStart_1001265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001265 prefixEnd_1001265 := by exact prefixLift 1001265
  have htrace : WordTrace (prefixWord ++ tailWord_1001265) baseStart_1001265 baseEnd_1001265 := by
    simpa [prefixWord, tailWord_1001265, baseEnd_1001265] using wordTrace_append hprefix tailTrace_1001265
  have hstable : (prefixWord ++ tailWord_1001265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001265).length < 2 ^ (prefixWord ++ tailWord_1001265).sum := by decide
  have hdescent : baseEnd_1001265 < baseStart_1001265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001272 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_1001272 : Nat := 118140960795 + 1001272 * 2 ^ 59
def prefixEnd_1001272 : Nat := 4983230072969 + 3 ^ 40 * 1001272 * 2
def baseEnd_1001272 : Nat := 457007823901077113240213

theorem tailTrace_1001272 : CollatzResearch.WordTrace tailWord_1001272 prefixEnd_1001272 457007823901077113240213 := by
  unfold tailWord_1001272
  simp only [CollatzResearch.WordTrace]
  refine ⟨18259695014285011244207035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24346260019046681658942713 18259695014285011244207035)
  ·
    refine ⟨27389542521427516866310553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18259695014285011244207035 27389542521427516866310553)
    ·
      refine ⟨20542156891070637649732915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27389542521427516866310553 20542156891070637649732915)
      ·
        refine ⟨30813235336605956474599373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20542156891070637649732915 30813235336605956474599373)
        ·
          refine ⟨11554963251227233677974765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30813235336605956474599373 11554963251227233677974765)
          ·
            refine ⟨4333111219210212629240537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11554963251227233677974765 4333111219210212629240537)
            ·
              refine ⟨3249833414407659471930403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4333111219210212629240537 3249833414407659471930403)
              ·
                refine ⟨4874750121611489207895605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249833414407659471930403 4874750121611489207895605)
                ·
                  refine ⟨457007823901077113240213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4874750121611489207895605 457007823901077113240213)
                  ·
                    rfl

theorem cell20_1001272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_1001272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001272 prefixEnd_1001272 := by exact prefixLift 1001272
  have htrace : WordTrace (prefixWord ++ tailWord_1001272) baseStart_1001272 baseEnd_1001272 := by
    simpa [prefixWord, tailWord_1001272, baseEnd_1001272] using wordTrace_append hprefix tailTrace_1001272
  have hstable : (prefixWord ++ tailWord_1001272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001272).length < 2 ^ (prefixWord ++ tailWord_1001272).sum := by decide
  have hdescent : baseEnd_1001272 < baseStart_1001272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001324 : List Nat := [2, 2, 1, 1, 4, 10]
def baseStart_1001324 : Nat := 118140960795 + 1001324 * 2 ^ 59
def prefixEnd_1001324 : Nat := 4983230072969 + 3 ^ 40 * 1001324 * 2
def baseEnd_1001324 : Nat := 16927094745110964574321

theorem tailTrace_1001324 : CollatzResearch.WordTrace tailWord_1001324 prefixEnd_1001324 16927094745110964574321 := by
  unfold tailWord_1001324
  simp only [CollatzResearch.WordTrace]
  refine ⟨18260643312190817684653513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24347524416254423579538017 18260643312190817684653513)
  ·
    refine ⟨13695482484143113263490135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18260643312190817684653513 13695482484143113263490135)
    ·
      refine ⟨20543223726214669895235203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13695482484143113263490135 20543223726214669895235203)
      ·
        refine ⟨30814835589322004842852805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20543223726214669895235203 30814835589322004842852805)
        ·
          refine ⟨5777781672997875908034901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30814835589322004842852805 5777781672997875908034901)
          ·
            refine ⟨16927094745110964574321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5777781672997875908034901 16927094745110964574321)
            ·
              rfl

theorem cell20_1001324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 10].length) (baseStart_1001324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001324 prefixEnd_1001324 := by exact prefixLift 1001324
  have htrace : WordTrace (prefixWord ++ tailWord_1001324) baseStart_1001324 baseEnd_1001324 := by
    simpa [prefixWord, tailWord_1001324, baseEnd_1001324] using wordTrace_append hprefix tailTrace_1001324
  have hstable : (prefixWord ++ tailWord_1001324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001324).length < 2 ^ (prefixWord ++ tailWord_1001324).sum := by decide
  have hdescent : baseEnd_1001324 < baseStart_1001324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001400 : List Nat := [2, 1, 2, 1, 2, 3, 2, 7]
def baseStart_1001400 : Nat := 118140960795 + 1001400 * 2 ^ 59
def prefixEnd_1001400 : Nat := 4983230072969 + 3 ^ 40 * 1001400 * 2
def baseEnd_1001400 : Nat := 152355415529625852324341

theorem tailTrace_1001400 : CollatzResearch.WordTrace tailWord_1001400 prefixEnd_1001400 152355415529625852324341 := by
  unfold tailWord_1001400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18262029286053150174536827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24349372381404200232715769 18262029286053150174536827)
  ·
    refine ⟨27393043929079725261805241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18262029286053150174536827 27393043929079725261805241)
    ·
      refine ⟨20544782946809793946353931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27393043929079725261805241 20544782946809793946353931)
      ·
        refine ⟨30817174420214690919530897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20544782946809793946353931 30817174420214690919530897)
        ·
          refine ⟨23112880815161018189648173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30817174420214690919530897 23112880815161018189648173)
          ·
            refine ⟨8667330305685381821118065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23112880815161018189648173 8667330305685381821118065)
            ·
              refine ⟨6500497729264036365838549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8667330305685381821118065 6500497729264036365838549)
              ·
                refine ⟨152355415529625852324341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6500497729264036365838549 152355415529625852324341)
                ·
                  rfl

theorem cell20_1001400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_1001400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001400 prefixEnd_1001400 := by exact prefixLift 1001400
  have htrace : WordTrace (prefixWord ++ tailWord_1001400) baseStart_1001400 baseEnd_1001400 := by
    simpa [prefixWord, tailWord_1001400, baseEnd_1001400] using wordTrace_append hprefix tailTrace_1001400
  have hstable : (prefixWord ++ tailWord_1001400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001400).length < 2 ^ (prefixWord ++ tailWord_1001400).sum := by decide
  have hdescent : baseEnd_1001400 < baseStart_1001400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001434 : List Nat := [3, 1, 1, 2, 6, 1, 6]
def baseStart_1001434 : Nat := 118140960795 + 1001434 * 2 ^ 59
def prefixEnd_1001434 : Nat := 4983230072969 + 3 ^ 40 * 1001434 * 2
def baseEnd_1001434 : Nat := 50786862790591616648839

theorem tailTrace_1001434 : CollatzResearch.WordTrace tailWord_1001434 prefixEnd_1001434 50786862790591616648839 := by
  unfold tailWord_1001434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9131324663495781038952839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24350199102655416103874237 9131324663495781038952839)
  ·
    refine ⟨13696986995243671558429259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9131324663495781038952839 13696986995243671558429259)
    ·
      refine ⟨20545480492865507337643889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13696986995243671558429259 20545480492865507337643889)
      ·
        refine ⟨15409110369649130503232917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20545480492865507337643889 15409110369649130503232917)
        ·
          refine ⟨722302048577302992339043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15409110369649130503232917 722302048577302992339043)
          ·
            refine ⟨1083453072865954488508565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722302048577302992339043 1083453072865954488508565)
            ·
              refine ⟨50786862790591616648839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1083453072865954488508565 50786862790591616648839)
              ·
                rfl

theorem cell20_1001434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 6].length) (baseStart_1001434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001434 prefixEnd_1001434 := by exact prefixLift 1001434
  have htrace : WordTrace (prefixWord ++ tailWord_1001434) baseStart_1001434 baseEnd_1001434 := by
    simpa [prefixWord, tailWord_1001434, baseEnd_1001434] using wordTrace_append hprefix tailTrace_1001434
  have hstable : (prefixWord ++ tailWord_1001434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001434).length < 2 ^ (prefixWord ++ tailWord_1001434).sum := by decide
  have hdescent : baseEnd_1001434 < baseStart_1001434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001469 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1001469 : Nat := 118140960795 + 1001469 * 2 ^ 59
def prefixEnd_1001469 : Nat := 4983230072969 + 3 ^ 40 * 1001469 * 2
def baseEnd_1001469 : Nat := 457097740069019983672741

theorem tailTrace_1001469 : CollatzResearch.WordTrace tailWord_1001469 prefixEnd_1001469 457097740069019983672741 := by
  unfold tailWord_1001469
  simp only [CollatzResearch.WordTrace]
  refine ⟨36526575208856325133335461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24351050139237550088890307 36526575208856325133335461)
  ·
    refine ⟨6848732851660560962500399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36526575208856325133335461 6848732851660560962500399)
    ·
      refine ⟨10273099277490841443750599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6848732851660560962500399 10273099277490841443750599)
      ·
        refine ⟨15409648916236262165625899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10273099277490841443750599 15409648916236262165625899)
        ·
          refine ⟨23114473374354393248438849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15409648916236262165625899 23114473374354393248438849)
          ·
            refine ⟨17335855030765794936329137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23114473374354393248438849 17335855030765794936329137)
            ·
              refine ⟨13001891273074346202246853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17335855030765794936329137 13001891273074346202246853)
              ·
                refine ⟨2437854613701439912921285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13001891273074346202246853 2437854613701439912921285)
                ·
                  refine ⟨457097740069019983672741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2437854613701439912921285 457097740069019983672741)
                  ·
                    rfl

theorem cell20_1001469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1001469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001469 prefixEnd_1001469 := by exact prefixLift 1001469
  have htrace : WordTrace (prefixWord ++ tailWord_1001469) baseStart_1001469 baseEnd_1001469 := by
    simpa [prefixWord, tailWord_1001469, baseEnd_1001469] using wordTrace_append hprefix tailTrace_1001469
  have hstable : (prefixWord ++ tailWord_1001469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001469).length < 2 ^ (prefixWord ++ tailWord_1001469).sum := by decide
  have hdescent : baseEnd_1001469 < baseStart_1001469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001493 : List Nat := [1, 3, 2, 1, 6, 7]
def baseStart_1001493 : Nat := 118140960795 + 1001493 * 2 ^ 59
def prefixEnd_1001493 : Nat := 4983230072969 + 3 ^ 40 * 1001493 * 2
def baseEnd_1001493 : Nat := 16929951641591946921209

theorem tailTrace_1001493 : CollatzResearch.WordTrace tailWord_1001493 prefixEnd_1001493 16929951641591946921209 := by
  unfold tailWord_1001493
  simp only [CollatzResearch.WordTrace]
  refine ⟨36527450560769377232209133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24351633707179584821472755 36527450560769377232209133)
  ·
    refine ⟨13697793960288516462078425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36527450560769377232209133 13697793960288516462078425)
    ·
      refine ⟨10273345470216387346558819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13697793960288516462078425 10273345470216387346558819)
      ·
        refine ⟨15410018205324581019838229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10273345470216387346558819 15410018205324581019838229)
        ·
          refine ⟨722344603374589735304917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15410018205324581019838229 722344603374589735304917)
          ·
            refine ⟨16929951641591946921209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 722344603374589735304917 16929951641591946921209)
            ·
              rfl

theorem cell20_1001493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 7].length) (baseStart_1001493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001493 prefixEnd_1001493 := by exact prefixLift 1001493
  have htrace : WordTrace (prefixWord ++ tailWord_1001493) baseStart_1001493 baseEnd_1001493 := by
    simpa [prefixWord, tailWord_1001493, baseEnd_1001493] using wordTrace_append hprefix tailTrace_1001493
  have hstable : (prefixWord ++ tailWord_1001493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001493).length < 2 ^ (prefixWord ++ tailWord_1001493).sum := by decide
  have hdescent : baseEnd_1001493 < baseStart_1001493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001507 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_1001507 : Nat := 118140960795 + 1001507 * 2 ^ 59
def prefixEnd_1001507 : Nat := 4983230072969 + 3 ^ 40 * 1001507 * 2
def baseEnd_1001507 : Nat := 457115084304460740405919

theorem tailTrace_1001507 : CollatzResearch.WordTrace tailWord_1001507 prefixEnd_1001507 457115084304460740405919 := by
  unfold tailWord_1001507
  simp only [CollatzResearch.WordTrace]
  refine ⟨36527961182718657623218775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24351974121812438415479183 36527961182718657623218775)
  ·
    refine ⟨54791941774077986434828163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36527961182718657623218775 54791941774077986434828163)
    ·
      refine ⟨82187912661116979652242245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54791941774077986434828163 82187912661116979652242245)
      ·
        refine ⟨15410233623959433684795421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82187912661116979652242245 15410233623959433684795421)
        ·
          refine ⟨5778837608984787631798283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15410233623959433684795421 5778837608984787631798283)
          ·
            refine ⟨8668256413477181447697425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778837608984787631798283 8668256413477181447697425)
            ·
              refine ⟨6501192310107886085773069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8668256413477181447697425 6501192310107886085773069)
              ·
                refine ⟨2437947116290457282164901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6501192310107886085773069 2437947116290457282164901)
                ·
                  refine ⟨457115084304460740405919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2437947116290457282164901 457115084304460740405919)
                  ·
                    rfl

theorem cell20_1001507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_1001507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001507 prefixEnd_1001507 := by exact prefixLift 1001507
  have htrace : WordTrace (prefixWord ++ tailWord_1001507) baseStart_1001507 baseEnd_1001507 := by
    simpa [prefixWord, tailWord_1001507, baseEnd_1001507] using wordTrace_append hprefix tailTrace_1001507
  have hstable : (prefixWord ++ tailWord_1001507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001507).length < 2 ^ (prefixWord ++ tailWord_1001507).sum := by decide
  have hdescent : baseEnd_1001507 < baseStart_1001507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001558 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1001558 : Nat := 118140960795 + 1001558 * 2 ^ 59
def prefixEnd_1001558 : Nat := 4983230072969 + 3 ^ 40 * 1001558 * 2
def baseEnd_1001558 : Nat := 457138362094131229705711

theorem tailTrace_1001558 : CollatzResearch.WordTrace tailWord_1001558 prefixEnd_1001558 457138362094131229705711 := by
  unfold tailWord_1001558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283113831595868333332833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24353214203689262222216885 2283113831595868333332833)
  ·
    refine ⟨1712335373696901249999625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2283113831595868333332833 1712335373696901249999625)
    ·
      refine ⟨1284251530272675937499719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1712335373696901249999625 1284251530272675937499719)
      ·
        refine ⟨1926377295409013906249579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284251530272675937499719 1926377295409013906249579)
        ·
          refine ⟨2889565943113520859374369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926377295409013906249579 2889565943113520859374369)
          ·
            refine ⟨2167174457335140644530777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2889565943113520859374369 2167174457335140644530777)
            ·
              refine ⟨1625380843001355483398083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167174457335140644530777 1625380843001355483398083)
              ·
                refine ⟨2438071264502033225097125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625380843001355483398083 2438071264502033225097125)
                ·
                  refine ⟨457138362094131229705711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2438071264502033225097125 457138362094131229705711)
                  ·
                    rfl

theorem cell20_1001558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1001558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001558 prefixEnd_1001558 := by exact prefixLift 1001558
  have htrace : WordTrace (prefixWord ++ tailWord_1001558) baseStart_1001558 baseEnd_1001558 := by
    simpa [prefixWord, tailWord_1001558, baseEnd_1001558] using wordTrace_append hprefix tailTrace_1001558
  have hstable : (prefixWord ++ tailWord_1001558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001558).length < 2 ^ (prefixWord ++ tailWord_1001558).sum := by decide
  have hdescent : baseEnd_1001558 < baseStart_1001558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001562 : List Nat := [3, 1, 1, 2, 1, 1, 3, 6, 2]
def baseStart_1001562 : Nat := 118140960795 + 1001562 * 2 ^ 59
def prefixEnd_1001562 : Nat := 4983230072969 + 3 ^ 40 * 1001562 * 2
def baseEnd_1001562 : Nat := 457140187803124993572361

theorem tailTrace_1001562 : CollatzResearch.WordTrace tailWord_1001562 prefixEnd_1001562 457140187803124993572361 := by
  unfold tailWord_1001562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9132491799379850504117735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24353311465012934677647293 9132491799379850504117735)
  ·
    refine ⟨13698737699069775756176603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9132491799379850504117735 13698737699069775756176603)
    ·
      refine ⟨20548106548604663634264905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13698737699069775756176603 20548106548604663634264905)
      ·
        refine ⟨15411079911453497725698679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20548106548604663634264905 15411079911453497725698679)
        ·
          refine ⟨23116619867180246588548019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15411079911453497725698679 23116619867180246588548019)
          ·
            refine ⟨34674929800770369882822029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23116619867180246588548019 34674929800770369882822029)
            ·
              refine ⟨13003098675288888706058261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34674929800770369882822029 13003098675288888706058261)
              ·
                refine ⟨609520250404166658096481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13003098675288888706058261 609520250404166658096481)
                ·
                  refine ⟨457140187803124993572361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609520250404166658096481 457140187803124993572361)
                  ·
                    rfl

theorem cell20_1001562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_1001562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001562 prefixEnd_1001562 := by exact prefixLift 1001562
  have htrace : WordTrace (prefixWord ++ tailWord_1001562) baseStart_1001562 baseEnd_1001562 := by
    simpa [prefixWord, tailWord_1001562, baseEnd_1001562] using wordTrace_append hprefix tailTrace_1001562
  have hstable : (prefixWord ++ tailWord_1001562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001562).length < 2 ^ (prefixWord ++ tailWord_1001562).sum := by decide
  have hdescent : baseEnd_1001562 < baseStart_1001562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001583 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_1001583 : Nat := 118140960795 + 1001583 * 2 ^ 59
def prefixEnd_1001583 : Nat := 4983230072969 + 3 ^ 40 * 1001583 * 2
def baseEnd_1001583 : Nat := 457149772775342253872275

theorem tailTrace_1001583 : CollatzResearch.WordTrace tailWord_1001583 prefixEnd_1001583 457149772775342253872275 := by
  unfold tailWord_1001583
  simp only [CollatzResearch.WordTrace]
  refine ⟨36530733130443322602985403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24353822086962215068656935 36530733130443322602985403)
  ·
    refine ⟨54796099695664983904478105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36530733130443322602985403 54796099695664983904478105)
    ·
      refine ⟨41097074771748737928358579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54796099695664983904478105 41097074771748737928358579)
      ·
        refine ⟨61645612157623106892537869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41097074771748737928358579 61645612157623106892537869)
        ·
          refine ⟨23117104559108665084701701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61645612157623106892537869 23117104559108665084701701)
          ·
            refine ⟨4334457104832874703381569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23117104559108665084701701 4334457104832874703381569)
            ·
              refine ⟨3250842828624656027536177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334457104832874703381569 3250842828624656027536177)
              ·
                refine ⟨2438132121468492020652133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3250842828624656027536177 2438132121468492020652133)
                ·
                  refine ⟨457149772775342253872275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2438132121468492020652133 457149772775342253872275)
                  ·
                    rfl

theorem cell20_1001583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_1001583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001583 prefixEnd_1001583 := by exact prefixLift 1001583
  have htrace : WordTrace (prefixWord ++ tailWord_1001583) baseStart_1001583 baseEnd_1001583 := by
    simpa [prefixWord, tailWord_1001583, baseEnd_1001583] using wordTrace_append hprefix tailTrace_1001583
  have hstable : (prefixWord ++ tailWord_1001583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001583).length < 2 ^ (prefixWord ++ tailWord_1001583).sum := by decide
  have hdescent : baseEnd_1001583 < baseStart_1001583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001586 : List Nat := [3, 2, 1, 2, 2, 4, 2, 4]
def baseStart_1001586 : Nat := 118140960795 + 1001586 * 2 ^ 59
def prefixEnd_1001586 : Nat := 4983230072969 + 3 ^ 40 * 1001586 * 2
def baseEnd_1001586 : Nat := 152383714019029192257421

theorem tailTrace_1001586 : CollatzResearch.WordTrace tailWord_1001586 prefixEnd_1001586 152383714019029192257421 := by
  unfold tailWord_1001586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9132710637358113528836153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24353895032954969410229741 9132710637358113528836153)
  ·
    refine ⟨6849532978018585146627115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9132710637358113528836153 6849532978018585146627115)
    ·
      refine ⟨10274299467027877719940673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6849532978018585146627115 10274299467027877719940673)
      ·
        refine ⟨7705724600270908289955505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10274299467027877719940673 7705724600270908289955505)
        ·
          refine ⟨5779293450203181217466629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7705724600270908289955505 5779293450203181217466629)
          ·
            refine ⟨1083617521913096478274993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5779293450203181217466629 1083617521913096478274993)
            ·
              refine ⟨812713141434822358706245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083617521913096478274993 812713141434822358706245)
              ·
                refine ⟨152383714019029192257421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 812713141434822358706245 152383714019029192257421)
                ·
                  rfl

theorem cell20_1001586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_1001586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001586 prefixEnd_1001586 := by exact prefixLift 1001586
  have htrace : WordTrace (prefixWord ++ tailWord_1001586) baseStart_1001586 baseEnd_1001586 := by
    simpa [prefixWord, tailWord_1001586, baseEnd_1001586] using wordTrace_append hprefix tailTrace_1001586
  have hstable : (prefixWord ++ tailWord_1001586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001586).length < 2 ^ (prefixWord ++ tailWord_1001586).sum := by decide
  have hdescent : baseEnd_1001586 < baseStart_1001586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001631 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 3]
def baseStart_1001631 : Nat := 118140960795 + 1001631 * 2 ^ 59
def prefixEnd_1001631 : Nat := 4983230072969 + 3 ^ 40 * 1001631 * 2
def baseEnd_1001631 : Nat := 457171681283267420272079

theorem tailTrace_1001631 : CollatzResearch.WordTrace tailWord_1001631 prefixEnd_1001631 457171681283267420272079 := by
  unfold tailWord_1001631
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532483834269426800732747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24354989222846284533821831 36532483834269426800732747)
  ·
    refine ⟨54798725751404140201099121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36532483834269426800732747 54798725751404140201099121)
    ·
      refine ⟨41099044313553105150824341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54798725751404140201099121 41099044313553105150824341)
      ·
        refine ⟨1926517702197801803944891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41099044313553105150824341 1926517702197801803944891)
        ·
          refine ⟨2889776553296702705917337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926517702197801803944891 2889776553296702705917337)
          ·
            refine ⟨2167332414972527029438003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2889776553296702705917337 2167332414972527029438003)
            ·
              refine ⟨3250998622458790544157005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167332414972527029438003 3250998622458790544157005)
              ·
                refine ⟨1219124483422046454058877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3250998622458790544157005 1219124483422046454058877)
                ·
                  refine ⟨457171681283267420272079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219124483422046454058877 457171681283267420272079)
                  ·
                    rfl

theorem cell20_1001631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 3].length) (baseStart_1001631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001631 prefixEnd_1001631 := by exact prefixLift 1001631
  have htrace : WordTrace (prefixWord ++ tailWord_1001631) baseStart_1001631 baseEnd_1001631 := by
    simpa [prefixWord, tailWord_1001631, baseEnd_1001631] using wordTrace_append hprefix tailTrace_1001631
  have hstable : (prefixWord ++ tailWord_1001631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001631).length < 2 ^ (prefixWord ++ tailWord_1001631).sum := by decide
  have hdescent : baseEnd_1001631 < baseStart_1001631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001645 : List Nat := [1, 5, 2, 1, 2, 1, 2, 6]
def baseStart_1001645 : Nat := 118140960795 + 1001645 * 2 ^ 59
def prefixEnd_1001645 : Nat := 4983230072969 + 3 ^ 40 * 1001645 * 2
def baseEnd_1001645 : Nat := 152392690421581864601785

theorem tailTrace_1001645 : CollatzResearch.WordTrace tailWord_1001645 prefixEnd_1001645 152392690421581864601785 := by
  unfold tailWord_1001645
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532994456218707191742389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24355329637479138127828259 36532994456218707191742389)
  ·
    refine ⟨3424968230270503799225849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36532994456218707191742389 3424968230270503799225849)
    ·
      refine ⟨2568726172702877849419387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3424968230270503799225849 2568726172702877849419387)
      ·
        refine ⟨3853089259054316774129081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2568726172702877849419387 3853089259054316774129081)
        ·
          refine ⟨2889816944290737580596811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3853089259054316774129081 2889816944290737580596811)
          ·
            refine ⟨4334725416436106370895217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889816944290737580596811 4334725416436106370895217)
            ·
              refine ⟨3251044062327079778171413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334725416436106370895217 3251044062327079778171413)
              ·
                refine ⟨152392690421581864601785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3251044062327079778171413 152392690421581864601785)
                ·
                  rfl

theorem cell20_1001645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_1001645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001645 prefixEnd_1001645 := by exact prefixLift 1001645
  have htrace : WordTrace (prefixWord ++ tailWord_1001645) baseStart_1001645 baseEnd_1001645 := by
    simpa [prefixWord, tailWord_1001645, baseEnd_1001645] using wordTrace_append hprefix tailTrace_1001645
  have hstable : (prefixWord ++ tailWord_1001645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001645).length < 2 ^ (prefixWord ++ tailWord_1001645).sum := by decide
  have hdescent : baseEnd_1001645 < baseStart_1001645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001680 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_1001680 : Nat := 118140960795 + 1001680 * 2 ^ 59
def prefixEnd_1001680 : Nat := 4983230072969 + 3 ^ 40 * 1001680 * 2
def baseEnd_1001680 : Nat := 457194046218441027638545

theorem tailTrace_1001680 : CollatzResearch.WordTrace tailWord_1001680 prefixEnd_1001680 457194046218441027638545 := by
  unfold tailWord_1001680
  simp only [CollatzResearch.WordTrace]
  refine ⟨18267135505545954084633247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24356180674061272112844329 18267135505545954084633247)
  ·
    refine ⟨27400703258318931126949871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18267135505545954084633247 27400703258318931126949871)
    ·
      refine ⟨41101054887478396690424807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27400703258318931126949871 41101054887478396690424807)
      ·
        refine ⟨61651582331217595035637211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41101054887478396690424807 61651582331217595035637211)
        ·
          refine ⟨92477373496826392553455817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61651582331217595035637211 92477373496826392553455817)
          ·
            refine ⟨69358030122619794415091863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92477373496826392553455817 69358030122619794415091863)
            ·
              refine ⟨104037045183929691622637795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69358030122619794415091863 104037045183929691622637795)
              ·
                refine ⟨156055567775894537433956693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104037045183929691622637795 156055567775894537433956693)
                ·
                  refine ⟨457194046218441027638545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 156055567775894537433956693 457194046218441027638545)
                  ·
                    rfl

theorem cell20_1001680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_1001680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001680 prefixEnd_1001680 := by exact prefixLift 1001680
  have htrace : WordTrace (prefixWord ++ tailWord_1001680) baseStart_1001680 baseEnd_1001680 := by
    simpa [prefixWord, tailWord_1001680, baseEnd_1001680] using wordTrace_append hprefix tailTrace_1001680
  have hstable : (prefixWord ++ tailWord_1001680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001680).length < 2 ^ (prefixWord ++ tailWord_1001680).sum := by decide
  have hdescent : baseEnd_1001680 < baseStart_1001680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001686 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1001686 : Nat := 118140960795 + 1001686 * 2 ^ 59
def prefixEnd_1001686 : Nat := 4983230072969 + 3 ^ 40 * 1001686 * 2
def baseEnd_1001686 : Nat := 457196784781931673438521

theorem tailTrace_1001686 : CollatzResearch.WordTrace tailWord_1001686 prefixEnd_1001686 457196784781931673438521 := by
  unfold tailWord_1001686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283405615566885699624057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24356326566046780795989941 2283405615566885699624057)
  ·
    refine ⟨1712554211675164274718043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2283405615566885699624057 1712554211675164274718043)
    ·
      refine ⟨2568831317512746412077065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1712554211675164274718043 2568831317512746412077065)
      ·
        refine ⟨1926623488134559809057799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2568831317512746412077065 1926623488134559809057799)
        ·
          refine ⟨2889935232201839713586699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926623488134559809057799 2889935232201839713586699)
          ·
            refine ⟨4334902848302759570380049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889935232201839713586699 4334902848302759570380049)
            ·
              refine ⟨3251177136227069677785037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334902848302759570380049 3251177136227069677785037)
              ·
                refine ⟨1219191426085151129169389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3251177136227069677785037 1219191426085151129169389)
                ·
                  refine ⟨457196784781931673438521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219191426085151129169389 457196784781931673438521)
                  ·
                    rfl

theorem cell20_1001686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1001686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001686 prefixEnd_1001686 := by exact prefixLift 1001686
  have htrace : WordTrace (prefixWord ++ tailWord_1001686) baseStart_1001686 baseEnd_1001686 := by
    simpa [prefixWord, tailWord_1001686, baseEnd_1001686] using wordTrace_append hprefix tailTrace_1001686
  have hstable : (prefixWord ++ tailWord_1001686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001686).length < 2 ^ (prefixWord ++ tailWord_1001686).sum := by decide
  have hdescent : baseEnd_1001686 < baseStart_1001686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001690 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_1001690 : Nat := 118140960795 + 1001690 * 2 ^ 59
def prefixEnd_1001690 : Nat := 4983230072969 + 3 ^ 40 * 1001690 * 2
def baseEnd_1001690 : Nat := 457198610490925437305171

theorem tailTrace_1001690 : CollatzResearch.WordTrace tailWord_1001690 prefixEnd_1001690 457198610490925437305171 := by
  unfold tailWord_1001690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133658935263919969282631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24356423827370453251420349 9133658935263919969282631)
  ·
    refine ⟨13700488402895879953923947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9133658935263919969282631 13700488402895879953923947)
    ·
      refine ⟨20550732604343819930885921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13700488402895879953923947 20550732604343819930885921)
      ·
        refine ⟨15413049453257864948164441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20550732604343819930885921 15413049453257864948164441)
        ·
          refine ⟨11559787089943398711123331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15413049453257864948164441 11559787089943398711123331)
          ·
            refine ⟨17339680634915098066684997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11559787089943398711123331 17339680634915098066684997)
            ·
              refine ⟨3251190119046580887503437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17339680634915098066684997 3251190119046580887503437)
              ·
                refine ⟨1219196294642467832813789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3251190119046580887503437 1219196294642467832813789)
                ·
                  refine ⟨457198610490925437305171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219196294642467832813789 457198610490925437305171)
                  ·
                    rfl

theorem cell20_1001690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_1001690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001690 prefixEnd_1001690 := by exact prefixLift 1001690
  have htrace : WordTrace (prefixWord ++ tailWord_1001690) baseStart_1001690 baseEnd_1001690 := by
    simpa [prefixWord, tailWord_1001690, baseEnd_1001690] using wordTrace_append hprefix tailTrace_1001690
  have hstable : (prefixWord ++ tailWord_1001690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001690).length < 2 ^ (prefixWord ++ tailWord_1001690).sum := by decide
  have hdescent : baseEnd_1001690 < baseStart_1001690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001697 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_1001697 : Nat := 118140960795 + 1001697 * 2 ^ 59
def prefixEnd_1001697 : Nat := 4983230072969 + 3 ^ 40 * 1001697 * 2
def baseEnd_1001697 : Nat := 457201805481664524071809

theorem tailTrace_1001697 : CollatzResearch.WordTrace tailWord_1001697 prefixEnd_1001697 457201805481664524071809 := by
  unfold tailWord_1001697
  simp only [CollatzResearch.WordTrace]
  refine ⟨36534891052030320072635345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24356594034686880048423563 36534891052030320072635345)
  ·
    refine ⟨27401168289022740054476509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36534891052030320072635345 27401168289022740054476509)
    ·
      refine ⟨10275438108383527520428691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27401168289022740054476509 10275438108383527520428691)
      ·
        refine ⟨15413157162575291280643037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10275438108383527520428691 15413157162575291280643037)
        ·
          refine ⟨5779933935965734230241139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15413157162575291280643037 5779933935965734230241139)
          ·
            refine ⟨8669900903948601345361709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779933935965734230241139 8669900903948601345361709)
            ·
              refine ⟨3251212838980725504510641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8669900903948601345361709 3251212838980725504510641)
              ·
                refine ⟨2438409629235544128382981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251212838980725504510641 2438409629235544128382981)
                ·
                  refine ⟨457201805481664524071809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2438409629235544128382981 457201805481664524071809)
                  ·
                    rfl

theorem cell20_1001697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_1001697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001697 prefixEnd_1001697 := by exact prefixLift 1001697
  have htrace : WordTrace (prefixWord ++ tailWord_1001697) baseStart_1001697 baseEnd_1001697 := by
    simpa [prefixWord, tailWord_1001697, baseEnd_1001697] using wordTrace_append hprefix tailTrace_1001697
  have hstable : (prefixWord ++ tailWord_1001697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001697).length < 2 ^ (prefixWord ++ tailWord_1001697).sum := by decide
  have hdescent : baseEnd_1001697 < baseStart_1001697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001728 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 3]
def baseStart_1001728 : Nat := 118140960795 + 1001728 * 2 ^ 59
def prefixEnd_1001728 : Nat := 4983230072969 + 3 ^ 40 * 1001728 * 2
def baseEnd_1001728 : Nat := 457215954726366194038349

theorem tailTrace_1001728 : CollatzResearch.WordTrace tailWord_1001728 prefixEnd_1001728 457215954726366194038349 := by
  unfold tailWord_1001728
  simp only [CollatzResearch.WordTrace]
  refine ⟨18268010857459006183506919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24357347809945341578009225 18268010857459006183506919)
  ·
    refine ⟨27402016286188509275260379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18268010857459006183506919 27402016286188509275260379)
    ·
      refine ⟨41103024429282763912890569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27402016286188509275260379 41103024429282763912890569)
      ·
        refine ⟨30827268321962072934667927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41103024429282763912890569 30827268321962072934667927)
        ·
          refine ⟨46240902482943109402001891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30827268321962072934667927 46240902482943109402001891)
          ·
            refine ⟨69361353724414664103002837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46240902482943109402001891 69361353724414664103002837)
            ·
              refine ⟨1625656727915968689914129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69361353724414664103002837 1625656727915968689914129)
              ·
                refine ⟨1219242545936976517435597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1625656727915968689914129 1219242545936976517435597)
                ·
                  refine ⟨457215954726366194038349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219242545936976517435597 457215954726366194038349)
                  ·
                    rfl

theorem cell20_1001728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_1001728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001728 prefixEnd_1001728 := by exact prefixLift 1001728
  have htrace : WordTrace (prefixWord ++ tailWord_1001728) baseStart_1001728 baseEnd_1001728 := by
    simpa [prefixWord, tailWord_1001728, baseEnd_1001728] using wordTrace_append hprefix tailTrace_1001728
  have hstable : (prefixWord ++ tailWord_1001728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001728).length < 2 ^ (prefixWord ++ tailWord_1001728).sum := by decide
  have hdescent : baseEnd_1001728 < baseStart_1001728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001742 : List Nat := [4, 1, 1, 2, 1, 2, 2, 7]
def baseStart_1001742 : Nat := 118140960795 + 1001742 * 2 ^ 59
def prefixEnd_1001742 : Nat := 4983230072969 + 3 ^ 40 * 1001742 * 2
def baseEnd_1001742 : Nat := 152407448235948122523875

theorem tailTrace_1001742 : CollatzResearch.WordTrace tailWord_1001742 prefixEnd_1001742 152407448235948122523875 := by
  unfold tailWord_1001742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567066542108411594752935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24357688224578195172015653 4567066542108411594752935)
  ·
    refine ⟨6850599813162617392129403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4567066542108411594752935 6850599813162617392129403)
    ·
      refine ⟨10275899719743926088194105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6850599813162617392129403 10275899719743926088194105)
      ·
        refine ⟨7706924789807944566145579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10275899719743926088194105 7706924789807944566145579)
        ·
          refine ⟨11560387184711916849218369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7706924789807944566145579 11560387184711916849218369)
          ·
            refine ⟨8670290388533937636913777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11560387184711916849218369 8670290388533937636913777)
            ·
              refine ⟨6502717791400453227685333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8670290388533937636913777 6502717791400453227685333)
              ·
                refine ⟨152407448235948122523875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6502717791400453227685333 152407448235948122523875)
                ·
                  rfl

theorem cell20_1001742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_1001742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001742 prefixEnd_1001742 := by exact prefixLift 1001742
  have htrace : WordTrace (prefixWord ++ tailWord_1001742) baseStart_1001742 baseEnd_1001742 := by
    simpa [prefixWord, tailWord_1001742, baseEnd_1001742] using wordTrace_append hprefix tailTrace_1001742
  have hstable : (prefixWord ++ tailWord_1001742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001742).length < 2 ^ (prefixWord ++ tailWord_1001742).sum := by decide
  have hdescent : baseEnd_1001742 < baseStart_1001742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001745 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 3]
def baseStart_1001745 : Nat := 118140960795 + 1001745 * 2 ^ 59
def prefixEnd_1001745 : Nat := 4983230072969 + 3 ^ 40 * 1001745 * 2
def baseEnd_1001745 : Nat := 457223713989589690471613

theorem tailTrace_1001745 : CollatzResearch.WordTrace tailWord_1001745 prefixEnd_1001745 457223713989589690471613 := by
  unfold tailWord_1001745
  simp only [CollatzResearch.WordTrace]
  refine ⟨36536641755856424270382689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24357761170570949513588459 36536641755856424270382689)
  ·
    refine ⟨27402481316892318202787017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36536641755856424270382689 27402481316892318202787017)
    ·
      refine ⟨20551860987669238652090263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27402481316892318202787017 20551860987669238652090263)
      ·
        refine ⟨30827791481503857978135395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20551860987669238652090263 30827791481503857978135395)
        ·
          refine ⟨46241687222255786967203093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30827791481503857978135395 46241687222255786967203093)
          ·
            refine ⟨2167579088543240014087645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46241687222255786967203093 2167579088543240014087645)
            ·
              refine ⟨812842158203715005282867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2167579088543240014087645 812842158203715005282867)
              ·
                refine ⟨1219263237305572507924301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812842158203715005282867 1219263237305572507924301)
                ·
                  refine ⟨457223713989589690471613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219263237305572507924301 457223713989589690471613)
                  ·
                    rfl

theorem cell20_1001745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_1001745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001745 prefixEnd_1001745 := by exact prefixLift 1001745
  have htrace : WordTrace (prefixWord ++ tailWord_1001745) baseStart_1001745 baseEnd_1001745 := by
    simpa [prefixWord, tailWord_1001745, baseEnd_1001745] using wordTrace_append hprefix tailTrace_1001745
  have hstable : (prefixWord ++ tailWord_1001745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001745).length < 2 ^ (prefixWord ++ tailWord_1001745).sum := by decide
  have hdescent : baseEnd_1001745 < baseStart_1001745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001759 : List Nat := [1, 1, 2, 4, 3, 1, 4, 4]
def baseStart_1001759 : Nat := 118140960795 + 1001759 * 2 ^ 59
def prefixEnd_1001759 : Nat := 4983230072969 + 3 ^ 40 * 1001759 * 2
def baseEnd_1001759 : Nat := 152410034657022621334963

theorem tailTrace_1001759 : CollatzResearch.WordTrace tailWord_1001759 prefixEnd_1001759 152410034657022621334963 := by
  unfold tailWord_1001759
  simp only [CollatzResearch.WordTrace]
  refine ⟨36537152377805704661392331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24358101585203803107594887 36537152377805704661392331)
  ·
    refine ⟨54805728566708556992088497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36537152377805704661392331 54805728566708556992088497)
    ·
      refine ⟨41104296425031417744066373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54805728566708556992088497 41104296425031417744066373)
      ·
        refine ⟨7707055579693390827012445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41104296425031417744066373 7707055579693390827012445)
        ·
          refine ⟨2890145842385021560129667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7707055579693390827012445 2890145842385021560129667)
          ·
            refine ⟨4335218763577532340194501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890145842385021560129667 4335218763577532340194501)
            ·
              refine ⟨812853518170787313786469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4335218763577532340194501 812853518170787313786469)
              ·
                refine ⟨152410034657022621334963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 812853518170787313786469 152410034657022621334963)
                ·
                  rfl

theorem cell20_1001759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 4].length) (baseStart_1001759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001759 prefixEnd_1001759 := by exact prefixLift 1001759
  have htrace : WordTrace (prefixWord ++ tailWord_1001759) baseStart_1001759 baseEnd_1001759 := by
    simpa [prefixWord, tailWord_1001759, baseEnd_1001759] using wordTrace_append hprefix tailTrace_1001759
  have hstable : (prefixWord ++ tailWord_1001759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001759).length < 2 ^ (prefixWord ++ tailWord_1001759).sum := by decide
  have hdescent : baseEnd_1001759 < baseStart_1001759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001790 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1001790 : Nat := 118140960795 + 1001790 * 2 ^ 59
def prefixEnd_1001790 : Nat := 4983230072969 + 3 ^ 40 * 1001790 * 2
def baseEnd_1001790 : Nat := 457244253215769533971429

theorem tailTrace_1001790 : CollatzResearch.WordTrace tailWord_1001790 prefixEnd_1001790 457244253215769533971429 := by
  unfold tailWord_1001790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567285380086674619471353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24358855360462264637180549 4567285380086674619471353)
  ·
    refine ⟨3425464035065005964603515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4567285380086674619471353 3425464035065005964603515)
    ·
      refine ⟨5138196052597508946905273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3425464035065005964603515 5138196052597508946905273)
      ·
        refine ⟨3853647039448131710178955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5138196052597508946905273 3853647039448131710178955)
        ·
          refine ⟨5780470559172197565268433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3853647039448131710178955 5780470559172197565268433)
          ·
            refine ⟨4335352919379148173951325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5780470559172197565268433 4335352919379148173951325)
            ·
              refine ⟨1625757344767180565231747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4335352919379148173951325 1625757344767180565231747)
              ·
                refine ⟨2438636017150770847847621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625757344767180565231747 2438636017150770847847621)
                ·
                  refine ⟨457244253215769533971429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2438636017150770847847621 457244253215769533971429)
                  ·
                    rfl

theorem cell20_1001790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1001790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001790 prefixEnd_1001790 := by exact prefixLift 1001790
  have htrace : WordTrace (prefixWord ++ tailWord_1001790) baseStart_1001790 baseEnd_1001790 := by
    simpa [prefixWord, tailWord_1001790, baseEnd_1001790] using wordTrace_append hprefix tailTrace_1001790
  have hstable : (prefixWord ++ tailWord_1001790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001790).length < 2 ^ (prefixWord ++ tailWord_1001790).sum := by decide
  have hdescent : baseEnd_1001790 < baseStart_1001790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001796 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 3]
def baseStart_1001796 : Nat := 118140960795 + 1001796 * 2 ^ 59
def prefixEnd_1001796 : Nat := 4983230072969 + 3 ^ 40 * 1001796 * 2
def baseEnd_1001796 : Nat := 457246991779260179771405

theorem tailTrace_1001796 : CollatzResearch.WordTrace tailWord_1001796 prefixEnd_1001796 457246991779260179771405 := by
  unfold tailWord_1001796
  simp only [CollatzResearch.WordTrace]
  refine ⟨18269250939335829990244621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24359001252447773320326161 18269250939335829990244621)
  ·
    refine ⟨6850969102250936246341733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18269250939335829990244621 6850969102250936246341733)
    ·
      refine ⟨1284556706672050546189075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6850969102250936246341733 1284556706672050546189075)
      ·
        refine ⟨1926835060008075819283613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284556706672050546189075 1926835060008075819283613)
        ·
          refine ⟨722563147503028432231355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1926835060008075819283613 722563147503028432231355)
          ·
            refine ⟨1083844721254542648347033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722563147503028432231355 1083844721254542648347033)
            ·
              refine ⟨812883540940906986260275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083844721254542648347033 812883540940906986260275)
              ·
                refine ⟨1219325311411360479390413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812883540940906986260275 1219325311411360479390413)
                ·
                  refine ⟨457246991779260179771405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219325311411360479390413 457246991779260179771405)
                  ·
                    rfl

theorem cell20_1001796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_1001796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001796 prefixEnd_1001796 := by exact prefixLift 1001796
  have htrace : WordTrace (prefixWord ++ tailWord_1001796) baseStart_1001796 baseEnd_1001796 := by
    simpa [prefixWord, tailWord_1001796, baseEnd_1001796] using wordTrace_append hprefix tailTrace_1001796
  have hstable : (prefixWord ++ tailWord_1001796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001796).length < 2 ^ (prefixWord ++ tailWord_1001796).sum := by decide
  have hdescent : baseEnd_1001796 < baseStart_1001796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001804 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 3]
def baseStart_1001804 : Nat := 118140960795 + 1001804 * 2 ^ 59
def prefixEnd_1001804 : Nat := 4983230072969 + 3 ^ 40 * 1001804 * 2
def baseEnd_1001804 : Nat := 457250643197247707504705

theorem tailTrace_1001804 : CollatzResearch.WordTrace tailWord_1001804 prefixEnd_1001804 457250643197247707504705 := by
  unfold tailWord_1001804
  simp only [CollatzResearch.WordTrace]
  refine ⟨18269396831321338673390233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24359195775095118231186977 18269396831321338673390233)
  ·
    refine ⟨13702047623491004005042675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18269396831321338673390233 13702047623491004005042675)
    ·
      refine ⟨20553071435236506007564013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13702047623491004005042675 20553071435236506007564013)
      ·
        refine ⟨7707401788213689752836505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20553071435236506007564013 7707401788213689752836505)
        ·
          refine ⟨5780551341160267314627379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7707401788213689752836505 5780551341160267314627379)
          ·
            refine ⟨8670827011740400971941069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780551341160267314627379 8670827011740400971941069)
            ·
              refine ⟨3251560129402650364477901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8670827011740400971941069 3251560129402650364477901)
              ·
                refine ⟨1219335048525993886679213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3251560129402650364477901 1219335048525993886679213)
                ·
                  refine ⟨457250643197247707504705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219335048525993886679213 457250643197247707504705)
                  ·
                    rfl

theorem cell20_1001804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_1001804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001804 prefixEnd_1001804 := by exact prefixLift 1001804
  have htrace : WordTrace (prefixWord ++ tailWord_1001804) baseStart_1001804 baseEnd_1001804 := by
    simpa [prefixWord, tailWord_1001804, baseEnd_1001804] using wordTrace_append hprefix tailTrace_1001804
  have hstable : (prefixWord ++ tailWord_1001804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001804).length < 2 ^ (prefixWord ++ tailWord_1001804).sum := by decide
  have hdescent : baseEnd_1001804 < baseStart_1001804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001828 : List Nat := [2, 3, 1, 1, 3, 1, 2, 5, 2]
def baseStart_1001828 : Nat := 118140960795 + 1001828 * 2 ^ 59
def prefixEnd_1001828 : Nat := 4983230072969 + 3 ^ 40 * 1001828 * 2
def baseEnd_1001828 : Nat := 457261597451210290704607

theorem tailTrace_1001828 : CollatzResearch.WordTrace tailWord_1001828 prefixEnd_1001828 457261597451210290704607 := by
  unfold tailWord_1001828
  simp only [CollatzResearch.WordTrace]
  refine ⟨18269834507277864722827069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24359779343037152963769425 18269834507277864722827069)
  ·
    refine ⟨6851187940229199271060151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18269834507277864722827069 6851187940229199271060151)
    ·
      refine ⟨10276781910343798906590227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6851187940229199271060151 10276781910343798906590227)
      ·
        refine ⟨15415172865515698359885341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10276781910343798906590227 15415172865515698359885341)
        ·
          refine ⟨5780689824568386884957003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15415172865515698359885341 5780689824568386884957003)
          ·
            refine ⟨8671034736852580327435505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780689824568386884957003 8671034736852580327435505)
            ·
              refine ⟨6503276052639435245576629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8671034736852580327435505 6503276052639435245576629)
              ·
                refine ⟨609682129934947054272809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6503276052639435245576629 609682129934947054272809)
                ·
                  refine ⟨457261597451210290704607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609682129934947054272809 457261597451210290704607)
                  ·
                    rfl

theorem cell20_1001828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_1001828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001828 prefixEnd_1001828 := by exact prefixLift 1001828
  have htrace : WordTrace (prefixWord ++ tailWord_1001828) baseStart_1001828 baseEnd_1001828 := by
    simpa [prefixWord, tailWord_1001828, baseEnd_1001828] using wordTrace_append hprefix tailTrace_1001828
  have hstable : (prefixWord ++ tailWord_1001828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001828).length < 2 ^ (prefixWord ++ tailWord_1001828).sum := by decide
  have hdescent : baseEnd_1001828 < baseStart_1001828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001842 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_1001842 : Nat := 118140960795 + 1001842 * 2 ^ 59
def prefixEnd_1001842 : Nat := 4983230072969 + 3 ^ 40 * 1001842 * 2
def baseEnd_1001842 : Nat := 457267987432688464237883

theorem tailTrace_1001842 : CollatzResearch.WordTrace tailWord_1001842 prefixEnd_1001842 457267987432688464237883 := by
  unfold tailWord_1001842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9135044909126252459165945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24360119757670006557775853 9135044909126252459165945)
  ·
    refine ⟨6851283681844689344374459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9135044909126252459165945 6851283681844689344374459)
    ·
      refine ⟨10276925522767034016561689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6851283681844689344374459 10276925522767034016561689)
      ·
        refine ⟨7707694142075275512421267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10276925522767034016561689 7707694142075275512421267)
        ·
          refine ⟨11561541213112913268631901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7707694142075275512421267 11561541213112913268631901)
          ·
            refine ⟨4335577954917342475736963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11561541213112913268631901 4335577954917342475736963)
            ·
              refine ⟨6503366932376013713605445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335577954917342475736963 6503366932376013713605445)
              ·
                refine ⟨1219381299820502571301021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6503366932376013713605445 1219381299820502571301021)
                ·
                  refine ⟨457267987432688464237883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219381299820502571301021 457267987432688464237883)
                  ·
                    rfl

theorem cell20_1001842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_1001842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001842 prefixEnd_1001842 := by exact prefixLift 1001842
  have htrace : WordTrace (prefixWord ++ tailWord_1001842) baseStart_1001842 baseEnd_1001842 := by
    simpa [prefixWord, tailWord_1001842, baseEnd_1001842] using wordTrace_append hprefix tailTrace_1001842
  have hstable : (prefixWord ++ tailWord_1001842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001842).length < 2 ^ (prefixWord ++ tailWord_1001842).sum := by decide
  have hdescent : baseEnd_1001842 < baseStart_1001842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001845 : List Nat := [1, 3, 4, 1, 2, 2, 1, 4, 2]
def baseStart_1001845 : Nat := 118140960795 + 1001845 * 2 ^ 59
def prefixEnd_1001845 : Nat := 4983230072969 + 3 ^ 40 * 1001845 * 2
def baseEnd_1001845 : Nat := 457269356714433787137871

theorem tailTrace_1001845 : CollatzResearch.WordTrace tailWord_1001845 prefixEnd_1001845 457269356714433787137871 := by
  unfold tailWord_1001845
  simp only [CollatzResearch.WordTrace]
  refine ⟨36540289055494141349022989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24360192703662760899348659 36540289055494141349022989)
  ·
    refine ⟨13702608395810303005883621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36540289055494141349022989 13702608395810303005883621)
    ·
      refine ⟨2569239074214431813603179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13702608395810303005883621 2569239074214431813603179)
      ·
        refine ⟨3853858611321647720404769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569239074214431813603179 3853858611321647720404769)
        ·
          refine ⟨2890393958491235790303577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3853858611321647720404769 2890393958491235790303577)
          ·
            refine ⟨2167795468868426842727683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2890393958491235790303577 2167795468868426842727683)
            ·
              refine ⟨3251693203302640264091525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167795468868426842727683 3251693203302640264091525)
              ·
                refine ⟨609692475619245049517161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3251693203302640264091525 609692475619245049517161)
                ·
                  refine ⟨457269356714433787137871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609692475619245049517161 457269356714433787137871)
                  ·
                    rfl

theorem cell20_1001845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_1001845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001845 prefixEnd_1001845 := by exact prefixLift 1001845
  have htrace : WordTrace (prefixWord ++ tailWord_1001845) baseStart_1001845 baseEnd_1001845 := by
    simpa [prefixWord, tailWord_1001845, baseEnd_1001845] using wordTrace_append hprefix tailTrace_1001845
  have hstable : (prefixWord ++ tailWord_1001845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001845).length < 2 ^ (prefixWord ++ tailWord_1001845).sum := by decide
  have hdescent : baseEnd_1001845 < baseStart_1001845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001918 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1001918 : Nat := 118140960795 + 1001918 * 2 ^ 59
def prefixEnd_1001918 : Nat := 4983230072969 + 3 ^ 40 * 1001918 * 2
def baseEnd_1001918 : Nat := 457302675903569977704239

theorem tailTrace_1001918 : CollatzResearch.WordTrace tailWord_1001918 prefixEnd_1001918 457302675903569977704239 := by
  unfold tailWord_1001918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567868948028709352053801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24361967722819783210953605 4567868948028709352053801)
  ·
    refine ⟨3425901711021532014040351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4567868948028709352053801 3425901711021532014040351)
    ·
      refine ⟨5138852566532298021060527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3425901711021532014040351 5138852566532298021060527)
      ·
        refine ⟨7708278849798447031590791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5138852566532298021060527 7708278849798447031590791)
        ·
          refine ⟨11562418274697670547386187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708278849798447031590791 11562418274697670547386187)
          ·
            refine ⟨17343627412046505821079281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11562418274697670547386187 17343627412046505821079281)
            ·
              refine ⟨13007720559034879365809461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17343627412046505821079281 13007720559034879365809461)
              ·
                refine ⟨1219473802409519940544637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13007720559034879365809461 1219473802409519940544637)
                ·
                  refine ⟨457302675903569977704239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219473802409519940544637 457302675903569977704239)
                  ·
                    rfl

theorem cell20_1001918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1001918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001918 prefixEnd_1001918 := by exact prefixLift 1001918
  have htrace : WordTrace (prefixWord ++ tailWord_1001918) baseStart_1001918 baseEnd_1001918 := by
    simpa [prefixWord, tailWord_1001918, baseEnd_1001918] using wordTrace_append hprefix tailTrace_1001918
  have hstable : (prefixWord ++ tailWord_1001918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001918).length < 2 ^ (prefixWord ++ tailWord_1001918).sum := by decide
  have hdescent : baseEnd_1001918 < baseStart_1001918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001959 : List Nat := [1, 1, 5, 2, 1, 1, 5, 2, 2]
def baseStart_1001959 : Nat := 118140960795 + 1001959 * 2 ^ 59
def prefixEnd_1001959 : Nat := 4983230072969 + 3 ^ 40 * 1001959 * 2
def baseEnd_1001959 : Nat := 457321389420756057337405

theorem tailTrace_1001959 : CollatzResearch.WordTrace tailWord_1001959 prefixEnd_1001959 457321389420756057337405 := by
  unfold tailWord_1001959
  simp only [CollatzResearch.WordTrace]
  refine ⟨36544446977081138818672931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24362964651387425879115287 36544446977081138818672931)
  ·
    refine ⟨54816670465621708228009397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36544446977081138818672931 54816670465621708228009397)
    ·
      refine ⟨5139062856152035146375881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54816670465621708228009397 5139062856152035146375881)
      ·
        refine ⟨3854297142114026359781911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5139062856152035146375881 3854297142114026359781911)
        ·
          refine ⟨5781445713171039539672867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854297142114026359781911 5781445713171039539672867)
          ·
            refine ⟨8672168569756559309509301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781445713171039539672867 8672168569756559309509301)
            ·
              refine ⟨813015803414677435266497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8672168569756559309509301 813015803414677435266497)
              ·
                refine ⟨609761852561008076449873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813015803414677435266497 609761852561008076449873)
                ·
                  refine ⟨457321389420756057337405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609761852561008076449873 457321389420756057337405)
                  ·
                    rfl

theorem cell20_1001959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 2].length) (baseStart_1001959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1001959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1001959 prefixEnd_1001959 := by exact prefixLift 1001959
  have htrace : WordTrace (prefixWord ++ tailWord_1001959) baseStart_1001959 baseEnd_1001959 := by
    simpa [prefixWord, tailWord_1001959, baseEnd_1001959] using wordTrace_append hprefix tailTrace_1001959
  have hstable : (prefixWord ++ tailWord_1001959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001959).length < 2 ^ (prefixWord ++ tailWord_1001959).sum := by decide
  have hdescent : baseEnd_1001959 < baseStart_1001959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002060 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_1002060 : Nat := 118140960795 + 1002060 * 2 ^ 59
def prefixEnd_1002060 : Nat := 4983230072969 + 3 ^ 40 * 1002060 * 2
def baseEnd_1002060 : Nat := 457367488572848594970325

theorem tailTrace_1002060 : CollatzResearch.WordTrace tailWord_1002060 prefixEnd_1002060 457367488572848594970325 := by
  unfold tailWord_1002060
  simp only [CollatzResearch.WordTrace]
  refine ⟨18274065374857616534049817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24365420499810155378733089 18274065374857616534049817)
  ·
    refine ⟨13705549031143212400537363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18274065374857616534049817 13705549031143212400537363)
    ·
      refine ⟨20558323546714818600806045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13705549031143212400537363 20558323546714818600806045)
      ·
        refine ⟨7709371330018056975302267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20558323546714818600806045 7709371330018056975302267)
        ·
          refine ⟨11564056995027085462953401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709371330018056975302267 11564056995027085462953401)
          ·
            refine ⟨8673042746270314097215051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11564056995027085462953401 8673042746270314097215051)
            ·
              refine ⟨13009564119405471145822577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8673042746270314097215051 13009564119405471145822577)
              ·
                refine ⟨9757173089554103359366933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13009564119405471145822577 9757173089554103359366933)
                ·
                  refine ⟨457367488572848594970325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9757173089554103359366933 457367488572848594970325)
                  ·
                    rfl

theorem cell20_1002060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_1002060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002060 prefixEnd_1002060 := by exact prefixLift 1002060
  have htrace : WordTrace (prefixWord ++ tailWord_1002060) baseStart_1002060 baseEnd_1002060 := by
    simpa [prefixWord, tailWord_1002060, baseEnd_1002060] using wordTrace_append hprefix tailTrace_1002060
  have hstable : (prefixWord ++ tailWord_1002060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002060).length < 2 ^ (prefixWord ++ tailWord_1002060).sum := by decide
  have hdescent : baseEnd_1002060 < baseStart_1002060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002101 : List Nat := [1, 3, 4, 2, 2, 1, 1, 6]
def baseStart_1002101 : Nat := 118140960795 + 1002101 * 2 ^ 59
def prefixEnd_1002101 : Nat := 4983230072969 + 3 ^ 40 * 1002101 * 2
def baseEnd_1002101 : Nat := 152462067363344891534497

theorem tailTrace_1002101 : CollatzResearch.WordTrace tailWord_1002101 prefixEnd_1002101 152462067363344891534497 := by
  unfold tailWord_1002101
  simp only [CollatzResearch.WordTrace]
  refine ⟨36549626142566697070342157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24366417428377798046894771 36549626142566697070342157)
  ·
    refine ⟨13706109803462511401378309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36549626142566697070342157 13706109803462511401378309)
    ·
      refine ⟨2569895588149220887758433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13706109803462511401378309 2569895588149220887758433)
      ·
        refine ⟨1927421691111915665818825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2569895588149220887758433 1927421691111915665818825)
        ·
          refine ⟨1445566268333936749364119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1927421691111915665818825 1445566268333936749364119)
          ·
            refine ⟨2168349402500905124046179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445566268333936749364119 2168349402500905124046179)
            ·
              refine ⟨3252524103751357686069269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168349402500905124046179 3252524103751357686069269)
              ·
                refine ⟨152462067363344891534497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3252524103751357686069269 152462067363344891534497)
                ·
                  rfl

theorem cell20_1002101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 6].length) (baseStart_1002101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002101 prefixEnd_1002101 := by exact prefixLift 1002101
  have htrace : WordTrace (prefixWord ++ tailWord_1002101) baseStart_1002101 baseEnd_1002101 := by
    simpa [prefixWord, tailWord_1002101, baseEnd_1002101] using wordTrace_append hprefix tailTrace_1002101
  have hstable : (prefixWord ++ tailWord_1002101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002101).length < 2 ^ (prefixWord ++ tailWord_1002101).sum := by decide
  have hdescent : baseEnd_1002101 < baseStart_1002101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002114 : List Nat := [3, 4, 3, 1, 2, 1, 6]
def baseStart_1002114 : Nat := 118140960795 + 1002114 * 2 ^ 59
def prefixEnd_1002114 : Nat := 4983230072969 + 3 ^ 40 * 1002114 * 2
def baseEnd_1002114 : Nat := 50821348404918267463345

theorem tailTrace_1002114 : CollatzResearch.WordTrace tailWord_1002114 prefixEnd_1002114 50821348404918267463345 := by
  unfold tailWord_1002114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9137525072879900072641349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24366733527679733527043597 9137525072879900072641349)
  ·
    refine ⟨1713285951164981263620253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9137525072879900072641349 1713285951164981263620253)
    ·
      refine ⟨642482231686867973857595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1713285951164981263620253 642482231686867973857595)
      ·
        refine ⟨963723347530301960786393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642482231686867973857595 963723347530301960786393)
        ·
          refine ⟨722792510647726470589795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963723347530301960786393 722792510647726470589795)
          ·
            refine ⟨1084188765971589705884693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722792510647726470589795 1084188765971589705884693)
            ·
              refine ⟨50821348404918267463345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1084188765971589705884693 50821348404918267463345)
              ·
                rfl

theorem cell20_1002114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 6].length) (baseStart_1002114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002114 prefixEnd_1002114 := by exact prefixLift 1002114
  have htrace : WordTrace (prefixWord ++ tailWord_1002114) baseStart_1002114 baseEnd_1002114 := by
    simpa [prefixWord, tailWord_1002114, baseEnd_1002114] using wordTrace_append hprefix tailTrace_1002114
  have hstable : (prefixWord ++ tailWord_1002114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002114).length < 2 ^ (prefixWord ++ tailWord_1002114).sum := by decide
  have hdescent : baseEnd_1002114 < baseStart_1002114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002132 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1002132 : Nat := 118140960795 + 1002132 * 2 ^ 59
def prefixEnd_1002132 : Nat := 4983230072969 + 3 ^ 40 * 1002132 * 2
def baseEnd_1002132 : Nat := 457400351334736344570031

theorem tailTrace_1002132 : CollatzResearch.WordTrace tailWord_1002132 prefixEnd_1002132 457400351334736344570031 := by
  unfold tailWord_1002132
  simp only [CollatzResearch.WordTrace]
  refine ⟨18275378402727194682360325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24367171203636259576480433 18275378402727194682360325)
  ·
    refine ⟨3426633450511349002942561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18275378402727194682360325 3426633450511349002942561)
    ·
      refine ⟨2569975087883511752206921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3426633450511349002942561 2569975087883511752206921)
      ·
        refine ⟨1927481315912633814155191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2569975087883511752206921 1927481315912633814155191)
        ·
          refine ⟨2891221973868950721232787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927481315912633814155191 2891221973868950721232787)
          ·
            refine ⟨4336832960803426081849181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891221973868950721232787 4336832960803426081849181)
            ·
              refine ⟨1626312360301284780693443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4336832960803426081849181 1626312360301284780693443)
              ·
                refine ⟨2439468540451927171040165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626312360301284780693443 2439468540451927171040165)
                ·
                  refine ⟨457400351334736344570031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2439468540451927171040165 457400351334736344570031)
                  ·
                    rfl

theorem cell20_1002132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1002132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002132 prefixEnd_1002132 := by exact prefixLift 1002132
  have htrace : WordTrace (prefixWord ++ tailWord_1002132) baseStart_1002132 baseEnd_1002132 := by
    simpa [prefixWord, tailWord_1002132, baseEnd_1002132] using wordTrace_append hprefix tailTrace_1002132
  have hstable : (prefixWord ++ tailWord_1002132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002132).length < 2 ^ (prefixWord ++ tailWord_1002132).sum := by decide
  have hdescent : baseEnd_1002132 < baseStart_1002132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002177 : List Nat := [1, 2, 6, 2, 1, 8]
def baseStart_1002177 : Nat := 118140960795 + 1002177 * 2 ^ 59
def prefixEnd_1002177 : Nat := 4983230072969 + 3 ^ 40 * 1002177 * 2
def baseEnd_1002177 : Nat := 16941514465219118076661

theorem tailTrace_1002177 : CollatzResearch.WordTrace tailWord_1002177 prefixEnd_1002177 16941514465219118076661 := by
  unfold tailWord_1002177
  simp only [CollatzResearch.WordTrace]
  refine ⟨36552398090291362050108785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24368265393527574700072523 36552398090291362050108785)
  ·
    refine ⟨27414298567718521537581589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36552398090291362050108785 27414298567718521537581589)
    ·
      refine ⟨1285045245361805697074137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27414298567718521537581589 1285045245361805697074137)
      ·
        refine ⟨963783934021354272805603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1285045245361805697074137 963783934021354272805603)
        ·
          refine ⟨1445675901032031409208405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963783934021354272805603 1445675901032031409208405)
          ·
            refine ⟨16941514465219118076661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1445675901032031409208405 16941514465219118076661)
            ·
              rfl

theorem cell20_1002177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 8].length) (baseStart_1002177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002177 prefixEnd_1002177 := by exact prefixLift 1002177
  have htrace : WordTrace (prefixWord ++ tailWord_1002177) baseStart_1002177 baseEnd_1002177 := by
    simpa [prefixWord, tailWord_1002177, baseEnd_1002177] using wordTrace_append hprefix tailTrace_1002177
  have hstable : (prefixWord ++ tailWord_1002177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002177).length < 2 ^ (prefixWord ++ tailWord_1002177).sum := by decide
  have hdescent : baseEnd_1002177 < baseStart_1002177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002184 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 3]
def baseStart_1002184 : Nat := 118140960795 + 1002184 * 2 ^ 59
def prefixEnd_1002184 : Nat := 4983230072969 + 3 ^ 40 * 1002184 * 2
def baseEnd_1002184 : Nat := 457424085551655274836485

theorem tailTrace_1002184 : CollatzResearch.WordTrace tailWord_1002184 prefixEnd_1002184 457424085551655274836485 := by
  unfold tailWord_1002184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18276326700633001122806803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24368435600844001497075737 18276326700633001122806803)
  ·
    refine ⟨27414490050949501684210205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18276326700633001122806803 27414490050949501684210205)
    ·
      refine ⟨10280433769106063131578827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27414490050949501684210205 10280433769106063131578827)
      ·
        refine ⟨15420650653659094697368241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10280433769106063131578827 15420650653659094697368241)
        ·
          refine ⟨11565487990244321023026181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15420650653659094697368241 11565487990244321023026181)
          ·
            refine ⟨2168528998170810191817409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11565487990244321023026181 2168528998170810191817409)
            ·
              refine ⟨1626396748628107643863057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168528998170810191817409 1626396748628107643863057)
              ·
                refine ⟨1219797561471080732897293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626396748628107643863057 1219797561471080732897293)
                ·
                  refine ⟨457424085551655274836485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219797561471080732897293 457424085551655274836485)
                  ·
                    rfl

theorem cell20_1002184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_1002184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002184 prefixEnd_1002184 := by exact prefixLift 1002184
  have htrace : WordTrace (prefixWord ++ tailWord_1002184) baseStart_1002184 baseEnd_1002184 := by
    simpa [prefixWord, tailWord_1002184, baseEnd_1002184] using wordTrace_append hprefix tailTrace_1002184
  have hstable : (prefixWord ++ tailWord_1002184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002184).length < 2 ^ (prefixWord ++ tailWord_1002184).sum := by decide
  have hdescent : baseEnd_1002184 < baseStart_1002184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002194 : List Nat := [3, 2, 2, 2, 4, 1, 1, 5]
def baseStart_1002194 : Nat := 118140960795 + 1002194 * 2 ^ 59
def prefixEnd_1002194 : Nat := 4983230072969 + 3 ^ 40 * 1002194 * 2
def baseEnd_1002194 : Nat := 152476216608046561501037

theorem tailTrace_1002194 : CollatzResearch.WordTrace tailWord_1002194 prefixEnd_1002194 152476216608046561501037 := by
  unfold tailWord_1002194
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138254532807443488369409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24368678754153182635651757 9138254532807443488369409)
  ·
    refine ⟨6853690899605582616277057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9138254532807443488369409 6853690899605582616277057)
    ·
      refine ⟨5140268174704186962207793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6853690899605582616277057 5140268174704186962207793)
      ·
        refine ⟨3855201131028140221655845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5140268174704186962207793 3855201131028140221655845)
        ·
          refine ⟨722850212067776291560471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3855201131028140221655845 722850212067776291560471)
          ·
            refine ⟨1084275318101664437340707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722850212067776291560471 1084275318101664437340707)
            ·
              refine ⟨1626412977152496656011061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084275318101664437340707 1626412977152496656011061)
              ·
                refine ⟨152476216608046561501037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1626412977152496656011061 152476216608046561501037)
                ·
                  rfl

theorem cell20_1002194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_1002194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002194 prefixEnd_1002194 := by exact prefixLift 1002194
  have htrace : WordTrace (prefixWord ++ tailWord_1002194) baseStart_1002194 baseEnd_1002194 := by
    simpa [prefixWord, tailWord_1002194, baseEnd_1002194] using wordTrace_append hprefix tailTrace_1002194
  have hstable : (prefixWord ++ tailWord_1002194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002194).length < 2 ^ (prefixWord ++ tailWord_1002194).sum := by decide
  have hdescent : baseEnd_1002194 < baseStart_1002194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002212 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1002212 : Nat := 118140960795 + 1002212 * 2 ^ 59
def prefixEnd_1002212 : Nat := 4983230072969 + 3 ^ 40 * 1002212 * 2
def baseEnd_1002212 : Nat := 457436865514611621903037

theorem tailTrace_1002212 : CollatzResearch.WordTrace tailWord_1002212 prefixEnd_1002212 457436865514611621903037 := by
  unfold tailWord_1002212
  simp only [CollatzResearch.WordTrace]
  refine ⟨18276837322582281513816445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24369116430109708685088593 18276837322582281513816445)
  ·
    refine ⟨6853813995968355567681167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18276837322582281513816445 6853813995968355567681167)
    ·
      refine ⟨10280720993952533351521751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6853813995968355567681167 10280720993952533351521751)
      ·
        refine ⟨15421081490928800027282627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10280720993952533351521751 15421081490928800027282627)
        ·
          refine ⟨23131622236393200040923941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15421081490928800027282627 23131622236393200040923941)
          ·
            refine ⟨4337179169323725007673239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23131622236393200040923941 4337179169323725007673239)
            ·
              refine ⟨6505768753985587511509859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337179169323725007673239 6505768753985587511509859)
              ·
                refine ⟨9758653130978381267264789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6505768753985587511509859 9758653130978381267264789)
                ·
                  refine ⟨457436865514611621903037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9758653130978381267264789 457436865514611621903037)
                  ·
                    rfl

theorem cell20_1002212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1002212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002212 prefixEnd_1002212 := by exact prefixLift 1002212
  have htrace : WordTrace (prefixWord ++ tailWord_1002212) baseStart_1002212 baseEnd_1002212 := by
    simpa [prefixWord, tailWord_1002212, baseEnd_1002212] using wordTrace_append hprefix tailTrace_1002212
  have hstable : (prefixWord ++ tailWord_1002212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002212).length < 2 ^ (prefixWord ++ tailWord_1002212).sum := by decide
  have hdescent : baseEnd_1002212 < baseStart_1002212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002274 : List Nat := [3, 3, 1, 1, 2, 3, 1, 6]
def baseStart_1002274 : Nat := 118140960795 + 1002274 * 2 ^ 59
def prefixEnd_1002274 : Nat := 4983230072969 + 3 ^ 40 * 1002274 * 2
def baseEnd_1002274 : Nat := 152488388001338320612039

theorem tailTrace_1002274 : CollatzResearch.WordTrace tailWord_1002274 prefixEnd_1002274 152488388001338320612039 := by
  unfold tailWord_1002274
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138983992734986904097469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24370623980626631744259917 9138983992734986904097469)
  ·
    refine ⟨3427118997275620089036551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9138983992734986904097469 3427118997275620089036551)
    ·
      refine ⟨5140678495913430133554827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427118997275620089036551 5140678495913430133554827)
      ·
        refine ⟨7711017743870145200332241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140678495913430133554827 7711017743870145200332241)
        ·
          refine ⟨5783263307902608900249181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7711017743870145200332241 5783263307902608900249181)
          ·
            refine ⟨2168723740463478337593443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5783263307902608900249181 2168723740463478337593443)
            ·
              refine ⟨3253085610695217506390165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168723740463478337593443 3253085610695217506390165)
              ·
                refine ⟨152488388001338320612039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3253085610695217506390165 152488388001338320612039)
                ·
                  rfl

theorem cell20_1002274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_1002274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002274 prefixEnd_1002274 := by exact prefixLift 1002274
  have htrace : WordTrace (prefixWord ++ tailWord_1002274) baseStart_1002274 baseEnd_1002274 := by
    simpa [prefixWord, tailWord_1002274, baseEnd_1002274] using wordTrace_append hprefix tailTrace_1002274
  have hstable : (prefixWord ++ tailWord_1002274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002274).length < 2 ^ (prefixWord ++ tailWord_1002274).sum := by decide
  have hdescent : baseEnd_1002274 < baseStart_1002274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002301 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 4]
def baseStart_1002301 : Nat := 118140960795 + 1002301 * 2 ^ 59
def prefixEnd_1002301 : Nat := 4983230072969 + 3 ^ 40 * 1002301 * 2
def baseEnd_1002301 : Nat := 457477487539722867936007

theorem tailTrace_1002301 : CollatzResearch.WordTrace tailWord_1002301 prefixEnd_1002301 457477487539722867936007 := by
  unfold tailWord_1002301
  simp only [CollatzResearch.WordTrace]
  refine ⟨36556920741842131227622757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24371280494561420818415171 36556920741842131227622757)
  ·
    refine ⟨6854422639095399605179267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36556920741842131227622757 6854422639095399605179267)
    ·
      refine ⟨10281633958643099407768901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6854422639095399605179267 10281633958643099407768901)
      ·
        refine ⟨1927806367245581138956669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10281633958643099407768901 1927806367245581138956669)
        ·
          refine ⟨722927387717092927108751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1927806367245581138956669 722927387717092927108751)
          ·
            refine ⟨1084391081575639390663127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722927387717092927108751 1084391081575639390663127)
            ·
              refine ⟨1626586622363459085994691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084391081575639390663127 1626586622363459085994691)
              ·
                refine ⟨2439879933545188628992037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626586622363459085994691 2439879933545188628992037)
                ·
                  refine ⟨457477487539722867936007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2439879933545188628992037 457477487539722867936007)
                  ·
                    rfl

theorem cell20_1002301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_1002301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002301 prefixEnd_1002301 := by exact prefixLift 1002301
  have htrace : WordTrace (prefixWord ++ tailWord_1002301) baseStart_1002301 baseEnd_1002301 := by
    simpa [prefixWord, tailWord_1002301, baseEnd_1002301] using wordTrace_append hprefix tailTrace_1002301
  have hstable : (prefixWord ++ tailWord_1002301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002301).length < 2 ^ (prefixWord ++ tailWord_1002301).sum := by decide
  have hdescent : baseEnd_1002301 < baseStart_1002301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002308 : List Nat := [2, 3, 4, 2, 1, 1, 2, 5]
def baseStart_1002308 : Nat := 118140960795 + 1002308 * 2 ^ 59
def prefixEnd_1002308 : Nat := 4983230072969 + 3 ^ 40 * 1002308 * 2
def baseEnd_1002308 : Nat := 152493560843487318234215

theorem tailTrace_1002308 : CollatzResearch.WordTrace tailWord_1002308 prefixEnd_1002308 152493560843487318234215 := by
  unfold tailWord_1002308
  simp only [CollatzResearch.WordTrace]
  refine ⟨18278588026408385711563789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24371450701877847615418385 18278588026408385711563789)
  ·
    refine ⟨6854470509903144641836421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18278588026408385711563789 6854470509903144641836421)
    ·
      refine ⟨1285213220606839620344329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6854470509903144641836421 1285213220606839620344329)
      ·
        refine ⟨963909915455129715258247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1285213220606839620344329 963909915455129715258247)
        ·
          refine ⟨1445864873182694572887371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963909915455129715258247 1445864873182694572887371)
          ·
            refine ⟨2168797309774041859331057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445864873182694572887371 2168797309774041859331057)
            ·
              refine ⟨1626597982330531394498293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168797309774041859331057 1626597982330531394498293)
              ·
                refine ⟨152493560843487318234215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1626597982330531394498293 152493560843487318234215)
                ·
                  rfl

theorem cell20_1002308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_1002308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002308 prefixEnd_1002308 := by exact prefixLift 1002308
  have htrace : WordTrace (prefixWord ++ tailWord_1002308) baseStart_1002308 baseEnd_1002308 := by
    simpa [prefixWord, tailWord_1002308, baseEnd_1002308] using wordTrace_append hprefix tailTrace_1002308
  have hstable : (prefixWord ++ tailWord_1002308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002308).length < 2 ^ (prefixWord ++ tailWord_1002308).sum := by decide
  have hdescent : baseEnd_1002308 < baseStart_1002308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002350 : List Nat := [4, 1, 2, 3, 2, 8]
def baseStart_1002350 : Nat := 118140960795 + 1002350 * 2 ^ 59
def prefixEnd_1002350 : Nat := 4983230072969 + 3 ^ 40 * 1002350 * 2
def baseEnd_1002350 : Nat := 16944438980551721307499

theorem tailTrace_1002350 : CollatzResearch.WordTrace tailWord_1002350 prefixEnd_1002350 16944438980551721307499 := by
  unfold tailWord_1002350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4569838489833076574519563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24372471945776408397437669 4569838489833076574519563)
  ·
    refine ⟨6854757734749614861779345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4569838489833076574519563 6854757734749614861779345)
    ·
      refine ⟨5141068301062211146334509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6854757734749614861779345 5141068301062211146334509)
      ·
        refine ⟨1927900612898329179875441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5141068301062211146334509 1927900612898329179875441)
        ·
          refine ⟨1445925459673746884906581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1927900612898329179875441 1445925459673746884906581)
          ·
            refine ⟨16944438980551721307499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1445925459673746884906581 16944438980551721307499)
            ·
              rfl

theorem cell20_1002350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 8].length) (baseStart_1002350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002350 prefixEnd_1002350 := by exact prefixLift 1002350
  have htrace : WordTrace (prefixWord ++ tailWord_1002350) baseStart_1002350 baseEnd_1002350 := by
    simpa [prefixWord, tailWord_1002350, baseEnd_1002350] using wordTrace_append hprefix tailTrace_1002350
  have hstable : (prefixWord ++ tailWord_1002350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002350).length < 2 ^ (prefixWord ++ tailWord_1002350).sum := by decide
  have hdescent : baseEnd_1002350 < baseStart_1002350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002429 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 3]
def baseStart_1002429 : Nat := 118140960795 + 1002429 * 2 ^ 59
def prefixEnd_1002429 : Nat := 4983230072969 + 3 ^ 40 * 1002429 * 2
def baseEnd_1002429 : Nat := 457535910227523311668817

theorem tailTrace_1002429 : CollatzResearch.WordTrace tailWord_1002429 prefixEnd_1002429 457535910227523311668817 := by
  unfold tailWord_1002429
  simp only [CollatzResearch.WordTrace]
  refine ⟨36561589285378409088282341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24374392856918939392188227 36561589285378409088282341)
  ·
    refine ⟨6855297991008451704052939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36561589285378409088282341 6855297991008451704052939)
    ·
      refine ⟨10282946986512677556079409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6855297991008451704052939 10282946986512677556079409)
      ·
        refine ⟨7712210239884508167059557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10282946986512677556079409 7712210239884508167059557)
        ·
          refine ⟨1446039419978345281323667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7712210239884508167059557 1446039419978345281323667)
          ·
            refine ⟨2169059129967517921985501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446039419978345281323667 2169059129967517921985501)
            ·
              refine ⟨813397173737819220744563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2169059129967517921985501 813397173737819220744563)
              ·
                refine ⟨1220095760606728831116845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813397173737819220744563 1220095760606728831116845)
                ·
                  refine ⟨457535910227523311668817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220095760606728831116845 457535910227523311668817)
                  ·
                    rfl

theorem cell20_1002429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_1002429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002429 prefixEnd_1002429 := by exact prefixLift 1002429
  have htrace : WordTrace (prefixWord ++ tailWord_1002429) baseStart_1002429 baseEnd_1002429 := by
    simpa [prefixWord, tailWord_1002429, baseEnd_1002429] using wordTrace_append hprefix tailTrace_1002429
  have hstable : (prefixWord ++ tailWord_1002429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002429).length < 2 ^ (prefixWord ++ tailWord_1002429).sum := by decide
  have hdescent : baseEnd_1002429 < baseStart_1002429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002447 : List Nat := [1, 1, 2, 1, 1, 7, 1, 6]
def baseStart_1002447 : Nat := 118140960795 + 1002447 * 2 ^ 59
def prefixEnd_1002447 : Nat := 4983230072969 + 3 ^ 40 * 1002447 * 2
def baseEnd_1002447 : Nat := 152514708639331749689581

theorem tailTrace_1002447 : CollatzResearch.WordTrace tailWord_1002447 prefixEnd_1002447 152514708639331749689581 := by
  unfold tailWord_1002447
  simp only [CollatzResearch.WordTrace]
  refine ⟨36562245799313198162437595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24374830532875465441625063 36562245799313198162437595)
  ·
    refine ⟨54843368698969797243656393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36562245799313198162437595 54843368698969797243656393)
    ·
      refine ⟨41132526524227347932742295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54843368698969797243656393 41132526524227347932742295)
      ·
        refine ⟨61698789786341021899113443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41132526524227347932742295 61698789786341021899113443)
        ·
          refine ⟨92548184679511532848670165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61698789786341021899113443 92548184679511532848670165)
          ·
            refine ⟨2169098078426051551140707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 92548184679511532848670165 2169098078426051551140707)
            ·
              refine ⟨3253647117639077326711061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169098078426051551140707 3253647117639077326711061)
              ·
                refine ⟨152514708639331749689581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3253647117639077326711061 152514708639331749689581)
                ·
                  rfl

theorem cell20_1002447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_1002447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002447 prefixEnd_1002447 := by exact prefixLift 1002447
  have htrace : WordTrace (prefixWord ++ tailWord_1002447) baseStart_1002447 baseEnd_1002447 := by
    simpa [prefixWord, tailWord_1002447, baseEnd_1002447] using wordTrace_append hprefix tailTrace_1002447
  have hstable : (prefixWord ++ tailWord_1002447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002447).length < 2 ^ (prefixWord ++ tailWord_1002447).sum := by decide
  have hdescent : baseEnd_1002447 < baseStart_1002447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002453 : List Nat := [1, 3, 2, 3, 3, 2, 1, 3, 2]
def baseStart_1002453 : Nat := 118140960795 + 1002453 * 2 ^ 59
def prefixEnd_1002453 : Nat := 4983230072969 + 3 ^ 40 * 1002453 * 2
def baseEnd_1002453 : Nat := 457546864481485894868719

theorem tailTrace_1002453 : CollatzResearch.WordTrace tailWord_1002453 prefixEnd_1002453 457546864481485894868719 := by
  unfold tailWord_1002453
  simp only [CollatzResearch.WordTrace]
  refine ⟨36562464637291461187156013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24374976424860974124770675 36562464637291461187156013)
  ·
    refine ⟨13710924238984297945183505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36562464637291461187156013 13710924238984297945183505)
    ·
      refine ⟨10283193179238223458887629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13710924238984297945183505 10283193179238223458887629)
      ·
        refine ⟨3856197442214333797082861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10283193179238223458887629 3856197442214333797082861)
        ·
          refine ⟨1446074040830375173906073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3856197442214333797082861 1446074040830375173906073)
          ·
            refine ⟨1084555530622781380429555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446074040830375173906073 1084555530622781380429555)
            ·
              refine ⟨1626833295934172070644333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084555530622781380429555 1626833295934172070644333)
              ·
                refine ⟨610062485975314526491625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1626833295934172070644333 610062485975314526491625)
                ·
                  refine ⟨457546864481485894868719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610062485975314526491625 457546864481485894868719)
                  ·
                    rfl

theorem cell20_1002453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_1002453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002453 prefixEnd_1002453 := by exact prefixLift 1002453
  have htrace : WordTrace (prefixWord ++ tailWord_1002453) baseStart_1002453 baseEnd_1002453 := by
    simpa [prefixWord, tailWord_1002453, baseEnd_1002453] using wordTrace_append hprefix tailTrace_1002453
  have hstable : (prefixWord ++ tailWord_1002453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002453).length < 2 ^ (prefixWord ++ tailWord_1002453).sum := by decide
  have hdescent : baseEnd_1002453 < baseStart_1002453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002471 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_1002471 : Nat := 118140960795 + 1002471 * 2 ^ 59
def prefixEnd_1002471 : Nat := 4983230072969 + 3 ^ 40 * 1002471 * 2
def baseEnd_1002471 : Nat := 457555080171957832268645

theorem tailTrace_1002471 : CollatzResearch.WordTrace tailWord_1002471 prefixEnd_1002471 457555080171957832268645 := by
  unfold tailWord_1002471
  simp only [CollatzResearch.WordTrace]
  refine ⟨36563121151226250261311267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24375414100817500174207511 36563121151226250261311267)
  ·
    refine ⟨54844681726839375391966901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36563121151226250261311267 54844681726839375391966901)
    ·
      refine ⟨5141688911891191442996897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54844681726839375391966901 5141688911891191442996897)
      ·
        refine ⟨3856266683918393582247673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5141688911891191442996897 3856266683918393582247673)
        ·
          refine ⟨2892200012938795186685755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3856266683918393582247673 2892200012938795186685755)
          ·
            refine ⟨4338300019408192780028633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892200012938795186685755 4338300019408192780028633)
            ·
              refine ⟨3253725014556144585021475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4338300019408192780028633 3253725014556144585021475)
              ·
                refine ⟨4880587521834216877532213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3253725014556144585021475 4880587521834216877532213)
                ·
                  refine ⟨457555080171957832268645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4880587521834216877532213 457555080171957832268645)
                  ·
                    rfl

theorem cell20_1002471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_1002471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002471 prefixEnd_1002471 := by exact prefixLift 1002471
  have htrace : WordTrace (prefixWord ++ tailWord_1002471) baseStart_1002471 baseEnd_1002471 := by
    simpa [prefixWord, tailWord_1002471, baseEnd_1002471] using wordTrace_append hprefix tailTrace_1002471
  have hstable : (prefixWord ++ tailWord_1002471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002471).length < 2 ^ (prefixWord ++ tailWord_1002471).sum := by decide
  have hdescent : baseEnd_1002471 < baseStart_1002471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002529 : List Nat := [1, 2, 3, 2, 3, 3, 2, 2, 2]
def baseStart_1002529 : Nat := 118140960795 + 1002529 * 2 ^ 59
def prefixEnd_1002529 : Nat := 4983230072969 + 3 ^ 40 * 1002529 * 2
def baseEnd_1002529 : Nat := 457581552952367408335075

theorem tailTrace_1002529 : CollatzResearch.WordTrace tailWord_1002529 prefixEnd_1002529 457581552952367408335075 := by
  unfold tailWord_1002529
  simp only [CollatzResearch.WordTrace]
  refine ⟨36565236585016126166922641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24376824390010750777948427 36565236585016126166922641)
  ·
    refine ⟨27423927438762094625191981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36565236585016126166922641 27423927438762094625191981)
    ·
      refine ⟨10283972789535785484446993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27423927438762094625191981 10283972789535785484446993)
      ·
        refine ⟨7712979592151839113335245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10283972789535785484446993 7712979592151839113335245)
        ·
          refine ⟨2892367347056939667500717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7712979592151839113335245 2892367347056939667500717)
          ·
            refine ⟨1084637755146352375312769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2892367347056939667500717 1084637755146352375312769)
            ·
              refine ⟨813478316359764281484577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084637755146352375312769 813478316359764281484577)
              ·
                refine ⟨610108737269823211113433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813478316359764281484577 610108737269823211113433)
                ·
                  refine ⟨457581552952367408335075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610108737269823211113433 457581552952367408335075)
                  ·
                    rfl

theorem cell20_1002529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_1002529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002529 prefixEnd_1002529 := by exact prefixLift 1002529
  have htrace : WordTrace (prefixWord ++ tailWord_1002529) baseStart_1002529 baseEnd_1002529 := by
    simpa [prefixWord, tailWord_1002529, baseEnd_1002529] using wordTrace_append hprefix tailTrace_1002529
  have hstable : (prefixWord ++ tailWord_1002529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002529).length < 2 ^ (prefixWord ++ tailWord_1002529).sum := by decide
  have hdescent : baseEnd_1002529 < baseStart_1002529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002533 : List Nat := [1, 3, 1, 2, 2, 2, 3, 4, 2]
def baseStart_1002533 : Nat := 118140960795 + 1002533 * 2 ^ 59
def prefixEnd_1002533 : Nat := 4983230072969 + 3 ^ 40 * 1002533 * 2
def baseEnd_1002533 : Nat := 457583378661361172201725

theorem tailTrace_1002533 : CollatzResearch.WordTrace tailWord_1002533 prefixEnd_1002533 457583378661361172201725 := by
  unfold tailWord_1002533
  simp only [CollatzResearch.WordTrace]
  refine ⟨36565382477001634850068253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24376921651334423233378835 36565382477001634850068253)
  ·
    refine ⟨13712018428875613068775595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36565382477001634850068253 13712018428875613068775595)
    ·
      refine ⟨20568027643313419603163393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13712018428875613068775595 20568027643313419603163393)
      ·
        refine ⟨15426020732485064702372545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20568027643313419603163393 15426020732485064702372545)
        ·
          refine ⟨11569515549363798526779409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15426020732485064702372545 11569515549363798526779409)
          ·
            refine ⟨8677136662022848895084557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11569515549363798526779409 8677136662022848895084557)
            ·
              refine ⟨3253926248258568335656709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8677136662022848895084557 3253926248258568335656709)
              ·
                refine ⟨610111171548481562935633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3253926248258568335656709 610111171548481562935633)
                ·
                  refine ⟨457583378661361172201725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610111171548481562935633 457583378661361172201725)
                  ·
                    rfl

theorem cell20_1002533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_1002533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002533 prefixEnd_1002533 := by exact prefixLift 1002533
  have htrace : WordTrace (prefixWord ++ tailWord_1002533) baseStart_1002533 baseEnd_1002533 := by
    simpa [prefixWord, tailWord_1002533, baseEnd_1002533] using wordTrace_append hprefix tailTrace_1002533
  have hstable : (prefixWord ++ tailWord_1002533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002533).length < 2 ^ (prefixWord ++ tailWord_1002533).sum := by decide
  have hdescent : baseEnd_1002533 < baseStart_1002533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002568 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_1002568 : Nat := 118140960795 + 1002568 * 2 ^ 59
def prefixEnd_1002568 : Nat := 4983230072969 + 3 ^ 40 * 1002568 * 2
def baseEnd_1002568 : Nat := 457599353615056606034915

theorem tailTrace_1002568 : CollatzResearch.WordTrace tailWord_1002568 prefixEnd_1002568 457599353615056606034915 := by
  unfold tailWord_1002568
  simp only [CollatzResearch.WordTrace]
  refine ⟨18283329515937417913796179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24377772687916557218394905 18283329515937417913796179)
  ·
    refine ⟨27424994273906126870694269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18283329515937417913796179 27424994273906126870694269)
    ·
      refine ⟨10284372852714797576510351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27424994273906126870694269 10284372852714797576510351)
      ·
        refine ⟨15426559279072196364765527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10284372852714797576510351 15426559279072196364765527)
        ·
          refine ⟨23139838918608294547148291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15426559279072196364765527 23139838918608294547148291)
          ·
            refine ⟨34709758377912441820722437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23139838918608294547148291 34709758377912441820722437)
            ·
              refine ⟨6508079695858582841385457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34709758377912441820722437 6508079695858582841385457)
              ·
                refine ⟨4881059771893937131039093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6508079695858582841385457 4881059771893937131039093)
                ·
                  refine ⟨457599353615056606034915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4881059771893937131039093 457599353615056606034915)
                  ·
                    rfl

theorem cell20_1002568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_1002568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002568 prefixEnd_1002568 := by exact prefixLift 1002568
  have htrace : WordTrace (prefixWord ++ tailWord_1002568) baseStart_1002568 baseEnd_1002568 := by
    simpa [prefixWord, tailWord_1002568, baseEnd_1002568] using wordTrace_append hprefix tailTrace_1002568
  have hstable : (prefixWord ++ tailWord_1002568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002568).length < 2 ^ (prefixWord ++ tailWord_1002568).sum := by decide
  have hdescent : baseEnd_1002568 < baseStart_1002568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002592 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_1002592 : Nat := 118140960795 + 1002592 * 2 ^ 59
def prefixEnd_1002592 : Nat := 4983230072969 + 3 ^ 40 * 1002592 * 2
def baseEnd_1002592 : Nat := 457610307869019189234817

theorem tailTrace_1002592 : CollatzResearch.WordTrace tailWord_1002592 prefixEnd_1002592 457610307869019189234817 := by
  unfold tailWord_1002592
  simp only [CollatzResearch.WordTrace]
  refine ⟨18283767191893943963233015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24378356255858591950977353 18283767191893943963233015)
  ·
    refine ⟨27425650787840915944849523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18283767191893943963233015 27425650787840915944849523)
    ·
      refine ⟨41138476181761373917274285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27425650787840915944849523 41138476181761373917274285)
      ·
        refine ⟨15426928568160515218977857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41138476181761373917274285 15426928568160515218977857)
        ·
          refine ⟨11570196426120386414233393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15426928568160515218977857 11570196426120386414233393)
          ·
            refine ⟨8677647319590289810675045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11570196426120386414233393 8677647319590289810675045)
            ·
              refine ⟨1627058872423179339501571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8677647319590289810675045 1627058872423179339501571)
              ·
                refine ⟨2440588308634769009252357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627058872423179339501571 2440588308634769009252357)
                ·
                  refine ⟨457610307869019189234817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440588308634769009252357 457610307869019189234817)
                  ·
                    rfl

theorem cell20_1002592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_1002592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002592 prefixEnd_1002592 := by exact prefixLift 1002592
  have htrace : WordTrace (prefixWord ++ tailWord_1002592) baseStart_1002592 baseEnd_1002592 := by
    simpa [prefixWord, tailWord_1002592, baseEnd_1002592] using wordTrace_append hprefix tailTrace_1002592
  have hstable : (prefixWord ++ tailWord_1002592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002592).length < 2 ^ (prefixWord ++ tailWord_1002592).sum := by decide
  have hdescent : baseEnd_1002592 < baseStart_1002592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002647 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 4]
def baseStart_1002647 : Nat := 118140960795 + 1002647 * 2 ^ 59
def prefixEnd_1002647 : Nat := 4983230072969 + 3 ^ 40 * 1002647 * 2
def baseEnd_1002647 : Nat := 457635411367683442401259

theorem tailTrace_1002647 : CollatzResearch.WordTrace tailWord_1002647 prefixEnd_1002647 457635411367683442401259 := by
  unfold tailWord_1002647
  simp only [CollatzResearch.WordTrace]
  refine ⟨36569540398588632319718195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24379693599059088213145463 36569540398588632319718195)
  ·
    refine ⟨54854310597882948479577293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36569540398588632319718195 54854310597882948479577293)
    ·
      refine ⟨20570366474206105679841485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54854310597882948479577293 20570366474206105679841485)
      ·
        refine ⟨7713887427827289629940557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20570366474206105679841485 7713887427827289629940557)
        ·
          refine ⟨2892707785435233611227709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7713887427827289629940557 2892707785435233611227709)
          ·
            refine ⟨1084765419538212604210391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2892707785435233611227709 1084765419538212604210391)
            ·
              refine ⟨1627148129307318906315587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084765419538212604210391 1627148129307318906315587)
              ·
                refine ⟨2440722193960978359473381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627148129307318906315587 2440722193960978359473381)
                ·
                  refine ⟨457635411367683442401259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440722193960978359473381 457635411367683442401259)
                  ·
                    rfl

theorem cell20_1002647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 4].length) (baseStart_1002647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002647 prefixEnd_1002647 := by exact prefixLift 1002647
  have htrace : WordTrace (prefixWord ++ tailWord_1002647) baseStart_1002647 baseEnd_1002647 := by
    simpa [prefixWord, tailWord_1002647, baseEnd_1002647] using wordTrace_append hprefix tailTrace_1002647
  have hstable : (prefixWord ++ tailWord_1002647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002647).length < 2 ^ (prefixWord ++ tailWord_1002647).sum := by decide
  have hdescent : baseEnd_1002647 < baseStart_1002647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002654 : List Nat := [4, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1002654 : Nat := 118140960795 + 1002654 * 2 ^ 59
def prefixEnd_1002654 : Nat := 4983230072969 + 3 ^ 40 * 1002654 * 2
def baseEnd_1002654 : Nat := 152546202119474176389299

theorem tailTrace_1002654 : CollatzResearch.WordTrace tailWord_1002654 prefixEnd_1002654 152546202119474176389299 := by
  unfold tailWord_1002654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571224463695409064402877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24379863806375515010148677 4571224463695409064402877)
  ·
    refine ⟨1714209173885778399151079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4571224463695409064402877 1714209173885778399151079)
    ·
      refine ⟨2571313760828667598726619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714209173885778399151079 2571313760828667598726619)
      ·
        refine ⟨3856970641243001398089929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571313760828667598726619 3856970641243001398089929)
        ·
          refine ⟨2892727980932251048567447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3856970641243001398089929 2892727980932251048567447)
          ·
            refine ⟨4339091971398376572851171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892727980932251048567447 4339091971398376572851171)
            ·
              refine ⟨6508637957097564859276757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339091971398376572851171 6508637957097564859276757)
              ·
                refine ⟨152546202119474176389299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6508637957097564859276757 152546202119474176389299)
                ·
                  rfl

theorem cell20_1002654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1002654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002654 prefixEnd_1002654 := by exact prefixLift 1002654
  have htrace : WordTrace (prefixWord ++ tailWord_1002654) baseStart_1002654 baseEnd_1002654 := by
    simpa [prefixWord, tailWord_1002654, baseEnd_1002654] using wordTrace_append hprefix tailTrace_1002654
  have hstable : (prefixWord ++ tailWord_1002654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002654).length < 2 ^ (prefixWord ++ tailWord_1002654).sum := by decide
  have hdescent : baseEnd_1002654 < baseStart_1002654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002661 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 3]
def baseStart_1002661 : Nat := 118140960795 + 1002661 * 2 ^ 59
def prefixEnd_1002661 : Nat := 4983230072969 + 3 ^ 40 * 1002661 * 2
def baseEnd_1002661 : Nat := 457641801349161615934535

theorem tailTrace_1002661 : CollatzResearch.WordTrace tailWord_1002661 prefixEnd_1002661 457641801349161615934535 := by
  unfold tailWord_1002661
  simp only [CollatzResearch.WordTrace]
  refine ⟨36570051020537912710727837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24380034013691941807151891 36570051020537912710727837)
  ·
    refine ⟨13713769132701717266522939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36570051020537912710727837 13713769132701717266522939)
    ·
      refine ⟨20570653699052575899784409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13713769132701717266522939 20570653699052575899784409)
      ·
        refine ⟨15427990274289431924838307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20570653699052575899784409 15427990274289431924838307)
        ·
          refine ⟨23141985411434147887257461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15427990274289431924838307 23141985411434147887257461)
          ·
            refine ⟨2169561132321951364430387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23141985411434147887257461 2169561132321951364430387)
            ·
              refine ⟨3254341698482927046645581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169561132321951364430387 3254341698482927046645581)
              ·
                refine ⟨1220378136931097642492093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3254341698482927046645581 1220378136931097642492093)
                ·
                  refine ⟨457641801349161615934535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220378136931097642492093 457641801349161615934535)
                  ·
                    rfl

theorem cell20_1002661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_1002661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002661 prefixEnd_1002661 := by exact prefixLift 1002661
  have htrace : WordTrace (prefixWord ++ tailWord_1002661) baseStart_1002661 baseEnd_1002661 := by
    simpa [prefixWord, tailWord_1002661, baseEnd_1002661] using wordTrace_append hprefix tailTrace_1002661
  have hstable : (prefixWord ++ tailWord_1002661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002661).length < 2 ^ (prefixWord ++ tailWord_1002661).sum := by decide
  have hdescent : baseEnd_1002661 < baseStart_1002661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002692 : List Nat := [2, 3, 3, 1, 4, 7]
def baseStart_1002692 : Nat := 118140960795 + 1002692 * 2 ^ 59
def prefixEnd_1002692 : Nat := 4983230072969 + 3 ^ 40 * 1002692 * 2
def baseEnd_1002692 : Nat := 16950220392365306885225

theorem tailTrace_1002692 : CollatzResearch.WordTrace tailWord_1002692 prefixEnd_1002692 16950220392365306885225 := by
  unfold tailWord_1002692
  simp only [CollatzResearch.WordTrace]
  refine ⟨18285590841712802502553165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24380787788950403336737553 18285590841712802502553165)
  ·
    refine ⟨6857096565642300938457437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18285590841712802502553165 6857096565642300938457437)
    ·
      refine ⟨2571411212115862851921539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6857096565642300938457437 2571411212115862851921539)
      ·
        refine ⟨3857116818173794277882309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571411212115862851921539 3857116818173794277882309)
        ·
          refine ⟨723209403407586427102933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3857116818173794277882309 723209403407586427102933)
          ·
            refine ⟨16950220392365306885225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 723209403407586427102933 16950220392365306885225)
            ·
              rfl

theorem cell20_1002692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 7].length) (baseStart_1002692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002692 prefixEnd_1002692 := by exact prefixLift 1002692
  have htrace : WordTrace (prefixWord ++ tailWord_1002692) baseStart_1002692 baseEnd_1002692 := by
    simpa [prefixWord, tailWord_1002692, baseEnd_1002692] using wordTrace_append hprefix tailTrace_1002692
  have hstable : (prefixWord ++ tailWord_1002692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002692).length < 2 ^ (prefixWord ++ tailWord_1002692).sum := by decide
  have hdescent : baseEnd_1002692 < baseStart_1002692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002694 : List Nat := [6, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1002694 : Nat := 118140960795 + 1002694 * 2 ^ 59
def prefixEnd_1002694 : Nat := 4983230072969 + 3 ^ 40 * 1002694 * 2
def baseEnd_1002694 : Nat := 457656863448360167834401

theorem tailTrace_1002694 : CollatzResearch.WordTrace tailWord_1002694 prefixEnd_1002694 457656863448360167834401 := by
  unfold tailWord_1002694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142851707169323729583723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24380836419612239564452757 1142851707169323729583723)
  ·
    refine ⟨1714277560753985594375585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1142851707169323729583723 1714277560753985594375585)
    ·
      refine ⟨1285708170565489195781689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1714277560753985594375585 1285708170565489195781689)
      ·
        refine ⟨964281127924116896836267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1285708170565489195781689 964281127924116896836267)
        ·
          refine ⟨1446421691886175345254401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964281127924116896836267 1446421691886175345254401)
          ·
            refine ⟨1084816268914631508940801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446421691886175345254401 1084816268914631508940801)
            ·
              refine ⟨813612201685973631705601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084816268914631508940801 813612201685973631705601)
              ·
                refine ⟨610209151264480223779201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813612201685973631705601 610209151264480223779201)
                ·
                  refine ⟨457656863448360167834401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610209151264480223779201 457656863448360167834401)
                  ·
                    rfl

theorem cell20_1002694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1002694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002694 prefixEnd_1002694 := by exact prefixLift 1002694
  have htrace : WordTrace (prefixWord ++ tailWord_1002694) baseStart_1002694 baseEnd_1002694 := by
    simpa [prefixWord, tailWord_1002694, baseEnd_1002694] using wordTrace_append hprefix tailTrace_1002694
  have hstable : (prefixWord ++ tailWord_1002694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002694).length < 2 ^ (prefixWord ++ tailWord_1002694).sum := by decide
  have hdescent : baseEnd_1002694 < baseStart_1002694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002702 : List Nat := [4, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_1002702 : Nat := 118140960795 + 1002702 * 2 ^ 59
def prefixEnd_1002702 : Nat := 4983230072969 + 3 ^ 40 * 1002702 * 2
def baseEnd_1002702 : Nat := 457660514866347695567701

theorem tailTrace_1002702 : CollatzResearch.WordTrace tailWord_1002702 prefixEnd_1002702 457660514866347695567701 := by
  unfold tailWord_1002702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571443301673672089121295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24381030942259584475313573 4571443301673672089121295)
  ·
    refine ⟨6857164952510508133681943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4571443301673672089121295 6857164952510508133681943)
    ·
      refine ⟨10285747428765762200522915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6857164952510508133681943 10285747428765762200522915)
      ·
        refine ⟨15428621143148643300784373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10285747428765762200522915 15428621143148643300784373)
        ·
          refine ⟨1446433232170185309448535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15428621143148643300784373 1446433232170185309448535)
          ·
            refine ⟨2169649848255277964172803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446433232170185309448535 2169649848255277964172803)
            ·
              refine ⟨3254474772382916946259205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169649848255277964172803 3254474772382916946259205)
              ·
                refine ⟨610214019821796927423601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3254474772382916946259205 610214019821796927423601)
                ·
                  refine ⟨457660514866347695567701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610214019821796927423601 457660514866347695567701)
                  ·
                    rfl

theorem cell20_1002702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_1002702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002702 prefixEnd_1002702 := by exact prefixLift 1002702
  have htrace : WordTrace (prefixWord ++ tailWord_1002702) baseStart_1002702 baseEnd_1002702 := by
    simpa [prefixWord, tailWord_1002702, baseEnd_1002702] using wordTrace_append hprefix tailTrace_1002702
  have hstable : (prefixWord ++ tailWord_1002702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002702).length < 2 ^ (prefixWord ++ tailWord_1002702).sum := by decide
  have hdescent : baseEnd_1002702 < baseStart_1002702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002706 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1002706 : Nat := 118140960795 + 1002706 * 2 ^ 59
def prefixEnd_1002706 : Nat := 4983230072969 + 3 ^ 40 * 1002706 * 2
def baseEnd_1002706 : Nat := 457662340575341459434351

theorem tailTrace_1002706 : CollatzResearch.WordTrace tailWord_1002706 prefixEnd_1002706 457662340575341459434351 := by
  unfold tailWord_1002706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142923076343721349028993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24381128203583256930743981 9142923076343721349028993)
  ·
    refine ⟨6857192307257791011771745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9142923076343721349028993 6857192307257791011771745)
    ·
      refine ⟨5142894230443343258828809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6857192307257791011771745 5142894230443343258828809)
      ·
        refine ⟨3857170672832507444121607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5142894230443343258828809 3857170672832507444121607)
        ·
          refine ⟨5785756009248761166182411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857170672832507444121607 5785756009248761166182411)
          ·
            refine ⟨8678634013873141749273617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5785756009248761166182411 8678634013873141749273617)
            ·
              refine ⟨6508975510404856311955213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8678634013873141749273617 6508975510404856311955213)
              ·
                refine ⟨2440865816401821116983205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6508975510404856311955213 2440865816401821116983205)
                ·
                  refine ⟨457662340575341459434351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440865816401821116983205 457662340575341459434351)
                  ·
                    rfl

theorem cell20_1002706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1002706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002706 prefixEnd_1002706 := by exact prefixLift 1002706
  have htrace : WordTrace (prefixWord ++ tailWord_1002706) baseStart_1002706 baseEnd_1002706 := by
    simpa [prefixWord, tailWord_1002706, baseEnd_1002706] using wordTrace_append hprefix tailTrace_1002706
  have hstable : (prefixWord ++ tailWord_1002706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002706).length < 2 ^ (prefixWord ++ tailWord_1002706).sum := by decide
  have hdescent : baseEnd_1002706 < baseStart_1002706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002730 : List Nat := [3, 1, 3, 1, 1, 4, 3, 4]
def baseStart_1002730 : Nat := 118140960795 + 1002730 * 2 ^ 59
def prefixEnd_1002730 : Nat := 4983230072969 + 3 ^ 40 * 1002730 * 2
def baseEnd_1002730 : Nat := 152557764943101347544751

theorem tailTrace_1002730 : CollatzResearch.WordTrace tailWord_1002730 prefixEnd_1002730 152557764943101347544751 := by
  unfold tailWord_1002730
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143141914321984373747411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24381711771525291663326429 9143141914321984373747411)
  ·
    refine ⟨13714712871482976560621117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9143141914321984373747411 13714712871482976560621117)
    ·
      refine ⟨5143017326806116210232919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13714712871482976560621117 5143017326806116210232919)
      ·
        refine ⟨7714525990209174315349379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5143017326806116210232919 7714525990209174315349379)
        ·
          refine ⟨11571788985313761473024069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7714525990209174315349379 11571788985313761473024069)
          ·
            refine ⟨2169710434746330276192013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11571788985313761473024069 2169710434746330276192013)
            ·
              refine ⟨813641413029873853572005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2169710434746330276192013 813641413029873853572005)
              ·
                refine ⟨152557764943101347544751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 813641413029873853572005 152557764943101347544751)
                ·
                  rfl

theorem cell20_1002730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_1002730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002730 prefixEnd_1002730 := by exact prefixLift 1002730
  have htrace : WordTrace (prefixWord ++ tailWord_1002730) baseStart_1002730 baseEnd_1002730 := by
    simpa [prefixWord, tailWord_1002730, baseEnd_1002730] using wordTrace_append hprefix tailTrace_1002730
  have hstable : (prefixWord ++ tailWord_1002730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002730).length < 2 ^ (prefixWord ++ tailWord_1002730).sum := by decide
  have hdescent : baseEnd_1002730 < baseStart_1002730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002754 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1002754 : Nat := 118140960795 + 1002754 * 2 ^ 59
def prefixEnd_1002754 : Nat := 4983230072969 + 3 ^ 40 * 1002754 * 2
def baseEnd_1002754 : Nat := 457684249083266625834155

theorem tailTrace_1002754 : CollatzResearch.WordTrace tailWord_1002754 prefixEnd_1002754 457684249083266625834155 := by
  unfold tailWord_1002754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143360752300247398465829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24382295339467326395908877 9143360752300247398465829)
  ·
    refine ⟨1714380141056296387212343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9143360752300247398465829 1714380141056296387212343)
    ·
      refine ⟨2571570211584444580818515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714380141056296387212343 2571570211584444580818515)
      ·
        refine ⟨3857355317376666871227773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571570211584444580818515 3857355317376666871227773)
        ·
          refine ⟨1446508244016250076710415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3857355317376666871227773 1446508244016250076710415)
          ·
            refine ⟨2169762366024375115065623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446508244016250076710415 2169762366024375115065623)
            ·
              refine ⟨3254643549036562672598435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169762366024375115065623 3254643549036562672598435)
              ·
                refine ⟨4881965323554844008897653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254643549036562672598435 4881965323554844008897653)
                ·
                  refine ⟨457684249083266625834155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4881965323554844008897653 457684249083266625834155)
                  ·
                    rfl

theorem cell20_1002754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1002754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002754 prefixEnd_1002754 := by exact prefixLift 1002754
  have htrace : WordTrace (prefixWord ++ tailWord_1002754) baseStart_1002754 baseEnd_1002754 := by
    simpa [prefixWord, tailWord_1002754, baseEnd_1002754] using wordTrace_append hprefix tailTrace_1002754
  have hstable : (prefixWord ++ tailWord_1002754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002754).length < 2 ^ (prefixWord ++ tailWord_1002754).sum := by decide
  have hdescent : baseEnd_1002754 < baseStart_1002754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002789 : List Nat := [1, 3, 1, 2, 4, 2, 1, 6]
def baseStart_1002789 : Nat := 118140960795 + 1002789 * 2 ^ 59
def prefixEnd_1002789 : Nat := 4983230072969 + 3 ^ 40 * 1002789 * 2
def baseEnd_1002789 : Nat := 152566741345654019889115

theorem tailTrace_1002789 : CollatzResearch.WordTrace tailWord_1002789 prefixEnd_1002789 152566741345654019889115 := by
  unfold tailWord_1002789
  simp only [CollatzResearch.WordTrace]
  refine ⟨36574719564074190571387421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24383146376049460380924947 36574719564074190571387421)
  ·
    refine ⟨13715519836527821464270283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36574719564074190571387421 13715519836527821464270283)
    ·
      refine ⟨20573279754791732196405425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13715519836527821464270283 20573279754791732196405425)
      ·
        refine ⟨15429959816093799147304069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20573279754791732196405425 15429959816093799147304069)
        ·
          refine ⟨2893117465517587340119513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15429959816093799147304069 2893117465517587340119513)
          ·
            refine ⟨2169838099138190505089635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2893117465517587340119513 2169838099138190505089635)
            ·
              refine ⟨3254757148707285757634453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169838099138190505089635 3254757148707285757634453)
              ·
                refine ⟨152566741345654019889115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3254757148707285757634453 152566741345654019889115)
                ·
                  rfl

theorem cell20_1002789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_1002789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002789 prefixEnd_1002789 := by exact prefixLift 1002789
  have htrace : WordTrace (prefixWord ++ tailWord_1002789) baseStart_1002789 baseEnd_1002789 := by
    simpa [prefixWord, tailWord_1002789, baseEnd_1002789] using wordTrace_append hprefix tailTrace_1002789
  have hstable : (prefixWord ++ tailWord_1002789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002789).length < 2 ^ (prefixWord ++ tailWord_1002789).sum := by decide
  have hdescent : baseEnd_1002789 < baseStart_1002789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002822 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_1002822 : Nat := 118140960795 + 1002822 * 2 ^ 59
def prefixEnd_1002822 : Nat := 4983230072969 + 3 ^ 40 * 1002822 * 2
def baseEnd_1002822 : Nat := 457715286136160611567211

theorem tailTrace_1002822 : CollatzResearch.WordTrace tailWord_1002822 prefixEnd_1002822 457715286136160611567211 := by
  unfold tailWord_1002822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142997599154832412729335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24383948781969758138225813 1142997599154832412729335)
  ·
    refine ⟨1714496398732248619094003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1142997599154832412729335 1714496398732248619094003)
    ·
      refine ⟨2571744598098372928641005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714496398732248619094003 2571744598098372928641005)
      ·
        refine ⟨964404224286889848240377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2571744598098372928641005 964404224286889848240377)
        ·
          refine ⟨723303168215167386180283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964404224286889848240377 723303168215167386180283)
          ·
            refine ⟨1084954752322751079270425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723303168215167386180283 1084954752322751079270425)
            ·
              refine ⟨813716064242063309452819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084954752322751079270425 813716064242063309452819)
              ·
                refine ⟨1220574096363094964179229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813716064242063309452819 1220574096363094964179229)
                ·
                  refine ⟨457715286136160611567211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220574096363094964179229 457715286136160611567211)
                  ·
                    rfl

theorem cell20_1002822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_1002822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002822 prefixEnd_1002822 := by exact prefixLift 1002822
  have htrace : WordTrace (prefixWord ++ tailWord_1002822) baseStart_1002822 baseEnd_1002822 := by
    simpa [prefixWord, tailWord_1002822, baseEnd_1002822] using wordTrace_append hprefix tailTrace_1002822
  have hstable : (prefixWord ++ tailWord_1002822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002822).length < 2 ^ (prefixWord ++ tailWord_1002822).sum := by decide
  have hdescent : baseEnd_1002822 < baseStart_1002822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002841 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_1002841 : Nat := 118140960795 + 1002841 * 2 ^ 59
def prefixEnd_1002841 : Nat := 4983230072969 + 3 ^ 40 * 1002841 * 2
def baseEnd_1002841 : Nat := 457723958253880989933799

theorem tailTrace_1002841 : CollatzResearch.WordTrace tailWord_1002841 prefixEnd_1002841 457723958253880989933799 := by
  unfold tailWord_1002841
  simp only [CollatzResearch.WordTrace]
  refine ⟨36576616159885803452280377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24384410773257202301520251 36576616159885803452280377)
  ·
    refine ⟨27432462119914352589210283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36576616159885803452280377 27432462119914352589210283)
    ·
      refine ⟨41148693179871528883815425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27432462119914352589210283 41148693179871528883815425)
      ·
        refine ⟨30861519884903646662861569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41148693179871528883815425 30861519884903646662861569)
        ·
          refine ⟨23146139913677734997146177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30861519884903646662861569 23146139913677734997146177)
          ·
            refine ⟨17359604935258301247859633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23146139913677734997146177 17359604935258301247859633)
            ·
              refine ⟨13019703701443725935894725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17359604935258301247859633 13019703701443725935894725)
              ·
                refine ⟨2441194444020698612980261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13019703701443725935894725 2441194444020698612980261)
                ·
                  refine ⟨457723958253880989933799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441194444020698612980261 457723958253880989933799)
                  ·
                    rfl

theorem cell20_1002841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_1002841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002841 prefixEnd_1002841 := by exact prefixLift 1002841
  have htrace : WordTrace (prefixWord ++ tailWord_1002841) baseStart_1002841 baseEnd_1002841 := by
    simpa [prefixWord, tailWord_1002841, baseEnd_1002841] using wordTrace_append hprefix tailTrace_1002841
  have hstable : (prefixWord ++ tailWord_1002841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002841).length < 2 ^ (prefixWord ++ tailWord_1002841).sum := by decide
  have hdescent : baseEnd_1002841 < baseStart_1002841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002878 : List Nat := [4, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1002878 : Nat := 118140960795 + 1002878 * 2 ^ 59
def prefixEnd_1002878 : Nat := 4983230072969 + 3 ^ 40 * 1002878 * 2
def baseEnd_1002878 : Nat := 152580282020691101900105

theorem tailTrace_1002878 : CollatzResearch.WordTrace tailWord_1002878 prefixEnd_1002878 152580282020691101900105 := by
  unfold tailWord_1002878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572245707593969846422161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24385310440501172514251525 4572245707593969846422161)
  ·
    refine ⟨3429184280695477384816621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4572245707593969846422161 3429184280695477384816621)
    ·
      refine ⟨1285944105260804019306233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3429184280695477384816621 1285944105260804019306233)
      ·
        refine ⟨964458078945603014479675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1285944105260804019306233 964458078945603014479675)
        ·
          refine ⟨1446687118418404521719513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964458078945603014479675 1446687118418404521719513)
          ·
            refine ⟨1085015338813803391289635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446687118418404521719513 1085015338813803391289635)
            ·
              refine ⟨1627523008220705086934453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085015338813803391289635 1627523008220705086934453)
              ·
                refine ⟨152580282020691101900105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1627523008220705086934453 152580282020691101900105)
                ·
                  rfl

theorem cell20_1002878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1002878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002878 prefixEnd_1002878 := by exact prefixLift 1002878
  have htrace : WordTrace (prefixWord ++ tailWord_1002878) baseStart_1002878 baseEnd_1002878 := by
    simpa [prefixWord, tailWord_1002878, baseEnd_1002878] using wordTrace_append hprefix tailTrace_1002878
  have hstable : (prefixWord ++ tailWord_1002878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002878).length < 2 ^ (prefixWord ++ tailWord_1002878).sum := by decide
  have hdescent : baseEnd_1002878 < baseStart_1002878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002920 : List Nat := [2, 1, 6, 1, 2, 1, 7]
def baseStart_1002920 : Nat := 118140960795 + 1002920 * 2 ^ 59
def prefixEnd_1002920 : Nat := 4983230072969 + 3 ^ 40 * 1002920 * 2
def baseEnd_1002920 : Nat := 50862224000723091811127

theorem tailTrace_1002920 : CollatzResearch.WordTrace tailWord_1002920 prefixEnd_1002920 50862224000723091811127 := by
  unfold tailWord_1002920
  simp only [CollatzResearch.WordTrace]
  refine ⟨18289748763299799972203107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24386331684399733296270809 18289748763299799972203107)
  ·
    refine ⟨27434623144949699958304661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18289748763299799972203107 27434623144949699958304661)
    ·
      refine ⟨1285997959919517185545531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27434623144949699958304661 1285997959919517185545531)
      ·
        refine ⟨1928996939879275778318297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285997959919517185545531 1928996939879275778318297)
        ·
          refine ⟨1446747704909456833738723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928996939879275778318297 1446747704909456833738723)
          ·
            refine ⟨2170121557364185250608085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446747704909456833738723 2170121557364185250608085)
            ·
              refine ⟨50862224000723091811127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2170121557364185250608085 50862224000723091811127)
              ·
                rfl

theorem cell20_1002920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 7].length) (baseStart_1002920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002920 prefixEnd_1002920 := by exact prefixLift 1002920
  have htrace : WordTrace (prefixWord ++ tailWord_1002920) baseStart_1002920 baseEnd_1002920 := by
    simpa [prefixWord, tailWord_1002920, baseEnd_1002920] using wordTrace_append hprefix tailTrace_1002920
  have hstable : (prefixWord ++ tailWord_1002920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002920).length < 2 ^ (prefixWord ++ tailWord_1002920).sum := by decide
  have hdescent : baseEnd_1002920 < baseStart_1002920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002955 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_1002955 : Nat := 118140960795 + 1002955 * 2 ^ 59
def prefixEnd_1002955 : Nat := 4983230072969 + 3 ^ 40 * 1002955 * 2
def baseEnd_1002955 : Nat := 457775990960203260133333

theorem tailTrace_1002955 : CollatzResearch.WordTrace tailWord_1002955 prefixEnd_1002955 457775990960203260133333 := by
  unfold tailWord_1002955
  simp only [CollatzResearch.WordTrace]
  refine ⟨36580774081472800921930319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24387182720981867281286879 36580774081472800921930319)
  ·
    refine ⟨54871161122209201382895479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36580774081472800921930319 54871161122209201382895479)
    ·
      refine ⟨82306741683313802074343219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54871161122209201382895479 82306741683313802074343219)
      ·
        refine ⟨123460112524970703111514829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82306741683313802074343219 123460112524970703111514829)
        ·
          refine ⟨46297542196864013666818061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123460112524970703111514829 46297542196864013666818061)
          ·
            refine ⟨17361578323824005125056773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46297542196864013666818061 17361578323824005125056773)
            ·
              refine ⟨3255295935717000960948145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17361578323824005125056773 3255295935717000960948145)
              ·
                refine ⟨2441471951787750720711109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255295935717000960948145 2441471951787750720711109)
                ·
                  refine ⟨457775990960203260133333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441471951787750720711109 457775990960203260133333)
                  ·
                    rfl

theorem cell20_1002955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_1002955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002955 prefixEnd_1002955 := by exact prefixLift 1002955
  have htrace : WordTrace (prefixWord ++ tailWord_1002955) baseStart_1002955 baseEnd_1002955 := by
    simpa [prefixWord, tailWord_1002955, baseEnd_1002955] using wordTrace_append hprefix tailTrace_1002955
  have hstable : (prefixWord ++ tailWord_1002955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002955).length < 2 ^ (prefixWord ++ tailWord_1002955).sum := by decide
  have hdescent : baseEnd_1002955 < baseStart_1002955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002979 : List Nat := [1, 1, 1, 6, 2, 3, 6]
def baseStart_1002979 : Nat := 118140960795 + 1002979 * 2 ^ 59
def prefixEnd_1002979 : Nat := 4983230072969 + 3 ^ 40 * 1002979 * 2
def baseEnd_1002979 : Nat := 50865216134907315925915

theorem tailTrace_1002979 : CollatzResearch.WordTrace tailWord_1002979 prefixEnd_1002979 50865216134907315925915 := by
  unfold tailWord_1002979
  simp only [CollatzResearch.WordTrace]
  refine ⟨36581649433385853020803991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24387766288923902013869327 36581649433385853020803991)
  ·
    refine ⟨54872474150078779531205987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36581649433385853020803991 54872474150078779531205987)
    ·
      refine ⟨82308711225118169296808981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54872474150078779531205987 82308711225118169296808981)
      ·
        refine ⟨3858220838677414185787921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82308711225118169296808981 3858220838677414185787921)
        ·
          refine ⟨2893665629008060639340941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3858220838677414185787921 2893665629008060639340941)
          ·
            refine ⟨1085124610878022739752853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2893665629008060639340941 1085124610878022739752853)
            ·
              refine ⟨50865216134907315925915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1085124610878022739752853 50865216134907315925915)
              ·
                rfl

theorem cell20_1002979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 6].length) (baseStart_1002979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1002979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1002979 prefixEnd_1002979 := by exact prefixLift 1002979
  have htrace : WordTrace (prefixWord ++ tailWord_1002979) baseStart_1002979 baseEnd_1002979 := by
    simpa [prefixWord, tailWord_1002979, baseEnd_1002979] using wordTrace_append hprefix tailTrace_1002979
  have hstable : (prefixWord ++ tailWord_1002979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002979).length < 2 ^ (prefixWord ++ tailWord_1002979).sum := by decide
  have hdescent : baseEnd_1002979 < baseStart_1002979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003000 : List Nat := [2, 1, 2, 1, 1, 5, 1, 7]
def baseStart_1003000 : Nat := 118140960795 + 1003000 * 2 ^ 59
def prefixEnd_1003000 : Nat := 4983230072969 + 3 ^ 40 * 1003000 * 2
def baseEnd_1003000 : Nat := 152598843395461034544383

theorem tailTrace_1003000 : CollatzResearch.WordTrace tailWord_1003000 prefixEnd_1003000 152598843395461034544383 := by
  unfold tailWord_1003000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18291207683154886803659227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24388276910873182404878969 18291207683154886803659227)
  ·
    refine ⟨27436811524732330205488841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18291207683154886803659227 27436811524732330205488841)
    ·
      refine ⟨20577608643549247654116631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27436811524732330205488841 20577608643549247654116631)
      ·
        refine ⟨30866412965323871481174947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20577608643549247654116631 30866412965323871481174947)
        ·
          refine ⟨46299619447985807221762421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30866412965323871481174947 46299619447985807221762421)
          ·
            refine ⟨4340589323248669427040227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46299619447985807221762421 4340589323248669427040227)
            ·
              refine ⟨6510883984873004140560341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340589323248669427040227 6510883984873004140560341)
              ·
                refine ⟨152598843395461034544383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6510883984873004140560341 152598843395461034544383)
                ·
                  rfl

theorem cell20_1003000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_1003000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003000 prefixEnd_1003000 := by exact prefixLift 1003000
  have htrace : WordTrace (prefixWord ++ tailWord_1003000) baseStart_1003000 baseEnd_1003000 := by
    simpa [prefixWord, tailWord_1003000, baseEnd_1003000] using wordTrace_append hprefix tailTrace_1003000
  have hstable : (prefixWord ++ tailWord_1003000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003000).length < 2 ^ (prefixWord ++ tailWord_1003000).sum := by decide
  have hdescent : baseEnd_1003000 < baseStart_1003000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003007 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_1003007 : Nat := 118140960795 + 1003007 * 2 ^ 59
def prefixEnd_1003007 : Nat := 4983230072969 + 3 ^ 40 * 1003007 * 2
def baseEnd_1003007 : Nat := 457799725177122190399787

theorem tailTrace_1003007 : CollatzResearch.WordTrace tailWord_1003007 prefixEnd_1003007 457799725177122190399787 := by
  unfold tailWord_1003007
  simp only [CollatzResearch.WordTrace]
  refine ⟨36582670677284413802823275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24388447118189609201882183 36582670677284413802823275)
  ·
    refine ⟨54874006015926620704234913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36582670677284413802823275 54874006015926620704234913)
    ·
      refine ⟨41155504511944965528176185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54874006015926620704234913 41155504511944965528176185)
      ·
        refine ⟨30866628383958724146132139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41155504511944965528176185 30866628383958724146132139)
        ·
          refine ⟨46299942575938086219198209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30866628383958724146132139 46299942575938086219198209)
          ·
            refine ⟨34724956931953564664398657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46299942575938086219198209 34724956931953564664398657)
            ·
              refine ⟨26043717698965173498298993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34724956931953564664398657 26043717698965173498298993)
              ·
                refine ⟨19532788274223880123724245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26043717698965173498298993 19532788274223880123724245)
                ·
                  refine ⟨457799725177122190399787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19532788274223880123724245 457799725177122190399787)
                  ·
                    rfl

theorem cell20_1003007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_1003007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003007 prefixEnd_1003007 := by exact prefixLift 1003007
  have htrace : WordTrace (prefixWord ++ tailWord_1003007) baseStart_1003007 baseEnd_1003007 := by
    simpa [prefixWord, tailWord_1003007, baseEnd_1003007] using wordTrace_append hprefix tailTrace_1003007
  have hstable : (prefixWord ++ tailWord_1003007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003007).length < 2 ^ (prefixWord ++ tailWord_1003007).sum := by decide
  have hdescent : baseEnd_1003007 < baseStart_1003007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003041 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 3]
def baseStart_1003041 : Nat := 118140960795 + 1003041 * 2 ^ 59
def prefixEnd_1003041 : Nat := 4983230072969 + 3 ^ 40 * 1003041 * 2
def baseEnd_1003041 : Nat := 457815243703569183266315

theorem tailTrace_1003041 : CollatzResearch.WordTrace tailWord_1003041 prefixEnd_1003041 457815243703569183266315 := by
  unfold tailWord_1003041
  simp only [CollatzResearch.WordTrace]
  refine ⟨36583910759161237609560977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24389273839440825073040651 36583910759161237609560977)
  ·
    refine ⟨27437933069370928207170733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36583910759161237609560977 27437933069370928207170733)
    ·
      refine ⟨10289224901014098077689025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27437933069370928207170733 10289224901014098077689025)
      ·
        refine ⟨7716918675760573558266769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10289224901014098077689025 7716918675760573558266769)
        ·
          refine ⟨5787689006820430168700077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7716918675760573558266769 5787689006820430168700077)
          ·
            refine ⟨2170383377557661313262529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5787689006820430168700077 2170383377557661313262529)
            ·
              refine ⟨1627787533168245984946897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2170383377557661313262529 1627787533168245984946897)
              ·
                refine ⟨1220840649876184488710173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1627787533168245984946897 1220840649876184488710173)
                ·
                  refine ⟨457815243703569183266315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220840649876184488710173 457815243703569183266315)
                  ·
                    rfl

theorem cell20_1003041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_1003041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003041 prefixEnd_1003041 := by exact prefixLift 1003041
  have htrace : WordTrace (prefixWord ++ tailWord_1003041) baseStart_1003041 baseEnd_1003041 := by
    simpa [prefixWord, tailWord_1003041, baseEnd_1003041] using wordTrace_append hprefix tailTrace_1003041
  have hstable : (prefixWord ++ tailWord_1003041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003041).length < 2 ^ (prefixWord ++ tailWord_1003041).sum := by decide
  have hdescent : baseEnd_1003041 < baseStart_1003041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003083 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_1003083 : Nat := 118140960795 + 1003083 * 2 ^ 59
def prefixEnd_1003083 : Nat := 4983230072969 + 3 ^ 40 * 1003083 * 2
def baseEnd_1003083 : Nat := 457834413648003703866143

theorem tailTrace_1003083 : CollatzResearch.WordTrace tailWord_1003083 prefixEnd_1003083 457834413648003703866143 := by
  unfold tailWord_1003083
  simp only [CollatzResearch.WordTrace]
  refine ⟨36585442625009078782589903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24390295083339385855059935 36585442625009078782589903)
  ·
    refine ⟨54878163937513618173884855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36585442625009078782589903 54878163937513618173884855)
    ·
      refine ⟨82317245906270427260827283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54878163937513618173884855 82317245906270427260827283)
      ·
        refine ⟨123475868859405640891240925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82317245906270427260827283 123475868859405640891240925)
        ·
          refine ⟨46303450822277115334215347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123475868859405640891240925 46303450822277115334215347)
          ·
            refine ⟨69455176233415673001323021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46303450822277115334215347 69455176233415673001323021)
            ·
              refine ⟨26045691087530877375496133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69455176233415673001323021 26045691087530877375496133)
              ·
                refine ⟨4883567078912039507905525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26045691087530877375496133 4883567078912039507905525)
                ·
                  refine ⟨457834413648003703866143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4883567078912039507905525 457834413648003703866143)
                  ·
                    rfl

theorem cell20_1003083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_1003083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003083 prefixEnd_1003083 := by exact prefixLift 1003083
  have htrace : WordTrace (prefixWord ++ tailWord_1003083) baseStart_1003083 baseEnd_1003083 := by
    simpa [prefixWord, tailWord_1003083, baseEnd_1003083] using wordTrace_append hprefix tailTrace_1003083
  have hstable : (prefixWord ++ tailWord_1003083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003083).length < 2 ^ (prefixWord ++ tailWord_1003083).sum := by decide
  have hdescent : baseEnd_1003083 < baseStart_1003083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003107 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_1003107 : Nat := 118140960795 + 1003107 * 2 ^ 59
def prefixEnd_1003107 : Nat := 4983230072969 + 3 ^ 40 * 1003107 * 2
def baseEnd_1003107 : Nat := 457845367901966287066045

theorem tailTrace_1003107 : CollatzResearch.WordTrace tailWord_1003107 prefixEnd_1003107 457845367901966287066045 := by
  unfold tailWord_1003107
  simp only [CollatzResearch.WordTrace]
  refine ⟨36586317976922130881463575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24390878651281420587642383 36586317976922130881463575)
  ·
    refine ⟨54879476965383196322195363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36586317976922130881463575 54879476965383196322195363)
    ·
      refine ⟨82319215448074794483293045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54879476965383196322195363 82319215448074794483293045)
      ·
        refine ⟨7717426448257011982808723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82319215448074794483293045 7717426448257011982808723)
        ·
          refine ⟨11576139672385517974213085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7717426448257011982808723 11576139672385517974213085)
          ·
            refine ⟨4341052377144569240329907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11576139672385517974213085 4341052377144569240329907)
            ·
              refine ⟨6511578565716853860494861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341052377144569240329907 6511578565716853860494861)
              ·
                refine ⟨2441841962143820197685573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6511578565716853860494861 2441841962143820197685573)
                ·
                  refine ⟨457845367901966287066045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441841962143820197685573 457845367901966287066045)
                  ·
                    rfl

theorem cell20_1003107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_1003107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003107 prefixEnd_1003107 := by exact prefixLift 1003107
  have htrace : WordTrace (prefixWord ++ tailWord_1003107) baseStart_1003107 baseEnd_1003107 := by
    simpa [prefixWord, tailWord_1003107, baseEnd_1003107] using wordTrace_append hprefix tailTrace_1003107
  have hstable : (prefixWord ++ tailWord_1003107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003107).length < 2 ^ (prefixWord ++ tailWord_1003107).sum := by decide
  have hdescent : baseEnd_1003107 < baseStart_1003107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003169 : List Nat := [1, 2, 3, 3, 2, 2, 2, 5]
def baseStart_1003169 : Nat := 118140960795 + 1003169 * 2 ^ 59
def prefixEnd_1003169 : Nat := 4983230072969 + 3 ^ 40 * 1003169 * 2
def baseEnd_1003169 : Nat := 152624555463789875666375

theorem tailTrace_1003169 : CollatzResearch.WordTrace tailWord_1003169 prefixEnd_1003169 152624555463789875666375 := by
  unfold tailWord_1003169
  simp only [CollatzResearch.WordTrace]
  refine ⟨36588579302697515470220561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24392386201798343646813707 36588579302697515470220561)
  ·
    refine ⟨27441434477023136602665421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36588579302697515470220561 27441434477023136602665421)
    ·
      refine ⟨10290537928883676225999533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27441434477023136602665421 10290537928883676225999533)
      ·
        refine ⟨3858951723331378584749825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10290537928883676225999533 3858951723331378584749825)
        ·
          refine ⟨2894213792498533938562369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3858951723331378584749825 2894213792498533938562369)
          ·
            refine ⟨2170660344373900453921777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2894213792498533938562369 2170660344373900453921777)
            ·
              refine ⟨1627995258280425340441333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2170660344373900453921777 1627995258280425340441333)
              ·
                refine ⟨152624555463789875666375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1627995258280425340441333 152624555463789875666375)
                ·
                  rfl

theorem cell20_1003169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_1003169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003169 prefixEnd_1003169 := by exact prefixLift 1003169
  have htrace : WordTrace (prefixWord ++ tailWord_1003169) baseStart_1003169 baseEnd_1003169 := by
    simpa [prefixWord, tailWord_1003169, baseEnd_1003169] using wordTrace_append hprefix tailTrace_1003169
  have hstable : (prefixWord ++ tailWord_1003169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003169).length < 2 ^ (prefixWord ++ tailWord_1003169).sum := by decide
  have hdescent : baseEnd_1003169 < baseStart_1003169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003172 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 3]
def baseStart_1003172 : Nat := 118140960795 + 1003172 * 2 ^ 59
def prefixEnd_1003172 : Nat := 4983230072969 + 3 ^ 40 * 1003172 * 2
def baseEnd_1003172 : Nat := 457875035673114949899113

theorem tailTrace_1003172 : CollatzResearch.WordTrace tailWord_1003172 prefixEnd_1003172 457875035673114949899113 := by
  unfold tailWord_1003172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18294344360843323491289885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24392459147791097988386513 18294344360843323491289885)
  ·
    refine ⟨6860379135316246309233707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18294344360843323491289885 6860379135316246309233707)
    ·
      refine ⟨10290568702974369463850561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6860379135316246309233707 10290568702974369463850561)
      ·
        refine ⟨7717926527230777097887921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10290568702974369463850561 7717926527230777097887921)
        ·
          refine ⟨5788444895423082823415941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7717926527230777097887921 5788444895423082823415941)
          ·
            refine ⟨1085333417891828029390489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5788444895423082823415941 1085333417891828029390489)
            ·
              refine ⟨814000063418871022042867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085333417891828029390489 814000063418871022042867)
              ·
                refine ⟨1221000095128306533064301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814000063418871022042867 1221000095128306533064301)
                ·
                  refine ⟨457875035673114949899113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221000095128306533064301 457875035673114949899113)
                  ·
                    rfl

theorem cell20_1003172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_1003172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003172 prefixEnd_1003172 := by exact prefixLift 1003172
  have htrace : WordTrace (prefixWord ++ tailWord_1003172) baseStart_1003172 baseEnd_1003172 := by
    simpa [prefixWord, tailWord_1003172, baseEnd_1003172] using wordTrace_append hprefix tailTrace_1003172
  have hstable : (prefixWord ++ tailWord_1003172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003172).length < 2 ^ (prefixWord ++ tailWord_1003172).sum := by decide
  have hdescent : baseEnd_1003172 < baseStart_1003172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003200 : List Nat := [2, 1, 1, 2, 4, 1, 2, 5, 2]
def baseStart_1003200 : Nat := 118140960795 + 1003200 * 2 ^ 59
def prefixEnd_1003200 : Nat := 4983230072969 + 3 ^ 40 * 1003200 * 2
def baseEnd_1003200 : Nat := 457887815636071296965665

theorem tailTrace_1003200 : CollatzResearch.WordTrace tailWord_1003200 prefixEnd_1003200 457887815636071296965665 := by
  unfold tailWord_1003200
  simp only [CollatzResearch.WordTrace]
  refine ⟨18294854982792603882299527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24393139977056805176399369 18294854982792603882299527)
  ·
    refine ⟨27442282474188905823449291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18294854982792603882299527 27442282474188905823449291)
    ·
      refine ⟨41163423711283358735173937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27442282474188905823449291 41163423711283358735173937)
      ·
        refine ⟨30872567783462519051380453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41163423711283358735173937 30872567783462519051380453)
        ·
          refine ⟨5788606459399222322133835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30872567783462519051380453 5788606459399222322133835)
          ·
            refine ⟨8682909689098833483200753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788606459399222322133835 8682909689098833483200753)
            ·
              refine ⟨6512182266824125112400565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8682909689098833483200753 6512182266824125112400565)
              ·
                refine ⟨610517087514761729287553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6512182266824125112400565 610517087514761729287553)
                ·
                  refine ⟨457887815636071296965665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610517087514761729287553 457887815636071296965665)
                  ·
                    rfl

theorem cell20_1003200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_1003200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003200 prefixEnd_1003200 := by exact prefixLift 1003200
  have htrace : WordTrace (prefixWord ++ tailWord_1003200) baseStart_1003200 baseEnd_1003200 := by
    simpa [prefixWord, tailWord_1003200, baseEnd_1003200] using wordTrace_append hprefix tailTrace_1003200
  have hstable : (prefixWord ++ tailWord_1003200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003200).length < 2 ^ (prefixWord ++ tailWord_1003200).sum := by decide
  have hdescent : baseEnd_1003200 < baseStart_1003200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003213 : List Nat := [1, 6, 2, 1, 1, 1, 4, 2, 2]
def baseStart_1003213 : Nat := 118140960795 + 1003213 * 2 ^ 59
def prefixEnd_1003213 : Nat := 4983230072969 + 3 ^ 40 * 1003213 * 2
def baseEnd_1003213 : Nat := 457893749190301029532279

theorem tailTrace_1003213 : CollatzResearch.WordTrace tailWord_1003213 prefixEnd_1003213 457893749190301029532279 := by
  unfold tailWord_1003213
  simp only [CollatzResearch.WordTrace]
  refine ⟨36590184114538110984822293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24393456076358740656548195 36590184114538110984822293)
  ·
    refine ⟨1715164880368973952413545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36590184114538110984822293 1715164880368973952413545)
    ·
      refine ⟨1286373660276730464310159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1715164880368973952413545 1286373660276730464310159)
      ·
        refine ⟨1929560490415095696465239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286373660276730464310159 1929560490415095696465239)
        ·
          refine ⟨2894340735622643544697859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929560490415095696465239 2894340735622643544697859)
          ·
            refine ⟨4341511103433965317046789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894340735622643544697859 4341511103433965317046789)
            ·
              refine ⟨814033331893868496946273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4341511103433965317046789 814033331893868496946273)
              ·
                refine ⟨610524998920401372709705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814033331893868496946273 610524998920401372709705)
                ·
                  refine ⟨457893749190301029532279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610524998920401372709705 457893749190301029532279)
                  ·
                    rfl

theorem cell20_1003213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_1003213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003213 prefixEnd_1003213 := by exact prefixLift 1003213
  have htrace : WordTrace (prefixWord ++ tailWord_1003213) baseStart_1003213 baseEnd_1003213 := by
    simpa [prefixWord, tailWord_1003213, baseEnd_1003213] using wordTrace_append hprefix tailTrace_1003213
  have hstable : (prefixWord ++ tailWord_1003213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003213).length < 2 ^ (prefixWord ++ tailWord_1003213).sum := by decide
  have hdescent : baseEnd_1003213 < baseStart_1003213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003217 : List Nat := [1, 2, 2, 1, 2, 4, 4, 2, 2]
def baseStart_1003217 : Nat := 118140960795 + 1003217 * 2 ^ 59
def prefixEnd_1003217 : Nat := 4983230072969 + 3 ^ 40 * 1003217 * 2
def baseEnd_1003217 : Nat := 457895574899294793398929

theorem tailTrace_1003217 : CollatzResearch.WordTrace tailWord_1003217 prefixEnd_1003217 457895574899294793398929 := by
  unfold tailWord_1003217
  simp only [CollatzResearch.WordTrace]
  refine ⟨36590330006523619667967905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24393553337682413111978603 36590330006523619667967905)
  ·
    refine ⟨27442747504892714750975929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36590330006523619667967905 27442747504892714750975929)
    ·
      refine ⟨20582060628669536063231947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27442747504892714750975929 20582060628669536063231947)
      ·
        refine ⟨30873090943004304094847921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20582060628669536063231947 30873090943004304094847921)
        ·
          refine ⟨23154818207253228071135941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30873090943004304094847921 23154818207253228071135941)
          ·
            refine ⟨4341528413859980263337989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23154818207253228071135941 4341528413859980263337989)
            ·
              refine ⟨814036577598746299375873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4341528413859980263337989 814036577598746299375873)
              ·
                refine ⟨610527433199059724531905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814036577598746299375873 610527433199059724531905)
                ·
                  refine ⟨457895574899294793398929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610527433199059724531905 457895574899294793398929)
                  ·
                    rfl

theorem cell20_1003217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_1003217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003217 prefixEnd_1003217 := by exact prefixLift 1003217
  have htrace : WordTrace (prefixWord ++ tailWord_1003217) baseStart_1003217 baseEnd_1003217 := by
    simpa [prefixWord, tailWord_1003217, baseEnd_1003217] using wordTrace_append hprefix tailTrace_1003217
  have hstable : (prefixWord ++ tailWord_1003217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003217).length < 2 ^ (prefixWord ++ tailWord_1003217).sum := by decide
  have hdescent : baseEnd_1003217 < baseStart_1003217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003276 : List Nat := [2, 2, 1, 2, 2, 1, 4, 4, 2]
def baseStart_1003276 : Nat := 118140960795 + 1003276 * 2 ^ 59
def prefixEnd_1003276 : Nat := 4983230072969 + 3 ^ 40 * 1003276 * 2
def baseEnd_1003276 : Nat := 457922504106952810432021

theorem tailTrace_1003276 : CollatzResearch.WordTrace tailWord_1003276 prefixEnd_1003276 457922504106952810432021 := by
  unfold tailWord_1003276
  simp only [CollatzResearch.WordTrace]
  refine ⟨18296240956654936372182841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24394987942206581829577121 18296240956654936372182841)
  ·
    refine ⟨13722180717491202279137131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18296240956654936372182841 13722180717491202279137131)
    ·
      refine ⟨20583271076236803418705697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13722180717491202279137131 20583271076236803418705697)
      ·
        refine ⟨15437453307177602564029273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20583271076236803418705697 15437453307177602564029273)
        ·
          refine ⟨11578089980383201923021955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15437453307177602564029273 11578089980383201923021955)
          ·
            refine ⟨17367134970574802884532933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11578089980383201923021955 17367134970574802884532933)
            ·
              refine ⟨3256337806982775540849925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17367134970574802884532933 3256337806982775540849925)
              ·
                refine ⟨610563338809270413909361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3256337806982775540849925 610563338809270413909361)
                ·
                  refine ⟨457922504106952810432021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610563338809270413909361 457922504106952810432021)
                  ·
                    rfl

theorem cell20_1003276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_1003276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003276 prefixEnd_1003276 := by exact prefixLift 1003276
  have htrace : WordTrace (prefixWord ++ tailWord_1003276) baseStart_1003276 baseEnd_1003276 := by
    simpa [prefixWord, tailWord_1003276, baseEnd_1003276] using wordTrace_append hprefix tailTrace_1003276
  have hstable : (prefixWord ++ tailWord_1003276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003276).length < 2 ^ (prefixWord ++ tailWord_1003276).sum := by decide
  have hdescent : baseEnd_1003276 < baseStart_1003276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003297 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_1003297 : Nat := 118140960795 + 1003297 * 2 ^ 59
def prefixEnd_1003297 : Nat := 4983230072969 + 3 ^ 40 * 1003297 * 2
def baseEnd_1003297 : Nat := 457932089079170070731935

theorem tailTrace_1003297 : CollatzResearch.WordTrace tailWord_1003297 prefixEnd_1003297 457932089079170070731935 := by
  unfold tailWord_1003297
  simp only [CollatzResearch.WordTrace]
  refine ⟨36593247846233793330880145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24395498564155862220586763 36593247846233793330880145)
  ·
    refine ⟨27444935884675344998160109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36593247846233793330880145 27444935884675344998160109)
    ·
      refine ⟨10291850956753254374310041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27444935884675344998160109 10291850956753254374310041)
      ·
        refine ⟨7718888217564940780732531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10291850956753254374310041 7718888217564940780732531)
        ·
          refine ⟨11578332326347411171098797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7718888217564940780732531 11578332326347411171098797)
          ·
            refine ⟨4341874622380279189162049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11578332326347411171098797 4341874622380279189162049)
            ·
              refine ⟨3256405966785209391871537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4341874622380279189162049 3256405966785209391871537)
              ·
                refine ⟨2442304475088907043903653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3256405966785209391871537 2442304475088907043903653)
                ·
                  refine ⟨457932089079170070731935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2442304475088907043903653 457932089079170070731935)
                  ·
                    rfl

theorem cell20_1003297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_1003297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003297 prefixEnd_1003297 := by exact prefixLift 1003297
  have htrace : WordTrace (prefixWord ++ tailWord_1003297) baseStart_1003297 baseEnd_1003297 := by
    simpa [prefixWord, tailWord_1003297, baseEnd_1003297] using wordTrace_append hprefix tailTrace_1003297
  have hstable : (prefixWord ++ tailWord_1003297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003297).length < 2 ^ (prefixWord ++ tailWord_1003297).sum := by decide
  have hdescent : baseEnd_1003297 < baseStart_1003297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003300 : List Nat := [2, 3, 1, 3, 2, 3, 2, 4]
def baseStart_1003300 : Nat := 118140960795 + 1003300 * 2 ^ 59
def prefixEnd_1003300 : Nat := 4983230072969 + 3 ^ 40 * 1003300 * 2
def baseEnd_1003300 : Nat := 152644486120305131210641

theorem tailTrace_1003300 : CollatzResearch.WordTrace tailWord_1003300 prefixEnd_1003300 152644486120305131210641 := by
  unfold tailWord_1003300
  simp only [CollatzResearch.WordTrace]
  refine ⟨18296678632611462421619677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24395571510148616562159569 18296678632611462421619677)
  ·
    refine ⟨6861254487229298408107379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18296678632611462421619677 6861254487229298408107379)
    ·
      refine ⟨10291881730843947612161069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6861254487229298408107379 10291881730843947612161069)
      ·
        refine ⟨3859455649066480354560401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10291881730843947612161069 3859455649066480354560401)
        ·
          refine ⟨2894591736799860265920301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3859455649066480354560401 2894591736799860265920301)
          ·
            refine ⟨1085471901299947599720113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2894591736799860265920301 1085471901299947599720113)
            ·
              refine ⟨814103925974960699790085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085471901299947599720113 814103925974960699790085)
              ·
                refine ⟨152644486120305131210641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 814103925974960699790085 152644486120305131210641)
                ·
                  rfl

theorem cell20_1003300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_1003300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003300 prefixEnd_1003300 := by exact prefixLift 1003300
  have htrace : WordTrace (prefixWord ++ tailWord_1003300) baseStart_1003300 baseEnd_1003300 := by
    simpa [prefixWord, tailWord_1003300, baseEnd_1003300] using wordTrace_append hprefix tailTrace_1003300
  have hstable : (prefixWord ++ tailWord_1003300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003300).length < 2 ^ (prefixWord ++ tailWord_1003300).sum := by decide
  have hdescent : baseEnd_1003300 < baseStart_1003300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003331 : List Nat := [1, 1, 1, 3, 1, 6, 3, 2, 2]
def baseStart_1003331 : Nat := 118140960795 + 1003331 * 2 ^ 59
def prefixEnd_1003331 : Nat := 4983230072969 + 3 ^ 40 * 1003331 * 2
def baseEnd_1003331 : Nat := 457947607605617063598463

theorem tailTrace_1003331 : CollatzResearch.WordTrace tailWord_1003331 prefixEnd_1003331 457947607605617063598463 := by
  unfold tailWord_1003331
  simp only [CollatzResearch.WordTrace]
  refine ⟨36594487928110617137617847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24396325285407078091745231 36594487928110617137617847)
  ·
    refine ⟨54891731892165925706426771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36594487928110617137617847 54891731892165925706426771)
    ·
      refine ⟨82337597838248888559640157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54891731892165925706426771 82337597838248888559640157)
      ·
        refine ⟨30876599189343333209865059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82337597838248888559640157 30876599189343333209865059)
        ·
          refine ⟨46314898784014999814797589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30876599189343333209865059 46314898784014999814797589)
          ·
            refine ⟨2171010880500703116318637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46314898784014999814797589 2171010880500703116318637)
            ·
              refine ⟨814129080187763668619489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2171010880500703116318637 814129080187763668619489)
              ·
                refine ⟨610596810140822751464617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814129080187763668619489 610596810140822751464617)
                ·
                  refine ⟨457947607605617063598463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610596810140822751464617 457947607605617063598463)
                  ·
                    rfl

theorem cell20_1003331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 2].length) (baseStart_1003331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003331 prefixEnd_1003331 := by exact prefixLift 1003331
  have htrace : WordTrace (prefixWord ++ tailWord_1003331) baseStart_1003331 baseEnd_1003331 := by
    simpa [prefixWord, tailWord_1003331, baseEnd_1003331] using wordTrace_append hprefix tailTrace_1003331
  have hstable : (prefixWord ++ tailWord_1003331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003331).length < 2 ^ (prefixWord ++ tailWord_1003331).sum := by decide
  have hdescent : baseEnd_1003331 < baseStart_1003331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003335 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 4]
def baseStart_1003335 : Nat := 118140960795 + 1003335 * 2 ^ 59
def prefixEnd_1003335 : Nat := 4983230072969 + 3 ^ 40 * 1003335 * 2
def baseEnd_1003335 : Nat := 457949433314610827465113

theorem tailTrace_1003335 : CollatzResearch.WordTrace tailWord_1003335 prefixEnd_1003335 457949433314610827465113 := by
  unfold tailWord_1003335
  simp only [CollatzResearch.WordTrace]
  refine ⟨36594633820096125820763459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24396422546730750547175639 36594633820096125820763459)
  ·
    refine ⟨54891950730144188731145189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36594633820096125820763459 54891950730144188731145189)
    ·
      refine ⟨10292240761902035387089723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54891950730144188731145189 10292240761902035387089723)
      ·
        refine ⟨15438361142853053080634585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10292240761902035387089723 15438361142853053080634585)
        ·
          refine ⟨11578770857139789810475939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15438361142853053080634585 11578770857139789810475939)
          ·
            refine ⟨17368156285709684715713909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11578770857139789810475939 17368156285709684715713909)
            ·
              refine ⟨1628264651785282942098179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17368156285709684715713909 1628264651785282942098179)
              ·
                refine ⟨2442396977677924413147269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628264651785282942098179 2442396977677924413147269)
                ·
                  refine ⟨457949433314610827465113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2442396977677924413147269 457949433314610827465113)
                  ·
                    rfl

theorem cell20_1003335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_1003335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003335 prefixEnd_1003335 := by exact prefixLift 1003335
  have htrace : WordTrace (prefixWord ++ tailWord_1003335) baseStart_1003335 baseEnd_1003335 := by
    simpa [prefixWord, tailWord_1003335, baseEnd_1003335] using wordTrace_append hprefix tailTrace_1003335
  have hstable : (prefixWord ++ tailWord_1003335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003335).length < 2 ^ (prefixWord ++ tailWord_1003335).sum := by decide
  have hdescent : baseEnd_1003335 < baseStart_1003335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003341 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1003341 : Nat := 118140960795 + 1003341 * 2 ^ 59
def prefixEnd_1003341 : Nat := 4983230072969 + 3 ^ 40 * 1003341 * 2
def baseEnd_1003341 : Nat := 457952171878101473265089

theorem tailTrace_1003341 : CollatzResearch.WordTrace tailWord_1003341 prefixEnd_1003341 457952171878101473265089 := by
  unfold tailWord_1003341
  simp only [CollatzResearch.WordTrace]
  refine ⟨36594852658074388845481877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24396568438716259230321251 36594852658074388845481877)
  ·
    refine ⟨1715383718347236977131963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36594852658074388845481877 1715383718347236977131963)
    ·
      refine ⟨2573075577520855465697945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1715383718347236977131963 2573075577520855465697945)
      ·
        refine ⟨1929806683140641599273459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2573075577520855465697945 1929806683140641599273459)
        ·
          refine ⟨2894710024710962398910189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929806683140641599273459 2894710024710962398910189)
          ·
            refine ⟨1085516259266610899591321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2894710024710962398910189 1085516259266610899591321)
            ·
              refine ⟨814137194449958174693491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085516259266610899591321 814137194449958174693491)
              ·
                refine ⟨1221205791674937262040237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814137194449958174693491 1221205791674937262040237)
                ·
                  refine ⟨457952171878101473265089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221205791674937262040237 457952171878101473265089)
                  ·
                    rfl

theorem cell20_1003341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1003341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003341 prefixEnd_1003341 := by exact prefixLift 1003341
  have htrace : WordTrace (prefixWord ++ tailWord_1003341) baseStart_1003341 baseEnd_1003341 := by
    simpa [prefixWord, tailWord_1003341, baseEnd_1003341] using wordTrace_append hprefix tailTrace_1003341
  have hstable : (prefixWord ++ tailWord_1003341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003341).length < 2 ^ (prefixWord ++ tailWord_1003341).sum := by decide
  have hdescent : baseEnd_1003341 < baseStart_1003341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003345 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 3]
def baseStart_1003345 : Nat := 118140960795 + 1003345 * 2 ^ 59
def prefixEnd_1003345 : Nat := 4983230072969 + 3 ^ 40 * 1003345 * 2
def baseEnd_1003345 : Nat := 457953997587095237131739

theorem tailTrace_1003345 : CollatzResearch.WordTrace tailWord_1003345 prefixEnd_1003345 457953997587095237131739 := by
  unfold tailWord_1003345
  simp only [CollatzResearch.WordTrace]
  refine ⟨36594998550059897528627489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24396665700039931685751659 36594998550059897528627489)
  ·
    refine ⟨27446248912544923146470617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36594998550059897528627489 27446248912544923146470617)
    ·
      refine ⟨20584686684408692359852963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27446248912544923146470617 20584686684408692359852963)
      ·
        refine ⟨30877030026613038539779445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20584686684408692359852963 30877030026613038539779445)
        ·
          refine ⟨2894721564994972363104323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30877030026613038539779445 2894721564994972363104323)
          ·
            refine ⟨4342082347492458544656485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894721564994972363104323 4342082347492458544656485)
            ·
              refine ⟨814140440154835977123091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4342082347492458544656485 814140440154835977123091)
              ·
                refine ⟨1221210660232253965684637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814140440154835977123091 1221210660232253965684637)
                ·
                  refine ⟨457953997587095237131739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221210660232253965684637 457953997587095237131739)
                  ·
                    rfl

theorem cell20_1003345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_1003345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003345 prefixEnd_1003345 := by exact prefixLift 1003345
  have htrace : WordTrace (prefixWord ++ tailWord_1003345) baseStart_1003345 baseEnd_1003345 := by
    simpa [prefixWord, tailWord_1003345, baseEnd_1003345] using wordTrace_append hprefix tailTrace_1003345
  have hstable : (prefixWord ++ tailWord_1003345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003345).length < 2 ^ (prefixWord ++ tailWord_1003345).sum := by decide
  have hdescent : baseEnd_1003345 < baseStart_1003345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003382 : List Nat := [5, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_1003382 : Nat := 118140960795 + 1003382 * 2 ^ 59
def prefixEnd_1003382 : Nat := 4983230072969 + 3 ^ 40 * 1003382 * 2
def baseEnd_1003382 : Nat := 457970885395287552898255

theorem tailTrace_1003382 : CollatzResearch.WordTrace tailWord_1003382 prefixEnd_1003382 457970885395287552898255 := by
  unfold tailWord_1003382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287271753182865802982775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24397565367283901898482933 2287271753182865802982775)
  ·
    refine ⟨3430907629774298704474163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287271753182865802982775 3430907629774298704474163)
    ·
      refine ⟨5146361444661448056711245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3430907629774298704474163 5146361444661448056711245)
      ·
        refine ⟨1929885541748043021266717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5146361444661448056711245 1929885541748043021266717)
        ·
          refine ⟨723707078155516132975019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1929885541748043021266717 723707078155516132975019)
          ·
            refine ⟨1085560617233274199462529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723707078155516132975019 1085560617233274199462529)
            ·
              refine ⟨814170462924955649596897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085560617233274199462529 814170462924955649596897)
              ·
                refine ⟨610627847193716737197673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814170462924955649596897 610627847193716737197673)
                ·
                  refine ⟨457970885395287552898255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610627847193716737197673 457970885395287552898255)
                  ·
                    rfl

theorem cell20_1003382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_1003382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003382 prefixEnd_1003382 := by exact prefixLift 1003382
  have htrace : WordTrace (prefixWord ++ tailWord_1003382) baseStart_1003382 baseEnd_1003382 := by
    simpa [prefixWord, tailWord_1003382, baseEnd_1003382] using wordTrace_append hprefix tailTrace_1003382
  have hstable : (prefixWord ++ tailWord_1003382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003382).length < 2 ^ (prefixWord ++ tailWord_1003382).sum := by decide
  have hdescent : baseEnd_1003382 < baseStart_1003382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003393 : List Nat := [1, 2, 4, 4, 2, 1, 1, 5]
def baseStart_1003393 : Nat := 118140960795 + 1003393 * 2 ^ 59
def prefixEnd_1003393 : Nat := 4983230072969 + 3 ^ 40 * 1003393 * 2
def baseEnd_1003393 : Nat := 152658635365006801177181

theorem tailTrace_1003393 : CollatzResearch.WordTrace tailWord_1003393 prefixEnd_1003393 152658635365006801177181 := by
  unfold tailWord_1003393
  simp only [CollatzResearch.WordTrace]
  refine ⟨36596749253886001726374833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24397832835924001150916555 36596749253886001726374833)
  ·
    refine ⟨27447561940414501294781125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36596749253886001726374833 27447561940414501294781125)
    ·
      refine ⟨5146417863827718992771461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27447561940414501294781125 5146417863827718992771461)
      ·
        refine ⟨964953349467697311144649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5146417863827718992771461 964953349467697311144649)
        ·
          refine ⟨723715012100772983358487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964953349467697311144649 723715012100772983358487)
          ·
            refine ⟨1085572518151159475037731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723715012100772983358487 1085572518151159475037731)
            ·
              refine ⟨1628358777226739212556597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085572518151159475037731 1628358777226739212556597)
              ·
                refine ⟨152658635365006801177181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1628358777226739212556597 152658635365006801177181)
                ·
                  rfl

theorem cell20_1003393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 5].length) (baseStart_1003393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003393 prefixEnd_1003393 := by exact prefixLift 1003393
  have htrace : WordTrace (prefixWord ++ tailWord_1003393) baseStart_1003393 baseEnd_1003393 := by
    simpa [prefixWord, tailWord_1003393, baseEnd_1003393] using wordTrace_append hprefix tailTrace_1003393
  have hstable : (prefixWord ++ tailWord_1003393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003393).length < 2 ^ (prefixWord ++ tailWord_1003393).sum := by decide
  have hdescent : baseEnd_1003393 < baseStart_1003393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003428 : List Nat := [2, 3, 1, 2, 1, 3, 1, 5, 2]
def baseStart_1003428 : Nat := 118140960795 + 1003428 * 2 ^ 59
def prefixEnd_1003428 : Nat := 4983230072969 + 3 ^ 40 * 1003428 * 2
def baseEnd_1003428 : Nat := 457991881048715837364733

theorem tailTrace_1003428 : CollatzResearch.WordTrace tailWord_1003428 prefixEnd_1003428 457991881048715837364733 := by
  unfold tailWord_1003428
  simp only [CollatzResearch.WordTrace]
  refine ⟨18299012904379601351949469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24398683872506135135932625 18299012904379601351949469)
  ·
    refine ⟨6862129839142350506981051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18299012904379601351949469 6862129839142350506981051)
    ·
      refine ⟨10293194758713525760471577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6862129839142350506981051 10293194758713525760471577)
      ·
        refine ⟨7719896069035144320353683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10293194758713525760471577 7719896069035144320353683)
        ·
          refine ⟨11579844103552716480530525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7719896069035144320353683 11579844103552716480530525)
          ·
            refine ⟨4342441538832268680198947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11579844103552716480530525 4342441538832268680198947)
            ·
              refine ⟨6513662308248403020298421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342441538832268680198947 6513662308248403020298421)
              ·
                refine ⟨610655841398287783152977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6513662308248403020298421 610655841398287783152977)
                ·
                  refine ⟨457991881048715837364733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610655841398287783152977 457991881048715837364733)
                  ·
                    rfl

theorem cell20_1003428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_1003428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003428 prefixEnd_1003428 := by exact prefixLift 1003428
  have htrace : WordTrace (prefixWord ++ tailWord_1003428) baseStart_1003428 baseEnd_1003428 := by
    simpa [prefixWord, tailWord_1003428, baseEnd_1003428] using wordTrace_append hprefix tailTrace_1003428
  have hstable : (prefixWord ++ tailWord_1003428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003428).length < 2 ^ (prefixWord ++ tailWord_1003428).sum := by decide
  have hdescent : baseEnd_1003428 < baseStart_1003428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003439 : List Nat := [1, 1, 2, 1, 2, 2, 11]
def baseStart_1003439 : Nat := 118140960795 + 1003439 * 2 ^ 59
def prefixEnd_1003439 : Nat := 4983230072969 + 3 ^ 40 * 1003439 * 2
def baseEnd_1003439 : Nat := 50888544638716520888669

theorem tailTrace_1003439 : CollatzResearch.WordTrace tailWord_1003439 prefixEnd_1003439 50888544638716520888669 := by
  unfold tailWord_1003439
  simp only [CollatzResearch.WordTrace]
  refine ⟨36598427011719351582549371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24398951341146234388366247 36598427011719351582549371)
  ·
    refine ⟨54897640517579027373824057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36598427011719351582549371 54897640517579027373824057)
    ·
      refine ⟨41173230388184270530368043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54897640517579027373824057 41173230388184270530368043)
      ·
        refine ⟨61759845582276405795552065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41173230388184270530368043 61759845582276405795552065)
        ·
          refine ⟨46319884186707304346664049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61759845582276405795552065 46319884186707304346664049)
          ·
            refine ⟨34739913140030478259998037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46319884186707304346664049 34739913140030478259998037)
            ·
              refine ⟨50888544638716520888669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34739913140030478259998037 50888544638716520888669)
              ·
                rfl

theorem cell20_1003439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 11].length) (baseStart_1003439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003439 prefixEnd_1003439 := by exact prefixLift 1003439
  have htrace : WordTrace (prefixWord ++ tailWord_1003439) baseStart_1003439 baseEnd_1003439 := by
    simpa [prefixWord, tailWord_1003439, baseEnd_1003439] using wordTrace_append hprefix tailTrace_1003439
  have hstable : (prefixWord ++ tailWord_1003439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003439).length < 2 ^ (prefixWord ++ tailWord_1003439).sum := by decide
  have hdescent : baseEnd_1003439 < baseStart_1003439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003449 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 4]
def baseStart_1003449 : Nat := 118140960795 + 1003449 * 2 ^ 59
def prefixEnd_1003449 : Nat := 4983230072969 + 3 ^ 40 * 1003449 * 2
def baseEnd_1003449 : Nat := 458001466020933097664647

theorem tailTrace_1003449 : CollatzResearch.WordTrace tailWord_1003449 prefixEnd_1003449 458001466020933097664647 := by
  unfold tailWord_1003449
  simp only [CollatzResearch.WordTrace]
  refine ⟨36598791741683123290413401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24399194494455415526942267 36598791741683123290413401)
  ·
    refine ⟨27449093806262342467810051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36598791741683123290413401 27449093806262342467810051)
    ·
      refine ⟨41173640709393513701715077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27449093806262342467810051 41173640709393513701715077)
      ·
        refine ⟨7720057633011283819071577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41173640709393513701715077 7720057633011283819071577)
        ·
          refine ⟨5790043224758462864303683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7720057633011283819071577 5790043224758462864303683)
          ·
            refine ⟨8685064837137694296455525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790043224758462864303683 8685064837137694296455525)
            ·
              refine ⟨1628449656963317680585411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8685064837137694296455525 1628449656963317680585411)
              ·
                refine ⟨2442674485444976520878117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628449656963317680585411 2442674485444976520878117)
                ·
                  refine ⟨458001466020933097664647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2442674485444976520878117 458001466020933097664647)
                  ·
                    rfl

theorem cell20_1003449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_1003449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003449 prefixEnd_1003449 := by exact prefixLift 1003449
  have htrace : WordTrace (prefixWord ++ tailWord_1003449) baseStart_1003449 baseEnd_1003449 := by
    simpa [prefixWord, tailWord_1003449, baseEnd_1003449] using wordTrace_append hprefix tailTrace_1003449
  have hstable : (prefixWord ++ tailWord_1003449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003449).length < 2 ^ (prefixWord ++ tailWord_1003449).sum := by decide
  have hdescent : baseEnd_1003449 < baseStart_1003449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003490 : List Nat := [3, 3, 3, 1, 2, 2, 6]
def baseStart_1003490 : Nat := 118140960795 + 1003490 * 2 ^ 59
def prefixEnd_1003490 : Nat := 4983230072969 + 3 ^ 40 * 1003490 * 2
def baseEnd_1003490 : Nat := 50891131059791019699757

theorem tailTrace_1003490 : CollatzResearch.WordTrace tailWord_1003490 prefixEnd_1003490 50891131059791019699757 := by
  unfold tailWord_1003490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9150071783633646823163981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24400191423023058195103949 9150071783633646823163981)
  ·
    refine ⟨3431276918862617558686493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9150071783633646823163981 3431276918862617558686493)
    ·
      refine ⟨1286728844573481584507435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3431276918862617558686493 1286728844573481584507435)
      ·
        refine ⟨1930093266860222376761153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286728844573481584507435 1930093266860222376761153)
        ·
          refine ⟨1447569950145166782570865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930093266860222376761153 1447569950145166782570865)
          ·
            refine ⟨1085677462608875086928149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1447569950145166782570865 1085677462608875086928149)
            ·
              refine ⟨50891131059791019699757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1085677462608875086928149 50891131059791019699757)
              ·
                rfl

theorem cell20_1003490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 6].length) (baseStart_1003490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003490 prefixEnd_1003490 := by exact prefixLift 1003490
  have htrace : WordTrace (prefixWord ++ tailWord_1003490) baseStart_1003490 baseEnd_1003490 := by
    simpa [prefixWord, tailWord_1003490, baseEnd_1003490] using wordTrace_append hprefix tailTrace_1003490
  have hstable : (prefixWord ++ tailWord_1003490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003490).length < 2 ^ (prefixWord ++ tailWord_1003490).sum := by decide
  have hdescent : baseEnd_1003490 < baseStart_1003490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003515 : List Nat := [1, 1, 1, 1, 1, 3, 5, 7]
def baseStart_1003515 : Nat := 118140960795 + 1003515 * 2 ^ 59
def prefixEnd_1003515 : Nat := 4983230072969 + 3 ^ 40 * 1003515 * 2
def baseEnd_1003515 : Nat := 152677196739776733821459

theorem tailTrace_1003515 : CollatzResearch.WordTrace tailWord_1003515 prefixEnd_1003515 152677196739776733821459 := by
  unfold tailWord_1003515
  simp only [CollatzResearch.WordTrace]
  refine ⟨36601198959444016562315999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24400799306296011041543999 36601198959444016562315999)
  ·
    refine ⟨54901798439166024843473999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36601198959444016562315999 54901798439166024843473999)
    ·
      refine ⟨82352697658749037265210999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54901798439166024843473999 82352697658749037265210999)
      ·
        refine ⟨123529046488123555897816499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82352697658749037265210999 123529046488123555897816499)
        ·
          refine ⟨185293569732185333846724749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123529046488123555897816499 185293569732185333846724749)
          ·
            refine ⟨69485088649569500192521781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185293569732185333846724749 69485088649569500192521781)
            ·
              refine ⟨6514227060897140643048917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69485088649569500192521781 6514227060897140643048917)
              ·
                refine ⟨152677196739776733821459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6514227060897140643048917 152677196739776733821459)
                ·
                  rfl

theorem cell20_1003515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_1003515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003515 prefixEnd_1003515 := by exact prefixLift 1003515
  have htrace : WordTrace (prefixWord ++ tailWord_1003515) baseStart_1003515 baseEnd_1003515 := by
    simpa [prefixWord, tailWord_1003515, baseEnd_1003515] using wordTrace_append hprefix tailTrace_1003515
  have hstable : (prefixWord ++ tailWord_1003515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003515).length < 2 ^ (prefixWord ++ tailWord_1003515).sum := by decide
  have hdescent : baseEnd_1003515 < baseStart_1003515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003553 : List Nat := [1, 2, 3, 2, 12]
def baseStart_1003553 : Nat := 118140960795 + 1003553 * 2 ^ 59
def prefixEnd_1003553 : Nat := 4983230072969 + 3 ^ 40 * 1003553 * 2
def baseEnd_1003553 : Nat := 5654925116725567385155

theorem tailTrace_1003553 : CollatzResearch.WordTrace tailWord_1003553 prefixEnd_1003553 5654925116725567385155 := by
  unfold tailWord_1003553
  simp only [CollatzResearch.WordTrace]
  refine ⟨36602584933306349052199313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24401723288870899368132875 36602584933306349052199313)
  ·
    refine ⟨27451938699979761789149485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36602584933306349052199313 27451938699979761789149485)
    ·
      refine ⟨10294477012492410670931057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27451938699979761789149485 10294477012492410670931057)
      ·
        refine ⟨7720857759369308003198293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10294477012492410670931057 7720857759369308003198293)
        ·
          refine ⟨5654925116725567385155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7720857759369308003198293 5654925116725567385155)
          ·
            rfl

theorem cell20_1003553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 12].length) (baseStart_1003553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003553 prefixEnd_1003553 := by exact prefixLift 1003553
  have htrace : WordTrace (prefixWord ++ tailWord_1003553) baseStart_1003553 baseEnd_1003553 := by
    simpa [prefixWord, tailWord_1003553, baseEnd_1003553] using wordTrace_append hprefix tailTrace_1003553
  have hstable : (prefixWord ++ tailWord_1003553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003553).length < 2 ^ (prefixWord ++ tailWord_1003553).sum := by decide
  have hdescent : baseEnd_1003553 < baseStart_1003553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003570 : List Nat := [3, 2, 1, 1, 2, 3, 3, 5]
def baseStart_1003570 : Nat := 118140960795 + 1003570 * 2 ^ 59
def prefixEnd_1003570 : Nat := 4983230072969 + 3 ^ 40 * 1003570 * 2
def baseEnd_1003570 : Nat := 152685564572664818210273

theorem tailTrace_1003570 : CollatzResearch.WordTrace tailWord_1003570 prefixEnd_1003570 152685564572664818210273 := by
  unfold tailWord_1003570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9150801243561190238892041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24402136649496507303712109 9150801243561190238892041)
  ·
    refine ⟨6863100932670892679169031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9150801243561190238892041 6863100932670892679169031)
    ·
      refine ⟨10294651399006339018753547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6863100932670892679169031 10294651399006339018753547)
      ·
        refine ⟨15441977098509508528130321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10294651399006339018753547 15441977098509508528130321)
        ·
          refine ⟨11581482823882131396097741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15441977098509508528130321 11581482823882131396097741)
          ·
            refine ⟨4343056058955799273536653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11581482823882131396097741 4343056058955799273536653)
            ·
              refine ⟨1628646022108424727576245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4343056058955799273536653 1628646022108424727576245)
              ·
                refine ⟨152685564572664818210273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1628646022108424727576245 152685564572664818210273)
                ·
                  rfl

theorem cell20_1003570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_1003570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003570 prefixEnd_1003570 := by exact prefixLift 1003570
  have htrace : WordTrace (prefixWord ++ tailWord_1003570) baseStart_1003570 baseEnd_1003570 := by
    simpa [prefixWord, tailWord_1003570, baseEnd_1003570] using wordTrace_append hprefix tailTrace_1003570
  have hstable : (prefixWord ++ tailWord_1003570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003570).length < 2 ^ (prefixWord ++ tailWord_1003570).sum := by decide
  have hdescent : baseEnd_1003570 < baseStart_1003570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003584 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_1003584 : Nat := 118140960795 + 1003584 * 2 ^ 59
def prefixEnd_1003584 : Nat := 4983230072969 + 3 ^ 40 * 1003584 * 2
def baseEnd_1003584 : Nat := 458063083699472628164095

theorem tailTrace_1003584 : CollatzResearch.WordTrace tailWord_1003584 prefixEnd_1003584 458063083699472628164095 := by
  unfold tailWord_1003584
  simp only [CollatzResearch.WordTrace]
  refine ⟨18301857798097020673288903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24402477064129360897718537 18301857798097020673288903)
  ·
    refine ⟨27452786697145531009933355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18301857798097020673288903 27452786697145531009933355)
    ·
      refine ⟨41179180045718296514900033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27452786697145531009933355 41179180045718296514900033)
      ·
        refine ⟨30884385034288722386175025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41179180045718296514900033 30884385034288722386175025)
        ·
          refine ⟨23163288775716541789631269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30884385034288722386175025 23163288775716541789631269)
          ·
            refine ⟨4343116645446851585555863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23163288775716541789631269 4343116645446851585555863)
            ·
              refine ⟨6514674968170277378333795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343116645446851585555863 6514674968170277378333795)
              ·
                refine ⟨9772012452255416067500693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6514674968170277378333795 9772012452255416067500693)
                ·
                  refine ⟨458063083699472628164095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9772012452255416067500693 458063083699472628164095)
                  ·
                    rfl

theorem cell20_1003584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_1003584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003584 prefixEnd_1003584 := by exact prefixLift 1003584
  have htrace : WordTrace (prefixWord ++ tailWord_1003584) baseStart_1003584 baseEnd_1003584 := by
    simpa [prefixWord, tailWord_1003584, baseEnd_1003584] using wordTrace_append hprefix tailTrace_1003584
  have hstable : (prefixWord ++ tailWord_1003584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003584).length < 2 ^ (prefixWord ++ tailWord_1003584).sum := by decide
  have hdescent : baseEnd_1003584 < baseStart_1003584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003597 : List Nat := [1, 6, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1003597 : Nat := 118140960795 + 1003597 * 2 ^ 59
def prefixEnd_1003597 : Nat := 4983230072969 + 3 ^ 40 * 1003597 * 2
def baseEnd_1003597 : Nat := 458069017253702360730709

theorem tailTrace_1003597 : CollatzResearch.WordTrace tailWord_1003597 prefixEnd_1003597 458069017253702360730709 := by
  unfold tailWord_1003597
  simp only [CollatzResearch.WordTrace]
  refine ⟨36604189745146944566801045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24402793163431296377867363 36604189745146944566801045)
  ·
    refine ⟨1715821394303763026568799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36604189745146944566801045 1715821394303763026568799)
    ·
      refine ⟨2573732091455644539853199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1715821394303763026568799 2573732091455644539853199)
      ·
        refine ⟨3860598137183466809779799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2573732091455644539853199 3860598137183466809779799)
        ·
          refine ⟨5790897205775200214669699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860598137183466809779799 5790897205775200214669699)
          ·
            refine ⟨8686345808662800322004549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790897205775200214669699 8686345808662800322004549)
            ·
              refine ⟨1628689839124275060375853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8686345808662800322004549 1628689839124275060375853)
              ·
                refine ⟨610758689671603147640945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1628689839124275060375853 610758689671603147640945)
                ·
                  refine ⟨458069017253702360730709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610758689671603147640945 458069017253702360730709)
                  ·
                    rfl

theorem cell20_1003597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1003597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003597 prefixEnd_1003597 := by exact prefixLift 1003597
  have htrace : WordTrace (prefixWord ++ tailWord_1003597) baseStart_1003597 baseEnd_1003597 := by
    simpa [prefixWord, tailWord_1003597, baseEnd_1003597] using wordTrace_append hprefix tailTrace_1003597
  have hstable : (prefixWord ++ tailWord_1003597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003597).length < 2 ^ (prefixWord ++ tailWord_1003597).sum := by decide
  have hdescent : baseEnd_1003597 < baseStart_1003597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003614 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1003614 : Nat := 118140960795 + 1003614 * 2 ^ 59
def prefixEnd_1003614 : Nat := 4983230072969 + 3 ^ 40 * 1003614 * 2
def baseEnd_1003614 : Nat := 458076776516925857163973

theorem tailTrace_1003614 : CollatzResearch.WordTrace tailWord_1003614 prefixEnd_1003614 458076776516925857163973 := by
  unfold tailWord_1003614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4575601223260669558771237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24403206524056904313446597 4575601223260669558771237)
  ·
    refine ⟨857925229361375542269607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4575601223260669558771237 857925229361375542269607)
    ·
      refine ⟨1286887844042063313404411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857925229361375542269607 1286887844042063313404411)
      ·
        refine ⟨1930331766063094970106617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286887844042063313404411 1930331766063094970106617)
        ·
          refine ⟨1447748824547321227579963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930331766063094970106617 1447748824547321227579963)
          ·
            refine ⟨2171623236820981841369945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447748824547321227579963 2171623236820981841369945)
            ·
              refine ⟨1628717427615736381027459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171623236820981841369945 1628717427615736381027459)
              ·
                refine ⟨2443076141423604571541189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628717427615736381027459 2443076141423604571541189)
                ·
                  refine ⟨458076776516925857163973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2443076141423604571541189 458076776516925857163973)
                  ·
                    rfl

theorem cell20_1003614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1003614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003614 prefixEnd_1003614 := by exact prefixLift 1003614
  have htrace : WordTrace (prefixWord ++ tailWord_1003614) baseStart_1003614 baseEnd_1003614 := by
    simpa [prefixWord, tailWord_1003614, baseEnd_1003614] using wordTrace_append hprefix tailTrace_1003614
  have hstable : (prefixWord ++ tailWord_1003614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003614).length < 2 ^ (prefixWord ++ tailWord_1003614).sum := by decide
  have hdescent : baseEnd_1003614 < baseStart_1003614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003615 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 3]
def baseStart_1003615 : Nat := 118140960795 + 1003615 * 2 ^ 59
def prefixEnd_1003615 : Nat := 4983230072969 + 3 ^ 40 * 1003615 * 2
def baseEnd_1003615 : Nat := 458077232944174298130635

theorem tailTrace_1003615 : CollatzResearch.WordTrace tailWord_1003615 prefixEnd_1003615 458077232944174298130635 := by
  unfold tailWord_1003615
  simp only [CollatzResearch.WordTrace]
  refine ⟨36604846259081733640956299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24403230839387822427304199 36604846259081733640956299)
  ·
    refine ⟨54907269388622600461434449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36604846259081733640956299 54907269388622600461434449)
    ·
      refine ⟨41180452041466950346075837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54907269388622600461434449 41180452041466950346075837)
      ·
        refine ⟨15442669515550106379778439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41180452041466950346075837 15442669515550106379778439)
        ·
          refine ⟨23164004273325159569667659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15442669515550106379778439 23164004273325159569667659)
          ·
            refine ⟨34746006409987739354501489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23164004273325159569667659 34746006409987739354501489)
            ·
              refine ⟨26059504807490804515876117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34746006409987739354501489 26059504807490804515876117)
              ·
                refine ⟨1221539287851131461681693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26059504807490804515876117 1221539287851131461681693)
                ·
                  refine ⟨458077232944174298130635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221539287851131461681693 458077232944174298130635)
                  ·
                    rfl

theorem cell20_1003615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 3].length) (baseStart_1003615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003615 prefixEnd_1003615 := by exact prefixLift 1003615
  have htrace : WordTrace (prefixWord ++ tailWord_1003615) baseStart_1003615 baseEnd_1003615 := by
    simpa [prefixWord, tailWord_1003615, baseEnd_1003615] using wordTrace_append hprefix tailTrace_1003615
  have hstable : (prefixWord ++ tailWord_1003615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003615).length < 2 ^ (prefixWord ++ tailWord_1003615).sum := by decide
  have hdescent : baseEnd_1003615 < baseStart_1003615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003653 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1003653 : Nat := 118140960795 + 1003653 * 2 ^ 59
def prefixEnd_1003653 : Nat := 4983230072969 + 3 ^ 40 * 1003653 * 2
def baseEnd_1003653 : Nat := 458094577179615054863813

theorem tailTrace_1003653 : CollatzResearch.WordTrace tailWord_1003653 prefixEnd_1003653 458094577179615054863813 := by
  unfold tailWord_1003653
  simp only [CollatzResearch.WordTrace]
  refine ⟨36606232232944066130839613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24404154821962710753893075 36606232232944066130839613)
  ·
    refine ⟨13727337087354024799064855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36606232232944066130839613 13727337087354024799064855)
    ·
      refine ⟨20591005631031037198597283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13727337087354024799064855 20591005631031037198597283)
      ·
        refine ⟨30886508446546555797895925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20591005631031037198597283 30886508446546555797895925)
        ·
          refine ⟨2895610166863739606052743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30886508446546555797895925 2895610166863739606052743)
          ·
            refine ⟨4343415250295609409079115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895610166863739606052743 4343415250295609409079115)
            ·
              refine ⟨6515122875443414113618673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343415250295609409079115 6515122875443414113618673)
              ·
                refine ⟨4886342156582560585214005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6515122875443414113618673 4886342156582560585214005)
                ·
                  refine ⟨458094577179615054863813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4886342156582560585214005 458094577179615054863813)
                  ·
                    rfl

theorem cell20_1003653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1003653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003653 prefixEnd_1003653 := by exact prefixLift 1003653
  have htrace : WordTrace (prefixWord ++ tailWord_1003653) baseStart_1003653 baseEnd_1003653 := by
    simpa [prefixWord, tailWord_1003653, baseEnd_1003653] using wordTrace_append hprefix tailTrace_1003653
  have hstable : (prefixWord ++ tailWord_1003653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003653).length < 2 ^ (prefixWord ++ tailWord_1003653).sum := by decide
  have hdescent : baseEnd_1003653 < baseStart_1003653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003677 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1003677 : Nat := 118140960795 + 1003677 * 2 ^ 59
def prefixEnd_1003677 : Nat := 4983230072969 + 3 ^ 40 * 1003677 * 2
def baseEnd_1003677 : Nat := 458105531433577638063715

theorem tailTrace_1003677 : CollatzResearch.WordTrace tailWord_1003677 prefixEnd_1003677 458105531433577638063715 := by
  unfold tailWord_1003677
  simp only [CollatzResearch.WordTrace]
  refine ⟨36607107584857118229713285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24404738389904745486475523 36607107584857118229713285)
  ·
    refine ⟨6863832672160709668071241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36607107584857118229713285 6863832672160709668071241)
    ·
      refine ⟨5147874504120532251053431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6863832672160709668071241 5147874504120532251053431)
      ·
        refine ⟨7721811756180798376580147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5147874504120532251053431 7721811756180798376580147)
        ·
          refine ⟨11582717634271197564870221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7721811756180798376580147 11582717634271197564870221)
          ·
            refine ⟨4343519112851699086826333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11582717634271197564870221 4343519112851699086826333)
            ·
              refine ⟨1628819667319387157559875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4343519112851699086826333 1628819667319387157559875)
              ·
                refine ⟨2443229500979080736339813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628819667319387157559875 2443229500979080736339813)
                ·
                  refine ⟨458105531433577638063715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2443229500979080736339813 458105531433577638063715)
                  ·
                    rfl

theorem cell20_1003677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1003677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003677 prefixEnd_1003677 := by exact prefixLift 1003677
  have htrace : WordTrace (prefixWord ++ tailWord_1003677) baseStart_1003677 baseEnd_1003677 := by
    simpa [prefixWord, tailWord_1003677, baseEnd_1003677] using wordTrace_append hprefix tailTrace_1003677
  have hstable : (prefixWord ++ tailWord_1003677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003677).length < 2 ^ (prefixWord ++ tailWord_1003677).sum := by decide
  have hdescent : baseEnd_1003677 < baseStart_1003677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003687 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 3]
def baseStart_1003687 : Nat := 118140960795 + 1003687 * 2 ^ 59
def prefixEnd_1003687 : Nat := 4983230072969 + 3 ^ 40 * 1003687 * 2
def baseEnd_1003687 : Nat := 458110095706062047730341

theorem tailTrace_1003687 : CollatzResearch.WordTrace tailWord_1003687 prefixEnd_1003687 458110095706062047730341 := by
  unfold tailWord_1003687
  simp only [CollatzResearch.WordTrace]
  refine ⟨36607472314820889937577315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24404981543213926625051543 36607472314820889937577315)
  ·
    refine ⟨54911208472231334906365973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36607472314820889937577315 54911208472231334906365973)
    ·
      refine ⟨2573962897135843823735905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54911208472231334906365973 2573962897135843823735905)
      ·
        refine ⟨1930472172851882867801929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2573962897135843823735905 1930472172851882867801929)
        ·
          refine ⟨1447854129638912150851447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930472172851882867801929 1447854129638912150851447)
          ·
            refine ⟨2171781194458368226277171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447854129638912150851447 2171781194458368226277171)
            ·
              refine ⟨3257671791687552339415757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171781194458368226277171 3257671791687552339415757)
              ·
                refine ⟨1221626921882832127280909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3257671791687552339415757 1221626921882832127280909)
                ·
                  refine ⟨458110095706062047730341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221626921882832127280909 458110095706062047730341)
                  ·
                    rfl

theorem cell20_1003687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 3].length) (baseStart_1003687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003687 prefixEnd_1003687 := by exact prefixLift 1003687
  have htrace : WordTrace (prefixWord ++ tailWord_1003687) baseStart_1003687 baseEnd_1003687 := by
    simpa [prefixWord, tailWord_1003687, baseEnd_1003687] using wordTrace_append hprefix tailTrace_1003687
  have hstable : (prefixWord ++ tailWord_1003687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003687).length < 2 ^ (prefixWord ++ tailWord_1003687).sum := by decide
  have hdescent : baseEnd_1003687 < baseStart_1003687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003698 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1003698 : Nat := 118140960795 + 1003698 * 2 ^ 59
def prefixEnd_1003698 : Nat := 4983230072969 + 3 ^ 40 * 1003698 * 2
def baseEnd_1003698 : Nat := 458115116405794898363629

theorem tailTrace_1003698 : CollatzResearch.WordTrace tailWord_1003698 prefixEnd_1003698 458115116405794898363629 := by
  unfold tailWord_1003698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151968379445259704056937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24405249011854025877485165 9151968379445259704056937)
  ·
    refine ⟨6863976284583944778042703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9151968379445259704056937 6863976284583944778042703)
    ·
      refine ⟨10295964426875917167064055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6863976284583944778042703 10295964426875917167064055)
      ·
        refine ⟨15443946640313875750596083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10295964426875917167064055 15443946640313875750596083)
        ·
          refine ⟨23165919960470813625894125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15443946640313875750596083 23165919960470813625894125)
          ·
            refine ⟨8687219985176555109710297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23165919960470813625894125 8687219985176555109710297)
            ·
              refine ⟨6515414988882416332282723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8687219985176555109710297 6515414988882416332282723)
              ·
                refine ⟨9773122483323624498424085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6515414988882416332282723 9773122483323624498424085)
                ·
                  refine ⟨458115116405794898363629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9773122483323624498424085 458115116405794898363629)
                  ·
                    rfl

theorem cell20_1003698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1003698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003698 prefixEnd_1003698 := by exact prefixLift 1003698
  have htrace : WordTrace (prefixWord ++ tailWord_1003698) baseStart_1003698 baseEnd_1003698 := by
    simpa [prefixWord, tailWord_1003698, baseEnd_1003698] using wordTrace_append hprefix tailTrace_1003698
  have hstable : (prefixWord ++ tailWord_1003698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003698).length < 2 ^ (prefixWord ++ tailWord_1003698).sum := by decide
  have hdescent : baseEnd_1003698 < baseStart_1003698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003705 : List Nat := [1, 2, 1, 4, 1, 2, 1, 8]
def baseStart_1003705 : Nat := 118140960795 + 1003705 * 2 ^ 59
def prefixEnd_1003705 : Nat := 4983230072969 + 3 ^ 40 * 1003705 * 2
def baseEnd_1003705 : Nat := 152706103798844661710089

theorem tailTrace_1003705 : CollatzResearch.WordTrace tailWord_1003705 prefixEnd_1003705 152706103798844661710089 := by
  unfold tailWord_1003705
  simp only [CollatzResearch.WordTrace]
  refine ⟨36608128828755679011732569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24405419219170452674488379 36608128828755679011732569)
  ·
    refine ⟨27456096621566759258799427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36608128828755679011732569 27456096621566759258799427)
    ·
      refine ⟨41184144932350138888199141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27456096621566759258799427 41184144932350138888199141)
      ·
        refine ⟨7722027174815651041537339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41184144932350138888199141 7722027174815651041537339)
        ·
          refine ⟨11583040762223476562306009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7722027174815651041537339 11583040762223476562306009)
          ·
            refine ⟨8687280571667607421729507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11583040762223476562306009 8687280571667607421729507)
            ·
              refine ⟨13030920857501411132594261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8687280571667607421729507 13030920857501411132594261)
              ·
                refine ⟨152706103798844661710089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13030920857501411132594261 152706103798844661710089)
                ·
                  rfl

theorem cell20_1003705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_1003705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003705 prefixEnd_1003705 := by exact prefixLift 1003705
  have htrace : WordTrace (prefixWord ++ tailWord_1003705) baseStart_1003705 baseEnd_1003705 := by
    simpa [prefixWord, tailWord_1003705, baseEnd_1003705] using wordTrace_append hprefix tailTrace_1003705
  have hstable : (prefixWord ++ tailWord_1003705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003705).length < 2 ^ (prefixWord ++ tailWord_1003705).sum := by decide
  have hdescent : baseEnd_1003705 < baseStart_1003705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003729 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 3]
def baseStart_1003729 : Nat := 118140960795 + 1003729 * 2 ^ 59
def prefixEnd_1003729 : Nat := 4983230072969 + 3 ^ 40 * 1003729 * 2
def baseEnd_1003729 : Nat := 458129265650496568330169

theorem tailTrace_1003729 : CollatzResearch.WordTrace tailWord_1003729 prefixEnd_1003729 458129265650496568330169 := by
  unfold tailWord_1003729
  simp only [CollatzResearch.WordTrace]
  refine ⟨36609004180668731110606241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24406002787112487407070827 36609004180668731110606241)
  ·
    refine ⟨27456753135501548332954681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36609004180668731110606241 27456753135501548332954681)
    ·
      refine ⟨20592564851626161249716011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27456753135501548332954681 20592564851626161249716011)
      ·
        refine ⟨30888847277439241874574017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20592564851626161249716011 30888847277439241874574017)
        ·
          refine ⟨23166635458079431405930513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30888847277439241874574017 23166635458079431405930513)
          ·
            refine ⟨17374976593559573554447885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23166635458079431405930513 17374976593559573554447885)
            ·
              refine ⟨6515616222584840082917957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17374976593559573554447885 6515616222584840082917957)
              ·
                refine ⟨1221678041734657515547117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6515616222584840082917957 1221678041734657515547117)
                ·
                  refine ⟨458129265650496568330169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221678041734657515547117 458129265650496568330169)
                  ·
                    rfl

theorem cell20_1003729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_1003729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003729 prefixEnd_1003729 := by exact prefixLift 1003729
  have htrace : WordTrace (prefixWord ++ tailWord_1003729) baseStart_1003729 baseEnd_1003729 := by
    simpa [prefixWord, tailWord_1003729, baseEnd_1003729] using wordTrace_append hprefix tailTrace_1003729
  have hstable : (prefixWord ++ tailWord_1003729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003729).length < 2 ^ (prefixWord ++ tailWord_1003729).sum := by decide
  have hdescent : baseEnd_1003729 < baseStart_1003729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003770 : List Nat := [3, 1, 1, 1, 1, 6, 2, 3, 2]
def baseStart_1003770 : Nat := 118140960795 + 1003770 * 2 ^ 59
def prefixEnd_1003770 : Nat := 4983230072969 + 3 ^ 40 * 1003770 * 2
def baseEnd_1003770 : Nat := 458147979167682647963335

theorem tailTrace_1003770 : CollatzResearch.WordTrace tailWord_1003770 prefixEnd_1003770 458147979167682647963335 := by
  unfold tailWord_1003770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9152624893380048778212191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24406999715680130075232509 9152624893380048778212191)
  ·
    refine ⟨13728937340070073167318287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9152624893380048778212191 13728937340070073167318287)
    ·
      refine ⟨20593406010105109750977431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13728937340070073167318287 20593406010105109750977431)
      ·
        refine ⟨30890109015157664626466147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20593406010105109750977431 30890109015157664626466147)
        ·
          refine ⟨46335163522736496939699221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30890109015157664626466147 46335163522736496939699221)
          ·
            refine ⟨2171960790128273294048401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46335163522736496939699221 2171960790128273294048401)
            ·
              refine ⟨1628970592596204970536301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171960790128273294048401 1628970592596204970536301)
              ·
                refine ⟨610863972223576863951113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1628970592596204970536301 610863972223576863951113)
                ·
                  refine ⟨458147979167682647963335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610863972223576863951113 458147979167682647963335)
                  ·
                    rfl

theorem cell20_1003770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_1003770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003770 prefixEnd_1003770 := by exact prefixLift 1003770
  have htrace : WordTrace (prefixWord ++ tailWord_1003770) baseStart_1003770 baseEnd_1003770 := by
    simpa [prefixWord, tailWord_1003770, baseEnd_1003770] using wordTrace_append hprefix tailTrace_1003770
  have hstable : (prefixWord ++ tailWord_1003770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003770).length < 2 ^ (prefixWord ++ tailWord_1003770).sum := by decide
  have hdescent : baseEnd_1003770 < baseStart_1003770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003780 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 3]
def baseStart_1003780 : Nat := 118140960795 + 1003780 * 2 ^ 59
def prefixEnd_1003780 : Nat := 4983230072969 + 3 ^ 40 * 1003780 * 2
def baseEnd_1003780 : Nat := 458152543440167057629961

theorem tailTrace_1003780 : CollatzResearch.WordTrace tailWord_1003780 prefixEnd_1003780 458152543440167057629961 := by
  unfold tailWord_1003780
  simp only [CollatzResearch.WordTrace]
  refine ⟨18305432151741983410356397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24407242868989311213808529 18305432151741983410356397)
  ·
    refine ⟨6864537056903243778883649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18305432151741983410356397 6864537056903243778883649)
    ·
      refine ⟨5148402792677432834162737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6864537056903243778883649 5148402792677432834162737)
      ·
        refine ⟨3861302094508074625622053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5148402792677432834162737 3861302094508074625622053)
        ·
          refine ⟨723994142720263992304135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3861302094508074625622053 723994142720263992304135)
          ·
            refine ⟨1085991214080395988456203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723994142720263992304135 1085991214080395988456203)
            ·
              refine ⟨1628986821120593982684305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085991214080395988456203 1628986821120593982684305)
              ·
                refine ⟨1221740115840445487013229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1628986821120593982684305 1221740115840445487013229)
                ·
                  refine ⟨458152543440167057629961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221740115840445487013229 458152543440167057629961)
                  ·
                    rfl

theorem cell20_1003780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_1003780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003780 prefixEnd_1003780 := by exact prefixLift 1003780
  have htrace : WordTrace (prefixWord ++ tailWord_1003780) baseStart_1003780 baseEnd_1003780 := by
    simpa [prefixWord, tailWord_1003780, baseEnd_1003780] using wordTrace_append hprefix tailTrace_1003780
  have hstable : (prefixWord ++ tailWord_1003780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003780).length < 2 ^ (prefixWord ++ tailWord_1003780).sum := by decide
  have hdescent : baseEnd_1003780 < baseStart_1003780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003784 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 3]
def baseStart_1003784 : Nat := 118140960795 + 1003784 * 2 ^ 59
def prefixEnd_1003784 : Nat := 4983230072969 + 3 ^ 40 * 1003784 * 2
def baseEnd_1003784 : Nat := 458154369149160821496611

theorem tailTrace_1003784 : CollatzResearch.WordTrace tailWord_1003784 prefixEnd_1003784 458154369149160821496611 := by
  unfold tailWord_1003784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18305505097734737751929203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24407340130312983669238937 18305505097734737751929203)
  ·
    refine ⟨27458257646602106627893805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18305505097734737751929203 27458257646602106627893805)
    ·
      refine ⟨10296846617475789985460177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27458257646602106627893805 10296846617475789985460177)
      ·
        refine ⟨7722634963106842489095133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10296846617475789985460177 7722634963106842489095133)
        ·
          refine ⟨2895988111165065933410675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7722634963106842489095133 2895988111165065933410675)
          ·
            refine ⟨4343982166747598900116013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895988111165065933410675 4343982166747598900116013)
            ·
              refine ⟨1628993312530349587543505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4343982166747598900116013 1628993312530349587543505)
              ·
                refine ⟨1221744984397762190657629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1628993312530349587543505 1221744984397762190657629)
                ·
                  refine ⟨458154369149160821496611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221744984397762190657629 458154369149160821496611)
                  ·
                    rfl

theorem cell20_1003784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_1003784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003784 prefixEnd_1003784 := by exact prefixLift 1003784
  have htrace : WordTrace (prefixWord ++ tailWord_1003784) baseStart_1003784 baseEnd_1003784 := by
    simpa [prefixWord, tailWord_1003784, baseEnd_1003784] using wordTrace_append hprefix tailTrace_1003784
  have hstable : (prefixWord ++ tailWord_1003784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003784).length < 2 ^ (prefixWord ++ tailWord_1003784).sum := by decide
  have hdescent : baseEnd_1003784 < baseStart_1003784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003821 : List Nat := [1, 5, 3, 1, 3, 1, 1, 3, 2]
def baseStart_1003821 : Nat := 118140960795 + 1003821 * 2 ^ 59
def prefixEnd_1003821 : Nat := 4983230072969 + 3 ^ 40 * 1003821 * 2
def baseEnd_1003821 : Nat := 458171256957353137263127

theorem tailTrace_1003821 : CollatzResearch.WordTrace tailWord_1003821 prefixEnd_1003821 458171256957353137263127 := by
  unfold tailWord_1003821
  simp only [CollatzResearch.WordTrace]
  refine ⟨36612359696335430822955317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24408239797556953881970211 36612359696335430822955317)
  ·
    refine ⟨3432408721531446639652061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36612359696335430822955317 3432408721531446639652061)
    ·
      refine ⟨1287153270574292489869523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3432408721531446639652061 1287153270574292489869523)
      ·
        refine ⟨1930729905861438734804285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287153270574292489869523 1930729905861438734804285)
        ·
          refine ⟨724023714698039525551607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1930729905861438734804285 724023714698039525551607)
          ·
            refine ⟨1086035572047059288327411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724023714698039525551607 1086035572047059288327411)
            ·
              refine ⟨1629053358070588932491117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086035572047059288327411 1629053358070588932491117)
              ·
                refine ⟨610895009276470849684169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1629053358070588932491117 610895009276470849684169)
                ·
                  refine ⟨458171256957353137263127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610895009276470849684169 458171256957353137263127)
                  ·
                    rfl

theorem cell20_1003821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_1003821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003821 prefixEnd_1003821 := by exact prefixLift 1003821
  have htrace : WordTrace (prefixWord ++ tailWord_1003821) baseStart_1003821 baseEnd_1003821 := by
    simpa [prefixWord, tailWord_1003821, baseEnd_1003821] using wordTrace_append hprefix tailTrace_1003821
  have hstable : (prefixWord ++ tailWord_1003821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003821).length < 2 ^ (prefixWord ++ tailWord_1003821).sum := by decide
  have hdescent : baseEnd_1003821 < baseStart_1003821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003825 : List Nat := [1, 2, 2, 3, 4, 2, 1, 3, 2]
def baseStart_1003825 : Nat := 118140960795 + 1003825 * 2 ^ 59
def prefixEnd_1003825 : Nat := 4983230072969 + 3 ^ 40 * 1003825 * 2
def baseEnd_1003825 : Nat := 458173082666346901129777

theorem tailTrace_1003825 : CollatzResearch.WordTrace tailWord_1003825 prefixEnd_1003825 458173082666346901129777 := by
  unfold tailWord_1003825
  simp only [CollatzResearch.WordTrace]
  refine ⟨36612505588320939506100929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24408337058880626337400619 36612505588320939506100929)
  ·
    refine ⟨27459379191240704629575697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36612505588320939506100929 27459379191240704629575697)
    ·
      refine ⟨20594534393430528472181773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27459379191240704629575697 20594534393430528472181773)
      ·
        refine ⟨7722950397536448177068165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20594534393430528472181773 7722950397536448177068165)
        ·
          refine ⟨1448053199538084033200281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7722950397536448177068165 1448053199538084033200281)
          ·
            refine ⟨1086039899653563024900211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448053199538084033200281 1086039899653563024900211)
            ·
              refine ⟨1629059849480344537350317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086039899653563024900211 1629059849480344537350317)
              ·
                refine ⟨610897443555129201506369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1629059849480344537350317 610897443555129201506369)
                ·
                  refine ⟨458173082666346901129777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610897443555129201506369 458173082666346901129777)
                  ·
                    rfl

theorem cell20_1003825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_1003825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003825 prefixEnd_1003825 := by exact prefixLift 1003825
  have htrace : WordTrace (prefixWord ++ tailWord_1003825) baseStart_1003825 baseEnd_1003825 := by
    simpa [prefixWord, tailWord_1003825, baseEnd_1003825] using wordTrace_append hprefix tailTrace_1003825
  have hstable : (prefixWord ++ tailWord_1003825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003825).length < 2 ^ (prefixWord ++ tailWord_1003825).sum := by decide
  have hdescent : baseEnd_1003825 < baseStart_1003825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003857 : List Nat := [1, 2, 2, 1, 4, 2, 1, 7]
def baseStart_1003857 : Nat := 118140960795 + 1003857 * 2 ^ 59
def prefixEnd_1003857 : Nat := 4983230072969 + 3 ^ 40 * 1003857 * 2
def baseEnd_1003857 : Nat := 152729229446099004020993

theorem tailTrace_1003857 : CollatzResearch.WordTrace tailWord_1003857 prefixEnd_1003857 152729229446099004020993 := by
  unfold tailWord_1003857
  simp only [CollatzResearch.WordTrace]
  refine ⟨36613672724205008971265825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24409115149470005980843883 36613672724205008971265825)
  ·
    refine ⟨27460254543153756728449369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36613672724205008971265825 27460254543153756728449369)
    ·
      refine ⟨20595190907365317546337027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27460254543153756728449369 20595190907365317546337027)
      ·
        refine ⟨30892786361047976319505541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20595190907365317546337027 30892786361047976319505541)
        ·
          refine ⟨5792397442696495559907289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30892786361047976319505541 5792397442696495559907289)
          ·
            refine ⟨4344298082022371669930467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5792397442696495559907289 4344298082022371669930467)
            ·
              refine ⟨6516447123033557504895701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344298082022371669930467 6516447123033557504895701)
              ·
                refine ⟨152729229446099004020993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6516447123033557504895701 152729229446099004020993)
                ·
                  rfl

theorem cell20_1003857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_1003857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003857 prefixEnd_1003857 := by exact prefixLift 1003857
  have htrace : WordTrace (prefixWord ++ tailWord_1003857) baseStart_1003857 baseEnd_1003857 := by
    simpa [prefixWord, tailWord_1003857, baseEnd_1003857] using wordTrace_append hprefix tailTrace_1003857
  have hstable : (prefixWord ++ tailWord_1003857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003857).length < 2 ^ (prefixWord ++ tailWord_1003857).sum := by decide
  have hdescent : baseEnd_1003857 < baseStart_1003857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003860 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1003860 : Nat := 118140960795 + 1003860 * 2 ^ 59
def prefixEnd_1003860 : Nat := 4983230072969 + 3 ^ 40 * 1003860 * 2
def baseEnd_1003860 : Nat := 458189057620042334962967

theorem tailTrace_1003860 : CollatzResearch.WordTrace tailWord_1003860 prefixEnd_1003860 458189057620042334962967 := by
  unfold tailWord_1003860
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306891071597070241812517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24409188095462760322416689 18306891071597070241812517)
  ·
    refine ⟨3432542075924450670339847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18306891071597070241812517 3432542075924450670339847)
    ·
      refine ⟨5148813113886676005509771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3432542075924450670339847 5148813113886676005509771)
      ·
        refine ⟨7723219670830014008264657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148813113886676005509771 7723219670830014008264657)
        ·
          refine ⟨5792414753122510506198493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7723219670830014008264657 5792414753122510506198493)
          ·
            refine ⟨2172155532420941439824435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5792414753122510506198493 2172155532420941439824435)
            ·
              refine ⟨3258233298631412159736653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172155532420941439824435 3258233298631412159736653)
              ·
                refine ⟨1221837486986779559901245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3258233298631412159736653 1221837486986779559901245)
                ·
                  refine ⟨458189057620042334962967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221837486986779559901245 458189057620042334962967)
                  ·
                    rfl

theorem cell20_1003860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1003860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003860 prefixEnd_1003860 := by exact prefixLift 1003860
  have htrace : WordTrace (prefixWord ++ tailWord_1003860) baseStart_1003860 baseEnd_1003860 := by
    simpa [prefixWord, tailWord_1003860, baseEnd_1003860] using wordTrace_append hprefix tailTrace_1003860
  have hstable : (prefixWord ++ tailWord_1003860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003860).length < 2 ^ (prefixWord ++ tailWord_1003860).sum := by decide
  have hdescent : baseEnd_1003860 < baseStart_1003860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003864 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_1003864 : Nat := 118140960795 + 1003864 * 2 ^ 59
def prefixEnd_1003864 : Nat := 4983230072969 + 3 ^ 40 * 1003864 * 2
def baseEnd_1003864 : Nat := 458190883329036098829617

theorem tailTrace_1003864 : CollatzResearch.WordTrace tailWord_1003864 prefixEnd_1003864 458190883329036098829617 := by
  unfold tailWord_1003864
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306964017589824583385323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24409285356786432777847097 18306964017589824583385323)
  ·
    refine ⟨27460446026384736875077985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18306964017589824583385323 27460446026384736875077985)
    ·
      refine ⟨20595334519788552656308489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27460446026384736875077985 20595334519788552656308489)
      ·
        refine ⟨15446500889841414492231367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20595334519788552656308489 15446500889841414492231367)
        ·
          refine ⟨23169751334762121738347051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15446500889841414492231367 23169751334762121738347051)
          ·
            refine ⟨34754627002143182607520577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23169751334762121738347051 34754627002143182607520577)
            ·
              refine ⟨26065970251607386955640433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34754627002143182607520577 26065970251607386955640433)
              ·
                refine ⟨19549477688705540216730325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26065970251607386955640433 19549477688705540216730325)
                ·
                  refine ⟨458190883329036098829617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19549477688705540216730325 458190883329036098829617)
                  ·
                    rfl

theorem cell20_1003864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_1003864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003864 prefixEnd_1003864 := by exact prefixLift 1003864
  have htrace : WordTrace (prefixWord ++ tailWord_1003864) baseStart_1003864 baseEnd_1003864 := by
    simpa [prefixWord, tailWord_1003864, baseEnd_1003864] using wordTrace_append hprefix tailTrace_1003864
  have hstable : (prefixWord ++ tailWord_1003864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003864).length < 2 ^ (prefixWord ++ tailWord_1003864).sum := by decide
  have hdescent : baseEnd_1003864 < baseStart_1003864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003874 : List Nat := [3, 3, 2, 1, 1, 2, 2, 6]
def baseStart_1003874 : Nat := 118140960795 + 1003874 * 2 ^ 59
def prefixEnd_1003874 : Nat := 4983230072969 + 3 ^ 40 * 1003874 * 2
def baseEnd_1003874 : Nat := 152731815867173502832081

theorem tailTrace_1003874 : CollatzResearch.WordTrace tailWord_1003874 prefixEnd_1003874 152731815867173502832081 := by
  unfold tailWord_1003874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153573191285855218658669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24409528510095613916423117 9153573191285855218658669)
  ·
    refine ⟨3432589946732195706997001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9153573191285855218658669 3432589946732195706997001)
    ·
      refine ⟨2574442460049146780247751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3432589946732195706997001 2574442460049146780247751)
      ·
        refine ⟨3861663690073720170371627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574442460049146780247751 3861663690073720170371627)
        ·
          refine ⟨5792495535110580255557441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861663690073720170371627 5792495535110580255557441)
          ·
            refine ⟨4344371651332935191668081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5792495535110580255557441 4344371651332935191668081)
            ·
              refine ⟨3258278738499701393751061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4344371651332935191668081 3258278738499701393751061)
              ·
                refine ⟨152731815867173502832081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3258278738499701393751061 152731815867173502832081)
                ·
                  rfl

theorem cell20_1003874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_1003874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003874 prefixEnd_1003874 := by exact prefixLift 1003874
  have htrace : WordTrace (prefixWord ++ tailWord_1003874) baseStart_1003874 baseEnd_1003874 := by
    simpa [prefixWord, tailWord_1003874, baseEnd_1003874] using wordTrace_append hprefix tailTrace_1003874
  have hstable : (prefixWord ++ tailWord_1003874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003874).length < 2 ^ (prefixWord ++ tailWord_1003874).sum := by decide
  have hdescent : baseEnd_1003874 < baseStart_1003874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003894 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1003894 : Nat := 118140960795 + 1003894 * 2 ^ 59
def prefixEnd_1003894 : Nat := 4983230072969 + 3 ^ 40 * 1003894 * 2
def baseEnd_1003894 : Nat := 458204576146489327829495

theorem tailTrace_1003894 : CollatzResearch.WordTrace tailWord_1003894 prefixEnd_1003894 458204576146489327829495 := by
  unfold tailWord_1003894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288438889066935268147671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24410014816713976193575157 2288438889066935268147671)
  ·
    refine ⟨3432658333600402902221507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2288438889066935268147671 3432658333600402902221507)
    ·
      refine ⟨5148987500400604353332261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3432658333600402902221507 5148987500400604353332261)
      ·
        refine ⟨965435156325113316249799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5148987500400604353332261 965435156325113316249799)
        ·
          refine ⟨1448152734487669974374699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965435156325113316249799 1448152734487669974374699)
          ·
            refine ⟨2172229101731504961562049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448152734487669974374699 2172229101731504961562049)
            ·
              refine ⟨1629171826298628721171537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172229101731504961562049 1629171826298628721171537)
              ·
                refine ⟨1221878869723971540878653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629171826298628721171537 1221878869723971540878653)
                ·
                  refine ⟨458204576146489327829495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221878869723971540878653 458204576146489327829495)
                  ·
                    rfl

theorem cell20_1003894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1003894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003894 prefixEnd_1003894 := by exact prefixLift 1003894
  have htrace : WordTrace (prefixWord ++ tailWord_1003894) baseStart_1003894 baseEnd_1003894 := by
    simpa [prefixWord, tailWord_1003894, baseEnd_1003894] using wordTrace_append hprefix tailTrace_1003894
  have hstable : (prefixWord ++ tailWord_1003894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003894).length < 2 ^ (prefixWord ++ tailWord_1003894).sum := by decide
  have hdescent : baseEnd_1003894 < baseStart_1003894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003901 : List Nat := [1, 4, 1, 1, 2, 5, 2, 2, 2]
def baseStart_1003901 : Nat := 118140960795 + 1003901 * 2 ^ 59
def prefixEnd_1003901 : Nat := 4983230072969 + 3 ^ 40 * 1003901 * 2
def baseEnd_1003901 : Nat := 458207771137228414596133

theorem tailTrace_1003901 : CollatzResearch.WordTrace tailWord_1003901 prefixEnd_1003901 458207771137228414596133 := by
  unfold tailWord_1003901
  simp only [CollatzResearch.WordTrace]
  refine ⟨36615277536045604485867557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24410185024030402990578371 36615277536045604485867557)
  ·
    refine ⟨6865364538008550841100167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36615277536045604485867557 6865364538008550841100167)
    ·
      refine ⟨10298046807012826261650251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6865364538008550841100167 10298046807012826261650251)
      ·
        refine ⟨15447070210519239392475377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10298046807012826261650251 15447070210519239392475377)
        ·
          refine ⟨11585302657889429544356533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15447070210519239392475377 11585302657889429544356533)
          ·
            refine ⟨1086122124177134019783425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11585302657889429544356533 1086122124177134019783425)
            ·
              refine ⟨814591593132850514837569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086122124177134019783425 814591593132850514837569)
              ·
                refine ⟨610943694849637886128177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814591593132850514837569 610943694849637886128177)
                ·
                  refine ⟨458207771137228414596133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610943694849637886128177 458207771137228414596133)
                  ·
                    rfl

theorem cell20_1003901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_1003901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003901 prefixEnd_1003901 := by exact prefixLift 1003901
  have htrace : WordTrace (prefixWord ++ tailWord_1003901) baseStart_1003901 baseEnd_1003901 := by
    simpa [prefixWord, tailWord_1003901, baseEnd_1003901] using wordTrace_append hprefix tailTrace_1003901
  have hstable : (prefixWord ++ tailWord_1003901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003901).length < 2 ^ (prefixWord ++ tailWord_1003901).sum := by decide
  have hdescent : baseEnd_1003901 < baseStart_1003901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003946 : List Nat := [3, 1, 6, 1, 1, 1, 7]
def baseStart_1003946 : Nat := 118140960795 + 1003946 * 2 ^ 59
def prefixEnd_1003946 : Nat := 4983230072969 + 3 ^ 40 * 1003946 * 2
def baseEnd_1003946 : Nat := 50914256707045362010661

theorem tailTrace_1003946 : CollatzResearch.WordTrace tailWord_1003946 prefixEnd_1003946 50914256707045362010661 := by
  unfold tailWord_1003946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9154229705220644292813923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24411279213921718114170461 9154229705220644292813923)
  ·
    refine ⟨13731344557830966439220885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9154229705220644292813923 13731344557830966439220885)
    ·
      refine ⟨643656776148326551838479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13731344557830966439220885 643656776148326551838479)
      ·
        refine ⟨965485164222489827757719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643656776148326551838479 965485164222489827757719)
        ·
          refine ⟨1448227746333734741636579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965485164222489827757719 1448227746333734741636579)
          ·
            refine ⟨2172341619500602112454869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448227746333734741636579 2172341619500602112454869)
            ·
              refine ⟨50914256707045362010661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2172341619500602112454869 50914256707045362010661)
              ·
                rfl

theorem cell20_1003946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 7].length) (baseStart_1003946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003946 prefixEnd_1003946 := by exact prefixLift 1003946
  have htrace : WordTrace (prefixWord ++ tailWord_1003946) baseStart_1003946 baseEnd_1003946 := by
    simpa [prefixWord, tailWord_1003946, baseEnd_1003946] using wordTrace_append hprefix tailTrace_1003946
  have hstable : (prefixWord ++ tailWord_1003946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003946).length < 2 ^ (prefixWord ++ tailWord_1003946).sum := by decide
  have hdescent : baseEnd_1003946 < baseStart_1003946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003988 : List Nat := [2, 4, 1, 2, 2, 2, 1, 6]
def baseStart_1003988 : Nat := 118140960795 + 1003988 * 2 ^ 59
def prefixEnd_1003988 : Nat := 4983230072969 + 3 ^ 40 * 1003988 * 2
def baseEnd_1003988 : Nat := 152749160102614259565259

theorem tailTrace_1003988 : CollatzResearch.WordTrace tailWord_1003988 prefixEnd_1003988 152749160102614259565259 := by
  unfold tailWord_1003988
  simp only [CollatzResearch.WordTrace]
  refine ⟨18309225343365209172142309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24412300457820278896189745 18309225343365209172142309)
  ·
    refine ⟨3432979751880976719776683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18309225343365209172142309 3432979751880976719776683)
    ·
      refine ⟨5149469627821465079665025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3432979751880976719776683 5149469627821465079665025)
      ·
        refine ⟨3862102220866098809748769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5149469627821465079665025 3862102220866098809748769)
        ·
          refine ⟨2896576665649574107311577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3862102220866098809748769 2896576665649574107311577)
          ·
            refine ⟨2172432499237180580483683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2896576665649574107311577 2172432499237180580483683)
            ·
              refine ⟨3258648748855770870725525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172432499237180580483683 3258648748855770870725525)
              ·
                refine ⟨152749160102614259565259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3258648748855770870725525 152749160102614259565259)
                ·
                  rfl

theorem cell20_1003988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_1003988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1003988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1003988 prefixEnd_1003988 := by exact prefixLift 1003988
  have htrace : WordTrace (prefixWord ++ tailWord_1003988) baseStart_1003988 baseEnd_1003988 := by
    simpa [prefixWord, tailWord_1003988, baseEnd_1003988] using wordTrace_append hprefix tailTrace_1003988
  have hstable : (prefixWord ++ tailWord_1003988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003988).length < 2 ^ (prefixWord ++ tailWord_1003988).sum := by decide
  have hdescent : baseEnd_1003988 < baseStart_1003988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004005 : List Nat := [1, 3, 1, 5, 3, 1, 6]
def baseStart_1004005 : Nat := 118140960795 + 1004005 * 2 ^ 59
def prefixEnd_1004005 : Nat := 4983230072969 + 3 ^ 40 * 1004005 * 2
def baseEnd_1004005 : Nat := 50917248841229586125449

theorem tailTrace_1004005 : CollatzResearch.WordTrace tailWord_1004005 prefixEnd_1004005 50917248841229586125449 := by
  unfold tailWord_1004005
  simp only [CollatzResearch.WordTrace]
  refine ⟨36619070727668830247653469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24412713818445886831768979 36619070727668830247653469)
  ·
    refine ⟨13732151522875811342870051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36619070727668830247653469 13732151522875811342870051)
    ·
      refine ⟨20598227284313717014305077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13732151522875811342870051 20598227284313717014305077)
      ·
        refine ⟨1931083807904410970091101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20598227284313717014305077 1931083807904410970091101)
        ·
          refine ⟨724156427964154113784163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1931083807904410970091101 724156427964154113784163)
          ·
            refine ⟨1086234641946231170676245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724156427964154113784163 1086234641946231170676245)
            ·
              refine ⟨50917248841229586125449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1086234641946231170676245 50917248841229586125449)
              ·
                rfl

theorem cell20_1004005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 6].length) (baseStart_1004005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004005 prefixEnd_1004005 := by exact prefixLift 1004005
  have htrace : WordTrace (prefixWord ++ tailWord_1004005) baseStart_1004005 baseEnd_1004005 := by
    simpa [prefixWord, tailWord_1004005, baseEnd_1004005] using wordTrace_append hprefix tailTrace_1004005
  have hstable : (prefixWord ++ tailWord_1004005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004005).length < 2 ^ (prefixWord ++ tailWord_1004005).sum := by decide
  have hdescent : baseEnd_1004005 < baseStart_1004005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004016 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_1004016 : Nat := 118140960795 + 1004016 * 2 ^ 59
def prefixEnd_1004016 : Nat := 4983230072969 + 3 ^ 40 * 1004016 * 2
def baseEnd_1004016 : Nat := 458260260270799125762329

theorem tailTrace_1004016 : CollatzResearch.WordTrace tailWord_1004016 prefixEnd_1004016 458260260270799125762329 := by
  unfold tailWord_1004016
  simp only [CollatzResearch.WordTrace]
  refine ⟨18309735965314489563151951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24412981287085986084202601 18309735965314489563151951)
  ·
    refine ⟨27464603947971734344727927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18309735965314489563151951 27464603947971734344727927)
    ·
      refine ⟨41196905921957601517091891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27464603947971734344727927 41196905921957601517091891)
      ·
        refine ⟨61795358882936402275637837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41196905921957601517091891 61795358882936402275637837)
        ·
          refine ⟨23173259581101150853364189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61795358882936402275637837 23173259581101150853364189)
          ·
            refine ⟨8689972342912931570011571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23173259581101150853364189 8689972342912931570011571)
            ·
              refine ⟨13034958514369397355017357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689972342912931570011571 13034958514369397355017357)
              ·
                refine ⟨4888109442888524008131509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13034958514369397355017357 4888109442888524008131509)
                ·
                  refine ⟨458260260270799125762329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4888109442888524008131509 458260260270799125762329)
                  ·
                    rfl

theorem cell20_1004016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_1004016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004016 prefixEnd_1004016 := by exact prefixLift 1004016
  have htrace : WordTrace (prefixWord ++ tailWord_1004016) baseStart_1004016 baseEnd_1004016 := by
    simpa [prefixWord, tailWord_1004016, baseEnd_1004016] using wordTrace_append hprefix tailTrace_1004016
  have hstable : (prefixWord ++ tailWord_1004016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004016).length < 2 ^ (prefixWord ++ tailWord_1004016).sum := by decide
  have hdescent : baseEnd_1004016 < baseStart_1004016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004064 : List Nat := [2, 1, 1, 6, 3, 7]
def baseStart_1004064 : Nat := 118140960795 + 1004064 * 2 ^ 59
def prefixEnd_1004064 : Nat := 4983230072969 + 3 ^ 40 * 1004064 * 2
def baseEnd_1004064 : Nat := 16973413658471270080079

theorem tailTrace_1004064 : CollatzResearch.WordTrace tailWord_1004064 prefixEnd_1004064 16973413658471270080079 := by
  unfold tailWord_1004064
  simp only [CollatzResearch.WordTrace]
  refine ⟨18310611317227541662025623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24414148422970055549367497 18310611317227541662025623)
  ·
    refine ⟨27465916975841312493038435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18310611317227541662025623 27465916975841312493038435)
    ·
      refine ⟨41198875463761968739557653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27465916975841312493038435 41198875463761968739557653)
      ·
        refine ⟨1931197287363842284666765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41198875463761968739557653 1931197287363842284666765)
        ·
          refine ⟨724198982761440856750037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1931197287363842284666765 724198982761440856750037)
          ·
            refine ⟨16973413658471270080079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 724198982761440856750037 16973413658471270080079)
            ·
              rfl

theorem cell20_1004064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 7].length) (baseStart_1004064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004064 prefixEnd_1004064 := by exact prefixLift 1004064
  have htrace : WordTrace (prefixWord ++ tailWord_1004064) baseStart_1004064 baseEnd_1004064 := by
    simpa [prefixWord, tailWord_1004064, baseEnd_1004064] using wordTrace_append hprefix tailTrace_1004064
  have hstable : (prefixWord ++ tailWord_1004064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004064).length < 2 ^ (prefixWord ++ tailWord_1004064).sum := by decide
  have hdescent : baseEnd_1004064 < baseStart_1004064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004074 : List Nat := [3, 1, 4, 1, 1, 3, 1, 4, 2]
def baseStart_1004074 : Nat := 118140960795 + 1004074 * 2 ^ 59
def prefixEnd_1004074 : Nat := 4983230072969 + 3 ^ 40 * 1004074 * 2
def baseEnd_1004074 : Nat := 458286733051208701828759

theorem tailTrace_1004074 : CollatzResearch.WordTrace tailWord_1004074 prefixEnd_1004074 458286733051208701828759 := by
  unfold tailWord_1004074
  simp only [CollatzResearch.WordTrace]
  refine ⟨9155396841104713757978819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24414391576279236687943517 9155396841104713757978819)
  ·
    refine ⟨13733095261657070636968229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9155396841104713757978819 13733095261657070636968229)
    ·
      refine ⟨2574955361560700744431543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13733095261657070636968229 2574955361560700744431543)
      ·
        refine ⟨3862433042341051116647315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574955361560700744431543 3862433042341051116647315)
        ·
          refine ⟨5793649563511576674970973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862433042341051116647315 5793649563511576674970973)
          ·
            refine ⟨2172618586316841253114115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5793649563511576674970973 2172618586316841253114115)
            ·
              refine ⟨3258927879475261879671173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172618586316841253114115 3258927879475261879671173)
              ·
                refine ⟨611048977401611602438345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3258927879475261879671173 611048977401611602438345)
                ·
                  refine ⟨458286733051208701828759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611048977401611602438345 458286733051208701828759)
                  ·
                    rfl

theorem cell20_1004074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_1004074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004074 prefixEnd_1004074 := by exact prefixLift 1004074
  have htrace : WordTrace (prefixWord ++ tailWord_1004074) baseStart_1004074 baseEnd_1004074 := by
    simpa [prefixWord, tailWord_1004074, baseEnd_1004074] using wordTrace_append hprefix tailTrace_1004074
  have hstable : (prefixWord ++ tailWord_1004074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004074).length < 2 ^ (prefixWord ++ tailWord_1004074).sum := by decide
  have hdescent : baseEnd_1004074 < baseStart_1004074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004077 : List Nat := [1, 5, 4, 1, 1, 2, 1, 5]
def baseStart_1004077 : Nat := 118140960795 + 1004077 * 2 ^ 59
def prefixEnd_1004077 : Nat := 4983230072969 + 3 ^ 40 * 1004077 * 2
def baseEnd_1004077 : Nat := 152762700777651341576249

theorem tailTrace_1004077 : CollatzResearch.WordTrace tailWord_1004077 prefixEnd_1004077 152762700777651341576249 := by
  unfold tailWord_1004077
  simp only [CollatzResearch.WordTrace]
  refine ⟨36621696783407986544274485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24414464522271991029516323 36621696783407986544274485)
  ·
    refine ⟨3433284073444498738525733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36621696783407986544274485 3433284073444498738525733)
    ·
      refine ⟨643740763770843513473575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3433284073444498738525733 643740763770843513473575)
      ·
        refine ⟨965611145656265270210363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643740763770843513473575 965611145656265270210363)
        ·
          refine ⟨1448416718484397905315545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965611145656265270210363 1448416718484397905315545)
          ·
            refine ⟨1086312538863298428986659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448416718484397905315545 1086312538863298428986659)
            ·
              refine ⟨1629468808294947643479989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086312538863298428986659 1629468808294947643479989)
              ·
                refine ⟨152762700777651341576249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1629468808294947643479989 152762700777651341576249)
                ·
                  rfl

theorem cell20_1004077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 5].length) (baseStart_1004077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004077 prefixEnd_1004077 := by exact prefixLift 1004077
  have htrace : WordTrace (prefixWord ++ tailWord_1004077) baseStart_1004077 baseEnd_1004077 := by
    simpa [prefixWord, tailWord_1004077, baseEnd_1004077] using wordTrace_append hprefix tailTrace_1004077
  have hstable : (prefixWord ++ tailWord_1004077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004077).length < 2 ^ (prefixWord ++ tailWord_1004077).sum := by decide
  have hdescent : baseEnd_1004077 < baseStart_1004077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004133 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 4]
def baseStart_1004133 : Nat := 118140960795 + 1004133 * 2 ^ 59
def prefixEnd_1004133 : Nat := 4983230072969 + 3 ^ 40 * 1004133 * 2
def baseEnd_1004133 : Nat := 458313662258866718861851

theorem tailTrace_1004133 : CollatzResearch.WordTrace tailWord_1004133 prefixEnd_1004133 458313662258866718861851 := by
  unfold tailWord_1004133
  simp only [CollatzResearch.WordTrace]
  refine ⟨36623739271205108108313053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24415826180803405405542035 36623739271205108108313053)
  ·
    refine ⟨13733902226701915540617395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36623739271205108108313053 13733902226701915540617395)
    ·
      refine ⟨20600853340052873310926093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13733902226701915540617395 20600853340052873310926093)
      ·
        refine ⟨7725320002519827491597285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20600853340052873310926093 7725320002519827491597285)
        ·
          refine ⟨1448497500472467654674491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7725320002519827491597285 1448497500472467654674491)
          ·
            refine ⟨2172746250708701482011737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448497500472467654674491 2172746250708701482011737)
            ·
              refine ⟨1629559688031526111508803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172746250708701482011737 1629559688031526111508803)
              ·
                refine ⟨2444339532047289167263205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629559688031526111508803 2444339532047289167263205)
                ·
                  refine ⟨458313662258866718861851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2444339532047289167263205 458313662258866718861851)
                  ·
                    rfl

theorem cell20_1004133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_1004133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004133 prefixEnd_1004133 := by exact prefixLift 1004133
  have htrace : WordTrace (prefixWord ++ tailWord_1004133) baseStart_1004133 baseEnd_1004133 := by
    simpa [prefixWord, tailWord_1004133, baseEnd_1004133] using wordTrace_append hprefix tailTrace_1004133
  have hstable : (prefixWord ++ tailWord_1004133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004133).length < 2 ^ (prefixWord ++ tailWord_1004133).sum := by decide
  have hdescent : baseEnd_1004133 < baseStart_1004133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004157 : List Nat := [1, 4, 1, 1, 5, 2, 2, 4]
def baseStart_1004157 : Nat := 118140960795 + 1004157 * 2 ^ 59
def prefixEnd_1004157 : Nat := 4983230072969 + 3 ^ 40 * 1004157 * 2
def baseEnd_1004157 : Nat := 152774872170943100687251

theorem tailTrace_1004157 : CollatzResearch.WordTrace tailWord_1004157 prefixEnd_1004157 152774872170943100687251 := by
  unfold tailWord_1004157
  simp only [CollatzResearch.WordTrace]
  refine ⟨36624614623118160207186725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24416409748745440138124483 36624614623118160207186725)
  ·
    refine ⟨6867115241834655038847511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36624614623118160207186725 6867115241834655038847511)
    ·
      refine ⟨10300672862751982558271267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6867115241834655038847511 10300672862751982558271267)
      ·
        refine ⟨15451009294127973837406901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10300672862751982558271267 15451009294127973837406901)
        ·
          refine ⟨1448532121324497547256897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15451009294127973837406901 1448532121324497547256897)
          ·
            refine ⟨1086399090993373160442673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448532121324497547256897 1086399090993373160442673)
            ·
              refine ⟨814799318245029870332005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086399090993373160442673 814799318245029870332005)
              ·
                refine ⟨152774872170943100687251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 814799318245029870332005 152774872170943100687251)
                ·
                  rfl

theorem cell20_1004157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 4].length) (baseStart_1004157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004157 prefixEnd_1004157 := by exact prefixLift 1004157
  have htrace : WordTrace (prefixWord ++ tailWord_1004157) baseStart_1004157 baseEnd_1004157 := by
    simpa [prefixWord, tailWord_1004157, baseEnd_1004157] using wordTrace_append hprefix tailTrace_1004157
  have hstable : (prefixWord ++ tailWord_1004157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004157).length < 2 ^ (prefixWord ++ tailWord_1004157).sum := by decide
  have hdescent : baseEnd_1004157 < baseStart_1004157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004161 : List Nat := [1, 2, 4, 2, 1, 1, 3, 6]
def baseStart_1004161 : Nat := 118140960795 + 1004161 * 2 ^ 59
def prefixEnd_1004161 : Nat := 4983230072969 + 3 ^ 40 * 1004161 * 2
def baseEnd_1004161 : Nat := 152775480740607688642801

theorem tailTrace_1004161 : CollatzResearch.WordTrace tailWord_1004161 prefixEnd_1004161 152775480740607688642801 := by
  unfold tailWord_1004161
  simp only [CollatzResearch.WordTrace]
  refine ⟨36624760515103668890332337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24416507010069112593554891 36624760515103668890332337)
  ·
    refine ⟨27468570386327751667749253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36624760515103668890332337 27468570386327751667749253)
    ·
      refine ⟨5150356947436453437702985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27468570386327751667749253 5150356947436453437702985)
      ·
        refine ⟨3862767710577340078277239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5150356947436453437702985 3862767710577340078277239)
        ·
          refine ⟨5794151565866010117415859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862767710577340078277239 5794151565866010117415859)
          ·
            refine ⟨8691227348799015176123789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794151565866010117415859 8691227348799015176123789)
            ·
              refine ⟨3259210255799630691046421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8691227348799015176123789 3259210255799630691046421)
              ·
                refine ⟨152775480740607688642801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3259210255799630691046421 152775480740607688642801)
                ·
                  rfl

theorem cell20_1004161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_1004161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004161 prefixEnd_1004161 := by exact prefixLift 1004161
  have htrace : WordTrace (prefixWord ++ tailWord_1004161) baseStart_1004161 baseEnd_1004161 := by
    simpa [prefixWord, tailWord_1004161, baseEnd_1004161] using wordTrace_append hprefix tailTrace_1004161
  have hstable : (prefixWord ++ tailWord_1004161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004161).length < 2 ^ (prefixWord ++ tailWord_1004161).sum := by decide
  have hdescent : baseEnd_1004161 < baseStart_1004161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004178 : List Nat := [3, 2, 3, 1, 2, 3, 6]
def baseStart_1004178 : Nat := 118140960795 + 1004178 * 2 ^ 59
def prefixEnd_1004178 : Nat := 4983230072969 + 3 ^ 40 * 1004178 * 2
def baseEnd_1004178 : Nat := 50926022387227395817963

theorem tailTrace_1004178 : CollatzResearch.WordTrace tailWord_1004178 prefixEnd_1004178 50926022387227395817963 := by
  unfold tailWord_1004178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9156345139010520198425297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24416920370694720529134125 9156345139010520198425297)
  ·
    refine ⟨6867258854257890148818973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9156345139010520198425297 6867258854257890148818973)
    ·
      refine ⟨2575222070346708805807115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6867258854257890148818973 2575222070346708805807115)
      ·
        refine ⟨3862833105520063208710673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575222070346708805807115 3862833105520063208710673)
        ·
          refine ⟨2897124829140047406533005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3862833105520063208710673 2897124829140047406533005)
          ·
            refine ⟨1086421810927517777449877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2897124829140047406533005 1086421810927517777449877)
            ·
              refine ⟨50926022387227395817963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1086421810927517777449877 50926022387227395817963)
              ·
                rfl

theorem cell20_1004178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 6].length) (baseStart_1004178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004178 prefixEnd_1004178 := by exact prefixLift 1004178
  have htrace : WordTrace (prefixWord ++ tailWord_1004178) baseStart_1004178 baseEnd_1004178 := by
    simpa [prefixWord, tailWord_1004178, baseEnd_1004178] using wordTrace_append hprefix tailTrace_1004178
  have hstable : (prefixWord ++ tailWord_1004178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004178).length < 2 ^ (prefixWord ++ tailWord_1004178).sum := by decide
  have hdescent : baseEnd_1004178 < baseStart_1004178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004247 : List Nat := [1, 1, 3, 2, 1, 5, 1, 4, 2]
def baseStart_1004247 : Nat := 118140960795 + 1004247 * 2 ^ 59
def prefixEnd_1004247 : Nat := 4983230072969 + 3 ^ 40 * 1004247 * 2
def baseEnd_1004247 : Nat := 458365694965188989061385

theorem tailTrace_1004247 : CollatzResearch.WordTrace tailWord_1004247 prefixEnd_1004247 458365694965188989061385 := by
  unfold tailWord_1004247
  simp only [CollatzResearch.WordTrace]
  refine ⟨36627897192792105577962995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24418598128528070385308663 36627897192792105577962995)
  ·
    refine ⟨54941845789188158366944493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36627897192792105577962995 54941845789188158366944493)
    ·
      refine ⟨20603192170945559387604185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54941845789188158366944493 20603192170945559387604185)
      ·
        refine ⟨15452394128209169540703139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20603192170945559387604185 15452394128209169540703139)
        ·
          refine ⟨23178591192313754311054709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15452394128209169540703139 23178591192313754311054709)
          ·
            refine ⟨2172992924279414466661379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23178591192313754311054709 2172992924279414466661379)
            ·
              refine ⟨3259489386419121699992069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172992924279414466661379 3259489386419121699992069)
              ·
                refine ⟨611154259953585318748513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3259489386419121699992069 611154259953585318748513)
                ·
                  refine ⟨458365694965188989061385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611154259953585318748513 458365694965188989061385)
                  ·
                    rfl

theorem cell20_1004247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 2].length) (baseStart_1004247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004247 prefixEnd_1004247 := by exact prefixLift 1004247
  have htrace : WordTrace (prefixWord ++ tailWord_1004247) baseStart_1004247 baseEnd_1004247 := by
    simpa [prefixWord, tailWord_1004247, baseEnd_1004247] using wordTrace_append hprefix tailTrace_1004247
  have hstable : (prefixWord ++ tailWord_1004247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004247).length < 2 ^ (prefixWord ++ tailWord_1004247).sum := by decide
  have hdescent : baseEnd_1004247 < baseStart_1004247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004261 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 3]
def baseStart_1004261 : Nat := 118140960795 + 1004261 * 2 ^ 59
def prefixEnd_1004261 : Nat := 4983230072969 + 3 ^ 40 * 1004261 * 2
def baseEnd_1004261 : Nat := 458372084946667162594661

theorem tailTrace_1004261 : CollatzResearch.WordTrace tailWord_1004261 prefixEnd_1004261 458372084946667162594661 := by
  unfold tailWord_1004261
  simp only [CollatzResearch.WordTrace]
  refine ⟨36628407814741385968972637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24418938543160923979315091 36628407814741385968972637)
  ·
    refine ⟨13735652930528019738364739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36628407814741385968972637 13735652930528019738364739)
    ·
      refine ⟨20603479395792029607547109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13735652930528019738364739 20603479395792029607547109)
      ·
        refine ⟨3863152386711005551415083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20603479395792029607547109 3863152386711005551415083)
        ·
          refine ⟨5794728580066508327122625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863152386711005551415083 5794728580066508327122625)
          ·
            refine ⟨4346046435049881245341969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5794728580066508327122625 4346046435049881245341969)
            ·
              refine ⟨3259534826287410934006477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4346046435049881245341969 3259534826287410934006477)
              ·
                refine ⟨1222325559857779100252429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3259534826287410934006477 1222325559857779100252429)
                ·
                  refine ⟨458372084946667162594661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222325559857779100252429 458372084946667162594661)
                  ·
                    rfl

theorem cell20_1004261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_1004261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004261 prefixEnd_1004261 := by exact prefixLift 1004261
  have htrace : WordTrace (prefixWord ++ tailWord_1004261) baseStart_1004261 baseEnd_1004261 := by
    simpa [prefixWord, tailWord_1004261, baseEnd_1004261] using wordTrace_append hprefix tailTrace_1004261
  have hstable : (prefixWord ++ tailWord_1004261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004261).length < 2 ^ (prefixWord ++ tailWord_1004261).sum := by decide
  have hdescent : baseEnd_1004261 < baseStart_1004261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004285 : List Nat := [1, 4, 1, 1, 1, 1, 6, 3, 2]
def baseStart_1004285 : Nat := 118140960795 + 1004285 * 2 ^ 59
def prefixEnd_1004285 : Nat := 4983230072969 + 3 ^ 40 * 1004285 * 2
def baseEnd_1004285 : Nat := 458383039200629745794563

theorem tailTrace_1004285 : CollatzResearch.WordTrace tailWord_1004285 prefixEnd_1004285 458383039200629745794563 := by
  unfold tailWord_1004285
  simp only [CollatzResearch.WordTrace]
  refine ⟨36629283166654438067846309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24419522111102958711897539 36629283166654438067846309)
  ·
    refine ⟨6867990593747707137721183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36629283166654438067846309 6867990593747707137721183)
    ·
      refine ⟨10301985890621560706581775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6867990593747707137721183 10301985890621560706581775)
      ·
        refine ⟨15452978835932341059872663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10301985890621560706581775 15452978835932341059872663)
        ·
          refine ⟨23179468253898511589808995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15452978835932341059872663 23179468253898511589808995)
          ·
            refine ⟨34769202380847767384713493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23179468253898511589808995 34769202380847767384713493)
            ·
              refine ⟨1629806361602239096158445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34769202380847767384713493 1629806361602239096158445)
              ·
                refine ⟨611177385600839661059417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1629806361602239096158445 611177385600839661059417)
                ·
                  refine ⟨458383039200629745794563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611177385600839661059417 458383039200629745794563)
                  ·
                    rfl

theorem cell20_1004285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_1004285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004285 prefixEnd_1004285 := by exact prefixLift 1004285
  have htrace : WordTrace (prefixWord ++ tailWord_1004285) baseStart_1004285 baseEnd_1004285 := by
    simpa [prefixWord, tailWord_1004285, baseEnd_1004285] using wordTrace_append hprefix tailTrace_1004285
  have hstable : (prefixWord ++ tailWord_1004285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004285).length < 2 ^ (prefixWord ++ tailWord_1004285).sum := by decide
  have hdescent : baseEnd_1004285 < baseStart_1004285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004289 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_1004289 : Nat := 118140960795 + 1004289 * 2 ^ 59
def prefixEnd_1004289 : Nat := 4983230072969 + 3 ^ 40 * 1004289 * 2
def baseEnd_1004289 : Nat := 458384864909623509661213

theorem tailTrace_1004289 : CollatzResearch.WordTrace tailWord_1004289 prefixEnd_1004289 458384864909623509661213 := by
  unfold tailWord_1004289
  simp only [CollatzResearch.WordTrace]
  refine ⟨36629429058639946750991921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24419619372426631167327947 36629429058639946750991921)
  ·
    refine ⟨27472071793979960063243941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36629429058639946750991921 27472071793979960063243941)
    ·
      refine ⟨5151013461371242511858239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27472071793979960063243941 5151013461371242511858239)
      ·
        refine ⟨7726520192056863767787359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151013461371242511858239 7726520192056863767787359)
        ·
          refine ⟨11589780288085295651681039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7726520192056863767787359 11589780288085295651681039)
          ·
            refine ⟨17384670432127943477521559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11589780288085295651681039 17384670432127943477521559)
            ·
              refine ⟨26077005648191915216282339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17384670432127943477521559 26077005648191915216282339)
              ·
                refine ⟨39115508472287872824423509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26077005648191915216282339 39115508472287872824423509)
                ·
                  refine ⟨458384864909623509661213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39115508472287872824423509 458384864909623509661213)
                  ·
                    rfl

theorem cell20_1004289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_1004289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004289 prefixEnd_1004289 := by exact prefixLift 1004289
  have htrace : WordTrace (prefixWord ++ tailWord_1004289) baseStart_1004289 baseEnd_1004289 := by
    simpa [prefixWord, tailWord_1004289, baseEnd_1004289] using wordTrace_append hprefix tailTrace_1004289
  have hstable : (prefixWord ++ tailWord_1004289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004289).length < 2 ^ (prefixWord ++ tailWord_1004289).sum := by decide
  have hdescent : baseEnd_1004289 < baseStart_1004289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004316 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 3]
def baseStart_1004316 : Nat := 118140960795 + 1004316 * 2 ^ 59
def prefixEnd_1004316 : Nat := 4983230072969 + 3 ^ 40 * 1004316 * 2
def baseEnd_1004316 : Nat := 458397188445331415761103

theorem tailTrace_1004316 : CollatzResearch.WordTrace tailWord_1004316 prefixEnd_1004316 458397188445331415761103 := by
  unfold tailWord_1004316
  simp only [CollatzResearch.WordTrace]
  refine ⟨18315206914771065181112401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24420275886361420241483201 18315206914771065181112401)
  ·
    refine ⟨13736405186078298885834301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18315206914771065181112401 13736405186078298885834301)
    ·
      refine ⟨5151151944779362082187863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13736405186078298885834301 5151151944779362082187863)
      ·
        refine ⟨7726727917169043123281795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151151944779362082187863 7726727917169043123281795)
        ·
          refine ⟨11590091875753564684922693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7726727917169043123281795 11590091875753564684922693)
          ·
            refine ⟨2173142226703793378423005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11590091875753564684922693 2173142226703793378423005)
            ·
              refine ⟨814928335013922516908627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2173142226703793378423005 814928335013922516908627)
              ·
                refine ⟨1222392502520883775362941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814928335013922516908627 1222392502520883775362941)
                ·
                  refine ⟨458397188445331415761103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222392502520883775362941 458397188445331415761103)
                  ·
                    rfl

theorem cell20_1004316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_1004316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004316 prefixEnd_1004316 := by exact prefixLift 1004316
  have htrace : WordTrace (prefixWord ++ tailWord_1004316) baseStart_1004316 baseEnd_1004316 := by
    simpa [prefixWord, tailWord_1004316, baseEnd_1004316] using wordTrace_append hprefix tailTrace_1004316
  have hstable : (prefixWord ++ tailWord_1004316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004316).length < 2 ^ (prefixWord ++ tailWord_1004316).sum := by decide
  have hdescent : baseEnd_1004316 < baseStart_1004316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004351 : List Nat := [1, 1, 2, 2, 5, 3, 6]
def baseStart_1004351 : Nat := 118140960795 + 1004351 * 2 ^ 59
def prefixEnd_1004351 : Nat := 4983230072969 + 3 ^ 40 * 1004351 * 2
def baseEnd_1004351 : Nat := 50934795933225205510477

theorem tailTrace_1004351 : CollatzResearch.WordTrace tailWord_1004351 prefixEnd_1004351 50934795933225205510477 := by
  unfold tailWord_1004351
  simp only [CollatzResearch.WordTrace]
  refine ⟨36631690384415331339748907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24421126922943554226499271 36631690384415331339748907)
  ·
    refine ⟨54947535576622997009623361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36631690384415331339748907 54947535576622997009623361)
    ·
      refine ⟨41210651682467247757217521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54947535576622997009623361 41210651682467247757217521)
      ·
        refine ⟨30907988761850435817913141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41210651682467247757217521 30907988761850435817913141)
        ·
          refine ⟨2897623946423478357929357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30907988761850435817913141 2897623946423478357929357)
          ·
            refine ⟨1086608979908804384223509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2897623946423478357929357 1086608979908804384223509)
            ·
              refine ⟨50934795933225205510477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1086608979908804384223509 50934795933225205510477)
              ·
                rfl

theorem cell20_1004351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 6].length) (baseStart_1004351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004351 prefixEnd_1004351 := by exact prefixLift 1004351
  have htrace : WordTrace (prefixWord ++ tailWord_1004351) baseStart_1004351 baseEnd_1004351 := by
    simpa [prefixWord, tailWord_1004351, baseEnd_1004351] using wordTrace_append hprefix tailTrace_1004351
  have hstable : (prefixWord ++ tailWord_1004351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004351).length < 2 ^ (prefixWord ++ tailWord_1004351).sum := by decide
  have hdescent : baseEnd_1004351 < baseStart_1004351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004375 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 3]
def baseStart_1004375 : Nat := 118140960795 + 1004375 * 2 ^ 59
def prefixEnd_1004375 : Nat := 4983230072969 + 3 ^ 40 * 1004375 * 2
def baseEnd_1004375 : Nat := 458424117652989432794195

theorem tailTrace_1004375 : CollatzResearch.WordTrace tailWord_1004375 prefixEnd_1004375 458424117652989432794195 := by
  unfold tailWord_1004375
  simp only [CollatzResearch.WordTrace]
  refine ⟨36632565736328383438622579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24421710490885588959081719 36632565736328383438622579)
  ·
    refine ⟨54948848604492575157933869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36632565736328383438622579 54948848604492575157933869)
    ·
      refine ⟨20605818226684715684225201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54948848604492575157933869 20605818226684715684225201)
      ·
        refine ⟨15454363670013536763168901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20605818226684715684225201 15454363670013536763168901)
        ·
          refine ⟨2897693188127538143094169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15454363670013536763168901 2897693188127538143094169)
          ·
            refine ⟨2173269891095653607320627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2897693188127538143094169 2173269891095653607320627)
            ·
              refine ⟨3259904836643480410980941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173269891095653607320627 3259904836643480410980941)
              ·
                refine ⟨1222464313741305154117853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3259904836643480410980941 1222464313741305154117853)
                ·
                  refine ⟨458424117652989432794195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222464313741305154117853 458424117652989432794195)
                  ·
                    rfl

theorem cell20_1004375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 3].length) (baseStart_1004375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004375 prefixEnd_1004375 := by exact prefixLift 1004375
  have htrace : WordTrace (prefixWord ++ tailWord_1004375) baseStart_1004375 baseEnd_1004375 := by
    simpa [prefixWord, tailWord_1004375, baseEnd_1004375] using wordTrace_append hprefix tailTrace_1004375
  have hstable : (prefixWord ++ tailWord_1004375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004375).length < 2 ^ (prefixWord ++ tailWord_1004375).sum := by decide
  have hdescent : baseEnd_1004375 < baseStart_1004375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004448 : List Nat := [2, 1, 1, 4, 1, 1, 2, 8]
def baseStart_1004448 : Nat := 118140960795 + 1004448 * 2 ^ 59
def prefixEnd_1004448 : Nat := 4983230072969 + 3 ^ 40 * 1004448 * 2
def baseEnd_1004448 : Nat := 152819145614041874453521

theorem tailTrace_1004448 : CollatzResearch.WordTrace tailWord_1004448 prefixEnd_1004448 152819145614041874453521 := by
  unfold tailWord_1004448
  simp only [CollatzResearch.WordTrace]
  refine ⟨18317614132531958453014999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24423485510042611270686665 18317614132531958453014999)
  ·
    refine ⟨27476421198797937679522499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18317614132531958453014999 27476421198797937679522499)
    ·
      refine ⟨41214631798196906519283749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27476421198797937679522499 41214631798196906519283749)
      ·
        refine ⟨7727743462161919972365703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41214631798196906519283749 7727743462161919972365703)
        ·
          refine ⟨11591615193242879958548555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7727743462161919972365703 11591615193242879958548555)
          ·
            refine ⟨17387422789864319937822833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591615193242879958548555 17387422789864319937822833)
            ·
              refine ⟨13040567092398239953367125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17387422789864319937822833 13040567092398239953367125)
              ·
                refine ⟨152819145614041874453521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13040567092398239953367125 152819145614041874453521)
                ·
                  rfl

theorem cell20_1004448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_1004448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004448 prefixEnd_1004448 := by exact prefixLift 1004448
  have htrace : WordTrace (prefixWord ++ tailWord_1004448) baseStart_1004448 baseEnd_1004448 := by
    simpa [prefixWord, tailWord_1004448, baseEnd_1004448] using wordTrace_append hprefix tailTrace_1004448
  have hstable : (prefixWord ++ tailWord_1004448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004448).length < 2 ^ (prefixWord ++ tailWord_1004448).sum := by decide
  have hdescent : baseEnd_1004448 < baseStart_1004448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004465 : List Nat := [1, 2, 2, 4, 3, 1, 7]
def baseStart_1004465 : Nat := 118140960795 + 1004465 * 2 ^ 59
def prefixEnd_1004465 : Nat := 4983230072969 + 3 ^ 40 * 1004465 * 2
def baseEnd_1004465 : Nat := 50940577345038791088203

theorem tailTrace_1004465 : CollatzResearch.WordTrace tailWord_1004465 prefixEnd_1004465 50940577345038791088203 := by
  unfold tailWord_1004465
  simp only [CollatzResearch.WordTrace]
  refine ⟨36635848306002328809398849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24423898870668219206265899 36635848306002328809398849)
  ·
    refine ⟨27476886229501746607049137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36635848306002328809398849 27476886229501746607049137)
    ·
      refine ⟨20607664672126309955286853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27476886229501746607049137 20607664672126309955286853)
      ·
        refine ⟨3863937126023683116616285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20607664672126309955286853 3863937126023683116616285)
        ·
          refine ⟨1448976422258881168731107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3863937126023683116616285 1448976422258881168731107)
          ·
            refine ⟨2173464633388321753096661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448976422258881168731107 2173464633388321753096661)
            ·
              refine ⟨50940577345038791088203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2173464633388321753096661 50940577345038791088203)
              ·
                rfl

theorem cell20_1004465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 7].length) (baseStart_1004465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004465 prefixEnd_1004465 := by exact prefixLift 1004465
  have htrace : WordTrace (prefixWord ++ tailWord_1004465) baseStart_1004465 baseEnd_1004465 := by
    simpa [prefixWord, tailWord_1004465, baseEnd_1004465] using wordTrace_append hprefix tailTrace_1004465
  have hstable : (prefixWord ++ tailWord_1004465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004465).length < 2 ^ (prefixWord ++ tailWord_1004465).sum := by decide
  have hdescent : baseEnd_1004465 < baseStart_1004465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004468 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1004468 : Nat := 118140960795 + 1004468 * 2 ^ 59
def prefixEnd_1004468 : Nat := 4983230072969 + 3 ^ 40 * 1004468 * 2
def baseEnd_1004468 : Nat := 458466565387094442693815

theorem tailTrace_1004468 : CollatzResearch.WordTrace tailWord_1004468 prefixEnd_1004468 458466565387094442693815 := by
  unfold tailWord_1004468
  simp only [CollatzResearch.WordTrace]
  refine ⟨18317978862495730160879029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24423971816660973547838705 18317978862495730160879029)
  ·
    refine ⟨1717310518358974702582409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18317978862495730160879029 1717310518358974702582409)
    ·
      refine ⟨1287982888769231026936807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1717310518358974702582409 1287982888769231026936807)
      ·
        refine ⟨1931974333153846540405211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287982888769231026936807 1931974333153846540405211)
        ·
          refine ⟨2897961499730769810607817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931974333153846540405211 2897961499730769810607817)
          ·
            refine ⟨2173471124798077357955863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2897961499730769810607817 2173471124798077357955863)
            ·
              refine ⟨3260206687197116036933795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173471124798077357955863 3260206687197116036933795)
              ·
                refine ⟨4890310030795674055400693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3260206687197116036933795 4890310030795674055400693)
                ·
                  refine ⟨458466565387094442693815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4890310030795674055400693 458466565387094442693815)
                  ·
                    rfl

theorem cell20_1004468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1004468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004468 prefixEnd_1004468 := by exact prefixLift 1004468
  have htrace : WordTrace (prefixWord ++ tailWord_1004468) baseStart_1004468 baseEnd_1004468 := by
    simpa [prefixWord, tailWord_1004468, baseEnd_1004468] using wordTrace_append hprefix tailTrace_1004468
  have hstable : (prefixWord ++ tailWord_1004468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004468).length < 2 ^ (prefixWord ++ tailWord_1004468).sum := by decide
  have hdescent : baseEnd_1004468 < baseStart_1004468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004472 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_1004472 : Nat := 118140960795 + 1004472 * 2 ^ 59
def prefixEnd_1004472 : Nat := 4983230072969 + 3 ^ 40 * 1004472 * 2
def baseEnd_1004472 : Nat := 458468391096088206560465

theorem tailTrace_1004472 : CollatzResearch.WordTrace tailWord_1004472 prefixEnd_1004472 458468391096088206560465 := by
  unfold tailWord_1004472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318051808488484502451835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24424069077984646003269113 18318051808488484502451835)
  ·
    refine ⟨27477077712732726753677753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18318051808488484502451835 27477077712732726753677753)
    ·
      refine ⟨20607808284549545065258315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27477077712732726753677753 20607808284549545065258315)
      ·
        refine ⟨30911712426824317597887473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20607808284549545065258315 30911712426824317597887473)
        ·
          refine ⟨23183784320118238198415605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30911712426824317597887473 23183784320118238198415605)
          ·
            refine ⟨2173479780011084831101463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23183784320118238198415605 2173479780011084831101463)
            ·
              refine ⟨3260219670016627246652195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173479780011084831101463 3260219670016627246652195)
              ·
                refine ⟨4890329505024940869978293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3260219670016627246652195 4890329505024940869978293)
                ·
                  refine ⟨458468391096088206560465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4890329505024940869978293 458468391096088206560465)
                  ·
                    rfl

theorem cell20_1004472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_1004472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004472 prefixEnd_1004472 := by exact prefixLift 1004472
  have htrace : WordTrace (prefixWord ++ tailWord_1004472) baseStart_1004472 baseEnd_1004472 := by
    simpa [prefixWord, tailWord_1004472, baseEnd_1004472] using wordTrace_append hprefix tailTrace_1004472
  have hstable : (prefixWord ++ tailWord_1004472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004472).length < 2 ^ (prefixWord ++ tailWord_1004472).sum := by decide
  have hdescent : baseEnd_1004472 < baseStart_1004472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004530 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_1004530 : Nat := 118140960795 + 1004530 * 2 ^ 59
def prefixEnd_1004530 : Nat := 4983230072969 + 3 ^ 40 * 1004530 * 2
def baseEnd_1004530 : Nat := 458494863876497782626895

theorem tailTrace_1004530 : CollatzResearch.WordTrace tailWord_1004530 prefixEnd_1004530 458494863876497782626895 := by
  unfold tailWord_1004530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9159554762691711227628761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24425479367177896607010029 9159554762691711227628761)
  ·
    refine ⟨6869666072018783420721571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9159554762691711227628761 6869666072018783420721571)
    ·
      refine ⟨10304499108028175131082357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6869666072018783420721571 10304499108028175131082357)
      ·
        refine ⟨966046791377641418538971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10304499108028175131082357 966046791377641418538971)
        ·
          refine ⟨1449070187066462127808457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966046791377641418538971 1449070187066462127808457)
          ·
            refine ⟨1086802640299846595856343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449070187066462127808457 1086802640299846595856343)
            ·
              refine ⟨1630203960449769893784515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086802640299846595856343 1630203960449769893784515)
              ·
                refine ⟨2445305940674654840676773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630203960449769893784515 2445305940674654840676773)
                ·
                  refine ⟨458494863876497782626895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445305940674654840676773 458494863876497782626895)
                  ·
                    rfl

theorem cell20_1004530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_1004530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004530 prefixEnd_1004530 := by exact prefixLift 1004530
  have htrace : WordTrace (prefixWord ++ tailWord_1004530) baseStart_1004530 baseEnd_1004530 := by
    simpa [prefixWord, tailWord_1004530, baseEnd_1004530] using wordTrace_append hprefix tailTrace_1004530
  have hstable : (prefixWord ++ tailWord_1004530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004530).length < 2 ^ (prefixWord ++ tailWord_1004530).sum := by decide
  have hdescent : baseEnd_1004530 < baseStart_1004530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004569 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_1004569 : Nat := 118140960795 + 1004569 * 2 ^ 59
def prefixEnd_1004569 : Nat := 4983230072969 + 3 ^ 40 * 1004569 * 2
def baseEnd_1004569 : Nat := 458512664539186980326735

theorem tailTrace_1004569 : CollatzResearch.WordTrace tailWord_1004569 prefixEnd_1004569 458512664539186980326735 := by
  unfold tailWord_1004569
  simp only [CollatzResearch.WordTrace]
  refine ⟨36639641497625554571184761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24426427665083703047456507 36639641497625554571184761)
  ·
    refine ⟨27479731123219165928388571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36639641497625554571184761 27479731123219165928388571)
    ·
      refine ⟨41219596684828748892582857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27479731123219165928388571 41219596684828748892582857)
      ·
        refine ⟨30914697513621561669437143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41219596684828748892582857 30914697513621561669437143)
        ·
          refine ⟨46372046270432342504155715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30914697513621561669437143 46372046270432342504155715)
          ·
            refine ⟨69558069405648513756233573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46372046270432342504155715 69558069405648513756233573)
            ·
              refine ⟨13042138013559096329293795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69558069405648513756233573 13042138013559096329293795)
              ·
                refine ⟨19563207020338644493940693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13042138013559096329293795 19563207020338644493940693)
                ·
                  refine ⟨458512664539186980326735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19563207020338644493940693 458512664539186980326735)
                  ·
                    rfl

theorem cell20_1004569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_1004569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004569 prefixEnd_1004569 := by exact prefixLift 1004569
  have htrace : WordTrace (prefixWord ++ tailWord_1004569) baseStart_1004569 baseEnd_1004569 := by
    simpa [prefixWord, tailWord_1004569, baseEnd_1004569] using wordTrace_append hprefix tailTrace_1004569
  have hstable : (prefixWord ++ tailWord_1004569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004569).length < 2 ^ (prefixWord ++ tailWord_1004569).sum := by decide
  have hdescent : baseEnd_1004569 < baseStart_1004569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004593 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_1004593 : Nat := 118140960795 + 1004593 * 2 ^ 59
def prefixEnd_1004593 : Nat := 4983230072969 + 3 ^ 40 * 1004593 * 2
def baseEnd_1004593 : Nat := 458523618793149563526637

theorem tailTrace_1004593 : CollatzResearch.WordTrace tailWord_1004593 prefixEnd_1004593 458523618793149563526637 := by
  unfold tailWord_1004593
  simp only [CollatzResearch.WordTrace]
  refine ⟨36640516849538606670058433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24427011233025737780038955 36640516849538606670058433)
  ·
    refine ⟨27480387637153955002543825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36640516849538606670058433 27480387637153955002543825)
    ·
      refine ⟨20610290727865466251907869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27480387637153955002543825 20610290727865466251907869)
      ·
        refine ⟨7728859022949549844465451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20610290727865466251907869 7728859022949549844465451)
        ·
          refine ⟨11593288534424324766698177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7728859022949549844465451 11593288534424324766698177)
          ·
            refine ⟨8694966400818243575023633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11593288534424324766698177 8694966400818243575023633)
            ·
              refine ⟨6521224800613682681267725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8694966400818243575023633 6521224800613682681267725)
              ·
                refine ⟨2445459300230131005475397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6521224800613682681267725 2445459300230131005475397)
                ·
                  refine ⟨458523618793149563526637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445459300230131005475397 458523618793149563526637)
                  ·
                    rfl

theorem cell20_1004593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_1004593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004593 prefixEnd_1004593 := by exact prefixLift 1004593
  have htrace : WordTrace (prefixWord ++ tailWord_1004593) baseStart_1004593 baseEnd_1004593 := by
    simpa [prefixWord, tailWord_1004593, baseEnd_1004593] using wordTrace_append hprefix tailTrace_1004593
  have hstable : (prefixWord ++ tailWord_1004593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004593).length < 2 ^ (prefixWord ++ tailWord_1004593).sum := by decide
  have hdescent : baseEnd_1004593 < baseStart_1004593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004596 : List Nat := [2, 5, 1, 2, 1, 1, 3, 5]
def baseStart_1004596 : Nat := 118140960795 + 1004596 * 2 ^ 59
def prefixEnd_1004596 : Nat := 4983230072969 + 3 ^ 40 * 1004596 * 2
def baseEnd_1004596 : Nat := 152841662691631628808875

theorem tailTrace_1004596 : CollatzResearch.WordTrace tailWord_1004596 prefixEnd_1004596 152841662691631628808875 := by
  unfold tailWord_1004596
  simp only [CollatzResearch.WordTrace]
  refine ⟨18320313134263869091208821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24427084179018492121611761 18320313134263869091208821)
  ·
    refine ⟨1717529356337237727300827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18320313134263869091208821 1717529356337237727300827)
    ·
      refine ⟨2576294034505856590951241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717529356337237727300827 2576294034505856590951241)
      ·
        refine ⟨1932220525879392443213431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2576294034505856590951241 1932220525879392443213431)
        ·
          refine ⟨2898330788819088664820147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932220525879392443213431 2898330788819088664820147)
          ·
            refine ⟨4347496183228632997230221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898330788819088664820147 4347496183228632997230221)
            ·
              refine ⟨1630311068710737373961333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4347496183228632997230221 1630311068710737373961333)
              ·
                refine ⟨152841662691631628808875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1630311068710737373961333 152841662691631628808875)
                ·
                  rfl

theorem cell20_1004596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_1004596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004596 prefixEnd_1004596 := by exact prefixLift 1004596
  have htrace : WordTrace (prefixWord ++ tailWord_1004596) baseStart_1004596 baseEnd_1004596 := by
    simpa [prefixWord, tailWord_1004596, baseEnd_1004596] using wordTrace_append hprefix tailTrace_1004596
  have hstable : (prefixWord ++ tailWord_1004596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004596).length < 2 ^ (prefixWord ++ tailWord_1004596).sum := by decide
  have hdescent : baseEnd_1004596 < baseStart_1004596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
