import V185TrunkScan20Chunk022

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_139981 : List Nat := [1, 6, 2, 1, 2, 2, 1, 5]
def baseStart_139981 : Nat := 118140960795 + 139981 * 2 ^ 59
def prefixEnd_139981 : Nat := 4983230072969 + 3 ^ 40 * 139981 * 2
def baseEnd_139981 : Nat := 21297047554702831820369

theorem tailTrace_139981 : CollatzResearch.WordTrace tailWord_139981 prefixEnd_139981 21297047554702831820369 := by
  unfold tailWord_139981
  simp only [CollatzResearch.WordTrace]
  refine ⟨5105526505880218696587797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3403684337253479131058531 5105526505880218696587797)
  ·
    refine ⟨239321554963135251402553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5105526505880218696587797 239321554963135251402553)
    ·
      refine ⟨179491166222351438551915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239321554963135251402553 179491166222351438551915)
      ·
        refine ⟨269236749333527157827873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179491166222351438551915 269236749333527157827873)
        ·
          refine ⟨201927562000145368370905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269236749333527157827873 201927562000145368370905)
          ·
            refine ⟨151445671500109026278179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201927562000145368370905 151445671500109026278179)
            ·
              refine ⟨227168507250163539417269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151445671500109026278179 227168507250163539417269)
              ·
                refine ⟨21297047554702831820369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 227168507250163539417269 21297047554702831820369)
                ·
                  rfl

theorem cell20_139981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 5].length) (baseStart_139981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139981 prefixEnd_139981 := by exact prefixLift 139981
  have htrace : WordTrace (prefixWord ++ tailWord_139981) baseStart_139981 baseEnd_139981 := by
    simpa [prefixWord, tailWord_139981, baseEnd_139981] using wordTrace_append hprefix tailTrace_139981
  have hstable : (prefixWord ++ tailWord_139981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139981).length < 2 ^ (prefixWord ++ tailWord_139981).sum := by decide
  have hdescent : baseEnd_139981 < baseStart_139981 := by decide
  rcases family_descends (prefixWord ++ tailWord_139981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139992 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 3]
def baseStart_139992 : Nat := 118140960795 + 139992 * 2 ^ 59
def prefixEnd_139992 : Nat := 4983230072969 + 3 ^ 40 * 139992 * 2
def baseEnd_139992 : Nat := 63896163363841346094395

theorem tailTrace_139992 : CollatzResearch.WordTrace tailWord_139992 prefixEnd_139992 63896163363841346094395 := by
  unfold tailWord_139992
  simp only [CollatzResearch.WordTrace]
  refine ⟨2552963854420183787619115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3403951805893578383492153 2552963854420183787619115)
  ·
    refine ⟨3829445781630275681428673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2552963854420183787619115 3829445781630275681428673)
    ·
      refine ⟨2872084336222706761071505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3829445781630275681428673 2872084336222706761071505)
      ·
        refine ⟨2154063252167030070803629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2872084336222706761071505 2154063252167030070803629)
        ·
          refine ⟨807773719562636276551361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2154063252167030070803629 807773719562636276551361)
          ·
            refine ⟨605830289671977207413521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 807773719562636276551361 605830289671977207413521)
            ·
              refine ⟨454372717253982905560141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605830289671977207413521 454372717253982905560141)
              ·
                refine ⟨170389768970243589585053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 454372717253982905560141 170389768970243589585053)
                ·
                  refine ⟨63896163363841346094395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170389768970243589585053 63896163363841346094395)
                  ·
                    rfl

theorem cell20_139992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_139992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139992 prefixEnd_139992 := by exact prefixLift 139992
  have htrace : WordTrace (prefixWord ++ tailWord_139992) baseStart_139992 baseEnd_139992 := by
    simpa [prefixWord, tailWord_139992, baseEnd_139992] using wordTrace_append hprefix tailTrace_139992
  have hstable : (prefixWord ++ tailWord_139992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139992).length < 2 ^ (prefixWord ++ tailWord_139992).sum := by decide
  have hdescent : baseEnd_139992 < baseStart_139992 := by decide
  rcases family_descends (prefixWord ++ tailWord_139992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139999 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 4]
def baseStart_139999 : Nat := 118140960795 + 139999 * 2 ^ 59
def prefixEnd_139999 : Nat := 4983230072969 + 3 ^ 40 * 139999 * 2
def baseEnd_139999 : Nat := 63899358354580432861033

theorem tailTrace_139999 : CollatzResearch.WordTrace tailWord_139999 prefixEnd_139999 63899358354580432861033 := by
  unfold tailWord_139999
  simp only [CollatzResearch.WordTrace]
  refine ⟨5106183019815007770743051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3404122013210005180495367 5106183019815007770743051)
  ·
    refine ⟨7659274529722511656114577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5106183019815007770743051 7659274529722511656114577)
    ·
      refine ⟨5744455897291883742085933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7659274529722511656114577 5744455897291883742085933)
      ·
        refine ⟨2154170961484456403282225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5744455897291883742085933 2154170961484456403282225)
        ·
          refine ⟨1615628221113342302461669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2154170961484456403282225 1615628221113342302461669)
          ·
            refine ⟨302930291458751681711563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1615628221113342302461669 302930291458751681711563)
            ·
              refine ⟨454395437188127522567345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302930291458751681711563 454395437188127522567345)
              ·
                refine ⟨340796577891095641925509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454395437188127522567345 340796577891095641925509)
                ·
                  refine ⟨63899358354580432861033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 340796577891095641925509 63899358354580432861033)
                  ·
                    rfl

theorem cell20_139999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_139999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139999 prefixEnd_139999 := by exact prefixLift 139999
  have htrace : WordTrace (prefixWord ++ tailWord_139999) baseStart_139999 baseEnd_139999 := by
    simpa [prefixWord, tailWord_139999, baseEnd_139999] using wordTrace_append hprefix tailTrace_139999
  have hstable : (prefixWord ++ tailWord_139999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139999).length < 2 ^ (prefixWord ++ tailWord_139999).sum := by decide
  have hdescent : baseEnd_139999 < baseStart_139999 := by decide
  rcases family_descends (prefixWord ++ tailWord_139999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140016 : List Nat := [2, 1, 1, 1, 3, 1, 6, 3, 2]
def baseStart_140016 : Nat := 118140960795 + 140016 * 2 ^ 59
def prefixEnd_140016 : Nat := 4983230072969 + 3 ^ 40 * 140016 * 2
def baseEnd_140016 : Nat := 63907117617803929294297

theorem tailTrace_140016 : CollatzResearch.WordTrace tailWord_140016 prefixEnd_140016 63907117617803929294297 := by
  unfold tailWord_140016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553401530376709837055951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3404535373835613116074601 2553401530376709837055951)
  ·
    refine ⟨3830102295565064755583927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2553401530376709837055951 3830102295565064755583927)
    ·
      refine ⟨5745153443347597133375891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3830102295565064755583927 5745153443347597133375891)
      ·
        refine ⟨8617730165021395700063837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5745153443347597133375891 8617730165021395700063837)
        ·
          refine ⟨3231648811883023387523939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8617730165021395700063837 3231648811883023387523939)
          ·
            refine ⟨4847473217824535081285909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231648811883023387523939 4847473217824535081285909)
            ·
              refine ⟨227225307085525081935277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4847473217824535081285909 227225307085525081935277)
              ·
                refine ⟨85209490157071905725729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227225307085525081935277 85209490157071905725729)
                ·
                  refine ⟨63907117617803929294297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85209490157071905725729 63907117617803929294297)
                  ·
                    rfl

theorem cell20_140016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_140016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140016 prefixEnd_140016 := by exact prefixLift 140016
  have htrace : WordTrace (prefixWord ++ tailWord_140016) baseStart_140016 baseEnd_140016 := by
    simpa [prefixWord, tailWord_140016, baseEnd_140016] using wordTrace_append hprefix tailTrace_140016
  have hstable : (prefixWord ++ tailWord_140016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140016).length < 2 ^ (prefixWord ++ tailWord_140016).sum := by decide
  have hdescent : baseEnd_140016 < baseStart_140016 := by decide
  rcases family_descends (prefixWord ++ tailWord_140016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140172 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_140172 : Nat := 118140960795 + 140172 * 2 ^ 59
def prefixEnd_140172 : Nat := 4983230072969 + 3 ^ 40 * 140172 * 2
def baseEnd_140172 : Nat := 63978320268560720093659

theorem tailTrace_140172 : CollatzResearch.WordTrace tailWord_140172 prefixEnd_140172 63978320268560720093659 := by
  unfold tailWord_140172
  simp only [CollatzResearch.WordTrace]
  refine ⟨2556246424094129158395385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3408328565458838877860513 2556246424094129158395385)
  ·
    refine ⟨1917184818070596868796539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2556246424094129158395385 1917184818070596868796539)
    ·
      refine ⟨2875777227105895303194809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1917184818070596868796539 2875777227105895303194809)
      ·
        refine ⟨2156832920329421477396107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2875777227105895303194809 2156832920329421477396107)
        ·
          refine ⟨3235249380494132216094161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156832920329421477396107 3235249380494132216094161)
          ·
            refine ⟨2426437035370599162070621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3235249380494132216094161 2426437035370599162070621)
            ·
              refine ⟨909913888263974685776483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2426437035370599162070621 909913888263974685776483)
              ·
                refine ⟨1364870832395962028664725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909913888263974685776483 1364870832395962028664725)
                ·
                  refine ⟨63978320268560720093659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1364870832395962028664725 63978320268560720093659)
                  ·
                    rfl

theorem cell20_140172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_140172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140172 prefixEnd_140172 := by exact prefixLift 140172
  have htrace : WordTrace (prefixWord ++ tailWord_140172) baseStart_140172 baseEnd_140172 := by
    simpa [prefixWord, tailWord_140172, baseEnd_140172] using wordTrace_append hprefix tailTrace_140172
  have hstable : (prefixWord ++ tailWord_140172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140172).length < 2 ^ (prefixWord ++ tailWord_140172).sum := by decide
  have hdescent : baseEnd_140172 < baseStart_140172 := by decide
  rcases family_descends (prefixWord ++ tailWord_140172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140261 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 4]
def baseStart_140261 : Nat := 118140960795 + 140261 * 2 ^ 59
def prefixEnd_140261 : Nat := 4983230072969 + 3 ^ 40 * 140261 * 2
def baseEnd_140261 : Nat := 64018942293671966126629

theorem tailTrace_140261 : CollatzResearch.WordTrace tailWord_140261 prefixEnd_140261 64018942293671966126629 := by
  unfold tailWord_140261
  simp only [CollatzResearch.WordTrace]
  refine ⟨5115738944865826516780637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3410492629910551011187091 5115738944865826516780637)
  ·
    refine ⟨1918402104324684943792739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5115738944865826516780637 1918402104324684943792739)
    ·
      refine ⟨2877603156487027415689109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1918402104324684943792739 2877603156487027415689109)
      ·
        refine ⟨134887647960329410110427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2877603156487027415689109 134887647960329410110427)
        ·
          refine ⟨202331471940494115165641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134887647960329410110427 202331471940494115165641)
          ·
            refine ⟨151748603955370586374231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202331471940494115165641 151748603955370586374231)
            ·
              refine ⟨227622905933055879561347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151748603955370586374231 227622905933055879561347)
              ·
                refine ⟨341434358899583819342021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227622905933055879561347 341434358899583819342021)
                ·
                  refine ⟨64018942293671966126629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 341434358899583819342021 64018942293671966126629)
                  ·
                    rfl

theorem cell20_140261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_140261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140261 prefixEnd_140261 := by exact prefixLift 140261
  have htrace : WordTrace (prefixWord ++ tailWord_140261) baseStart_140261 baseEnd_140261 := by
    simpa [prefixWord, tailWord_140261, baseEnd_140261] using wordTrace_append hprefix tailTrace_140261
  have hstable : (prefixWord ++ tailWord_140261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140261).length < 2 ^ (prefixWord ++ tailWord_140261).sum := by decide
  have hdescent : baseEnd_140261 < baseStart_140261 := by decide
  rcases family_descends (prefixWord ++ tailWord_140261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140293 : List Nat := [1, 3, 1, 1, 2, 3, 1, 8]
def baseStart_140293 : Nat := 118140960795 + 140293 * 2 ^ 59
def prefixEnd_140293 : Nat := 4983230072969 + 3 ^ 40 * 140293 * 2
def baseEnd_140293 : Nat := 21344515988540692353277

theorem tailTrace_140293 : CollatzResearch.WordTrace tailWord_140293 prefixEnd_140293 21344515988540692353277 := by
  unfold tailWord_140293
  simp only [CollatzResearch.WordTrace]
  refine ⟨5116906080749895981945533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3411270720499930654630355 5116906080749895981945533)
  ·
    refine ⟨1918839780281210993229575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5116906080749895981945533 1918839780281210993229575)
    ·
      refine ⟨2878259670421816489844363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1918839780281210993229575 2878259670421816489844363)
      ·
        refine ⟨4317389505632724734766545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2878259670421816489844363 4317389505632724734766545)
        ·
          refine ⟨3238042129224543551074909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4317389505632724734766545 3238042129224543551074909)
          ·
            refine ⟨1214265798459203831653091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3238042129224543551074909 1214265798459203831653091)
            ·
              refine ⟨1821398697688805747479637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214265798459203831653091 1821398697688805747479637)
              ·
                refine ⟨21344515988540692353277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1821398697688805747479637 21344515988540692353277)
                ·
                  rfl

theorem cell20_140293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_140293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140293 prefixEnd_140293 := by exact prefixLift 140293
  have htrace : WordTrace (prefixWord ++ tailWord_140293) baseStart_140293 baseEnd_140293 := by
    simpa [prefixWord, tailWord_140293, baseEnd_140293] using wordTrace_append hprefix tailTrace_140293
  have hstable : (prefixWord ++ tailWord_140293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140293).length < 2 ^ (prefixWord ++ tailWord_140293).sum := by decide
  have hdescent : baseEnd_140293 < baseStart_140293 := by decide
  rcases family_descends (prefixWord ++ tailWord_140293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140306 : List Nat := [3, 2, 5, 1, 1, 8]
def baseStart_140306 : Nat := 118140960795 + 140306 * 2 ^ 59
def prefixEnd_140306 : Nat := 4983230072969 + 3 ^ 40 * 140306 * 2
def baseEnd_140306 : Nat := 2371832648883400356535

theorem tailTrace_140306 : CollatzResearch.WordTrace tailWord_140306 prefixEnd_140306 2371832648883400356535 := by
  unfold tailWord_140306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1279345057425699800542193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3411586819801866134779181 1279345057425699800542193)
  ·
    refine ⟨959508793069274850406645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1279345057425699800542193 959508793069274850406645)
    ·
      refine ⟨89953949350244517225623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 959508793069274850406645 89953949350244517225623)
      ·
        refine ⟨134930924025366775838435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89953949350244517225623 134930924025366775838435)
        ·
          refine ⟨202396386038050163757653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134930924025366775838435 202396386038050163757653)
          ·
            refine ⟨2371832648883400356535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 202396386038050163757653 2371832648883400356535)
            ·
              rfl

theorem cell20_140306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 8].length) (baseStart_140306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140306 prefixEnd_140306 := by exact prefixLift 140306
  have htrace : WordTrace (prefixWord ++ tailWord_140306) baseStart_140306 baseEnd_140306 := by
    simpa [prefixWord, tailWord_140306, baseEnd_140306] using wordTrace_append hprefix tailTrace_140306
  have hstable : (prefixWord ++ tailWord_140306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140306).length < 2 ^ (prefixWord ++ tailWord_140306).sum := by decide
  have hdescent : baseEnd_140306 < baseStart_140306 := by decide
  rcases family_descends (prefixWord ++ tailWord_140306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140316 : List Nat := [2, 2, 3, 1, 4, 2, 2, 2, 2]
def baseStart_140316 : Nat := 118140960795 + 140316 * 2 ^ 59
def prefixEnd_140316 : Nat := 4983230072969 + 3 ^ 40 * 140316 * 2
def baseEnd_140316 : Nat := 64044045792336219293071

theorem tailTrace_140316 : CollatzResearch.WordTrace tailWord_140316 prefixEnd_140316 64044045792336219293071 := by
  unfold tailWord_140316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2558872479833285455016401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3411829973111047273355201 2558872479833285455016401)
  ·
    refine ⟨1919154359874964091262301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2558872479833285455016401 1919154359874964091262301)
    ·
      refine ⟨719682884953111534223363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1919154359874964091262301 719682884953111534223363)
      ·
        refine ⟨1079524327429667301335045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719682884953111534223363 1079524327429667301335045)
        ·
          refine ⟨202410811393062619000321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1079524327429667301335045 202410811393062619000321)
          ·
            refine ⟨151808108544796964250241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202410811393062619000321 151808108544796964250241)
            ·
              refine ⟨113856081408597723187681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151808108544796964250241 113856081408597723187681)
              ·
                refine ⟨85392061056448292390761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113856081408597723187681 85392061056448292390761)
                ·
                  refine ⟨64044045792336219293071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85392061056448292390761 64044045792336219293071)
                  ·
                    rfl

theorem cell20_140316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_140316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140316 prefixEnd_140316 := by exact prefixLift 140316
  have htrace : WordTrace (prefixWord ++ tailWord_140316) baseStart_140316 baseEnd_140316 := by
    simpa [prefixWord, tailWord_140316, baseEnd_140316] using wordTrace_append hprefix tailTrace_140316
  have hstable : (prefixWord ++ tailWord_140316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140316).length < 2 ^ (prefixWord ++ tailWord_140316).sum := by decide
  have hdescent : baseEnd_140316 < baseStart_140316 := by decide
  rcases family_descends (prefixWord ++ tailWord_140316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140327 : List Nat := [1, 1, 7, 1, 1, 1, 3, 5]
def baseStart_140327 : Nat := 118140960795 + 140327 * 2 ^ 59
def prefixEnd_140327 : Nat := 4983230072969 + 3 ^ 40 * 140327 * 2
def baseEnd_140327 : Nat := 21349688830689689975453

theorem tailTrace_140327 : CollatzResearch.WordTrace tailWord_140327 prefixEnd_140327 21349688830689689975453 := by
  unfold tailWord_140327
  simp only [CollatzResearch.WordTrace]
  refine ⟨5118146162626719788683235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3412097441751146525788823 5118146162626719788683235)
  ·
    refine ⟨7677219243940079683024853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5118146162626719788683235 7677219243940079683024853)
    ·
      refine ⟨179934826029845617570895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7677219243940079683024853 179934826029845617570895)
      ·
        refine ⟨269902239044768426356343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179934826029845617570895 269902239044768426356343)
        ·
          refine ⟨404853358567152639534515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269902239044768426356343 404853358567152639534515)
          ·
            refine ⟨607280037850728959301773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404853358567152639534515 607280037850728959301773)
            ·
              refine ⟨227730014194023359738165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 607280037850728959301773 227730014194023359738165)
              ·
                refine ⟨21349688830689689975453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 227730014194023359738165 21349688830689689975453)
                ·
                  rfl

theorem cell20_140327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 5].length) (baseStart_140327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140327 prefixEnd_140327 := by exact prefixLift 140327
  have htrace : WordTrace (prefixWord ++ tailWord_140327) baseStart_140327 baseEnd_140327 := by
    simpa [prefixWord, tailWord_140327, baseEnd_140327] using wordTrace_append hprefix tailTrace_140327
  have hstable : (prefixWord ++ tailWord_140327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140327).length < 2 ^ (prefixWord ++ tailWord_140327).sum := by decide
  have hdescent : baseEnd_140327 < baseStart_140327 := by decide
  rcases family_descends (prefixWord ++ tailWord_140327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140334 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_140334 : Nat := 118140960795 + 140334 * 2 ^ 59
def prefixEnd_140334 : Nat := 4983230072969 + 3 ^ 40 * 140334 * 2
def baseEnd_140334 : Nat := 64052261482808156692997

theorem tailTrace_140334 : CollatzResearch.WordTrace tailWord_140334 prefixEnd_140334 64052261482808156692997 := by
  unfold tailWord_140334
  simp only [CollatzResearch.WordTrace]
  refine ⟨639800184200169998023507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3412267649067573322792037 639800184200169998023507)
  ·
    refine ⟨959700276300254997035261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 639800184200169998023507 959700276300254997035261)
    ·
      refine ⟨359887603612595623888223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 959700276300254997035261 359887603612595623888223)
      ·
        refine ⟨539831405418893435832335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359887603612595623888223 539831405418893435832335)
        ·
          refine ⟨809747108128340153748503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539831405418893435832335 809747108128340153748503)
          ·
            refine ⟨1214620662192510230622755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809747108128340153748503 1214620662192510230622755)
            ·
              refine ⟨1821930993288765345934133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214620662192510230622755 1821930993288765345934133)
              ·
                refine ⟨170806030620821751181325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1821930993288765345934133 170806030620821751181325)
                ·
                  refine ⟨64052261482808156692997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170806030620821751181325 64052261482808156692997)
                  ·
                    rfl

theorem cell20_140334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_140334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140334 prefixEnd_140334 := by exact prefixLift 140334
  have htrace : WordTrace (prefixWord ++ tailWord_140334) baseStart_140334 baseEnd_140334 := by
    simpa [prefixWord, tailWord_140334, baseEnd_140334] using wordTrace_append hprefix tailTrace_140334
  have hstable : (prefixWord ++ tailWord_140334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140334).length < 2 ^ (prefixWord ++ tailWord_140334).sum := by decide
  have hdescent : baseEnd_140334 < baseStart_140334 := by decide
  rcases family_descends (prefixWord ++ tailWord_140334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140372 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 3]
def baseStart_140372 : Nat := 118140960795 + 140372 * 2 ^ 59
def prefixEnd_140372 : Nat := 4983230072969 + 3 ^ 40 * 140372 * 2
def baseEnd_140372 : Nat := 64069605718248913426175

theorem tailTrace_140372 : CollatzResearch.WordTrace tailWord_140372 prefixEnd_140372 64069605718248913426175 := by
  unfold tailWord_140372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559893723731846237035685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3413191631642461649380913 2559893723731846237035685)
  ·
    refine ⟨479980073199721169444191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2559893723731846237035685 479980073199721169444191)
    ·
      refine ⟨719970109799581754166287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 479980073199721169444191 719970109799581754166287)
      ·
        refine ⟨1079955164699372631249431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719970109799581754166287 1079955164699372631249431)
        ·
          refine ⟨1619932747049058946874147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079955164699372631249431 1619932747049058946874147)
          ·
            refine ⟨2429899120573588420311221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619932747049058946874147 2429899120573588420311221)
            ·
              refine ⟨227803042553773914404177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2429899120573588420311221 227803042553773914404177)
              ·
                refine ⟨170852281915330435803133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227803042553773914404177 170852281915330435803133)
                ·
                  refine ⟨64069605718248913426175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170852281915330435803133 64069605718248913426175)
                  ·
                    rfl

theorem cell20_140372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_140372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140372 prefixEnd_140372 := by exact prefixLift 140372
  have htrace : WordTrace (prefixWord ++ tailWord_140372) baseStart_140372 baseEnd_140372 := by
    simpa [prefixWord, tailWord_140372, baseEnd_140372] using wordTrace_append hprefix tailTrace_140372
  have hstable : (prefixWord ++ tailWord_140372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140372).length < 2 ^ (prefixWord ++ tailWord_140372).sum := by decide
  have hdescent : baseEnd_140372 < baseStart_140372 := by decide
  rcases family_descends (prefixWord ++ tailWord_140372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140400 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_140400 : Nat := 118140960795 + 140400 * 2 ^ 59
def prefixEnd_140400 : Nat := 4983230072969 + 3 ^ 40 * 140400 * 2
def baseEnd_140400 : Nat := 64082385681205260492727

theorem tailTrace_140400 : CollatzResearch.WordTrace tailWord_140400 prefixEnd_140400 64082385681205260492727 := by
  unfold tailWord_140400
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560404345681126628045327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3413872460908168837393769 2560404345681126628045327)
  ·
    refine ⟨3840606518521689942067991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560404345681126628045327 3840606518521689942067991)
    ·
      refine ⟨5760909777782534913101987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840606518521689942067991 5760909777782534913101987)
      ·
        refine ⟨8641364666673802369652981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5760909777782534913101987 8641364666673802369652981)
        ·
          refine ⟨810127937500668972154967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8641364666673802369652981 810127937500668972154967)
          ·
            refine ⟨1215191906251003458232451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810127937500668972154967 1215191906251003458232451)
            ·
              refine ⟨1822787859376505187348677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215191906251003458232451 1822787859376505187348677)
              ·
                refine ⟨341772723633094722627877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1822787859376505187348677 341772723633094722627877)
                ·
                  refine ⟨64082385681205260492727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 341772723633094722627877 64082385681205260492727)
                  ·
                    rfl

theorem cell20_140400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_140400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140400 prefixEnd_140400 := by exact prefixLift 140400
  have htrace : WordTrace (prefixWord ++ tailWord_140400) baseStart_140400 baseEnd_140400 := by
    simpa [prefixWord, tailWord_140400, baseEnd_140400] using wordTrace_append hprefix tailTrace_140400
  have hstable : (prefixWord ++ tailWord_140400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140400).length < 2 ^ (prefixWord ++ tailWord_140400).sum := by decide
  have hdescent : baseEnd_140400 < baseStart_140400 := by decide
  rcases family_descends (prefixWord ++ tailWord_140400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140407 : List Nat := [1, 1, 3, 1, 1, 4, 3, 6]
def baseStart_140407 : Nat := 118140960795 + 140407 * 2 ^ 59
def prefixEnd_140407 : Nat := 4983230072969 + 3 ^ 40 * 140407 * 2
def baseEnd_140407 : Nat := 21361860223981449086455

theorem tailTrace_140407 : CollatzResearch.WordTrace tailWord_140407 prefixEnd_140407 21361860223981449086455 := by
  unfold tailWord_140407
  simp only [CollatzResearch.WordTrace]
  refine ⟨5121064002336893451595475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3414042668224595634396983 5121064002336893451595475)
  ·
    refine ⟨7681596003505340177393213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5121064002336893451595475 7681596003505340177393213)
    ·
      refine ⟨2880598501314502566522455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7681596003505340177393213 2880598501314502566522455)
      ·
        refine ⟨4320897751971753849783683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880598501314502566522455 4320897751971753849783683)
        ·
          refine ⟨6481346627957630774675525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320897751971753849783683 6481346627957630774675525)
          ·
            refine ⟨1215252492742055770251661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6481346627957630774675525 1215252492742055770251661)
            ·
              refine ⟨455719684778270913844373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1215252492742055770251661 455719684778270913844373)
              ·
                refine ⟨21361860223981449086455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 455719684778270913844373 21361860223981449086455)
                ·
                  rfl

theorem cell20_140407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_140407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140407 prefixEnd_140407 := by exact prefixLift 140407
  have htrace : WordTrace (prefixWord ++ tailWord_140407) baseStart_140407 baseEnd_140407 := by
    simpa [prefixWord, tailWord_140407, baseEnd_140407] using wordTrace_append hprefix tailTrace_140407
  have hstable : (prefixWord ++ tailWord_140407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140407).length < 2 ^ (prefixWord ++ tailWord_140407).sum := by decide
  have hdescent : baseEnd_140407 < baseStart_140407 := by decide
  rcases family_descends (prefixWord ++ tailWord_140407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140434 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_140434 : Nat := 118140960795 + 140434 * 2 ^ 59
def prefixEnd_140434 : Nat := 4983230072969 + 3 ^ 40 * 140434 * 2
def baseEnd_140434 : Nat := 64097904207652253359255

theorem tailTrace_140434 : CollatzResearch.WordTrace tailWord_140434 prefixEnd_140434 64097904207652253359255 := by
  unfold tailWord_140434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280512193309769265707089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3414699182159384708552237 1280512193309769265707089)
  ·
    refine ⟨960384144982326949280317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1280512193309769265707089 960384144982326949280317)
    ·
      refine ⟨360144054368372605980119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 960384144982326949280317 360144054368372605980119)
      ·
        refine ⟨540216081552558908970179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360144054368372605980119 540216081552558908970179)
        ·
          refine ⟨810324122328838363455269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540216081552558908970179 810324122328838363455269)
          ·
            refine ⟨151935772936657193147863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 810324122328838363455269 151935772936657193147863)
            ·
              refine ⟨227903659404985789721795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151935772936657193147863 227903659404985789721795)
              ·
                refine ⟨341855489107478684582693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227903659404985789721795 341855489107478684582693)
                ·
                  refine ⟨64097904207652253359255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 341855489107478684582693 64097904207652253359255)
                  ·
                    rfl

theorem cell20_140434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_140434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140434 prefixEnd_140434 := by exact prefixLift 140434
  have htrace : WordTrace (prefixWord ++ tailWord_140434) baseStart_140434 baseEnd_140434 := by
    simpa [prefixWord, tailWord_140434, baseEnd_140434] using wordTrace_append hprefix tailTrace_140434
  have hstable : (prefixWord ++ tailWord_140434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140434).length < 2 ^ (prefixWord ++ tailWord_140434).sum := by decide
  have hdescent : baseEnd_140434 < baseStart_140434 := by decide
  rcases family_descends (prefixWord ++ tailWord_140434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140517 : List Nat := [1, 3, 1, 4, 3, 1, 3, 4]
def baseStart_140517 : Nat := 118140960795 + 140517 * 2 ^ 59
def prefixEnd_140517 : Nat := 4983230072969 + 3 ^ 40 * 140517 * 2
def baseEnd_140517 : Nat := 21378595889757617864083

theorem tailTrace_140517 : CollatzResearch.WordTrace tailWord_140517 prefixEnd_140517 21378595889757617864083 := by
  unfold tailWord_140517
  simp only [CollatzResearch.WordTrace]
  refine ⟨5125076031938382238099805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3416717354625588158733203 5125076031938382238099805)
  ·
    refine ⟨1921903511976893339287427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5125076031938382238099805 1921903511976893339287427)
    ·
      refine ⟨2882855267965340008931141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1921903511976893339287427 2882855267965340008931141)
      ·
        refine ⟨540535362743501251674589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2882855267965340008931141 540535362743501251674589)
        ·
          refine ⟨202700761028812969377971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 540535362743501251674589 202700761028812969377971)
          ·
            refine ⟨304051141543219454066957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202700761028812969377971 304051141543219454066957)
            ·
              refine ⟨114019178078707295275109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 304051141543219454066957 114019178078707295275109)
              ·
                refine ⟨21378595889757617864083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114019178078707295275109 21378595889757617864083)
                ·
                  rfl

theorem cell20_140517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 4].length) (baseStart_140517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140517 prefixEnd_140517 := by exact prefixLift 140517
  have htrace : WordTrace (prefixWord ++ tailWord_140517) baseStart_140517 baseEnd_140517 := by
    simpa [prefixWord, tailWord_140517, baseEnd_140517] using wordTrace_append hprefix tailTrace_140517
  have hstable : (prefixWord ++ tailWord_140517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140517).length < 2 ^ (prefixWord ++ tailWord_140517).sum := by decide
  have hdescent : baseEnd_140517 < baseStart_140517 := by decide
  rcases family_descends (prefixWord ++ tailWord_140517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140531 : List Nat := [1, 1, 1, 2, 2, 5, 1, 5, 2]
def baseStart_140531 : Nat := 118140960795 + 140531 * 2 ^ 59
def prefixEnd_140531 : Nat := 4983230072969 + 3 ^ 40 * 140531 * 2
def baseEnd_140531 : Nat := 64142177650751027125525

theorem tailTrace_140531 : CollatzResearch.WordTrace tailWord_140531 prefixEnd_140531 64142177650751027125525 := by
  unfold tailWord_140531
  simp only [CollatzResearch.WordTrace]
  refine ⟨5125586653887662629109447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3417057769258441752739631 5125586653887662629109447)
  ·
    refine ⟨7688379980831493943664171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5125586653887662629109447 7688379980831493943664171)
    ·
      refine ⟨11532569971247240915496257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7688379980831493943664171 11532569971247240915496257)
      ·
        refine ⟨8649427478435430686622193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11532569971247240915496257 8649427478435430686622193)
        ·
          refine ⟨6487070608826573014966645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8649427478435430686622193 6487070608826573014966645)
          ·
            refine ⟨608162869577491220153123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6487070608826573014966645 608162869577491220153123)
            ·
              refine ⟨912244304366236830229685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608162869577491220153123 912244304366236830229685)
              ·
                refine ⟨85522903534334702834033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 912244304366236830229685 85522903534334702834033)
                ·
                  refine ⟨64142177650751027125525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85522903534334702834033 64142177650751027125525)
                  ·
                    rfl

theorem cell20_140531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 2].length) (baseStart_140531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140531 prefixEnd_140531 := by exact prefixLift 140531
  have htrace : WordTrace (prefixWord ++ tailWord_140531) baseStart_140531 baseEnd_140531 := by
    simpa [prefixWord, tailWord_140531, baseEnd_140531] using wordTrace_append hprefix tailTrace_140531
  have hstable : (prefixWord ++ tailWord_140531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140531).length < 2 ^ (prefixWord ++ tailWord_140531).sum := by decide
  have hdescent : baseEnd_140531 < baseStart_140531 := by decide
  rcases family_descends (prefixWord ++ tailWord_140531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140545 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 5]
def baseStart_140545 : Nat := 118140960795 + 140545 * 2 ^ 59
def prefixEnd_140545 : Nat := 4983230072969 + 3 ^ 40 * 140545 * 2
def baseEnd_140545 : Nat := 64148567632229200658801

theorem tailTrace_140545 : CollatzResearch.WordTrace tailWord_140545 prefixEnd_140545 64148567632229200658801 := by
  unfold tailWord_140545
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126097275836943020119089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3417398183891295346746059 5126097275836943020119089)
  ·
    refine ⟨3844572956877707265089317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5126097275836943020119089 3844572956877707265089317)
    ·
      refine ⟨720857429414570112204247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3844572956877707265089317 720857429414570112204247)
      ·
        refine ⟨1081286144121855168306371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720857429414570112204247 1081286144121855168306371)
        ·
          refine ⟨1621929216182782752459557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081286144121855168306371 1621929216182782752459557)
          ·
            refine ⟨304111728034271766086167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1621929216182782752459557 304111728034271766086167)
            ·
              refine ⟨456167592051407649129251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304111728034271766086167 456167592051407649129251)
              ·
                refine ⟨684251388077111473693877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456167592051407649129251 684251388077111473693877)
                ·
                  refine ⟨64148567632229200658801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 684251388077111473693877 64148567632229200658801)
                  ·
                    rfl

theorem cell20_140545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_140545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140545 prefixEnd_140545 := by exact prefixLift 140545
  have htrace : WordTrace (prefixWord ++ tailWord_140545) baseStart_140545 baseEnd_140545 := by
    simpa [prefixWord, tailWord_140545, baseEnd_140545] using wordTrace_append hprefix tailTrace_140545
  have hstable : (prefixWord ++ tailWord_140545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140545).length < 2 ^ (prefixWord ++ tailWord_140545).sum := by decide
  have hdescent : baseEnd_140545 < baseStart_140545 := by decide
  rcases family_descends (prefixWord ++ tailWord_140545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140548 : List Nat := [2, 3, 2, 2, 2, 1, 2, 4, 2]
def baseStart_140548 : Nat := 118140960795 + 140548 * 2 ^ 59
def prefixEnd_140548 : Nat := 4983230072969 + 3 ^ 40 * 140548 * 2
def baseEnd_140548 : Nat := 64149936913974523558789

theorem tailTrace_140548 : CollatzResearch.WordTrace tailWord_140548 prefixEnd_140548 64149936913974523558789 := by
  unfold tailWord_140548
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563103347413037266239149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3417471129884049688318865 2563103347413037266239149)
  ·
    refine ⟨961163755279888974839681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2563103347413037266239149 961163755279888974839681)
    ·
      refine ⟨720872816459916731129761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 961163755279888974839681 720872816459916731129761)
      ·
        refine ⟨540654612344937548347321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720872816459916731129761 540654612344937548347321)
        ·
          refine ⟨405490959258703161260491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540654612344937548347321 405490959258703161260491)
          ·
            refine ⟨608236438888054741890737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405490959258703161260491 608236438888054741890737)
            ·
              refine ⟨456177329166041056418053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608236438888054741890737 456177329166041056418053)
              ·
                refine ⟨85533249218632698078385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 456177329166041056418053 85533249218632698078385)
                ·
                  refine ⟨64149936913974523558789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85533249218632698078385 64149936913974523558789)
                  ·
                    rfl

theorem cell20_140548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_140548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140548 prefixEnd_140548 := by exact prefixLift 140548
  have htrace : WordTrace (prefixWord ++ tailWord_140548) baseStart_140548 baseEnd_140548 := by
    simpa [prefixWord, tailWord_140548, baseEnd_140548] using wordTrace_append hprefix tailTrace_140548
  have hstable : (prefixWord ++ tailWord_140548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140548).length < 2 ^ (prefixWord ++ tailWord_140548).sum := by decide
  have hdescent : baseEnd_140548 < baseStart_140548 := by decide
  rcases family_descends (prefixWord ++ tailWord_140548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140576 : List Nat := [2, 1, 1, 5, 3, 1, 1, 6]
def baseStart_140576 : Nat := 118140960795 + 140576 * 2 ^ 59
def prefixEnd_140576 : Nat := 4983230072969 + 3 ^ 40 * 140576 * 2
def baseEnd_140576 : Nat := 21387572292310290208447

theorem tailTrace_140576 : CollatzResearch.WordTrace tailWord_140576 prefixEnd_140576 21387572292310290208447 := by
  unfold tailWord_140576
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563613969362317657248791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3418151959149756876331721 2563613969362317657248791)
  ·
    refine ⟨3845420954043476485873187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2563613969362317657248791 3845420954043476485873187)
    ·
      refine ⟨5768131431065214728809781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3845420954043476485873187 5768131431065214728809781)
      ·
        refine ⟨540762321662363880825917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5768131431065214728809781 540762321662363880825917)
        ·
          refine ⟨202785870623386455309719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 540762321662363880825917 202785870623386455309719)
          ·
            refine ⟨304178805935079682964579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202785870623386455309719 304178805935079682964579)
            ·
              refine ⟨456268208902619524446869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304178805935079682964579 456268208902619524446869)
              ·
                refine ⟨21387572292310290208447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 456268208902619524446869 21387572292310290208447)
                ·
                  rfl

theorem cell20_140576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_140576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140576 prefixEnd_140576 := by exact prefixLift 140576
  have htrace : WordTrace (prefixWord ++ tailWord_140576) baseStart_140576 baseEnd_140576 := by
    simpa [prefixWord, tailWord_140576, baseEnd_140576] using wordTrace_append hprefix tailTrace_140576
  have hstable : (prefixWord ++ tailWord_140576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140576).length < 2 ^ (prefixWord ++ tailWord_140576).sum := by decide
  have hdescent : baseEnd_140576 < baseStart_140576 := by decide
  rcases family_descends (prefixWord ++ tailWord_140576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140597 : List Nat := [1, 3, 3, 1, 2, 2, 8]
def baseStart_140597 : Nat := 118140960795 + 140597 * 2 ^ 59
def prefixEnd_140597 : Nat := 4983230072969 + 3 ^ 40 * 140597 * 2
def baseEnd_140597 : Nat := 7130255761016458991695

theorem tailTrace_140597 : CollatzResearch.WordTrace tailWord_140597 prefixEnd_140597 7130255761016458991695 := by
  unfold tailWord_140597
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127993871648555901012045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3418662581099037267341363 5127993871648555901012045)
  ·
    refine ⟨1922997701868208462879517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5127993871648555901012045 1922997701868208462879517)
    ·
      refine ⟨721124138200578173579819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1922997701868208462879517 721124138200578173579819)
      ·
        refine ⟨1081686207300867260369729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 721124138200578173579819 1081686207300867260369729)
        ·
          refine ⟨811264655475650445277297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1081686207300867260369729 811264655475650445277297)
          ·
            refine ⟨608448491606737833957973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811264655475650445277297 608448491606737833957973)
            ·
              refine ⟨7130255761016458991695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 608448491606737833957973 7130255761016458991695)
              ·
                rfl

theorem cell20_140597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 8].length) (baseStart_140597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140597 prefixEnd_140597 := by exact prefixLift 140597
  have htrace : WordTrace (prefixWord ++ tailWord_140597) baseStart_140597 baseEnd_140597 := by
    simpa [prefixWord, tailWord_140597, baseEnd_140597] using wordTrace_append hprefix tailTrace_140597
  have hstable : (prefixWord ++ tailWord_140597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140597).length < 2 ^ (prefixWord ++ tailWord_140597).sum := by decide
  have hdescent : baseEnd_140597 < baseStart_140597 := by decide
  rcases family_descends (prefixWord ++ tailWord_140597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140607 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 4]
def baseStart_140607 : Nat := 118140960795 + 140607 * 2 ^ 59
def prefixEnd_140607 : Nat := 4983230072969 + 3 ^ 40 * 140607 * 2
def baseEnd_140607 : Nat := 64176866121632540591881

theorem tailTrace_140607 : CollatzResearch.WordTrace tailWord_140607 prefixEnd_140607 64176866121632540591881 := by
  unfold tailWord_140607
  simp only [CollatzResearch.WordTrace]
  refine ⟨5128358601612327608876075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3418905734408218405917383 5128358601612327608876075)
  ·
    refine ⟨7692537902418491413314113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5128358601612327608876075 7692537902418491413314113)
    ·
      refine ⟨5769403426813868559985585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7692537902418491413314113 5769403426813868559985585)
      ·
        refine ⟨4327052570110401419989189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5769403426813868559985585 4327052570110401419989189)
        ·
          refine ⟨811322356895700266247973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4327052570110401419989189 811322356895700266247973)
          ·
            refine ⟨152122941917943799921495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 811322356895700266247973 152122941917943799921495)
            ·
              refine ⟨228184412876915699882243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152122941917943799921495 228184412876915699882243)
              ·
                refine ⟨342276619315373549823365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228184412876915699882243 342276619315373549823365)
                ·
                  refine ⟨64176866121632540591881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342276619315373549823365 64176866121632540591881)
                  ·
                    rfl

theorem cell20_140607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 4].length) (baseStart_140607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140607 prefixEnd_140607 := by exact prefixLift 140607
  have htrace : WordTrace (prefixWord ++ tailWord_140607) baseStart_140607 baseEnd_140607 := by
    simpa [prefixWord, tailWord_140607, baseEnd_140607] using wordTrace_append hprefix tailTrace_140607
  have hstable : (prefixWord ++ tailWord_140607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140607).length < 2 ^ (prefixWord ++ tailWord_140607).sum := by decide
  have hdescent : baseEnd_140607 < baseStart_140607 := by decide
  rcases family_descends (prefixWord ++ tailWord_140607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140628 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_140628 : Nat := 118140960795 + 140628 * 2 ^ 59
def prefixEnd_140628 : Nat := 4983230072969 + 3 ^ 40 * 140628 * 2
def baseEnd_140628 : Nat := 64186451093849800891795

theorem tailTrace_140628 : CollatzResearch.WordTrace tailWord_140628 prefixEnd_140628 64186451093849800891795 := by
  unfold tailWord_140628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564562267268124097695269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3419416356357498796927025 2564562267268124097695269)
  ·
    refine ⟨480855425112773268317863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2564562267268124097695269 480855425112773268317863)
    ·
      refine ⟨721283137669159902476795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480855425112773268317863 721283137669159902476795)
      ·
        refine ⟨1081924706503739853715193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 721283137669159902476795 1081924706503739853715193)
        ·
          refine ⟨811443529877804890286395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1081924706503739853715193 811443529877804890286395)
          ·
            refine ⟨1217165294816707335429593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811443529877804890286395 1217165294816707335429593)
            ·
              refine ⟨912873971112530501572195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1217165294816707335429593 912873971112530501572195)
              ·
                refine ⟨1369310956668795752358293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912873971112530501572195 1369310956668795752358293)
                ·
                  refine ⟨64186451093849800891795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1369310956668795752358293 64186451093849800891795)
                  ·
                    rfl

theorem cell20_140628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_140628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140628 prefixEnd_140628 := by exact prefixLift 140628
  have htrace : WordTrace (prefixWord ++ tailWord_140628) baseStart_140628 baseEnd_140628 := by
    simpa [prefixWord, tailWord_140628, baseEnd_140628] using wordTrace_append hprefix tailTrace_140628
  have hstable : (prefixWord ++ tailWord_140628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140628).length < 2 ^ (prefixWord ++ tailWord_140628).sum := by decide
  have hdescent : baseEnd_140628 < baseStart_140628 := by decide
  rcases family_descends (prefixWord ++ tailWord_140628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140645 : List Nat := [1, 3, 1, 3, 1, 2, 2, 5, 2]
def baseStart_140645 : Nat := 118140960795 + 140645 * 2 ^ 59
def prefixEnd_140645 : Nat := 4983230072969 + 3 ^ 40 * 140645 * 2
def baseEnd_140645 : Nat := 64194210357073297325059

theorem tailTrace_140645 : CollatzResearch.WordTrace tailWord_140645 prefixEnd_140645 64194210357073297325059 := by
  unfold tailWord_140645
  simp only [CollatzResearch.WordTrace]
  refine ⟨5129744575474660098759389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3419829716983106732506259 5129744575474660098759389)
  ·
    refine ⟨1923654215802997537034771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5129744575474660098759389 1923654215802997537034771)
    ·
      refine ⟨2885481323704496305552157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1923654215802997537034771 2885481323704496305552157)
      ·
        refine ⟨1082055496389186114582059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2885481323704496305552157 1082055496389186114582059)
        ·
          refine ⟨1623083244583779171873089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1082055496389186114582059 1623083244583779171873089)
          ·
            refine ⟨1217312433437834378904817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1623083244583779171873089 1217312433437834378904817)
            ·
              refine ⟨912984325078375784178613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1217312433437834378904817 912984325078375784178613)
              ·
                refine ⟨85592280476097729766745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 912984325078375784178613 85592280476097729766745)
                ·
                  refine ⟨64194210357073297325059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85592280476097729766745 64194210357073297325059)
                  ·
                    rfl

theorem cell20_140645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_140645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140645 prefixEnd_140645 := by exact prefixLift 140645
  have htrace : WordTrace (prefixWord ++ tailWord_140645) baseStart_140645 baseEnd_140645 := by
    simpa [prefixWord, tailWord_140645, baseEnd_140645] using wordTrace_append hprefix tailTrace_140645
  have hstable : (prefixWord ++ tailWord_140645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140645).length < 2 ^ (prefixWord ++ tailWord_140645).sum := by decide
  have hdescent : baseEnd_140645 < baseStart_140645 := by decide
  rcases family_descends (prefixWord ++ tailWord_140645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140649 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_140649 : Nat := 118140960795 + 140649 * 2 ^ 59
def prefixEnd_140649 : Nat := 4983230072969 + 3 ^ 40 * 140649 * 2
def baseEnd_140649 : Nat := 64196036066067061191709

theorem tailTrace_140649 : CollatzResearch.WordTrace tailWord_140649 prefixEnd_140649 64196036066067061191709 := by
  unfold tailWord_140649
  simp only [CollatzResearch.WordTrace]
  refine ⟨5129890467460168781905001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3419926978306779187936667 5129890467460168781905001)
  ·
    refine ⟨3847417850595126586428751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5129890467460168781905001 3847417850595126586428751)
    ·
      refine ⟨5771126775892689879643127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3847417850595126586428751 5771126775892689879643127)
      ·
        refine ⟨8656690163839034819464691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5771126775892689879643127 8656690163839034819464691)
        ·
          refine ⟨12985035245758552229197037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8656690163839034819464691 12985035245758552229197037)
          ·
            refine ⟨4869388217159457085948889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12985035245758552229197037 4869388217159457085948889)
            ·
              refine ⟨3652041162869592814461667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4869388217159457085948889 3652041162869592814461667)
              ·
                refine ⟨5478061744304389221692501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3652041162869592814461667 5478061744304389221692501)
                ·
                  refine ⟨64196036066067061191709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5478061744304389221692501 64196036066067061191709)
                  ·
                    rfl

theorem cell20_140649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_140649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140649 prefixEnd_140649 := by exact prefixLift 140649
  have htrace : WordTrace (prefixWord ++ tailWord_140649) baseStart_140649 baseEnd_140649 := by
    simpa [prefixWord, tailWord_140649, baseEnd_140649] using wordTrace_append hprefix tailTrace_140649
  have hstable : (prefixWord ++ tailWord_140649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140649).length < 2 ^ (prefixWord ++ tailWord_140649).sum := by decide
  have hdescent : baseEnd_140649 < baseStart_140649 := by decide
  rcases family_descends (prefixWord ++ tailWord_140649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140711 : List Nat := [1, 1, 6, 1, 1, 1, 9]
def baseStart_140711 : Nat := 118140960795 + 140711 * 2 ^ 59
def prefixEnd_140711 : Nat := 4983230072969 + 3 ^ 40 * 140711 * 2
def baseEnd_140711 : Nat := 7136037172830044569421

theorem tailTrace_140711 : CollatzResearch.WordTrace tailWord_140711 prefixEnd_140711 7136037172830044569421 := by
  unfold tailWord_140711
  simp only [CollatzResearch.WordTrace]
  refine ⟨5132151793235553370661987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3421434528823702247107991 5132151793235553370661987)
  ·
    refine ⟨7698227689853330055992981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5132151793235553370661987 7698227689853330055992981)
    ·
      refine ⟨360854422961874846374671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7698227689853330055992981 360854422961874846374671)
      ·
        refine ⟨541281634442812269562007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360854422961874846374671 541281634442812269562007)
        ·
          refine ⟨811922451664218404343011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541281634442812269562007 811922451664218404343011)
          ·
            refine ⟨1217883677496327606514517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811922451664218404343011 1217883677496327606514517)
            ·
              refine ⟨7136037172830044569421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1217883677496327606514517 7136037172830044569421)
              ·
                rfl

theorem cell20_140711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 9].length) (baseStart_140711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140711 prefixEnd_140711 := by exact prefixLift 140711
  have htrace : WordTrace (prefixWord ++ tailWord_140711) baseStart_140711 baseEnd_140711 := by
    simpa [prefixWord, tailWord_140711, baseEnd_140711] using wordTrace_append hprefix tailTrace_140711
  have hstable : (prefixWord ++ tailWord_140711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140711).length < 2 ^ (prefixWord ++ tailWord_140711).sum := by decide
  have hdescent : baseEnd_140711 < baseStart_140711 := by decide
  rcases family_descends (prefixWord ++ tailWord_140711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140721 : List Nat := [1, 2, 2, 4, 1, 1, 1, 6, 2]
def baseStart_140721 : Nat := 118140960795 + 140721 * 2 ^ 59
def prefixEnd_140721 : Nat := 4983230072969 + 3 ^ 40 * 140721 * 2
def baseEnd_140721 : Nat := 64228898827954810791415

theorem tailTrace_140721 : CollatzResearch.WordTrace tailWord_140721 prefixEnd_140721 64228898827954810791415 := by
  unfold tailWord_140721
  simp only [CollatzResearch.WordTrace]
  refine ⟨5132516523199325078526017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3421677682132883385684011 5132516523199325078526017)
  ·
    refine ⟨3849387392399493808894513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5132516523199325078526017 3849387392399493808894513)
    ·
      refine ⟨2887040544299620356670885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3849387392399493808894513 2887040544299620356670885)
      ·
        refine ⟨541320102056178816875791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2887040544299620356670885 541320102056178816875791)
        ·
          refine ⟨811980153084268225313687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541320102056178816875791 811980153084268225313687)
          ·
            refine ⟨1217970229626402337970531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811980153084268225313687 1217970229626402337970531)
            ·
              refine ⟨1826955344439603506955797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217970229626402337970531 1826955344439603506955797)
              ·
                refine ⟨85638531770606414388553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1826955344439603506955797 85638531770606414388553)
                ·
                  refine ⟨64228898827954810791415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85638531770606414388553 64228898827954810791415)
                  ·
                    rfl

theorem cell20_140721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_140721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140721 prefixEnd_140721 := by exact prefixLift 140721
  have htrace : WordTrace (prefixWord ++ tailWord_140721) baseStart_140721 baseEnd_140721 := by
    simpa [prefixWord, tailWord_140721, baseEnd_140721] using wordTrace_append hprefix tailTrace_140721
  have hstable : (prefixWord ++ tailWord_140721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140721).length < 2 ^ (prefixWord ++ tailWord_140721).sum := by decide
  have hdescent : baseEnd_140721 < baseStart_140721 := by decide
  rcases family_descends (prefixWord ++ tailWord_140721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140773 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 5]
def baseStart_140773 : Nat := 118140960795 + 140773 * 2 ^ 59
def prefixEnd_140773 : Nat := 4983230072969 + 3 ^ 40 * 140773 * 2
def baseEnd_140773 : Nat := 64252633044873741057869

theorem tailTrace_140773 : CollatzResearch.WordTrace tailWord_140773 prefixEnd_140773 64252633044873741057869 := by
  unfold tailWord_140773
  simp only [CollatzResearch.WordTrace]
  refine ⟨5134413119010937959418973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3422942079340625306279315 5134413119010937959418973)
  ·
    refine ⟨1925404919629101734782115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5134413119010937959418973 1925404919629101734782115)
    ·
      refine ⟨2888107379443652602173173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925404919629101734782115 2888107379443652602173173)
      ·
        refine ⟨270760066822842431453735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2888107379443652602173173 270760066822842431453735)
        ·
          refine ⟨406140100234263647180603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270760066822842431453735 406140100234263647180603)
          ·
            refine ⟨609210150351395470770905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406140100234263647180603 609210150351395470770905)
            ·
              refine ⟨456907612763546603078179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609210150351395470770905 456907612763546603078179)
              ·
                refine ⟨685361419145319904617269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456907612763546603078179 685361419145319904617269)
                ·
                  refine ⟨64252633044873741057869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 685361419145319904617269 64252633044873741057869)
                  ·
                    rfl

theorem cell20_140773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_140773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140773 prefixEnd_140773 := by exact prefixLift 140773
  have htrace : WordTrace (prefixWord ++ tailWord_140773) baseStart_140773 baseEnd_140773 := by
    simpa [prefixWord, tailWord_140773, baseEnd_140773] using wordTrace_append hprefix tailTrace_140773
  have hstable : (prefixWord ++ tailWord_140773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140773).length < 2 ^ (prefixWord ++ tailWord_140773).sum := by decide
  have hdescent : baseEnd_140773 < baseStart_140773 := by decide
  rcases family_descends (prefixWord ++ tailWord_140773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140776 : List Nat := [2, 1, 4, 1, 1, 2, 5, 2, 2]
def baseStart_140776 : Nat := 118140960795 + 140776 * 2 ^ 59
def prefixEnd_140776 : Nat := 4983230072969 + 3 ^ 40 * 140776 * 2
def baseEnd_140776 : Nat := 64254002326619063957857

theorem tailTrace_140776 : CollatzResearch.WordTrace tailWord_140776 prefixEnd_140776 64254002326619063957857 := by
  unfold tailWord_140776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2567261269000034735889091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3423015025333379647852121 2567261269000034735889091)
  ·
    refine ⟨3850891903500052103833637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2567261269000034735889091 3850891903500052103833637)
    ·
      refine ⟨722042231906259769468807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3850891903500052103833637 722042231906259769468807)
      ·
        refine ⟨1083063347859389654203211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722042231906259769468807 1083063347859389654203211)
        ·
          refine ⟨1624595021789084481304817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083063347859389654203211 1624595021789084481304817)
          ·
            refine ⟨1218446266341813360978613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1624595021789084481304817 1218446266341813360978613)
            ·
              refine ⟨114229337469545002591745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1218446266341813360978613 114229337469545002591745)
              ·
                refine ⟨85672003102158751943809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114229337469545002591745 85672003102158751943809)
                ·
                  refine ⟨64254002326619063957857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85672003102158751943809 64254002326619063957857)
                  ·
                    rfl

theorem cell20_140776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_140776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140776 prefixEnd_140776 := by exact prefixLift 140776
  have htrace : WordTrace (prefixWord ++ tailWord_140776) baseStart_140776 baseEnd_140776 := by
    simpa [prefixWord, tailWord_140776, baseEnd_140776] using wordTrace_append hprefix tailTrace_140776
  have hstable : (prefixWord ++ tailWord_140776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140776).length < 2 ^ (prefixWord ++ tailWord_140776).sum := by decide
  have hdescent : baseEnd_140776 < baseStart_140776 := by decide
  rcases family_descends (prefixWord ++ tailWord_140776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140790 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_140790 : Nat := 118140960795 + 140790 * 2 ^ 59
def prefixEnd_140790 : Nat := 4983230072969 + 3 ^ 40 * 140790 * 2
def baseEnd_140790 : Nat := 64260392308097237491133

theorem tailTrace_140790 : CollatzResearch.WordTrace tailWord_140790 prefixEnd_140790 64260392308097237491133 := by
  unfold tailWord_140790
  simp only [CollatzResearch.WordTrace]
  refine ⟨320939572496834366424239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3423355439966233241858549 320939572496834366424239)
  ·
    refine ⟨481409358745251549636359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320939572496834366424239 481409358745251549636359)
    ·
      refine ⟨722114038117877324454539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 481409358745251549636359 722114038117877324454539)
      ·
        refine ⟨1083171057176815986681809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722114038117877324454539 1083171057176815986681809)
        ·
          refine ⟨812378292882611990011357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1083171057176815986681809 812378292882611990011357)
          ·
            refine ⟨304641859830979496254259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 812378292882611990011357 304641859830979496254259)
            ·
              refine ⟨456962789746469244381389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304641859830979496254259 456962789746469244381389)
              ·
                refine ⟨171361046154925966643021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 456962789746469244381389 171361046154925966643021)
                ·
                  refine ⟨64260392308097237491133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171361046154925966643021 64260392308097237491133)
                  ·
                    rfl

theorem cell20_140790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_140790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140790 prefixEnd_140790 := by exact prefixLift 140790
  have htrace : WordTrace (prefixWord ++ tailWord_140790) baseStart_140790 baseEnd_140790 := by
    simpa [prefixWord, tailWord_140790, baseEnd_140790] using wordTrace_append hprefix tailTrace_140790
  have hstable : (prefixWord ++ tailWord_140790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140790).length < 2 ^ (prefixWord ++ tailWord_140790).sum := by decide
  have hdescent : baseEnd_140790 < baseStart_140790 := by decide
  rcases family_descends (prefixWord ++ tailWord_140790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140856 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_140856 : Nat := 118140960795 + 140856 * 2 ^ 59
def prefixEnd_140856 : Nat := 4983230072969 + 3 ^ 40 * 140856 * 2
def baseEnd_140856 : Nat := 64290516506494341290863

theorem tailTrace_140856 : CollatzResearch.WordTrace tailWord_140856 prefixEnd_140856 64290516506494341290863 := by
  unfold tailWord_140856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568720188855121567345211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3424960251806828756460281 2568720188855121567345211)
  ·
    refine ⟨3853080283282682351017817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2568720188855121567345211 3853080283282682351017817)
    ·
      refine ⟨2889810212462011763263363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3853080283282682351017817 2889810212462011763263363)
      ·
        refine ⟨4334715318693017644895045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889810212462011763263363 4334715318693017644895045)
        ·
          refine ⟨812759122254940808417821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4334715318693017644895045 812759122254940808417821)
          ·
            refine ⟨304784670845602803156683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 812759122254940808417821 304784670845602803156683)
            ·
              refine ⟨457177006268404204735025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304784670845602803156683 457177006268404204735025)
              ·
                refine ⟨342882754701303153551269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457177006268404204735025 342882754701303153551269)
                ·
                  refine ⟨64290516506494341290863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342882754701303153551269 64290516506494341290863)
                  ·
                    rfl

theorem cell20_140856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_140856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140856 prefixEnd_140856 := by exact prefixLift 140856
  have htrace : WordTrace (prefixWord ++ tailWord_140856) baseStart_140856 baseEnd_140856 := by
    simpa [prefixWord, tailWord_140856, baseEnd_140856] using wordTrace_append hprefix tailTrace_140856
  have hstable : (prefixWord ++ tailWord_140856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140856).length < 2 ^ (prefixWord ++ tailWord_140856).sum := by decide
  have hdescent : baseEnd_140856 < baseStart_140856 := by decide
  rcases family_descends (prefixWord ++ tailWord_140856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140887 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 3]
def baseStart_140887 : Nat := 118140960795 + 140887 * 2 ^ 59
def prefixEnd_140887 : Nat := 4983230072969 + 3 ^ 40 * 140887 * 2
def baseEnd_140887 : Nat := 64304665751196011257403

theorem tailTrace_140887 : CollatzResearch.WordTrace tailWord_140887 prefixEnd_140887 64304665751196011257403 := by
  unfold tailWord_140887
  simp only [CollatzResearch.WordTrace]
  refine ⟨5138571040597935429068915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3425714027065290286045943 5138571040597935429068915)
  ·
    refine ⟨7707856560896903143603373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5138571040597935429068915 7707856560896903143603373)
    ·
      refine ⟨2890446210336338678851265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7707856560896903143603373 2890446210336338678851265)
      ·
        refine ⟨2167834657752254009138449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2890446210336338678851265 2167834657752254009138449)
        ·
          refine ⟨1625875993314190506853837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2167834657752254009138449 1625875993314190506853837)
          ·
            refine ⟨609703497492821440070189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1625875993314190506853837 609703497492821440070189)
            ·
              refine ⟨228638811559808040026321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 609703497492821440070189 228638811559808040026321)
              ·
                refine ⟨171479108669856030019741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228638811559808040026321 171479108669856030019741)
                ·
                  refine ⟨64304665751196011257403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171479108669856030019741 64304665751196011257403)
                  ·
                    rfl

theorem cell20_140887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 3].length) (baseStart_140887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140887 prefixEnd_140887 := by exact prefixLift 140887
  have htrace : WordTrace (prefixWord ++ tailWord_140887) baseStart_140887 baseEnd_140887 := by
    simpa [prefixWord, tailWord_140887, baseEnd_140887] using wordTrace_append hprefix tailTrace_140887
  have hstable : (prefixWord ++ tailWord_140887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140887).length < 2 ^ (prefixWord ++ tailWord_140887).sum := by decide
  have hdescent : baseEnd_140887 < baseStart_140887 := by decide
  rcases family_descends (prefixWord ++ tailWord_140887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140918 : List Nat := [5, 1, 1, 2, 2, 2, 1, 6]
def baseStart_140918 : Nat := 118140960795 + 140918 * 2 ^ 59
def prefixEnd_140918 : Nat := 4983230072969 + 3 ^ 40 * 140918 * 2
def baseEnd_140918 : Nat := 21439604998632560407981

theorem tailTrace_140918 : CollatzResearch.WordTrace tailWord_140918 prefixEnd_140918 21439604998632560407981 := by
  unfold tailWord_140918
  simp only [CollatzResearch.WordTrace]
  refine ⟨321231356467851732715463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3426467802323751815631605 321231356467851732715463)
  ·
    refine ⟨481847034701777599073195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 321231356467851732715463 481847034701777599073195)
    ·
      refine ⟨722770552052666398609793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 481847034701777599073195 722770552052666398609793)
      ·
        refine ⟨542077914039499798957345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 722770552052666398609793 542077914039499798957345)
        ·
          refine ⟨406558435529624849218009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542077914039499798957345 406558435529624849218009)
          ·
            refine ⟨304918826647218636913507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406558435529624849218009 304918826647218636913507)
            ·
              refine ⟨457378239970827955370261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304918826647218636913507 457378239970827955370261)
              ·
                refine ⟨21439604998632560407981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 457378239970827955370261 21439604998632560407981)
                ·
                  rfl

theorem cell20_140918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_140918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140918 prefixEnd_140918 := by exact prefixLift 140918
  have htrace : WordTrace (prefixWord ++ tailWord_140918) baseStart_140918 baseEnd_140918 := by
    simpa [prefixWord, tailWord_140918, baseEnd_140918] using wordTrace_append hprefix tailTrace_140918
  have hstable : (prefixWord ++ tailWord_140918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140918).length < 2 ^ (prefixWord ++ tailWord_140918).sum := by decide
  have hdescent : baseEnd_140918 < baseStart_140918 := by decide
  rcases family_descends (prefixWord ++ tailWord_140918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140953 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_140953 : Nat := 118140960795 + 140953 * 2 ^ 59
def prefixEnd_140953 : Nat := 4983230072969 + 3 ^ 40 * 140953 * 2
def baseEnd_140953 : Nat := 64334789949593115057133

theorem tailTrace_140953 : CollatzResearch.WordTrace tailWord_140953 prefixEnd_140953 64334789949593115057133 := by
  unfold tailWord_140953
  simp only [CollatzResearch.WordTrace]
  refine ⟨5140978258358828700971513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3427318838905885800647675 5140978258358828700971513)
  ·
    refine ⟨3855733693769121525728635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5140978258358828700971513 3855733693769121525728635)
    ·
      refine ⟨5783600540653682288592953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3855733693769121525728635 5783600540653682288592953)
      ·
        refine ⟨4337700405490261716444715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5783600540653682288592953 4337700405490261716444715)
        ·
          refine ⟨6506550608235392574667073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4337700405490261716444715 6506550608235392574667073)
          ·
            refine ⟨4879912956176544431000305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6506550608235392574667073 4879912956176544431000305)
            ·
              refine ⟨3659934717132408323250229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4879912956176544431000305 3659934717132408323250229)
              ·
                refine ⟨343118879731163280304709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3659934717132408323250229 343118879731163280304709)
                ·
                  refine ⟨64334789949593115057133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343118879731163280304709 64334789949593115057133)
                  ·
                    rfl

theorem cell20_140953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_140953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140953 prefixEnd_140953 := by exact prefixLift 140953
  have htrace : WordTrace (prefixWord ++ tailWord_140953) baseStart_140953 baseEnd_140953 := by
    simpa [prefixWord, tailWord_140953, baseEnd_140953] using wordTrace_append hprefix tailTrace_140953
  have hstable : (prefixWord ++ tailWord_140953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140953).length < 2 ^ (prefixWord ++ tailWord_140953).sum := by decide
  have hdescent : baseEnd_140953 < baseStart_140953 := by decide
  rcases family_descends (prefixWord ++ tailWord_140953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140956 : List Nat := [2, 2, 3, 2, 3, 1, 2, 5]
def baseStart_140956 : Nat := 118140960795 + 140956 * 2 ^ 59
def prefixEnd_140956 : Nat := 4983230072969 + 3 ^ 40 * 140956 * 2
def baseEnd_140956 : Nat := 21445386410446145985707

theorem tailTrace_140956 : CollatzResearch.WordTrace tailWord_140956 prefixEnd_140956 21445386410446145985707 := by
  unfold tailWord_140956
  simp only [CollatzResearch.WordTrace]
  refine ⟨2570543838673980106665361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3427391784898640142220481 2570543838673980106665361)
  ·
    refine ⟨1927907879005485079999021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2570543838673980106665361 1927907879005485079999021)
    ·
      refine ⟨722965454627056904999633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1927907879005485079999021 722965454627056904999633)
      ·
        refine ⟨542224090970292678749725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 722965454627056904999633 542224090970292678749725)
        ·
          refine ⟨203334034113859754531147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 542224090970292678749725 203334034113859754531147)
          ·
            refine ⟨305001051170789631796721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203334034113859754531147 305001051170789631796721)
            ·
              refine ⟨228750788378092223847541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305001051170789631796721 228750788378092223847541)
              ·
                refine ⟨21445386410446145985707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228750788378092223847541 21445386410446145985707)
                ·
                  rfl

theorem cell20_140956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_140956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_140956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_140956 prefixEnd_140956 := by exact prefixLift 140956
  have htrace : WordTrace (prefixWord ++ tailWord_140956) baseStart_140956 baseEnd_140956 := by
    simpa [prefixWord, tailWord_140956, baseEnd_140956] using wordTrace_append hprefix tailTrace_140956
  have hstable : (prefixWord ++ tailWord_140956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140956).length < 2 ^ (prefixWord ++ tailWord_140956).sum := by decide
  have hdescent : baseEnd_140956 < baseStart_140956 := by decide
  rcases family_descends (prefixWord ++ tailWord_140956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141004 : List Nat := [2, 2, 1, 5, 2, 1, 1, 4, 2]
def baseStart_141004 : Nat := 118140960795 + 141004 * 2 ^ 59
def prefixEnd_141004 : Nat := 4983230072969 + 3 ^ 40 * 141004 * 2
def baseEnd_141004 : Nat := 64358067739263604356925

theorem tailTrace_141004 : CollatzResearch.WordTrace tailWord_141004 prefixEnd_141004 64358067739263604356925 := by
  unfold tailWord_141004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2571419190587032205539033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3428558920782709607385377 2571419190587032205539033)
  ·
    refine ⟨1928564392940274154154275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2571419190587032205539033 1928564392940274154154275)
    ·
      refine ⟨2892846589410411231231413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1928564392940274154154275 2892846589410411231231413)
      ·
        refine ⟨271204367757226052927945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2892846589410411231231413 271204367757226052927945)
        ·
          refine ⟨203403275817919539695959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271204367757226052927945 203403275817919539695959)
          ·
            refine ⟨305104913726879309543939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203403275817919539695959 305104913726879309543939)
            ·
              refine ⟨457657370590318964315909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305104913726879309543939 457657370590318964315909)
              ·
                refine ⟨85810756985684805809233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 457657370590318964315909 85810756985684805809233)
                ·
                  refine ⟨64358067739263604356925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85810756985684805809233 64358067739263604356925)
                  ·
                    rfl

theorem cell20_141004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_141004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141004 prefixEnd_141004 := by exact prefixLift 141004
  have htrace : WordTrace (prefixWord ++ tailWord_141004) baseStart_141004 baseEnd_141004 := by
    simpa [prefixWord, tailWord_141004, baseEnd_141004] using wordTrace_append hprefix tailTrace_141004
  have hstable : (prefixWord ++ tailWord_141004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141004).length < 2 ^ (prefixWord ++ tailWord_141004).sum := by decide
  have hdescent : baseEnd_141004 < baseStart_141004 := by decide
  rcases family_descends (prefixWord ++ tailWord_141004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141032 : List Nat := [2, 1, 4, 1, 3, 2, 3, 4]
def baseStart_141032 : Nat := 118140960795 + 141032 * 2 ^ 59
def prefixEnd_141032 : Nat := 4983230072969 + 3 ^ 40 * 141032 * 2
def baseEnd_141032 : Nat := 21456949234073317141159

theorem tailTrace_141032 : CollatzResearch.WordTrace tailWord_141032 prefixEnd_141032 21456949234073317141159 := by
  unfold tailWord_141032
  simp only [CollatzResearch.WordTrace]
  refine ⟨2571929812536312596548675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3429239750048416795398233 2571929812536312596548675)
  ·
    refine ⟨3857894718804468894823013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2571929812536312596548675 3857894718804468894823013)
    ·
      refine ⟨723355259775837917779315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3857894718804468894823013 723355259775837917779315)
      ·
        refine ⟨1085032889663756876668973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723355259775837917779315 1085032889663756876668973)
        ·
          refine ⟨406887333623908828750865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1085032889663756876668973 406887333623908828750865)
          ·
            refine ⟨305165500217931621563149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406887333623908828750865 305165500217931621563149)
            ·
              refine ⟨114437062581724358086181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305165500217931621563149 114437062581724358086181)
              ·
                refine ⟨21456949234073317141159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114437062581724358086181 21456949234073317141159)
                ·
                  rfl

theorem cell20_141032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_141032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141032 prefixEnd_141032 := by exact prefixLift 141032
  have htrace : WordTrace (prefixWord ++ tailWord_141032) baseStart_141032 baseEnd_141032 := by
    simpa [prefixWord, tailWord_141032, baseEnd_141032] using wordTrace_append hprefix tailTrace_141032
  have hstable : (prefixWord ++ tailWord_141032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141032).length < 2 ^ (prefixWord ++ tailWord_141032).sum := by decide
  have hdescent : baseEnd_141032 < baseStart_141032 := by decide
  rcases family_descends (prefixWord ++ tailWord_141032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141036 : List Nat := [2, 2, 1, 1, 2, 2, 2, 8]
def baseStart_141036 : Nat := 118140960795 + 141036 * 2 ^ 59
def prefixEnd_141036 : Nat := 4983230072969 + 3 ^ 40 * 141036 * 2
def baseEnd_141036 : Nat := 21457557803737905096709

theorem tailTrace_141036 : CollatzResearch.WordTrace tailWord_141036 prefixEnd_141036 21457557803737905096709 := by
  unfold tailWord_141036
  simp only [CollatzResearch.WordTrace]
  refine ⟨2572002758529066938121481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3429337011372089250828641 2572002758529066938121481)
  ·
    refine ⟨1929002068896800203591111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2572002758529066938121481 1929002068896800203591111)
    ·
      refine ⟨2893503103345200305386667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1929002068896800203591111 2893503103345200305386667)
      ·
        refine ⟨4340254655017800458080001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2893503103345200305386667 4340254655017800458080001)
        ·
          refine ⟨3255190991263350343560001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4340254655017800458080001 3255190991263350343560001)
          ·
            refine ⟨2441393243447512757670001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3255190991263350343560001 2441393243447512757670001)
            ·
              refine ⟨1831044932585634568252501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2441393243447512757670001 1831044932585634568252501)
              ·
                refine ⟨21457557803737905096709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1831044932585634568252501 21457557803737905096709)
                ·
                  rfl

theorem cell20_141036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_141036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141036 prefixEnd_141036 := by exact prefixLift 141036
  have htrace : WordTrace (prefixWord ++ tailWord_141036) baseStart_141036 baseEnd_141036 := by
    simpa [prefixWord, tailWord_141036, baseEnd_141036] using wordTrace_append hprefix tailTrace_141036
  have hstable : (prefixWord ++ tailWord_141036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141036).length < 2 ^ (prefixWord ++ tailWord_141036).sum := by decide
  have hdescent : baseEnd_141036 < baseStart_141036 := by decide
  rcases family_descends (prefixWord ++ tailWord_141036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141063 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 4]
def baseStart_141063 : Nat := 118140960795 + 141063 * 2 ^ 59
def prefixEnd_141063 : Nat := 4983230072969 + 3 ^ 40 * 141063 * 2
def baseEnd_141063 : Nat := 64384996946921621390017

theorem tailTrace_141063 : CollatzResearch.WordTrace tailWord_141063 prefixEnd_141063 64384996946921621390017 := by
  unfold tailWord_141063
  simp only [CollatzResearch.WordTrace]
  refine ⟨5144990287960317487475843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3429993525306878324983895 5144990287960317487475843)
  ·
    refine ⟨7717485431940476231213765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5144990287960317487475843 7717485431940476231213765)
    ·
      refine ⟨1447028518488839293352581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7717485431940476231213765 1447028518488839293352581)
      ·
        refine ⟨271317847216657367503609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1447028518488839293352581 271317847216657367503609)
        ·
          refine ⟨203488385412493025627707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271317847216657367503609 203488385412493025627707)
          ·
            refine ⟨305232578118739538441561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203488385412493025627707 305232578118739538441561)
            ·
              refine ⟨228924433589054653831171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305232578118739538441561 228924433589054653831171)
              ·
                refine ⟨343386650383581980746757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228924433589054653831171 343386650383581980746757)
                ·
                  refine ⟨64384996946921621390017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343386650383581980746757 64384996946921621390017)
                  ·
                    rfl

theorem cell20_141063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 4].length) (baseStart_141063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141063 prefixEnd_141063 := by exact prefixLift 141063
  have htrace : WordTrace (prefixWord ++ tailWord_141063) baseStart_141063 baseEnd_141063 := by
    simpa [prefixWord, tailWord_141063, baseEnd_141063] using wordTrace_append hprefix tailTrace_141063
  have hstable : (prefixWord ++ tailWord_141063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141063).length < 2 ^ (prefixWord ++ tailWord_141063).sum := by decide
  have hdescent : baseEnd_141063 < baseStart_141063 := by decide
  rcases family_descends (prefixWord ++ tailWord_141063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141067 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_141067 : Nat := 118140960795 + 141067 * 2 ^ 59
def prefixEnd_141067 : Nat := 4983230072969 + 3 ^ 40 * 141067 * 2
def baseEnd_141067 : Nat := 64386822655915385256667

theorem tailTrace_141067 : CollatzResearch.WordTrace tailWord_141067 prefixEnd_141067 64386822655915385256667 := by
  unfold tailWord_141067
  simp only [CollatzResearch.WordTrace]
  refine ⟨5145136179945826170621455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3430090786630550780414303 5145136179945826170621455)
  ·
    refine ⟨7717704269918739255932183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5145136179945826170621455 7717704269918739255932183)
    ·
      refine ⟨11576556404878108883898275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7717704269918739255932183 11576556404878108883898275)
      ·
        refine ⟨17364834607317163325847413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11576556404878108883898275 17364834607317163325847413)
        ·
          refine ⟨1627953244435984061798195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17364834607317163325847413 1627953244435984061798195)
          ·
            refine ⟨2441929866653976092697293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627953244435984061798195 2441929866653976092697293)
            ·
              refine ⟨915723699995241034761485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2441929866653976092697293 915723699995241034761485)
              ·
                refine ⟨343396387498215388035557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 915723699995241034761485 343396387498215388035557)
                ·
                  refine ⟨64386822655915385256667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343396387498215388035557 64386822655915385256667)
                  ·
                    rfl

theorem cell20_141067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_141067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141067 prefixEnd_141067 := by exact prefixLift 141067
  have htrace : WordTrace (prefixWord ++ tailWord_141067) baseStart_141067 baseEnd_141067 := by
    simpa [prefixWord, tailWord_141067, baseEnd_141067] using wordTrace_append hprefix tailTrace_141067
  have hstable : (prefixWord ++ tailWord_141067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141067).length < 2 ^ (prefixWord ++ tailWord_141067).sum := by decide
  have hdescent : baseEnd_141067 < baseStart_141067 := by decide
  rcases family_descends (prefixWord ++ tailWord_141067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141091 : List Nat := [1, 1, 1, 4, 2, 1, 6, 4]
def baseStart_141091 : Nat := 118140960795 + 141091 * 2 ^ 59
def prefixEnd_141091 : Nat := 4983230072969 + 3 ^ 40 * 141091 * 2
def baseEnd_141091 : Nat := 21465925636625989485523

theorem tailTrace_141091 : CollatzResearch.WordTrace tailWord_141091 prefixEnd_141091 21465925636625989485523 := by
  unfold tailWord_141091
  simp only [CollatzResearch.WordTrace]
  refine ⟨5146011531858878269495127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3430674354572585512996751 5146011531858878269495127)
  ·
    refine ⟨7719017297788317404242691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5146011531858878269495127 7719017297788317404242691)
    ·
      refine ⟨11578525946682476106364037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7719017297788317404242691 11578525946682476106364037)
      ·
        refine ⟨2170973615002964269943257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11578525946682476106364037 2170973615002964269943257)
        ·
          refine ⟨1628230211252223202457443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2170973615002964269943257 1628230211252223202457443)
          ·
            refine ⟨2442345316878334803686165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628230211252223202457443 2442345316878334803686165)
            ·
              refine ⟨114484936728671943922789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2442345316878334803686165 114484936728671943922789)
              ·
                refine ⟨21465925636625989485523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114484936728671943922789 21465925636625989485523)
                ·
                  rfl

theorem cell20_141091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 4].length) (baseStart_141091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141091 prefixEnd_141091 := by exact prefixLift 141091
  have htrace : WordTrace (prefixWord ++ tailWord_141091) baseStart_141091 baseEnd_141091 := by
    simpa [prefixWord, tailWord_141091, baseEnd_141091] using wordTrace_append hprefix tailTrace_141091
  have hstable : (prefixWord ++ tailWord_141091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141091).length < 2 ^ (prefixWord ++ tailWord_141091).sum := by decide
  have hdescent : baseEnd_141091 < baseStart_141091 := by decide
  rcases family_descends (prefixWord ++ tailWord_141091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141108 : List Nat := [2, 5, 1, 1, 2, 3, 6]
def baseStart_141108 : Nat := 118140960795 + 141108 * 2 ^ 59
def prefixEnd_141108 : Nat := 4983230072969 + 3 ^ 40 * 141108 * 2
def baseEnd_141108 : Nat := 7156170685900162765537

theorem tailTrace_141108 : CollatzResearch.WordTrace tailWord_141108 prefixEnd_141108 7156170685900162765537 := by
  unfold tailWord_141108
  simp only [CollatzResearch.WordTrace]
  refine ⟨2573315786398645086431989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3431087715198193448575985 2573315786398645086431989)
  ·
    refine ⟨241248354974872976852999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2573315786398645086431989 241248354974872976852999)
    ·
      refine ⟨361872532462309465279499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241248354974872976852999 361872532462309465279499)
      ·
        refine ⟨542808798693464197919249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361872532462309465279499 542808798693464197919249)
        ·
          refine ⟨407106599020098148439437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542808798693464197919249 407106599020098148439437)
          ·
            refine ⟨152664974632536805664789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 407106599020098148439437 152664974632536805664789)
            ·
              refine ⟨7156170685900162765537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 152664974632536805664789 7156170685900162765537)
              ·
                rfl

theorem cell20_141108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 6].length) (baseStart_141108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141108 prefixEnd_141108 := by exact prefixLift 141108
  have htrace : WordTrace (prefixWord ++ tailWord_141108) baseStart_141108 baseEnd_141108 := by
    simpa [prefixWord, tailWord_141108, baseEnd_141108] using wordTrace_append hprefix tailTrace_141108
  have hstable : (prefixWord ++ tailWord_141108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141108).length < 2 ^ (prefixWord ++ tailWord_141108).sum := by decide
  have hdescent : baseEnd_141108 < baseStart_141108 := by decide
  rcases family_descends (prefixWord ++ tailWord_141108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141112 : List Nat := [2, 1, 2, 1, 3, 3, 8]
def baseStart_141112 : Nat := 118140960795 + 141112 * 2 ^ 59
def prefixEnd_141112 : Nat := 4983230072969 + 3 ^ 40 * 141112 * 2
def baseEnd_141112 : Nat := 7156373542455025417387

theorem tailTrace_141112 : CollatzResearch.WordTrace tailWord_141112 prefixEnd_141112 7156373542455025417387 := by
  unfold tailWord_141112
  simp only [CollatzResearch.WordTrace]
  refine ⟨2573388732391399428004795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3431184976521865904006393 2573388732391399428004795)
  ·
    refine ⟨3860083098587099142007193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2573388732391399428004795 3860083098587099142007193)
    ·
      refine ⟨2895062323940324356505395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3860083098587099142007193 2895062323940324356505395)
      ·
        refine ⟨4342593485910486534758093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2895062323940324356505395 4342593485910486534758093)
        ·
          refine ⟨1628472557216432450534285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4342593485910486534758093 1628472557216432450534285)
          ·
            refine ⟨610677208956162168950357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1628472557216432450534285 610677208956162168950357)
            ·
              refine ⟨7156373542455025417387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 610677208956162168950357 7156373542455025417387)
              ·
                rfl

theorem cell20_141112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 8].length) (baseStart_141112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141112 prefixEnd_141112 := by exact prefixLift 141112
  have htrace : WordTrace (prefixWord ++ tailWord_141112) baseStart_141112 baseEnd_141112 := by
    simpa [prefixWord, tailWord_141112, baseEnd_141112] using wordTrace_append hprefix tailTrace_141112
  have hstable : (prefixWord ++ tailWord_141112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141112).length < 2 ^ (prefixWord ++ tailWord_141112).sum := by decide
  have hdescent : baseEnd_141112 < baseStart_141112 := by decide
  rcases family_descends (prefixWord ++ tailWord_141112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141181 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_141181 : Nat := 118140960795 + 141181 * 2 ^ 59
def prefixEnd_141181 : Nat := 4983230072969 + 3 ^ 40 * 141181 * 2
def baseEnd_141181 : Nat := 64438855362237655456201

theorem tailTrace_141181 : CollatzResearch.WordTrace tailWord_141181 prefixEnd_141181 64438855362237655456201 := by
  unfold tailWord_141181
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149294101532823640271397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3432862734355215760180931 5149294101532823640271397)
  ·
    refine ⟨965492644037404432550887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5149294101532823640271397 965492644037404432550887)
    ·
      refine ⟨1448238966056106648826331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 965492644037404432550887 1448238966056106648826331)
      ·
        refine ⟨2172358449084159973239497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448238966056106648826331 2172358449084159973239497)
        ·
          refine ⟨1629268836813119979929623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2172358449084159973239497 1629268836813119979929623)
          ·
            refine ⟨2443903255219679969894435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629268836813119979929623 2443903255219679969894435)
            ·
              refine ⟨3665854882829519954841653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443903255219679969894435 3665854882829519954841653)
              ·
                refine ⟨343673895265267495766405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3665854882829519954841653 343673895265267495766405)
                ·
                  refine ⟨64438855362237655456201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343673895265267495766405 64438855362237655456201)
                  ·
                    rfl

theorem cell20_141181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_141181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141181 prefixEnd_141181 := by exact prefixLift 141181
  have htrace : WordTrace (prefixWord ++ tailWord_141181) baseStart_141181 baseEnd_141181 := by
    simpa [prefixWord, tailWord_141181, baseEnd_141181] using wordTrace_append hprefix tailTrace_141181
  have hstable : (prefixWord ++ tailWord_141181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141181).length < 2 ^ (prefixWord ++ tailWord_141181).sum := by decide
  have hdescent : baseEnd_141181 < baseStart_141181 := by decide
  rcases family_descends (prefixWord ++ tailWord_141181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141195 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_141195 : Nat := 118140960795 + 141195 * 2 ^ 59
def prefixEnd_141195 : Nat := 4983230072969 + 3 ^ 40 * 141195 * 2
def baseEnd_141195 : Nat := 64445245343715828989477

theorem tailTrace_141195 : CollatzResearch.WordTrace tailWord_141195 prefixEnd_141195 64445245343715828989477 := by
  unfold tailWord_141195
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149804723482104031281039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3433203148988069354187359 5149804723482104031281039)
  ·
    refine ⟨7724707085223156046921559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5149804723482104031281039 7724707085223156046921559)
    ·
      refine ⟨11587060627834734070382339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7724707085223156046921559 11587060627834734070382339)
      ·
        refine ⟨17380590941752101105573509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11587060627834734070382339 17380590941752101105573509)
        ·
          refine ⟨3258860801578518957295033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17380590941752101105573509 3258860801578518957295033)
          ·
            refine ⟨2444145601183889217971275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3258860801578518957295033 2444145601183889217971275)
            ·
              refine ⟨3666218401775833826956913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2444145601183889217971275 3666218401775833826956913)
              ·
                refine ⟨2749663801331875370217685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3666218401775833826956913 2749663801331875370217685)
                ·
                  refine ⟨64445245343715828989477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2749663801331875370217685 64445245343715828989477)
                  ·
                    rfl

theorem cell20_141195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_141195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141195 prefixEnd_141195 := by exact prefixLift 141195
  have htrace : WordTrace (prefixWord ++ tailWord_141195) baseStart_141195 baseEnd_141195 := by
    simpa [prefixWord, tailWord_141195, baseEnd_141195] using wordTrace_append hprefix tailTrace_141195
  have hstable : (prefixWord ++ tailWord_141195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141195).length < 2 ^ (prefixWord ++ tailWord_141195).sum := by decide
  have hdescent : baseEnd_141195 < baseStart_141195 := by decide
  rcases family_descends (prefixWord ++ tailWord_141195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141205 : List Nat := [1, 3, 2, 1, 1, 3, 5, 4]
def baseStart_141205 : Nat := 118140960795 + 141205 * 2 ^ 59
def prefixEnd_141205 : Nat := 4983230072969 + 3 ^ 40 * 141205 * 2
def baseEnd_141205 : Nat := 21483269872066746218701

theorem tailTrace_141205 : CollatzResearch.WordTrace tailWord_141205 prefixEnd_141205 21483269872066746218701 := by
  unfold tailWord_141205
  simp only [CollatzResearch.WordTrace]
  refine ⟨5150169453445875739145069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3433446302297250492763379 5150169453445875739145069)
  ·
    refine ⟨1931313545042203402179401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5150169453445875739145069 1931313545042203402179401)
    ·
      refine ⟨1448485158781652551634551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1931313545042203402179401 1448485158781652551634551)
      ·
        refine ⟨2172727738172478827451827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448485158781652551634551 2172727738172478827451827)
        ·
          refine ⟨3259091607258718241177741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172727738172478827451827 3259091607258718241177741)
          ·
            refine ⟨1222159352722019340441653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3259091607258718241177741 1222159352722019340441653)
            ·
              refine ⟨114577439317689313166405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1222159352722019340441653 114577439317689313166405)
              ·
                refine ⟨21483269872066746218701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114577439317689313166405 21483269872066746218701)
                ·
                  rfl

theorem cell20_141205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 4].length) (baseStart_141205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141205 prefixEnd_141205 := by exact prefixLift 141205
  have htrace : WordTrace (prefixWord ++ tailWord_141205) baseStart_141205 baseEnd_141205 := by
    simpa [prefixWord, tailWord_141205, baseEnd_141205] using wordTrace_append hprefix tailTrace_141205
  have hstable : (prefixWord ++ tailWord_141205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141205).length < 2 ^ (prefixWord ++ tailWord_141205).sum := by decide
  have hdescent : baseEnd_141205 < baseStart_141205 := by decide
  rcases family_descends (prefixWord ++ tailWord_141205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141246 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_141246 : Nat := 118140960795 + 141246 * 2 ^ 59
def prefixEnd_141246 : Nat := 4983230072969 + 3 ^ 40 * 141246 * 2
def baseEnd_141246 : Nat := 64468523133386318289269

theorem tailTrace_141246 : CollatzResearch.WordTrace tailWord_141246 prefixEnd_141246 64468523133386318289269 := by
  unfold tailWord_141246
  simp only [CollatzResearch.WordTrace]
  refine ⟨643958105787167467673449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3434443230864893160925061 643958105787167467673449)
  ·
    refine ⟨482968579340375600755087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 643958105787167467673449 482968579340375600755087)
    ·
      refine ⟨724452869010563401132631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482968579340375600755087 724452869010563401132631)
      ·
        refine ⟨1086679303515845101698947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724452869010563401132631 1086679303515845101698947)
        ·
          refine ⟨1630018955273767652548421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086679303515845101698947 1630018955273767652548421)
          ·
            refine ⟨305628554113831434852829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1630018955273767652548421 305628554113831434852829)
            ·
              refine ⟨114610707792686788069811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305628554113831434852829 114610707792686788069811)
              ·
                refine ⟨171916061689030182104717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114610707792686788069811 171916061689030182104717)
                ·
                  refine ⟨64468523133386318289269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171916061689030182104717 64468523133386318289269)
                  ·
                    rfl

theorem cell20_141246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_141246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141246 prefixEnd_141246 := by exact prefixLift 141246
  have htrace : WordTrace (prefixWord ++ tailWord_141246) baseStart_141246 baseEnd_141246 := by
    simpa [prefixWord, tailWord_141246, baseEnd_141246] using wordTrace_append hprefix tailTrace_141246
  have hstable : (prefixWord ++ tailWord_141246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141246).length < 2 ^ (prefixWord ++ tailWord_141246).sum := by decide
  have hdescent : baseEnd_141246 < baseStart_141246 := by decide
  rcases family_descends (prefixWord ++ tailWord_141246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141260 : List Nat := [2, 2, 1, 4, 1, 4, 2, 4]
def baseStart_141260 : Nat := 118140960795 + 141260 * 2 ^ 59
def prefixEnd_141260 : Nat := 4983230072969 + 3 ^ 40 * 141260 * 2
def baseEnd_141260 : Nat := 21491637704954830607515

theorem tailTrace_141260 : CollatzResearch.WordTrace tailWord_141260 prefixEnd_141260 21491637704954830607515 := by
  unfold tailWord_141260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2576087734123310066198617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3434783645497746754931489 2576087734123310066198617)
  ·
    refine ⟨1932065800592482549648963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2576087734123310066198617 1932065800592482549648963)
    ·
      refine ⟨2898098700888723824473445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1932065800592482549648963 2898098700888723824473445)
      ·
        refine ⟨543393506416635717088771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2898098700888723824473445 543393506416635717088771)
        ·
          refine ⟨815090259624953575633157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543393506416635717088771 815090259624953575633157)
          ·
            refine ⟨152829423679678795431217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 815090259624953575633157 152829423679678795431217)
            ·
              refine ⟨114622067759759096573413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152829423679678795431217 114622067759759096573413)
              ·
                refine ⟨21491637704954830607515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114622067759759096573413 21491637704954830607515)
                ·
                  rfl

theorem cell20_141260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_141260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141260 prefixEnd_141260 := by exact prefixLift 141260
  have htrace : WordTrace (prefixWord ++ tailWord_141260) baseStart_141260 baseEnd_141260 := by
    simpa [prefixWord, tailWord_141260, baseEnd_141260] using wordTrace_append hprefix tailTrace_141260
  have hstable : (prefixWord ++ tailWord_141260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141260).length < 2 ^ (prefixWord ++ tailWord_141260).sum := by decide
  have hdescent : baseEnd_141260 < baseStart_141260 := by decide
  rcases family_descends (prefixWord ++ tailWord_141260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141271 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_141271 : Nat := 118140960795 + 141271 * 2 ^ 59
def prefixEnd_141271 : Nat := 4983230072969 + 3 ^ 40 * 141271 * 2
def baseEnd_141271 : Nat := 64479933814597342455833

theorem tailTrace_141271 : CollatzResearch.WordTrace tailWord_141271 prefixEnd_141271 64479933814597342455833 := by
  unfold tailWord_141271
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152576671206769011047667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3435051114137846007365111 5152576671206769011047667)
  ·
    refine ⟨7728865006810153516571501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5152576671206769011047667 7728865006810153516571501)
    ·
      refine ⟨2898324377553807568714313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7728865006810153516571501 2898324377553807568714313)
      ·
        refine ⟨2173743283165355676535735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2898324377553807568714313 2173743283165355676535735)
        ·
          refine ⟨3260614924748033514803603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173743283165355676535735 3260614924748033514803603)
          ·
            refine ⟨4890922387122050272205405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3260614924748033514803603 4890922387122050272205405)
            ·
              refine ⟨1834095895170768852077027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4890922387122050272205405 1834095895170768852077027)
              ·
                refine ⟨2751143842756153278115541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1834095895170768852077027 2751143842756153278115541)
                ·
                  refine ⟨64479933814597342455833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2751143842756153278115541 64479933814597342455833)
                  ·
                    rfl

theorem cell20_141271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_141271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141271 prefixEnd_141271 := by exact prefixLift 141271
  have htrace : WordTrace (prefixWord ++ tailWord_141271) baseStart_141271 baseEnd_141271 := by
    simpa [prefixWord, tailWord_141271, baseEnd_141271] using wordTrace_append hprefix tailTrace_141271
  have hstable : (prefixWord ++ tailWord_141271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141271).length < 2 ^ (prefixWord ++ tailWord_141271).sum := by decide
  have hdescent : baseEnd_141271 < baseStart_141271 := by decide
  rcases family_descends (prefixWord ++ tailWord_141271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141288 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 3]
def baseStart_141288 : Nat := 118140960795 + 141288 * 2 ^ 59
def prefixEnd_141288 : Nat := 4983230072969 + 3 ^ 40 * 141288 * 2
def baseEnd_141288 : Nat := 64487693077820838889097

theorem tailTrace_141288 : CollatzResearch.WordTrace tailWord_141288 prefixEnd_141288 64487693077820838889097 := by
  unfold tailWord_141288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2576598356072590457208259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3435464474763453942944345 2576598356072590457208259)
  ·
    refine ⟨3864897534108885685812389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2576598356072590457208259 3864897534108885685812389)
    ·
      refine ⟨724668287645416066089823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3864897534108885685812389 724668287645416066089823)
      ·
        refine ⟨1087002431468124099134735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724668287645416066089823 1087002431468124099134735)
        ·
          refine ⟨1630503647202186148702103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087002431468124099134735 1630503647202186148702103)
          ·
            refine ⟨2445755470803279223053155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630503647202186148702103 2445755470803279223053155)
            ·
              refine ⟨3668633206204918834579733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445755470803279223053155 3668633206204918834579733)
              ·
                refine ⟨171967181540855570370925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3668633206204918834579733 171967181540855570370925)
                ·
                  refine ⟨64487693077820838889097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171967181540855570370925 64487693077820838889097)
                  ·
                    rfl

theorem cell20_141288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_141288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141288 prefixEnd_141288 := by exact prefixLift 141288
  have htrace : WordTrace (prefixWord ++ tailWord_141288) baseStart_141288 baseEnd_141288 := by
    simpa [prefixWord, tailWord_141288, baseEnd_141288] using wordTrace_append hprefix tailTrace_141288
  have hstable : (prefixWord ++ tailWord_141288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141288).length < 2 ^ (prefixWord ++ tailWord_141288).sum := by decide
  have hdescent : baseEnd_141288 < baseStart_141288 := by decide
  rcases family_descends (prefixWord ++ tailWord_141288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141305 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 3]
def baseStart_141305 : Nat := 118140960795 + 141305 * 2 ^ 59
def prefixEnd_141305 : Nat := 4983230072969 + 3 ^ 40 * 141305 * 2
def baseEnd_141305 : Nat := 64495452341044335322361

theorem tailTrace_141305 : CollatzResearch.WordTrace tailWord_141305 prefixEnd_141305 64495452341044335322361 := by
  unfold tailWord_141305
  simp only [CollatzResearch.WordTrace]
  refine ⟨5153816753083592817785369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3435877835389061878523579 5153816753083592817785369)
  ·
    refine ⟨3865362564812694613339027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5153816753083592817785369 3865362564812694613339027)
    ·
      refine ⟨5798043847219041920008541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3865362564812694613339027 5798043847219041920008541)
      ·
        refine ⟨2174266442707140720003203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5798043847219041920008541 2174266442707140720003203)
        ·
          refine ⟨3261399664060711080004805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2174266442707140720003203 3261399664060711080004805)
          ·
            refine ⟨611512437011383327500901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3261399664060711080004805 611512437011383327500901)
            ·
              refine ⟨114658581939634373906419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 611512437011383327500901 114658581939634373906419)
              ·
                refine ⟨171987872909451560859629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114658581939634373906419 171987872909451560859629)
                ·
                  refine ⟨64495452341044335322361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171987872909451560859629 64495452341044335322361)
                  ·
                    rfl

theorem cell20_141305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_141305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141305 prefixEnd_141305 := by exact prefixLift 141305
  have htrace : WordTrace (prefixWord ++ tailWord_141305) baseStart_141305 baseEnd_141305 := by
    simpa [prefixWord, tailWord_141305, baseEnd_141305] using wordTrace_append hprefix tailTrace_141305
  have hstable : (prefixWord ++ tailWord_141305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141305).length < 2 ^ (prefixWord ++ tailWord_141305).sum := by decide
  have hdescent : baseEnd_141305 < baseStart_141305 := by decide
  rcases family_descends (prefixWord ++ tailWord_141305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141340 : List Nat := [2, 2, 3, 1, 3, 9]
def baseStart_141340 : Nat := 118140960795 + 141340 * 2 ^ 59
def prefixEnd_141340 : Nat := 4983230072969 + 3 ^ 40 * 141340 * 2
def baseEnd_141340 : Nat := 2389312122027398857613

theorem tailTrace_141340 : CollatzResearch.WordTrace tailWord_141340 prefixEnd_141340 2389312122027398857613 := by
  unfold tailWord_141340
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577546653978396897654737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3436728871971195863539649 2577546653978396897654737)
  ·
    refine ⟨1933159990483797673241053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2577546653978396897654737 1933159990483797673241053)
    ·
      refine ⟨724934996431424127465395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1933159990483797673241053 724934996431424127465395)
      ·
        refine ⟨1087402494647136191198093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724934996431424127465395 1087402494647136191198093)
        ·
          refine ⟨407775935492676071699285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1087402494647136191198093 407775935492676071699285)
          ·
            refine ⟨2389312122027398857613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 407775935492676071699285 2389312122027398857613)
            ·
              rfl

theorem cell20_141340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 9].length) (baseStart_141340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141340 prefixEnd_141340 := by exact prefixLift 141340
  have htrace : WordTrace (prefixWord ++ tailWord_141340) baseStart_141340 baseEnd_141340 := by
    simpa [prefixWord, tailWord_141340, baseEnd_141340] using wordTrace_append hprefix tailTrace_141340
  have hstable : (prefixWord ++ tailWord_141340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141340).length < 2 ^ (prefixWord ++ tailWord_141340).sum := by decide
  have hdescent : baseEnd_141340 < baseStart_141340 := by decide
  rcases family_descends (prefixWord ++ tailWord_141340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141385 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_141385 : Nat := 118140960795 + 141385 * 2 ^ 59
def prefixEnd_141385 : Nat := 4983230072969 + 3 ^ 40 * 141385 * 2
def baseEnd_141385 : Nat := 64531966520919612655367

theorem tailTrace_141385 : CollatzResearch.WordTrace tailWord_141385 prefixEnd_141385 64531966520919612655367 := by
  unfold tailWord_141385
  simp only [CollatzResearch.WordTrace]
  refine ⟨5156734592793766480697609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3437823061862510987131739 5156734592793766480697609)
  ·
    refine ⟨3867550944595324860523207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5156734592793766480697609 3867550944595324860523207)
    ·
      refine ⟨5801326416892987290784811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867550944595324860523207 5801326416892987290784811)
      ·
        refine ⟨8701989625339480936177217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5801326416892987290784811 8701989625339480936177217)
        ·
          refine ⟨6526492219004610702132913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8701989625339480936177217 6526492219004610702132913)
          ·
            refine ⟨4894869164253458026599685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6526492219004610702132913 4894869164253458026599685)
            ·
              refine ⟨917787968297523379987441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4894869164253458026599685 917787968297523379987441)
              ·
                refine ⟨688340976223142534990581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917787968297523379987441 688340976223142534990581)
                ·
                  refine ⟨64531966520919612655367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 688340976223142534990581 64531966520919612655367)
                  ·
                    rfl

theorem cell20_141385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_141385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141385 prefixEnd_141385 := by exact prefixLift 141385
  have htrace : WordTrace (prefixWord ++ tailWord_141385) baseStart_141385 baseEnd_141385 := by
    simpa [prefixWord, tailWord_141385, baseEnd_141385] using wordTrace_append hprefix tailTrace_141385
  have hstable : (prefixWord ++ tailWord_141385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141385).length < 2 ^ (prefixWord ++ tailWord_141385).sum := by decide
  have hdescent : baseEnd_141385 < baseStart_141385 := by decide
  rcases family_descends (prefixWord ++ tailWord_141385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141388 : List Nat := [2, 2, 1, 3, 1, 1, 3, 5, 2]
def baseStart_141388 : Nat := 118140960795 + 141388 * 2 ^ 59
def prefixEnd_141388 : Nat := 4983230072969 + 3 ^ 40 * 141388 * 2
def baseEnd_141388 : Nat := 64533335802664935555355

theorem tailTrace_141388 : CollatzResearch.WordTrace tailWord_141388 prefixEnd_141388 64533335802664935555355 := by
  unfold tailWord_141388
  simp only [CollatzResearch.WordTrace]
  refine ⟨2578422005891448996528409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3437896007855265328704545 2578422005891448996528409)
  ·
    refine ⟨1933816504418586747396307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2578422005891448996528409 1933816504418586747396307)
    ·
      refine ⟨2900724756627880121094461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1933816504418586747396307 2900724756627880121094461)
      ·
        refine ⟨1087771783735455045410423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2900724756627880121094461 1087771783735455045410423)
        ·
          refine ⟨1631657675603182568115635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087771783735455045410423 1631657675603182568115635)
          ·
            refine ⟨2447486513404773852173453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631657675603182568115635 2447486513404773852173453)
            ·
              refine ⟨917807442526790194565045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2447486513404773852173453 917807442526790194565045)
              ·
                refine ⟨86044447736886580740473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 917807442526790194565045 86044447736886580740473)
                ·
                  refine ⟨64533335802664935555355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86044447736886580740473 64533335802664935555355)
                  ·
                    rfl

theorem cell20_141388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_141388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141388 prefixEnd_141388 := by exact prefixLift 141388
  have htrace : WordTrace (prefixWord ++ tailWord_141388) baseStart_141388 baseEnd_141388 := by
    simpa [prefixWord, tailWord_141388, baseEnd_141388] using wordTrace_append hprefix tailTrace_141388
  have hstable : (prefixWord ++ tailWord_141388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141388).length < 2 ^ (prefixWord ++ tailWord_141388).sum := by decide
  have hdescent : baseEnd_141388 < baseStart_141388 := by decide
  rcases family_descends (prefixWord ++ tailWord_141388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141398 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_141398 : Nat := 118140960795 + 141398 * 2 ^ 59
def prefixEnd_141398 : Nat := 4983230072969 + 3 ^ 40 * 141398 * 2
def baseEnd_141398 : Nat := 64537900075149345221981

theorem tailTrace_141398 : CollatzResearch.WordTrace tailWord_141398 prefixEnd_141398 64537900075149345221981 := by
  unfold tailWord_141398
  simp only [CollatzResearch.WordTrace]
  refine ⟨322325546359166856307553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3438139161164446467280565 322325546359166856307553)
  ·
    refine ⟨241744159769375142230665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 322325546359166856307553 241744159769375142230665)
    ·
      refine ⟨181308119827031356672999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241744159769375142230665 181308119827031356672999)
      ·
        refine ⟨271962179740547035009499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181308119827031356672999 271962179740547035009499)
        ·
          refine ⟨407943269610820552514249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271962179740547035009499 407943269610820552514249)
          ·
            refine ⟨305957452208115414385687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407943269610820552514249 305957452208115414385687)
            ·
              refine ⟨458936178312173121578531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305957452208115414385687 458936178312173121578531)
              ·
                refine ⟨688404267468259682367797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458936178312173121578531 688404267468259682367797)
                ·
                  refine ⟨64537900075149345221981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 688404267468259682367797 64537900075149345221981)
                  ·
                    rfl

theorem cell20_141398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_141398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141398 prefixEnd_141398 := by exact prefixLift 141398
  have htrace : WordTrace (prefixWord ++ tailWord_141398) baseStart_141398 baseEnd_141398 := by
    simpa [prefixWord, tailWord_141398, baseEnd_141398] using wordTrace_append hprefix tailTrace_141398
  have hstable : (prefixWord ++ tailWord_141398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141398).length < 2 ^ (prefixWord ++ tailWord_141398).sum := by decide
  have hdescent : baseEnd_141398 < baseStart_141398 := by decide
  rcases family_descends (prefixWord ++ tailWord_141398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141405 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 4]
def baseStart_141405 : Nat := 118140960795 + 141405 * 2 ^ 59
def prefixEnd_141405 : Nat := 4983230072969 + 3 ^ 40 * 141405 * 2
def baseEnd_141405 : Nat := 64541095065888431988619

theorem tailTrace_141405 : CollatzResearch.WordTrace tailWord_141405 prefixEnd_141405 64541095065888431988619 := by
  unfold tailWord_141405
  simp only [CollatzResearch.WordTrace]
  refine ⟨5157464052721309896425669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3438309368480873264283779 5157464052721309896425669)
  ·
    refine ⟨967024509885245605579813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5157464052721309896425669 967024509885245605579813)
    ·
      refine ⟨181317095603483551046215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 967024509885245605579813 181317095603483551046215)
      ·
        refine ⟨271975643405225326569323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181317095603483551046215 271975643405225326569323)
        ·
          refine ⟨407963465107837989853985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271975643405225326569323 407963465107837989853985)
          ·
            refine ⟨305972598830878492390489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407963465107837989853985 305972598830878492390489)
            ·
              refine ⟨229479449123158869292867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305972598830878492390489 229479449123158869292867)
              ·
                refine ⟨344219173684738303939301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229479449123158869292867 344219173684738303939301)
                ·
                  refine ⟨64541095065888431988619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344219173684738303939301 64541095065888431988619)
                  ·
                    rfl

theorem cell20_141405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_141405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141405 prefixEnd_141405 := by exact prefixLift 141405
  have htrace : WordTrace (prefixWord ++ tailWord_141405) baseStart_141405 baseEnd_141405 := by
    simpa [prefixWord, tailWord_141405, baseEnd_141405] using wordTrace_append hprefix tailTrace_141405
  have hstable : (prefixWord ++ tailWord_141405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141405).length < 2 ^ (prefixWord ++ tailWord_141405).sum := by decide
  have hdescent : baseEnd_141405 < baseStart_141405 := by decide
  rcases family_descends (prefixWord ++ tailWord_141405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141433 : List Nat := [1, 2, 1, 3, 4, 1, 4, 4]
def baseStart_141433 : Nat := 118140960795 + 141433 * 2 ^ 59
def prefixEnd_141433 : Nat := 4983230072969 + 3 ^ 40 * 141433 * 2
def baseEnd_141433 : Nat := 21517958342948259685057

theorem tailTrace_141433 : CollatzResearch.WordTrace tailWord_141433 prefixEnd_141433 21517958342948259685057 := by
  unfold tailWord_141433
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158485296619870678444953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3438990197746580452296635 5158485296619870678444953)
  ·
    refine ⟨3868863972464903008833715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5158485296619870678444953 3868863972464903008833715)
    ·
      refine ⟨5803295958697354513250573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3868863972464903008833715 5803295958697354513250573)
      ·
        refine ⟨2176235984511507942468965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5803295958697354513250573 2176235984511507942468965)
        ·
          refine ⟨408044247095907739212931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2176235984511507942468965 408044247095907739212931)
          ·
            refine ⟨612066370643861608819397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408044247095907739212931 612066370643861608819397)
            ·
              refine ⟨114762444495724051653637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 612066370643861608819397 114762444495724051653637)
              ·
                refine ⟨21517958342948259685057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114762444495724051653637 21517958342948259685057)
                ·
                  rfl

theorem cell20_141433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 4].length) (baseStart_141433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141433 prefixEnd_141433 := by exact prefixLift 141433
  have htrace : WordTrace (prefixWord ++ tailWord_141433) baseStart_141433 baseEnd_141433 := by
    simpa [prefixWord, tailWord_141433, baseEnd_141433] using wordTrace_append hprefix tailTrace_141433
  have hstable : (prefixWord ++ tailWord_141433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141433).length < 2 ^ (prefixWord ++ tailWord_141433).sum := by decide
  have hdescent : baseEnd_141433 < baseStart_141433 := by decide
  rcases family_descends (prefixWord ++ tailWord_141433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141443 : List Nat := [1, 1, 1, 3, 3, 5, 1, 3, 2]
def baseStart_141443 : Nat := 118140960795 + 141443 * 2 ^ 59
def prefixEnd_141443 : Nat := 4983230072969 + 3 ^ 40 * 141443 * 2
def baseEnd_141443 : Nat := 64558439301329188721797

theorem tailTrace_141443 : CollatzResearch.WordTrace tailWord_141443 prefixEnd_141443 64558439301329188721797 := by
  unfold tailWord_141443
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158850026583642386308983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3439233351055761590872655 5158850026583642386308983)
  ·
    refine ⟨7738275039875463579463475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5158850026583642386308983 7738275039875463579463475)
    ·
      refine ⟨11607412559813195369195213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7738275039875463579463475 11607412559813195369195213)
      ·
        refine ⟨4352779709929948263448205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11607412559813195369195213 4352779709929948263448205)
        ·
          refine ⟨1632292391223730598793077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4352779709929948263448205 1632292391223730598793077)
          ·
            refine ⟨153027411677224743636851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1632292391223730598793077 153027411677224743636851)
            ·
              refine ⟨229541117515837115455277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153027411677224743636851 229541117515837115455277)
              ·
                refine ⟨86077919068438918295729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229541117515837115455277 86077919068438918295729)
                ·
                  refine ⟨64558439301329188721797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86077919068438918295729 64558439301329188721797)
                  ·
                    rfl

theorem cell20_141443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 2].length) (baseStart_141443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141443 prefixEnd_141443 := by exact prefixLift 141443
  have htrace : WordTrace (prefixWord ++ tailWord_141443) baseStart_141443 baseEnd_141443 := by
    simpa [prefixWord, tailWord_141443, baseEnd_141443] using wordTrace_append hprefix tailTrace_141443
  have hstable : (prefixWord ++ tailWord_141443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141443).length < 2 ^ (prefixWord ++ tailWord_141443).sum := by decide
  have hdescent : baseEnd_141443 < baseStart_141443 := by decide
  rcases family_descends (prefixWord ++ tailWord_141443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141460 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 4]
def baseStart_141460 : Nat := 118140960795 + 141460 * 2 ^ 59
def prefixEnd_141460 : Nat := 4983230072969 + 3 ^ 40 * 141460 * 2
def baseEnd_141460 : Nat := 64566198564552685155061

theorem tailTrace_141460 : CollatzResearch.WordTrace tailWord_141460 prefixEnd_141460 64566198564552685155061 := by
  unfold tailWord_141460
  simp only [CollatzResearch.WordTrace]
  refine ⟨2579735033761027144838917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3439646711681369526451889 2579735033761027144838917)
  ·
    refine ⟨483700318830192589657297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2579735033761027144838917 483700318830192589657297)
    ·
      refine ⟨362775239122644442242973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 483700318830192589657297 362775239122644442242973)
      ·
        refine ⟨136040714670991665841115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362775239122644442242973 136040714670991665841115)
        ·
          refine ⟨204061072006487498761673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136040714670991665841115 204061072006487498761673)
          ·
            refine ⟨153045804004865624071255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204061072006487498761673 153045804004865624071255)
            ·
              refine ⟨229568706007298436106883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153045804004865624071255 229568706007298436106883)
              ·
                refine ⟨344353059010947654160325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229568706007298436106883 344353059010947654160325)
                ·
                  refine ⟨64566198564552685155061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344353059010947654160325 64566198564552685155061)
                  ·
                    rfl

theorem cell20_141460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_141460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141460 prefixEnd_141460 := by exact prefixLift 141460
  have htrace : WordTrace (prefixWord ++ tailWord_141460) baseStart_141460 baseEnd_141460 := by
    simpa [prefixWord, tailWord_141460, baseEnd_141460] using wordTrace_append hprefix tailTrace_141460
  have hstable : (prefixWord ++ tailWord_141460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141460).length < 2 ^ (prefixWord ++ tailWord_141460).sum := by decide
  have hdescent : baseEnd_141460 < baseStart_141460 := by decide
  rcases family_descends (prefixWord ++ tailWord_141460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141461 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_141461 : Nat := 118140960795 + 141461 * 2 ^ 59
def prefixEnd_141461 : Nat := 4983230072969 + 3 ^ 40 * 141461 * 2
def baseEnd_141461 : Nat := 64566654991801126121723

theorem tailTrace_141461 : CollatzResearch.WordTrace tailWord_141461 prefixEnd_141461 64566654991801126121723 := by
  unfold tailWord_141461
  simp only [CollatzResearch.WordTrace]
  refine ⟨5159506540518431460464237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3439671027012287640309491 5159506540518431460464237)
  ·
    refine ⟨1934814952694411797674089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5159506540518431460464237 1934814952694411797674089)
    ·
      refine ⟨1451111214520808848255567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1934814952694411797674089 1451111214520808848255567)
      ·
        refine ⟨2176666821781213272383351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451111214520808848255567 2176666821781213272383351)
        ·
          refine ⟨3265000232671819908575027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2176666821781213272383351 3265000232671819908575027)
          ·
            refine ⟨4897500349007729862862541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3265000232671819908575027 4897500349007729862862541)
            ·
              refine ⟨1836562630877898698573453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4897500349007729862862541 1836562630877898698573453)
              ·
                refine ⟨688710986579212011965045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1836562630877898698573453 688710986579212011965045)
                ·
                  refine ⟨64566654991801126121723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 688710986579212011965045 64566654991801126121723)
                  ·
                    rfl

theorem cell20_141461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_141461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141461 prefixEnd_141461 := by exact prefixLift 141461
  have htrace : WordTrace (prefixWord ++ tailWord_141461) baseStart_141461 baseEnd_141461 := by
    simpa [prefixWord, tailWord_141461, baseEnd_141461] using wordTrace_append hprefix tailTrace_141461
  have hstable : (prefixWord ++ tailWord_141461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141461).length < 2 ^ (prefixWord ++ tailWord_141461).sum := by decide
  have hdescent : baseEnd_141461 < baseStart_141461 := by decide
  rcases family_descends (prefixWord ++ tailWord_141461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141470 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_141470 : Nat := 118140960795 + 141470 * 2 ^ 59
def prefixEnd_141470 : Nat := 4983230072969 + 3 ^ 40 * 141470 * 2
def baseEnd_141470 : Nat := 64570762837037094821687

theorem tailTrace_141470 : CollatzResearch.WordTrace tailWord_141470 prefixEnd_141470 64570762837037094821687 := by
  unfold tailWord_141470
  simp only [CollatzResearch.WordTrace]
  refine ⟨644979349685728249692733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3439889864990550665027909 644979349685728249692733)
  ·
    refine ⟨241867256132148093634775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 644979349685728249692733 241867256132148093634775)
    ·
      refine ⟨362800884198222140452163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241867256132148093634775 362800884198222140452163)
      ·
        refine ⟨544201326297333210678245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362800884198222140452163 544201326297333210678245)
        ·
          refine ⟨102037748680749977002171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 544201326297333210678245 102037748680749977002171)
          ·
            refine ⟨153056623021124965503257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102037748680749977002171 153056623021124965503257)
            ·
              refine ⟨114792467265843724127443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153056623021124965503257 114792467265843724127443)
              ·
                refine ⟨172188700898765586191165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114792467265843724127443 172188700898765586191165)
                ·
                  refine ⟨64570762837037094821687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172188700898765586191165 64570762837037094821687)
                  ·
                    rfl

theorem cell20_141470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_141470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141470 prefixEnd_141470 := by exact prefixLift 141470
  have htrace : WordTrace (prefixWord ++ tailWord_141470) baseStart_141470 baseEnd_141470 := by
    simpa [prefixWord, tailWord_141470, baseEnd_141470] using wordTrace_append hprefix tailTrace_141470
  have hstable : (prefixWord ++ tailWord_141470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141470).length < 2 ^ (prefixWord ++ tailWord_141470).sum := by decide
  have hdescent : baseEnd_141470 < baseStart_141470 := by decide
  rcases family_descends (prefixWord ++ tailWord_141470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141471 : List Nat := [1, 1, 2, 6, 1, 2, 2, 5]
def baseStart_141471 : Nat := 118140960795 + 141471 * 2 ^ 59
def prefixEnd_141471 : Nat := 4983230072969 + 3 ^ 40 * 141471 * 2
def baseEnd_141471 : Nat := 21523739754761845262783

theorem tailTrace_141471 : CollatzResearch.WordTrace tailWord_141471 prefixEnd_141471 21523739754761845262783 := by
  unfold tailWord_141471
  simp only [CollatzResearch.WordTrace]
  refine ⟨5159871270482203168328267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3439914180321468778885511 5159871270482203168328267)
  ·
    refine ⟨7739806905723304752492401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5159871270482203168328267 7739806905723304752492401)
    ·
      refine ⟨5804855179292478564369301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7739806905723304752492401 5804855179292478564369301)
      ·
        refine ⟨272102586529334932704811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5804855179292478564369301 272102586529334932704811)
        ·
          refine ⟨408153879794002399057217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272102586529334932704811 408153879794002399057217)
          ·
            refine ⟨306115409845501799292913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408153879794002399057217 306115409845501799292913)
            ·
              refine ⟨229586557384126349469685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306115409845501799292913 229586557384126349469685)
              ·
                refine ⟨21523739754761845262783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 229586557384126349469685 21523739754761845262783)
                ·
                  rfl

theorem cell20_141471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_141471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141471 prefixEnd_141471 := by exact prefixLift 141471
  have htrace : WordTrace (prefixWord ++ tailWord_141471) baseStart_141471 baseEnd_141471 := by
    simpa [prefixWord, tailWord_141471, baseEnd_141471] using wordTrace_append hprefix tailTrace_141471
  have hstable : (prefixWord ++ tailWord_141471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141471).length < 2 ^ (prefixWord ++ tailWord_141471).sum := by decide
  have hdescent : baseEnd_141471 < baseStart_141471 := by decide
  rcases family_descends (prefixWord ++ tailWord_141471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141474 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_141474 : Nat := 118140960795 + 141474 * 2 ^ 59
def prefixEnd_141474 : Nat := 4983230072969 + 3 ^ 40 * 141474 * 2
def baseEnd_141474 : Nat := 64572588546030858688337

theorem tailTrace_141474 : CollatzResearch.WordTrace tailWord_141474 prefixEnd_141474 64572588546030858688337 := by
  unfold tailWord_141474
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289995172367833670171869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3439987126314223120458317 1289995172367833670171869)
  ·
    refine ⟨483748189637937626314451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1289995172367833670171869 483748189637937626314451)
    ·
      refine ⟨725622284456906439471677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483748189637937626314451 725622284456906439471677)
      ·
        refine ⟨272108356671339914801879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 725622284456906439471677 272108356671339914801879)
        ·
          refine ⟨408162535007009872202819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272108356671339914801879 408162535007009872202819)
          ·
            refine ⟨612243802510514808304229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408162535007009872202819 612243802510514808304229)
            ·
              refine ⟨114795712970721526557043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 612243802510514808304229 114795712970721526557043)
              ·
                refine ⟨172193569456082289835565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114795712970721526557043 172193569456082289835565)
                ·
                  refine ⟨64572588546030858688337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172193569456082289835565 64572588546030858688337)
                  ·
                    rfl

theorem cell20_141474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_141474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141474 prefixEnd_141474 := by exact prefixLift 141474
  have htrace : WordTrace (prefixWord ++ tailWord_141474) baseStart_141474 baseEnd_141474 := by
    simpa [prefixWord, tailWord_141474, baseEnd_141474] using wordTrace_append hprefix tailTrace_141474
  have hstable : (prefixWord ++ tailWord_141474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141474).length < 2 ^ (prefixWord ++ tailWord_141474).sum := by decide
  have hdescent : baseEnd_141474 < baseStart_141474 := by decide
  rcases family_descends (prefixWord ++ tailWord_141474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141526 : List Nat := [5, 2, 1, 2, 1, 1, 3, 5]
def baseStart_141526 : Nat := 118140960795 + 141526 * 2 ^ 59
def prefixEnd_141526 : Nat := 4983230072969 + 3 ^ 40 * 141526 * 2
def baseEnd_141526 : Nat := 21532107587649929651597

theorem tailTrace_141526 : CollatzResearch.WordTrace tailWord_141526 prefixEnd_141526 21532107587649929651597 := by
  unfold tailWord_141526
  simp only [CollatzResearch.WordTrace]
  refine ⟨322617330330184222598777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3441251523521965041053621 322617330330184222598777)
  ·
    refine ⟨241962997747638166949083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 322617330330184222598777 241962997747638166949083)
    ·
      refine ⟨362944496621457250423625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241962997747638166949083 362944496621457250423625)
      ·
        refine ⟨272208372466092937817719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362944496621457250423625 272208372466092937817719)
        ·
          refine ⟨408312558699139406726579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272208372466092937817719 408312558699139406726579)
          ·
            refine ⟨612468838048709110089869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408312558699139406726579 612468838048709110089869)
            ·
              refine ⟨229675814268265916283701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 612468838048709110089869 229675814268265916283701)
              ·
                refine ⟨21532107587649929651597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 229675814268265916283701 21532107587649929651597)
                ·
                  rfl

theorem cell20_141526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_141526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141526 prefixEnd_141526 := by exact prefixLift 141526
  have htrace : WordTrace (prefixWord ++ tailWord_141526) baseStart_141526 baseEnd_141526 := by
    simpa [prefixWord, tailWord_141526, baseEnd_141526] using wordTrace_append hprefix tailTrace_141526
  have hstable : (prefixWord ++ tailWord_141526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141526).length < 2 ^ (prefixWord ++ tailWord_141526).sum := by decide
  have hdescent : baseEnd_141526 < baseStart_141526 := by decide
  rcases family_descends (prefixWord ++ tailWord_141526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141530 : List Nat := [3, 1, 1, 2, 2, 1, 5, 5]
def baseStart_141530 : Nat := 118140960795 + 141530 * 2 ^ 59
def prefixEnd_141530 : Nat := 4983230072969 + 3 ^ 40 * 141530 * 2
def baseEnd_141530 : Nat := 21532716157314517607147

theorem tailTrace_141530 : CollatzResearch.WordTrace tailWord_141530 prefixEnd_141530 21532716157314517607147 := by
  unfold tailWord_141530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290505794317114061181511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3441348784845637496484029 1290505794317114061181511)
  ·
    refine ⟨1935758691475671091772267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290505794317114061181511 1935758691475671091772267)
    ·
      refine ⟨2903638037213506637658401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935758691475671091772267 2903638037213506637658401)
      ·
        refine ⟨2177728527910129978243801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2903638037213506637658401 2177728527910129978243801)
        ·
          refine ⟨1633296395932597483682851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2177728527910129978243801 1633296395932597483682851)
          ·
            refine ⟨2449944593898896225524277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633296395932597483682851 2449944593898896225524277)
            ·
              refine ⟨229682305678021521142901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2449944593898896225524277 229682305678021521142901)
              ·
                refine ⟨21532716157314517607147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 229682305678021521142901 21532716157314517607147)
                ·
                  rfl

theorem cell20_141530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_141530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141530 prefixEnd_141530 := by exact prefixLift 141530
  have htrace : WordTrace (prefixWord ++ tailWord_141530) baseStart_141530 baseEnd_141530 := by
    simpa [prefixWord, tailWord_141530, baseEnd_141530] using wordTrace_append hprefix tailTrace_141530
  have hstable : (prefixWord ++ tailWord_141530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141530).length < 2 ^ (prefixWord ++ tailWord_141530).sum := by decide
  have hdescent : baseEnd_141530 < baseStart_141530 := by decide
  rcases family_descends (prefixWord ++ tailWord_141530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141533 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 3]
def baseStart_141533 : Nat := 118140960795 + 141533 * 2 ^ 59
def prefixEnd_141533 : Nat := 4983230072969 + 3 ^ 40 * 141533 * 2
def baseEnd_141533 : Nat := 64599517753688875721429

theorem tailTrace_141533 : CollatzResearch.WordTrace tailWord_141533 prefixEnd_141533 64599517753688875721429 := by
  unfold tailWord_141533
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162132596257587757085253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3441421730838391838056835 5162132596257587757085253)
  ·
    refine ⟨967899861798297704453485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5162132596257587757085253 967899861798297704453485)
    ·
      refine ⟨362962448174361639170057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 967899861798297704453485 362962448174361639170057)
      ·
        refine ⟨272221836130771229377543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362962448174361639170057 272221836130771229377543)
        ·
          refine ⟨408332754196156844066315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272221836130771229377543 408332754196156844066315)
          ·
            refine ⟨612499131294235266099473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408332754196156844066315 612499131294235266099473)
            ·
              refine ⟨459374348470676449574605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612499131294235266099473 459374348470676449574605)
              ·
                refine ⟨172265380676503668590477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 459374348470676449574605 172265380676503668590477)
                ·
                  refine ⟨64599517753688875721429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172265380676503668590477 64599517753688875721429)
                  ·
                    rfl

theorem cell20_141533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_141533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141533 prefixEnd_141533 := by exact prefixLift 141533
  have htrace : WordTrace (prefixWord ++ tailWord_141533) baseStart_141533 baseEnd_141533 := by
    simpa [prefixWord, tailWord_141533, baseEnd_141533] using wordTrace_append hprefix tailTrace_141533
  have hstable : (prefixWord ++ tailWord_141533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141533).length < 2 ^ (prefixWord ++ tailWord_141533).sum := by decide
  have hdescent : baseEnd_141533 < baseStart_141533 := by decide
  rcases family_descends (prefixWord ++ tailWord_141533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141578 : List Nat := [3, 1, 2, 2, 1, 1, 4, 4, 2]
def baseStart_141578 : Nat := 118140960795 + 141578 * 2 ^ 59
def prefixEnd_141578 : Nat := 4983230072969 + 3 ^ 40 * 141578 * 2
def baseEnd_141578 : Nat := 64620056979868719221245

theorem tailTrace_141578 : CollatzResearch.WordTrace tailWord_141578 prefixEnd_141578 64620056979868719221245 := by
  unfold tailWord_141578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290943470273640110618347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3442515920729706961648925 1290943470273640110618347)
  ·
    refine ⟨1936415205410460165927521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290943470273640110618347 1936415205410460165927521)
    ·
      refine ⟨1452311404057845124445641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1936415205410460165927521 1452311404057845124445641)
      ·
        refine ⟨1089233553043383843334231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1452311404057845124445641 1089233553043383843334231)
        ·
          refine ⟨1633850329565075765001347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089233553043383843334231 1633850329565075765001347)
          ·
            refine ⟨2450775494347613647502021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633850329565075765001347 2450775494347613647502021)
            ·
              refine ⟨459520405190177558906629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2450775494347613647502021 459520405190177558906629)
              ·
                refine ⟨86160075973158292294993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 459520405190177558906629 86160075973158292294993)
                ·
                  refine ⟨64620056979868719221245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86160075973158292294993 64620056979868719221245)
                  ·
                    rfl

theorem cell20_141578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_141578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141578 prefixEnd_141578 := by exact prefixLift 141578
  have htrace : WordTrace (prefixWord ++ tailWord_141578) baseStart_141578 baseEnd_141578 := by
    simpa [prefixWord, tailWord_141578, baseEnd_141578] using wordTrace_append hprefix tailTrace_141578
  have hstable : (prefixWord ++ tailWord_141578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141578).length < 2 ^ (prefixWord ++ tailWord_141578).sum := by decide
  have hdescent : baseEnd_141578 < baseStart_141578 := by decide
  rcases family_descends (prefixWord ++ tailWord_141578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141599 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_141599 : Nat := 118140960795 + 141599 * 2 ^ 59
def prefixEnd_141599 : Nat := 4983230072969 + 3 ^ 40 * 141599 * 2
def baseEnd_141599 : Nat := 64629641952085979521159

theorem tailTrace_141599 : CollatzResearch.WordTrace tailWord_141599 prefixEnd_141599 64629641952085979521159 := by
  unfold tailWord_141599
  simp only [CollatzResearch.WordTrace]
  refine ⟨5164539814018481028987851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3443026542678987352658567 5164539814018481028987851)
  ·
    refine ⟨7746809721027721543481777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5164539814018481028987851 7746809721027721543481777)
    ·
      refine ⟨5810107290770791157611333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7746809721027721543481777 5810107290770791157611333)
      ·
        refine ⟨1089395117019523342052125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5810107290770791157611333 1089395117019523342052125)
        ·
          refine ⟨408523168882321253269547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1089395117019523342052125 408523168882321253269547)
          ·
            refine ⟨612784753323481879904321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408523168882321253269547 612784753323481879904321)
            ·
              refine ⟨459588564992611409928241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612784753323481879904321 459588564992611409928241)
              ·
                refine ⟨344691423744458557446181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459588564992611409928241 344691423744458557446181)
                ·
                  refine ⟨64629641952085979521159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344691423744458557446181 64629641952085979521159)
                  ·
                    rfl

theorem cell20_141599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_141599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141599 prefixEnd_141599 := by exact prefixLift 141599
  have htrace : WordTrace (prefixWord ++ tailWord_141599) baseStart_141599 baseEnd_141599 := by
    simpa [prefixWord, tailWord_141599, baseEnd_141599] using wordTrace_append hprefix tailTrace_141599
  have hstable : (prefixWord ++ tailWord_141599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141599).length < 2 ^ (prefixWord ++ tailWord_141599).sum := by decide
  have hdescent : baseEnd_141599 < baseStart_141599 := by decide
  rcases family_descends (prefixWord ++ tailWord_141599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141602 : List Nat := [3, 3, 1, 1, 3, 3, 2, 4]
def baseStart_141602 : Nat := 118140960795 + 141602 * 2 ^ 59
def prefixEnd_141602 : Nat := 4983230072969 + 3 ^ 40 * 141602 * 2
def baseEnd_141602 : Nat := 21543670411277100807049

theorem tailTrace_141602 : CollatzResearch.WordTrace tailWord_141602 prefixEnd_141602 21543670411277100807049 := by
  unfold tailWord_141602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1291162308251903135336765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3443099488671741694231373 1291162308251903135336765)
  ·
    refine ⟨484185865594463675751287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1291162308251903135336765 484185865594463675751287)
    ·
      refine ⟨726278798391695513626931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 484185865594463675751287 726278798391695513626931)
      ·
        refine ⟨1089418197587543270440397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726278798391695513626931 1089418197587543270440397)
        ·
          refine ⟨408531824095328726415149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1089418197587543270440397 408531824095328726415149)
          ·
            refine ⟨153199434035748272405681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408531824095328726415149 153199434035748272405681)
            ·
              refine ⟨114899575526811204304261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153199434035748272405681 114899575526811204304261)
              ·
                refine ⟨21543670411277100807049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114899575526811204304261 21543670411277100807049)
                ·
                  rfl

theorem cell20_141602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_141602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141602 prefixEnd_141602 := by exact prefixLift 141602
  have htrace : WordTrace (prefixWord ++ tailWord_141602) baseStart_141602 baseEnd_141602 := by
    simpa [prefixWord, tailWord_141602, baseEnd_141602] using wordTrace_append hprefix tailTrace_141602
  have hstable : (prefixWord ++ tailWord_141602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141602).length < 2 ^ (prefixWord ++ tailWord_141602).sum := by decide
  have hdescent : baseEnd_141602 < baseStart_141602 := by decide
  rcases family_descends (prefixWord ++ tailWord_141602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141630 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_141630 : Nat := 118140960795 + 141630 * 2 ^ 59
def prefixEnd_141630 : Nat := 4983230072969 + 3 ^ 40 * 141630 * 2
def baseEnd_141630 : Nat := 64643791196787649487699

theorem tailTrace_141630 : CollatzResearch.WordTrace tailWord_141630 prefixEnd_141630 64643791196787649487699 := by
  unfold tailWord_141630
  simp only [CollatzResearch.WordTrace]
  refine ⟨645708809613271665420793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3443780317937448882244229 645708809613271665420793)
  ·
    refine ⟨484281607209953749065595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 645708809613271665420793 484281607209953749065595)
    ·
      refine ⟨726422410814930623598393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 484281607209953749065595 726422410814930623598393)
      ·
        refine ⟨544816808111197967698795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 726422410814930623598393 544816808111197967698795)
        ·
          refine ⟨817225212166796951548193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544816808111197967698795 817225212166796951548193)
          ·
            refine ⟨612918909125097713661145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817225212166796951548193 612918909125097713661145)
            ·
              refine ⟨459689181843823285245859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612918909125097713661145 459689181843823285245859)
              ·
                refine ⟨689533772765734927868789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459689181843823285245859 689533772765734927868789)
                ·
                  refine ⟨64643791196787649487699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 689533772765734927868789 64643791196787649487699)
                  ·
                    rfl

theorem cell20_141630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_141630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141630 prefixEnd_141630 := by exact prefixLift 141630
  have htrace : WordTrace (prefixWord ++ tailWord_141630) baseStart_141630 baseEnd_141630 := by
    simpa [prefixWord, tailWord_141630, baseEnd_141630] using wordTrace_append hprefix tailTrace_141630
  have hstable : (prefixWord ++ tailWord_141630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141630).length < 2 ^ (prefixWord ++ tailWord_141630).sum := by decide
  have hdescent : baseEnd_141630 < baseStart_141630 := by decide
  rcases family_descends (prefixWord ++ tailWord_141630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141633 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 4]
def baseStart_141633 : Nat := 118140960795 + 141633 * 2 ^ 59
def prefixEnd_141633 : Nat := 4983230072969 + 3 ^ 40 * 141633 * 2
def baseEnd_141633 : Nat := 64645160478532972387687

theorem tailTrace_141633 : CollatzResearch.WordTrace tailWord_141633 prefixEnd_141633 64645160478532972387687 := by
  unfold tailWord_141633
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165779895895304835725553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3443853263930203223817035 5165779895895304835725553)
  ·
    refine ⟨3874334921921478626794165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5165779895895304835725553 3874334921921478626794165)
    ·
      refine ⟨363218898930138621261953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3874334921921478626794165 363218898930138621261953)
      ·
        refine ⟨272414174197603965946465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363218898930138621261953 272414174197603965946465)
        ·
          refine ⟨204310630648202974459849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272414174197603965946465 204310630648202974459849)
          ·
            refine ⟨153232972986152230844887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204310630648202974459849 153232972986152230844887)
            ·
              refine ⟨229849459479228346267331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153232972986152230844887 229849459479228346267331)
              ·
                refine ⟨344774189218842519400997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229849459479228346267331 344774189218842519400997)
                ·
                  refine ⟨64645160478532972387687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344774189218842519400997 64645160478532972387687)
                  ·
                    rfl

theorem cell20_141633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_141633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141633 prefixEnd_141633 := by exact prefixLift 141633
  have htrace : WordTrace (prefixWord ++ tailWord_141633) baseStart_141633 baseEnd_141633 := by
    simpa [prefixWord, tailWord_141633, baseEnd_141633] using wordTrace_append hprefix tailTrace_141633
  have hstable : (prefixWord ++ tailWord_141633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141633).length < 2 ^ (prefixWord ++ tailWord_141633).sum := by decide
  have hdescent : baseEnd_141633 < baseStart_141633 := by decide
  rcases family_descends (prefixWord ++ tailWord_141633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141644 : List Nat := [2, 2, 1, 3, 2, 1, 4, 5]
def baseStart_141644 : Nat := 118140960795 + 141644 * 2 ^ 59
def prefixEnd_141644 : Nat := 4983230072969 + 3 ^ 40 * 141644 * 2
def baseEnd_141644 : Nat := 21550060392755274340325

theorem tailTrace_141644 : CollatzResearch.WordTrace tailWord_141644 prefixEnd_141644 21550060392755274340325 := by
  unfold tailWord_141644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2583090549427726857187993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3444120732570302476250657 2583090549427726857187993)
  ·
    refine ⟨1937317912070795142890995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2583090549427726857187993 1937317912070795142890995)
    ·
      refine ⟨2905976868106192714336493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1937317912070795142890995 2905976868106192714336493)
      ·
        refine ⟨1089741325539822267876185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2905976868106192714336493 1089741325539822267876185)
        ·
          refine ⟨817305994154866700907139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1089741325539822267876185 817305994154866700907139)
          ·
            refine ⟨1225958991232300051360709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817305994154866700907139 1225958991232300051360709)
            ·
              refine ⟨229867310856056259630133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1225958991232300051360709 229867310856056259630133)
              ·
                refine ⟨21550060392755274340325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 229867310856056259630133 21550060392755274340325)
                ·
                  rfl

theorem cell20_141644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_141644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141644 prefixEnd_141644 := by exact prefixLift 141644
  have htrace : WordTrace (prefixWord ++ tailWord_141644) baseStart_141644 baseEnd_141644 := by
    simpa [prefixWord, tailWord_141644, baseEnd_141644] using wordTrace_append hprefix tailTrace_141644
  have hstable : (prefixWord ++ tailWord_141644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141644).length < 2 ^ (prefixWord ++ tailWord_141644).sum := by decide
  have hdescent : baseEnd_141644 < baseStart_141644 := by decide
  rcases family_descends (prefixWord ++ tailWord_141644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141658 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_141658 : Nat := 118140960795 + 141658 * 2 ^ 59
def prefixEnd_141658 : Nat := 4983230072969 + 3 ^ 40 * 141658 * 2
def baseEnd_141658 : Nat := 64656571159743996554251

theorem tailTrace_141658 : CollatzResearch.WordTrace tailWord_141658 prefixEnd_141658 64656571159743996554251 := by
  unfold tailWord_141658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1291672930201183526346407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3444461147203156070257085 1291672930201183526346407)
  ·
    refine ⟨1937509395301775289519611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1291672930201183526346407 1937509395301775289519611)
    ·
      refine ⟨2906264092952662934279417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1937509395301775289519611 2906264092952662934279417)
      ·
        refine ⟨2179698069714497200709563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2906264092952662934279417 2179698069714497200709563)
        ·
          refine ⟨3269547104571745801064345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2179698069714497200709563 3269547104571745801064345)
          ·
            refine ⟨2452160328428809350798259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3269547104571745801064345 2452160328428809350798259)
            ·
              refine ⟨3678240492643214026197389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452160328428809350798259 3678240492643214026197389)
              ·
                refine ⟨1379340184741205259824021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3678240492643214026197389 1379340184741205259824021)
                ·
                  refine ⟨64656571159743996554251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1379340184741205259824021 64656571159743996554251)
                  ·
                    rfl

theorem cell20_141658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_141658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141658 prefixEnd_141658 := by exact prefixLift 141658
  have htrace : WordTrace (prefixWord ++ tailWord_141658) baseStart_141658 baseEnd_141658 := by
    simpa [prefixWord, tailWord_141658, baseEnd_141658] using wordTrace_append hprefix tailTrace_141658
  have hstable : (prefixWord ++ tailWord_141658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141658).length < 2 ^ (prefixWord ++ tailWord_141658).sum := by decide
  have hdescent : baseEnd_141658 < baseStart_141658 := by decide
  rcases family_descends (prefixWord ++ tailWord_141658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141685 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 3]
def baseStart_141685 : Nat := 118140960795 + 141685 * 2 ^ 59
def prefixEnd_141685 : Nat := 4983230072969 + 3 ^ 40 * 141685 * 2
def baseEnd_141685 : Nat := 64668894695451902654141

theorem tailTrace_141685 : CollatzResearch.WordTrace tailWord_141685 prefixEnd_141685 64668894695451902654141 := by
  unfold tailWord_141685
  simp only [CollatzResearch.WordTrace]
  refine ⟨5167676491706917716618509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3445117661137945144412339 5167676491706917716618509)
  ·
    refine ⟨1937878684390094143731941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5167676491706917716618509 1937878684390094143731941)
    ·
      refine ⟨363352253323142651949739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1937878684390094143731941 363352253323142651949739)
      ·
        refine ⟨545028379984713977924609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363352253323142651949739 545028379984713977924609)
        ·
          refine ⟨408771284988535483443457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 545028379984713977924609 408771284988535483443457)
          ·
            refine ⟨306578463741401612582593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408771284988535483443457 306578463741401612582593)
            ·
              refine ⟨229933847806051209436945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306578463741401612582593 229933847806051209436945)
              ·
                refine ⟨172450385854538407077709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229933847806051209436945 172450385854538407077709)
                ·
                  refine ⟨64668894695451902654141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172450385854538407077709 64668894695451902654141)
                  ·
                    rfl

theorem cell20_141685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_141685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141685 prefixEnd_141685 := by exact prefixLift 141685
  have htrace : WordTrace (prefixWord ++ tailWord_141685) baseStart_141685 baseEnd_141685 := by
    simpa [prefixWord, tailWord_141685, baseEnd_141685] using wordTrace_append hprefix tailTrace_141685
  have hstable : (prefixWord ++ tailWord_141685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141685).length < 2 ^ (prefixWord ++ tailWord_141685).sum := by decide
  have hdescent : baseEnd_141685 < baseStart_141685 := by decide
  rcases family_descends (prefixWord ++ tailWord_141685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141699 : List Nat := [1, 1, 1, 3, 6, 2, 1, 5]
def baseStart_141699 : Nat := 118140960795 + 141699 * 2 ^ 59
def prefixEnd_141699 : Nat := 4983230072969 + 3 ^ 40 * 141699 * 2
def baseEnd_141699 : Nat := 21558428225643358729139

theorem tailTrace_141699 : CollatzResearch.WordTrace tailWord_141699 prefixEnd_141699 21558428225643358729139 := by
  unfold tailWord_141699
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168187113656198107628151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3445458075770798738418767 5168187113656198107628151)
  ·
    refine ⟨7752280670484297161442227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5168187113656198107628151 7752280670484297161442227)
    ·
      refine ⟨11628421005726445742163341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7752280670484297161442227 11628421005726445742163341)
      ·
        refine ⟨4360657877147417153311253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11628421005726445742163341 4360657877147417153311253)
        ·
          refine ⟨204405837991285179061465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4360657877147417153311253 204405837991285179061465)
          ·
            refine ⟨153304378493463884296099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204405837991285179061465 153304378493463884296099)
            ·
              refine ⟨229956567740195826444149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153304378493463884296099 229956567740195826444149)
              ·
                refine ⟨21558428225643358729139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 229956567740195826444149 21558428225643358729139)
                ·
                  rfl

theorem cell20_141699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 5].length) (baseStart_141699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141699 prefixEnd_141699 := by exact prefixLift 141699
  have htrace : WordTrace (prefixWord ++ tailWord_141699) baseStart_141699 baseEnd_141699 := by
    simpa [prefixWord, tailWord_141699, baseEnd_141699] using wordTrace_append hprefix tailTrace_141699
  have hstable : (prefixWord ++ tailWord_141699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141699).length < 2 ^ (prefixWord ++ tailWord_141699).sum := by decide
  have hdescent : baseEnd_141699 < baseStart_141699 := by decide
  rcases family_descends (prefixWord ++ tailWord_141699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141716 : List Nat := [2, 4, 2, 1, 3, 1, 3, 4]
def baseStart_141716 : Nat := 118140960795 + 141716 * 2 ^ 59
def prefixEnd_141716 : Nat := 4983230072969 + 3 ^ 40 * 141716 * 2
def baseEnd_141716 : Nat := 21561014646717857540227

theorem tailTrace_141716 : CollatzResearch.WordTrace tailWord_141716 prefixEnd_141716 21561014646717857540227 := by
  unfold tailWord_141716
  simp only [CollatzResearch.WordTrace]
  refine ⟨2584403577297305005498501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3445871436396406673998001 2584403577297305005498501)
  ·
    refine ⟨484575670743244688530969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2584403577297305005498501 484575670743244688530969)
    ·
      refine ⟨363431753057433516398227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 484575670743244688530969 363431753057433516398227)
      ·
        refine ⟨545147629586150274597341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363431753057433516398227 545147629586150274597341)
        ·
          refine ⟨204430361094806352974003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 545147629586150274597341 204430361094806352974003)
          ·
            refine ⟨306645541642209529461005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204430361094806352974003 306645541642209529461005)
            ·
              refine ⟨114992078115828573547877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 306645541642209529461005 114992078115828573547877)
              ·
                refine ⟨21561014646717857540227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114992078115828573547877 21561014646717857540227)
                ·
                  rfl

theorem cell20_141716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_141716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141716 prefixEnd_141716 := by exact prefixLift 141716
  have htrace : WordTrace (prefixWord ++ tailWord_141716) baseStart_141716 baseEnd_141716 := by
    simpa [prefixWord, tailWord_141716, baseEnd_141716] using wordTrace_append hprefix tailTrace_141716
  have hstable : (prefixWord ++ tailWord_141716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141716).length < 2 ^ (prefixWord ++ tailWord_141716).sum := by decide
  have hdescent : baseEnd_141716 < baseStart_141716 := by decide
  rcases family_descends (prefixWord ++ tailWord_141716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141726 : List Nat := [4, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_141726 : Nat := 118140960795 + 141726 * 2 ^ 59
def prefixEnd_141726 : Nat := 4983230072969 + 3 ^ 40 * 141726 * 2
def baseEnd_141726 : Nat := 64687608212637982287307

theorem tailTrace_141726 : CollatzResearch.WordTrace tailWord_141726 prefixEnd_141726 64687608212637982287307 := by
  unfold tailWord_141726
  simp only [CollatzResearch.WordTrace]
  refine ⟨646146485569797714857629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3446114589705587812574021 646146485569797714857629)
  ·
    refine ⟨242304932088674143071611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 646146485569797714857629 242304932088674143071611)
    ·
      refine ⟨363457398133011214607417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242304932088674143071611 363457398133011214607417)
      ·
        refine ⟨272593048599758410955563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363457398133011214607417 272593048599758410955563)
        ·
          refine ⟨408889572899637616433345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272593048599758410955563 408889572899637616433345)
          ·
            refine ⟨306667179674728212325009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408889572899637616433345 306667179674728212325009)
            ·
              refine ⟨230000384756046159243757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306667179674728212325009 230000384756046159243757)
              ·
                refine ⟨86250144283517309716409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230000384756046159243757 86250144283517309716409)
                ·
                  refine ⟨64687608212637982287307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86250144283517309716409 64687608212637982287307)
                  ·
                    rfl

theorem cell20_141726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_141726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141726 prefixEnd_141726 := by exact prefixLift 141726
  have htrace : WordTrace (prefixWord ++ tailWord_141726) baseStart_141726 baseEnd_141726 := by
    simpa [prefixWord, tailWord_141726, baseEnd_141726] using wordTrace_append hprefix tailTrace_141726
  have hstable : (prefixWord ++ tailWord_141726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141726).length < 2 ^ (prefixWord ++ tailWord_141726).sum := by decide
  have hdescent : baseEnd_141726 < baseStart_141726 := by decide
  rcases family_descends (prefixWord ++ tailWord_141726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141727 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_141727 : Nat := 118140960795 + 141727 * 2 ^ 59
def prefixEnd_141727 : Nat := 4983230072969 + 3 ^ 40 * 141727 * 2
def baseEnd_141727 : Nat := 64688064639886423253969

theorem tailTrace_141727 : CollatzResearch.WordTrace tailWord_141727 prefixEnd_141727 64688064639886423253969 := by
  unfold tailWord_141727
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169208357554758889647435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3446138905036505926431623 5169208357554758889647435)
  ·
    refine ⟨7753812536332138334471153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5169208357554758889647435 7753812536332138334471153)
    ·
      refine ⟨5815359402249103750853365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7753812536332138334471153 5815359402249103750853365)
      ·
        refine ⟨545189943960853476642503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5815359402249103750853365 545189943960853476642503)
        ·
          refine ⟨817784915941280214963755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545189943960853476642503 817784915941280214963755)
          ·
            refine ⟨1226677373911920322445633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817784915941280214963755 1226677373911920322445633)
            ·
              refine ⟨920008030433940241834225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1226677373911920322445633 920008030433940241834225)
              ·
                refine ⟨690006022825455181375669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920008030433940241834225 690006022825455181375669)
                ·
                  refine ⟨64688064639886423253969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 690006022825455181375669 64688064639886423253969)
                  ·
                    rfl

theorem cell20_141727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_141727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141727 prefixEnd_141727 := by exact prefixLift 141727
  have htrace : WordTrace (prefixWord ++ tailWord_141727) baseStart_141727 baseEnd_141727 := by
    simpa [prefixWord, tailWord_141727, baseEnd_141727] using wordTrace_append hprefix tailTrace_141727
  have hstable : (prefixWord ++ tailWord_141727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141727).length < 2 ^ (prefixWord ++ tailWord_141727).sum := by decide
  have hdescent : baseEnd_141727 < baseStart_141727 := by decide
  rcases family_descends (prefixWord ++ tailWord_141727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141751 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 4]
def baseStart_141751 : Nat := 118140960795 + 141751 * 2 ^ 59
def prefixEnd_141751 : Nat := 4983230072969 + 3 ^ 40 * 141751 * 2
def baseEnd_141751 : Nat := 64699018893849006453871

theorem tailTrace_141751 : CollatzResearch.WordTrace tailWord_141751 prefixEnd_141751 64699018893849006453871 := by
  unfold tailWord_141751
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170083709467810988521107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3446722472978540659014071 5170083709467810988521107)
  ·
    refine ⟨7755125564201716482781661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5170083709467810988521107 7755125564201716482781661)
    ·
      refine ⟨2908172086575643681043123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7755125564201716482781661 2908172086575643681043123)
      ·
        refine ⟨4362258129863465521564685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2908172086575643681043123 4362258129863465521564685)
        ·
          refine ⟨1635846798698799570586757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4362258129863465521564685 1635846798698799570586757)
          ·
            refine ⟨306721274756024919485017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1635846798698799570586757 306721274756024919485017)
            ·
              refine ⟨230040956067018689613763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306721274756024919485017 230040956067018689613763)
              ·
                refine ⟨345061434100528034420645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230040956067018689613763 345061434100528034420645)
                ·
                  refine ⟨64699018893849006453871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 345061434100528034420645 64699018893849006453871)
                  ·
                    rfl

theorem cell20_141751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_141751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141751 prefixEnd_141751 := by exact prefixLift 141751
  have htrace : WordTrace (prefixWord ++ tailWord_141751) baseStart_141751 baseEnd_141751 := by
    simpa [prefixWord, tailWord_141751, baseEnd_141751] using wordTrace_append hprefix tailTrace_141751
  have hstable : (prefixWord ++ tailWord_141751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141751).length < 2 ^ (prefixWord ++ tailWord_141751).sum := by decide
  have hdescent : baseEnd_141751 < baseStart_141751 := by decide
  rcases family_descends (prefixWord ++ tailWord_141751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141782 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_141782 : Nat := 118140960795 + 141782 * 2 ^ 59
def prefixEnd_141782 : Nat := 4983230072969 + 3 ^ 40 * 141782 * 2
def baseEnd_141782 : Nat := 64713168138550676420411

theorem tailTrace_141782 : CollatzResearch.WordTrace tailWord_141782 prefixEnd_141782 64713168138550676420411 := by
  unfold tailWord_141782
  simp only [CollatzResearch.WordTrace]
  refine ⟨323200898272218955181225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3447476248237002188599733 323200898272218955181225)
  ·
    refine ⟨242400673704164216385919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 323200898272218955181225 242400673704164216385919)
    ·
      refine ⟨363601010556246324578879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242400673704164216385919 363601010556246324578879)
      ·
        refine ⟨545401515834369486868319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363601010556246324578879 545401515834369486868319)
        ·
          refine ⟨818102273751554230302479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545401515834369486868319 818102273751554230302479)
          ·
            refine ⟨1227153410627331345453719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818102273751554230302479 1227153410627331345453719)
            ·
              refine ⟨1840730115940997018180579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227153410627331345453719 1840730115940997018180579)
              ·
                refine ⟨2761095173911495527270869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840730115940997018180579 2761095173911495527270869)
                ·
                  refine ⟨64713168138550676420411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2761095173911495527270869 64713168138550676420411)
                  ·
                    rfl

theorem cell20_141782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_141782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141782 prefixEnd_141782 := by exact prefixLift 141782
  have htrace : WordTrace (prefixWord ++ tailWord_141782) baseStart_141782 baseEnd_141782 := by
    simpa [prefixWord, tailWord_141782, baseEnd_141782] using wordTrace_append hprefix tailTrace_141782
  have hstable : (prefixWord ++ tailWord_141782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141782).length < 2 ^ (prefixWord ++ tailWord_141782).sum := by decide
  have hdescent : baseEnd_141782 < baseStart_141782 := by decide
  rcases family_descends (prefixWord ++ tailWord_141782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141803 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 3]
def baseStart_141803 : Nat := 118140960795 + 141803 * 2 ^ 59
def prefixEnd_141803 : Nat := 4983230072969 + 3 ^ 40 * 141803 * 2
def baseEnd_141803 : Nat := 64722753110767936720325

theorem tailTrace_141803 : CollatzResearch.WordTrace tailWord_141803 prefixEnd_141803 64722753110767936720325 := by
  unfold tailWord_141803
  simp only [CollatzResearch.WordTrace]
  refine ⟨5171980305279423869414063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3447986870186282579609375 5171980305279423869414063)
  ·
    refine ⟨7757970457919135804121095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5171980305279423869414063 7757970457919135804121095)
    ·
      refine ⟨11636955686878703706181643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7757970457919135804121095 11636955686878703706181643)
      ·
        refine ⟨17455433530318055559272465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11636955686878703706181643 17455433530318055559272465)
        ·
          refine ⟨13091575147738541669454349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17455433530318055559272465 13091575147738541669454349)
          ·
            refine ⟨4909340680401953126045381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13091575147738541669454349 4909340680401953126045381)
            ·
              refine ⟨920501377575366211133509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4909340680401953126045381 920501377575366211133509)
              ·
                refine ⟨172594008295381164587533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 920501377575366211133509 172594008295381164587533)
                ·
                  refine ⟨64722753110767936720325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172594008295381164587533 64722753110767936720325)
                  ·
                    rfl

theorem cell20_141803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 3].length) (baseStart_141803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141803 prefixEnd_141803 := by exact prefixLift 141803
  have htrace : WordTrace (prefixWord ++ tailWord_141803) baseStart_141803 baseEnd_141803 := by
    simpa [prefixWord, tailWord_141803, baseEnd_141803] using wordTrace_append hprefix tailTrace_141803
  have hstable : (prefixWord ++ tailWord_141803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141803).length < 2 ^ (prefixWord ++ tailWord_141803).sum := by decide
  have hdescent : baseEnd_141803 < baseStart_141803 := by decide
  rcases family_descends (prefixWord ++ tailWord_141803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141806 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_141806 : Nat := 118140960795 + 141806 * 2 ^ 59
def prefixEnd_141806 : Nat := 4983230072969 + 3 ^ 40 * 141806 * 2
def baseEnd_141806 : Nat := 64724122392513259620313

theorem tailTrace_141806 : CollatzResearch.WordTrace tailWord_141806 prefixEnd_141806 64724122392513259620313 := by
  unfold tailWord_141806
  simp only [CollatzResearch.WordTrace]
  refine ⟨646511215533569422721659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3448059816179036921182181 646511215533569422721659)
  ·
    refine ⟨969766823300354134082489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646511215533569422721659 969766823300354134082489)
    ·
      refine ⟨727325117475265600561867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 969766823300354134082489 727325117475265600561867)
      ·
        refine ⟨1090987676212898400842801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727325117475265600561867 1090987676212898400842801)
        ·
          refine ⟨818240757159673800632101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1090987676212898400842801 818240757159673800632101)
          ·
            refine ⟨153420141967438837618519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 818240757159673800632101 153420141967438837618519)
            ·
              refine ⟨230130212951158256427779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153420141967438837618519 230130212951158256427779)
              ·
                refine ⟨345195319426737384641669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230130212951158256427779 345195319426737384641669)
                ·
                  refine ⟨64724122392513259620313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 345195319426737384641669 64724122392513259620313)
                  ·
                    rfl

theorem cell20_141806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_141806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141806 prefixEnd_141806 := by exact prefixLift 141806
  have htrace : WordTrace (prefixWord ++ tailWord_141806) baseStart_141806 baseEnd_141806 := by
    simpa [prefixWord, tailWord_141806, baseEnd_141806] using wordTrace_append hprefix tailTrace_141806
  have hstable : (prefixWord ++ tailWord_141806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141806).length < 2 ^ (prefixWord ++ tailWord_141806).sum := by decide
  have hdescent : baseEnd_141806 < baseStart_141806 := by decide
  rcases family_descends (prefixWord ++ tailWord_141806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141817 : List Nat := [1, 2, 1, 3, 1, 2, 3, 7]
def baseStart_141817 : Nat := 118140960795 + 141817 * 2 ^ 59
def prefixEnd_141817 : Nat := 4983230072969 + 3 ^ 40 * 141817 * 2
def baseEnd_141817 : Nat := 21576381030748703417867

theorem tailTrace_141817 : CollatzResearch.WordTrace tailWord_141817 prefixEnd_141817 21576381030748703417867 := by
  unfold tailWord_141817
  simp only [CollatzResearch.WordTrace]
  refine ⟨5172490927228704260423705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3448327284819136173615803 5172490927228704260423705)
  ·
    refine ⟨3879368195421528195317779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5172490927228704260423705 3879368195421528195317779)
    ·
      refine ⟨5819052293132292292976669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3879368195421528195317779 5819052293132292292976669)
      ·
        refine ⟨2182144609924609609866251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5819052293132292292976669 2182144609924609609866251)
        ·
          refine ⟨3273216914886914414799377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182144609924609609866251 3273216914886914414799377)
          ·
            refine ⟨2454912686165185811099533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3273216914886914414799377 2454912686165185811099533)
            ·
              refine ⟨920592257311944679162325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2454912686165185811099533 920592257311944679162325)
              ·
                refine ⟨21576381030748703417867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 920592257311944679162325 21576381030748703417867)
                ·
                  rfl

theorem cell20_141817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_141817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141817 prefixEnd_141817 := by exact prefixLift 141817
  have htrace : WordTrace (prefixWord ++ tailWord_141817) baseStart_141817 baseEnd_141817 := by
    simpa [prefixWord, tailWord_141817, baseEnd_141817] using wordTrace_append hprefix tailTrace_141817
  have hstable : (prefixWord ++ tailWord_141817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141817).length < 2 ^ (prefixWord ++ tailWord_141817).sum := by decide
  have hdescent : baseEnd_141817 < baseStart_141817 := by decide
  rcases family_descends (prefixWord ++ tailWord_141817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141879 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 3]
def baseStart_141879 : Nat := 118140960795 + 141879 * 2 ^ 59
def prefixEnd_141879 : Nat := 4983230072969 + 3 ^ 40 * 141879 * 2
def baseEnd_141879 : Nat := 64757441581649450186681

theorem tailTrace_141879 : CollatzResearch.WordTrace tailWord_141879 prefixEnd_141879 64757441581649450186681 := by
  unfold tailWord_141879
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174752253004088849180691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3449834835336059232787127 5174752253004088849180691)
  ·
    refine ⟨7762128379506133273771037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5174752253004088849180691 7762128379506133273771037)
    ·
      refine ⟨2910798142314799977664139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7762128379506133273771037 2910798142314799977664139)
      ·
        refine ⟨4366197213472199966496209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910798142314799977664139 4366197213472199966496209)
        ·
          refine ⟨3274647910104149974872157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4366197213472199966496209 3274647910104149974872157)
          ·
            refine ⟨1227992966289056240577059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3274647910104149974872157 1227992966289056240577059)
            ·
              refine ⟨1841989449433584360865589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227992966289056240577059 1841989449433584360865589)
              ·
                refine ⟨172686510884398533831149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1841989449433584360865589 172686510884398533831149)
                ·
                  refine ⟨64757441581649450186681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172686510884398533831149 64757441581649450186681)
                  ·
                    rfl

theorem cell20_141879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 3].length) (baseStart_141879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141879 prefixEnd_141879 := by exact prefixLift 141879
  have htrace : WordTrace (prefixWord ++ tailWord_141879) baseStart_141879 baseEnd_141879 := by
    simpa [prefixWord, tailWord_141879, baseEnd_141879] using wordTrace_append hprefix tailTrace_141879
  have hstable : (prefixWord ++ tailWord_141879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141879).length < 2 ^ (prefixWord ++ tailWord_141879).sum := by decide
  have hdescent : baseEnd_141879 < baseStart_141879 := by decide
  rcases family_descends (prefixWord ++ tailWord_141879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141889 : List Nat := [1, 2, 5, 1, 1, 3, 3, 4]
def baseStart_141889 : Nat := 118140960795 + 141889 * 2 ^ 59
def prefixEnd_141889 : Nat := 4983230072969 + 3 ^ 40 * 141889 * 2
def baseEnd_141889 : Nat := 21587335284711286617769

theorem tailTrace_141889 : CollatzResearch.WordTrace tailWord_141889 prefixEnd_141889 21587335284711286617769 := by
  unfold tailWord_141889
  simp only [CollatzResearch.WordTrace]
  refine ⟨5175116982967860557044721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3450077988645240371363147 5175116982967860557044721)
  ·
    refine ⟨3881337737225895417783541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5175116982967860557044721 3881337737225895417783541)
    ·
      refine ⟨363875412864927695417207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3881337737225895417783541 363875412864927695417207)
      ·
        refine ⟨545813119297391543125811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363875412864927695417207 545813119297391543125811)
        ·
          refine ⟨818719678946087314688717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545813119297391543125811 818719678946087314688717)
          ·
            refine ⟨307019879604782743008269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 818719678946087314688717 307019879604782743008269)
            ·
              refine ⟨115132454851793528628101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307019879604782743008269 115132454851793528628101)
              ·
                refine ⟨21587335284711286617769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115132454851793528628101 21587335284711286617769)
                ·
                  rfl

theorem cell20_141889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 4].length) (baseStart_141889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141889 prefixEnd_141889 := by exact prefixLift 141889
  have htrace : WordTrace (prefixWord ++ tailWord_141889) baseStart_141889 baseEnd_141889 := by
    simpa [prefixWord, tailWord_141889, baseEnd_141889] using wordTrace_append hprefix tailTrace_141889
  have hstable : (prefixWord ++ tailWord_141889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141889).length < 2 ^ (prefixWord ++ tailWord_141889).sum := by decide
  have hdescent : baseEnd_141889 < baseStart_141889 := by decide
  rcases family_descends (prefixWord ++ tailWord_141889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141903 : List Nat := [1, 1, 2, 1, 1, 2, 5, 5, 2]
def baseStart_141903 : Nat := 118140960795 + 141903 * 2 ^ 59
def prefixEnd_141903 : Nat := 4983230072969 + 3 ^ 40 * 141903 * 2
def baseEnd_141903 : Nat := 64768395835612033386583

theorem tailTrace_141903 : CollatzResearch.WordTrace tailWord_141903 prefixEnd_141903 64768395835612033386583 := by
  unfold tailWord_141903
  simp only [CollatzResearch.WordTrace]
  refine ⟨5175627604917140948054363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3450418403278093965369575 5175627604917140948054363)
  ·
    refine ⟨7763441407375711422081545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5175627604917140948054363 7763441407375711422081545)
    ·
      refine ⟨5822581055531783566561159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7763441407375711422081545 5822581055531783566561159)
      ·
        refine ⟨8733871583297675349841739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5822581055531783566561159 8733871583297675349841739)
        ·
          refine ⟨13100807374946513024762609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8733871583297675349841739 13100807374946513024762609)
          ·
            refine ⟨9825605531209884768571957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13100807374946513024762609 9825605531209884768571957)
            ·
              refine ⟨921150518550926697053621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9825605531209884768571957 921150518550926697053621)
              ·
                refine ⟨86357861114149377848777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 921150518550926697053621 86357861114149377848777)
                ·
                  refine ⟨64768395835612033386583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86357861114149377848777 64768395835612033386583)
                  ·
                    rfl

theorem cell20_141903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 2].length) (baseStart_141903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141903 prefixEnd_141903 := by exact prefixLift 141903
  have htrace : WordTrace (prefixWord ++ tailWord_141903) baseStart_141903 baseEnd_141903 := by
    simpa [prefixWord, tailWord_141903, baseEnd_141903] using wordTrace_append hprefix tailTrace_141903
  have hstable : (prefixWord ++ tailWord_141903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141903).length < 2 ^ (prefixWord ++ tailWord_141903).sum := by decide
  have hdescent : baseEnd_141903 < baseStart_141903 := by decide
  rcases family_descends (prefixWord ++ tailWord_141903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141948 : List Nat := [2, 2, 2, 1, 1, 2, 6, 4]
def baseStart_141948 : Nat := 118140960795 + 141948 * 2 ^ 59
def prefixEnd_141948 : Nat := 4983230072969 + 3 ^ 40 * 141948 * 2
def baseEnd_141948 : Nat := 21596311687263958962133

theorem tailTrace_141948 : CollatzResearch.WordTrace tailWord_141948 prefixEnd_141948 21596311687263958962133 := by
  unfold tailWord_141948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588634444877056816721249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3451512593169409088961665 2588634444877056816721249)
  ·
    refine ⟨1941475833657792612540937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2588634444877056816721249 1941475833657792612540937)
    ·
      refine ⟨1456106875243344459405703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1941475833657792612540937 1456106875243344459405703)
      ·
        refine ⟨2184160312865016689108555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456106875243344459405703 2184160312865016689108555)
        ·
          refine ⟨3276240469297525033662833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184160312865016689108555 3276240469297525033662833)
          ·
            refine ⟨2457180351973143775247125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3276240469297525033662833 2457180351973143775247125)
            ·
              refine ⟨115180328998741114464709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2457180351973143775247125 115180328998741114464709)
              ·
                refine ⟨21596311687263958962133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115180328998741114464709 21596311687263958962133)
                ·
                  rfl

theorem cell20_141948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_141948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141948 prefixEnd_141948 := by exact prefixLift 141948
  have htrace : WordTrace (prefixWord ++ tailWord_141948) baseStart_141948 baseEnd_141948 := by
    simpa [prefixWord, tailWord_141948, baseEnd_141948] using wordTrace_append hprefix tailTrace_141948
  have hstable : (prefixWord ++ tailWord_141948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141948).length < 2 ^ (prefixWord ++ tailWord_141948).sum := by decide
  have hdescent : baseEnd_141948 < baseStart_141948 := by decide
  rcases family_descends (prefixWord ++ tailWord_141948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141972 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_141972 : Nat := 118140960795 + 141972 * 2 ^ 59
def prefixEnd_141972 : Nat := 4983230072969 + 3 ^ 40 * 141972 * 2
def baseEnd_141972 : Nat := 64799889315754460086301

theorem tailTrace_141972 : CollatzResearch.WordTrace tailWord_141972 prefixEnd_141972 64799889315754460086301 := by
  unfold tailWord_141972
  simp only [CollatzResearch.WordTrace]
  refine ⟨2589072120833582866158085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3452096161111443821544113 2589072120833582866158085)
  ·
    refine ⟨485451022656296787404641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2589072120833582866158085 485451022656296787404641)
    ·
      refine ⟨364088266992222590553481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 485451022656296787404641 364088266992222590553481)
      ·
        refine ⟨273066200244166942915111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364088266992222590553481 273066200244166942915111)
        ·
          refine ⟨409599300366250414372667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273066200244166942915111 409599300366250414372667)
          ·
            refine ⟨614398950549375621559001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409599300366250414372667 614398950549375621559001)
            ·
              refine ⟨460799212912031716169251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614398950549375621559001 460799212912031716169251)
              ·
                refine ⟨691198819368047574253877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460799212912031716169251 691198819368047574253877)
                ·
                  refine ⟨64799889315754460086301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 691198819368047574253877 64799889315754460086301)
                  ·
                    rfl

theorem cell20_141972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_141972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_141972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_141972 prefixEnd_141972 := by exact prefixLift 141972
  have htrace : WordTrace (prefixWord ++ tailWord_141972) baseStart_141972 baseEnd_141972 := by
    simpa [prefixWord, tailWord_141972, baseEnd_141972] using wordTrace_append hprefix tailTrace_141972
  have hstable : (prefixWord ++ tailWord_141972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141972).length < 2 ^ (prefixWord ++ tailWord_141972).sum := by decide
  have hdescent : baseEnd_141972 < baseStart_141972 := by decide
  rcases family_descends (prefixWord ++ tailWord_141972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142103 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 3]
def baseStart_142103 : Nat := 118140960795 + 142103 * 2 ^ 59
def prefixEnd_142103 : Nat := 4983230072969 + 3 ^ 40 * 142103 * 2
def baseEnd_142103 : Nat := 64859681285300226719099

theorem tailTrace_142103 : CollatzResearch.WordTrace tailWord_142103 prefixEnd_142103 64859681285300226719099 := by
  unfold tailWord_142103
  simp only [CollatzResearch.WordTrace]
  refine ⟨5182922204192575105334963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3455281469461716736889975 5182922204192575105334963)
  ·
    refine ⟨7774383306288862658002445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5182922204192575105334963 7774383306288862658002445)
    ·
      refine ⟨2915393739858323496750917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7774383306288862658002445 2915393739858323496750917)
      ·
        refine ⟨546636326223435655640797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2915393739858323496750917 546636326223435655640797)
        ·
          refine ⟨204988622333788370865299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 546636326223435655640797 204988622333788370865299)
          ·
            refine ⟨307482933500682556297949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204988622333788370865299 307482933500682556297949)
            ·
              refine ⟨115306100062755958611731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307482933500682556297949 115306100062755958611731)
              ·
                refine ⟨172959150094133937917597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115306100062755958611731 172959150094133937917597)
                ·
                  refine ⟨64859681285300226719099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172959150094133937917597 64859681285300226719099)
                  ·
                    rfl

theorem cell20_142103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 3].length) (baseStart_142103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142103 prefixEnd_142103 := by exact prefixLift 142103
  have htrace : WordTrace (prefixWord ++ tailWord_142103) baseStart_142103 baseEnd_142103 := by
    simpa [prefixWord, tailWord_142103, baseEnd_142103] using wordTrace_append hprefix tailTrace_142103
  have hstable : (prefixWord ++ tailWord_142103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142103).length < 2 ^ (prefixWord ++ tailWord_142103).sum := by decide
  have hdescent : baseEnd_142103 < baseStart_142103 := by decide
  rcases family_descends (prefixWord ++ tailWord_142103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142134 : List Nat := [5, 1, 2, 2, 3, 1, 6]
def baseStart_142134 : Nat := 118140960795 + 142134 * 2 ^ 59
def prefixEnd_142134 : Nat := 4983230072969 + 3 ^ 40 * 142134 * 2
def baseEnd_142134 : Nat := 7208203392222432965071

theorem tailTrace_142134 : CollatzResearch.WordTrace tailWord_142134 prefixEnd_142134 7208203392222432965071 := by
  unfold tailWord_142134
  simp only [CollatzResearch.WordTrace]
  refine ⟨324003304192516712482091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3456035244720178266475637 324003304192516712482091)
  ·
    refine ⟨486004956288775068723137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 324003304192516712482091 486004956288775068723137)
    ·
      refine ⟨364503717216581301542353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 486004956288775068723137 364503717216581301542353)
      ·
        refine ⟨273377787912435976156765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364503717216581301542353 273377787912435976156765)
        ·
          refine ⟨102516670467163491058787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273377787912435976156765 102516670467163491058787)
          ·
            refine ⟨153775005700745236588181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102516670467163491058787 153775005700745236588181)
            ·
              refine ⟨7208203392222432965071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 153775005700745236588181 7208203392222432965071)
              ·
                rfl

theorem cell20_142134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 6].length) (baseStart_142134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142134 prefixEnd_142134 := by exact prefixLift 142134
  have htrace : WordTrace (prefixWord ++ tailWord_142134) baseStart_142134 baseEnd_142134 := by
    simpa [prefixWord, tailWord_142134, baseEnd_142134] using wordTrace_append hprefix tailTrace_142134
  have hstable : (prefixWord ++ tailWord_142134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142134).length < 2 ^ (prefixWord ++ tailWord_142134).sum := by decide
  have hdescent : baseEnd_142134 < baseStart_142134 := by decide
  rcases family_descends (prefixWord ++ tailWord_142134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142138 : List Nat := [3, 1, 1, 1, 6, 2, 6]
def baseStart_142138 : Nat := 118140960795 + 142138 * 2 ^ 59
def prefixEnd_142138 : Nat := 4983230072969 + 3 ^ 40 * 142138 * 2
def baseEnd_142138 : Nat := 7208406248777295616921

theorem tailTrace_142138 : CollatzResearch.WordTrace tailWord_142138 prefixEnd_142138 7208406248777295616921 := by
  unfold tailWord_142138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1296049689766444020714767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3456132506043850721906045 1296049689766444020714767)
  ·
    refine ⟨1944074534649666031072151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1296049689766444020714767 1944074534649666031072151)
    ·
      refine ⟨2916111801974499046608227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1944074534649666031072151 2916111801974499046608227)
      ·
        refine ⟨4374167702961748569912341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916111801974499046608227 4374167702961748569912341)
        ·
          refine ⟨205039111076331964214641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4374167702961748569912341 205039111076331964214641)
          ·
            refine ⟨153779333307248973160981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205039111076331964214641 153779333307248973160981)
            ·
              refine ⟨7208406248777295616921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 153779333307248973160981 7208406248777295616921)
              ·
                rfl

theorem cell20_142138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 6].length) (baseStart_142138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142138 prefixEnd_142138 := by exact prefixLift 142138
  have htrace : WordTrace (prefixWord ++ tailWord_142138) baseStart_142138 baseEnd_142138 := by
    simpa [prefixWord, tailWord_142138, baseEnd_142138] using wordTrace_append hprefix tailTrace_142138
  have hstable : (prefixWord ++ tailWord_142138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142138).length < 2 ^ (prefixWord ++ tailWord_142138).sum := by decide
  have hdescent : baseEnd_142138 < baseStart_142138 := by decide
  rcases family_descends (prefixWord ++ tailWord_142138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142197 : List Nat := [1, 3, 4, 1, 1, 10]
def baseStart_142197 : Nat := 118140960795 + 142197 * 2 ^ 59
def prefixEnd_142197 : Nat := 4983230072969 + 3 ^ 40 * 142197 * 2
def baseEnd_142197 : Nat := 2403799460987173243903

theorem tailTrace_142197 : CollatzResearch.WordTrace tailWord_142197 prefixEnd_142197 2403799460987173243903 := by
  unfold tailWord_142197
  simp only [CollatzResearch.WordTrace]
  refine ⟨5186350665852029159256845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3457567110568019439504563 5186350665852029159256845)
  ·
    refine ⟨1944881499694510934721317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5186350665852029159256845 1944881499694510934721317)
    ·
      refine ⟨364665281192720800260247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1944881499694510934721317 364665281192720800260247)
      ·
        refine ⟨546997921789081200390371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364665281192720800260247 546997921789081200390371)
        ·
          refine ⟨820496882683621800585557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546997921789081200390371 820496882683621800585557)
          ·
            refine ⟨2403799460987173243903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 820496882683621800585557 2403799460987173243903)
            ·
              rfl

theorem cell20_142197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 10].length) (baseStart_142197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142197 prefixEnd_142197 := by exact prefixLift 142197
  have htrace : WordTrace (prefixWord ++ tailWord_142197) baseStart_142197 baseEnd_142197 := by
    simpa [prefixWord, tailWord_142197, baseEnd_142197] using wordTrace_append hprefix tailTrace_142197
  have hstable : (prefixWord ++ tailWord_142197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142197).length < 2 ^ (prefixWord ++ tailWord_142197).sum := by decide
  have hdescent : baseEnd_142197 < baseStart_142197 := by decide
  rcases family_descends (prefixWord ++ tailWord_142197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142204 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_142204 : Nat := 118140960795 + 142204 * 2 ^ 59
def prefixEnd_142204 : Nat := 4983230072969 + 3 ^ 40 * 142204 * 2
def baseEnd_142204 : Nat := 64905780437392764352019

theorem tailTrace_142204 : CollatzResearch.WordTrace tailWord_142204 prefixEnd_142204 64905780437392764352019 := by
  unfold tailWord_142204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2593302988413334677380833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3457737317884446236507777 2593302988413334677380833)
  ·
    refine ⟨1944977241310001008035625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2593302988413334677380833 1944977241310001008035625)
    ·
      refine ⟨1458732930982500756026719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1944977241310001008035625 1458732930982500756026719)
      ·
        refine ⟨2188099396473751134040079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1458732930982500756026719 2188099396473751134040079)
        ·
          refine ⟨3282149094710626701060119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188099396473751134040079 3282149094710626701060119)
          ·
            refine ⟨4923223642065940051590179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3282149094710626701060119 4923223642065940051590179)
            ·
              refine ⟨7384835463098910077385269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923223642065940051590179 7384835463098910077385269)
              ·
                refine ⟨692328324665522819754869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7384835463098910077385269 692328324665522819754869)
                ·
                  refine ⟨64905780437392764352019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 692328324665522819754869 64905780437392764352019)
                  ·
                    rfl

theorem cell20_142204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_142204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142204 prefixEnd_142204 := by exact prefixLift 142204
  have htrace : WordTrace (prefixWord ++ tailWord_142204) baseStart_142204 baseEnd_142204 := by
    simpa [prefixWord, tailWord_142204, baseEnd_142204] using wordTrace_append hprefix tailTrace_142204
  have hstable : (prefixWord ++ tailWord_142204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142204).length < 2 ^ (prefixWord ++ tailWord_142204).sum := by decide
  have hdescent : baseEnd_142204 < baseStart_142204 := by decide
  rcases family_descends (prefixWord ++ tailWord_142204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142249 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_142249 : Nat := 118140960795 + 142249 * 2 ^ 59
def prefixEnd_142249 : Nat := 4983230072969 + 3 ^ 40 * 142249 * 2
def baseEnd_142249 : Nat := 64926319663572607851835

theorem tailTrace_142249 : CollatzResearch.WordTrace tailWord_142249 prefixEnd_142249 64926319663572607851835 := by
  unfold tailWord_142249
  simp only [CollatzResearch.WordTrace]
  refine ⟨5188247261663642040149801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3458831507775761360099867 5188247261663642040149801)
  ·
    refine ⟨3891185446247731530112351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5188247261663642040149801 3891185446247731530112351)
    ·
      refine ⟨5836778169371597295168527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3891185446247731530112351 5836778169371597295168527)
      ·
        refine ⟨8755167254057395942752791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5836778169371597295168527 8755167254057395942752791)
        ·
          refine ⟨13132750881086093914129187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8755167254057395942752791 13132750881086093914129187)
          ·
            refine ⟨19699126321629140871193781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13132750881086093914129187 19699126321629140871193781)
            ·
              refine ⟨1846793092652731956674417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19699126321629140871193781 1846793092652731956674417)
              ·
                refine ⟨1385094819489548967505813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846793092652731956674417 1385094819489548967505813)
                ·
                  refine ⟨64926319663572607851835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1385094819489548967505813 64926319663572607851835)
                  ·
                    rfl

theorem cell20_142249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_142249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142249 prefixEnd_142249 := by exact prefixLift 142249
  have htrace : WordTrace (prefixWord ++ tailWord_142249) baseStart_142249 baseEnd_142249 := by
    simpa [prefixWord, tailWord_142249, baseEnd_142249] using wordTrace_append hprefix tailTrace_142249
  have hstable : (prefixWord ++ tailWord_142249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142249).length < 2 ^ (prefixWord ++ tailWord_142249).sum := by decide
  have hdescent : baseEnd_142249 < baseStart_142249 := by decide
  rcases family_descends (prefixWord ++ tailWord_142249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142266 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_142266 : Nat := 118140960795 + 142266 * 2 ^ 59
def prefixEnd_142266 : Nat := 4983230072969 + 3 ^ 40 * 142266 * 2
def baseEnd_142266 : Nat := 64934078926796104285099

theorem tailTrace_142266 : CollatzResearch.WordTrace tailWord_142266 prefixEnd_142266 64934078926796104285099 := by
  unfold tailWord_142266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297216825650513485879663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3459244868401369295679101 1297216825650513485879663)
  ·
    refine ⟨1945825238475770228819495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1297216825650513485879663 1945825238475770228819495)
    ·
      refine ⟨2918737857713655343229243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1945825238475770228819495 2918737857713655343229243)
      ·
        refine ⟨4378106786570483014843865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918737857713655343229243 4378106786570483014843865)
        ·
          refine ⟨3283580089927862261132899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4378106786570483014843865 3283580089927862261132899)
          ·
            refine ⟨4925370134891793391699349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3283580089927862261132899 4925370134891793391699349)
            ·
              refine ⟨230876725073052815235907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4925370134891793391699349 230876725073052815235907)
              ·
                refine ⟨346315087609579222853861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230876725073052815235907 346315087609579222853861)
                ·
                  refine ⟨64934078926796104285099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 346315087609579222853861 64934078926796104285099)
                  ·
                    rfl

theorem cell20_142266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_142266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142266 prefixEnd_142266 := by exact prefixLift 142266
  have htrace : WordTrace (prefixWord ++ tailWord_142266) baseStart_142266 baseEnd_142266 := by
    simpa [prefixWord, tailWord_142266, baseEnd_142266] using wordTrace_append hprefix tailTrace_142266
  have hstable : (prefixWord ++ tailWord_142266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142266).length < 2 ^ (prefixWord ++ tailWord_142266).sum := by decide
  have hdescent : baseEnd_142266 < baseStart_142266 := by decide
  rcases family_descends (prefixWord ++ tailWord_142266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142290 : List Nat := [3, 2, 2, 3, 1, 2, 1, 6]
def baseStart_142290 : Nat := 118140960795 + 142290 * 2 ^ 59
def prefixEnd_142290 : Nat := 4983230072969 + 3 ^ 40 * 142290 * 2
def baseEnd_142290 : Nat := 21648344393586229161667

theorem tailTrace_142290 : CollatzResearch.WordTrace tailWord_142290 prefixEnd_142290 21648344393586229161667 := by
  unfold tailWord_142290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297435663628776510598081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3459828436343404028261549 1297435663628776510598081)
  ·
    refine ⟨973076747721582382948561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1297435663628776510598081 973076747721582382948561)
    ·
      refine ⟨729807560791186787211421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 973076747721582382948561 729807560791186787211421)
      ·
        refine ⟨273677835296695045204283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 729807560791186787211421 273677835296695045204283)
        ·
          refine ⟨410516752945042567806425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273677835296695045204283 410516752945042567806425)
          ·
            refine ⟨307887564708781925854819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410516752945042567806425 307887564708781925854819)
            ·
              refine ⟨461831347063172888782229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307887564708781925854819 461831347063172888782229)
              ·
                refine ⟨21648344393586229161667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 461831347063172888782229 21648344393586229161667)
                ·
                  rfl

theorem cell20_142290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_142290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142290 prefixEnd_142290 := by exact prefixLift 142290
  have htrace : WordTrace (prefixWord ++ tailWord_142290) baseStart_142290 baseEnd_142290 := by
    simpa [prefixWord, tailWord_142290, baseEnd_142290] using wordTrace_append hprefix tailTrace_142290
  have hstable : (prefixWord ++ tailWord_142290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142290).length < 2 ^ (prefixWord ++ tailWord_142290).sum := by decide
  have hdescent : baseEnd_142290 < baseStart_142290 := by decide
  rcases family_descends (prefixWord ++ tailWord_142290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142311 : List Nat := [1, 1, 5, 2, 2, 1, 8]
def baseStart_142311 : Nat := 118140960795 + 142311 * 2 ^ 59
def prefixEnd_142311 : Nat := 4983230072969 + 3 ^ 40 * 142311 * 2
def baseEnd_142311 : Nat := 7217179794775105309435

theorem tailTrace_142311 : CollatzResearch.WordTrace tailWord_142311 prefixEnd_142311 7217179794775105309435 := by
  unfold tailWord_142311
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190508587439026628906787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3460339058292684419271191 5190508587439026628906787)
  ·
    refine ⟨7785762881158539943360181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5190508587439026628906787 7785762881158539943360181)
    ·
      refine ⟨729915270108613119690017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7785762881158539943360181 729915270108613119690017)
      ·
        refine ⟨547436452581459839767513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 729915270108613119690017 547436452581459839767513)
        ·
          refine ⟨410577339436094879825635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547436452581459839767513 410577339436094879825635)
          ·
            refine ⟨615866009154142319738453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410577339436094879825635 615866009154142319738453)
            ·
              refine ⟨7217179794775105309435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 615866009154142319738453 7217179794775105309435)
              ·
                rfl

theorem cell20_142311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 8].length) (baseStart_142311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142311 prefixEnd_142311 := by exact prefixLift 142311
  have htrace : WordTrace (prefixWord ++ tailWord_142311) baseStart_142311 baseEnd_142311 := by
    simpa [prefixWord, tailWord_142311, baseEnd_142311] using wordTrace_append hprefix tailTrace_142311
  have hstable : (prefixWord ++ tailWord_142311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142311).length < 2 ^ (prefixWord ++ tailWord_142311).sum := by decide
  have hdescent : baseEnd_142311 < baseStart_142311 := by decide
  rcases family_descends (prefixWord ++ tailWord_142311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142321 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 4]
def baseStart_142321 : Nat := 118140960795 + 142321 * 2 ^ 59
def prefixEnd_142321 : Nat := 4983230072969 + 3 ^ 40 * 142321 * 2
def baseEnd_142321 : Nat := 64959182425460357451541

theorem tailTrace_142321 : CollatzResearch.WordTrace tailWord_142321 prefixEnd_142321 64959182425460357451541 := by
  unfold tailWord_142321
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190873317402798336770817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3460582211601865557847211 5190873317402798336770817)
  ·
    refine ⟨3893154988052098752578113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5190873317402798336770817 3893154988052098752578113)
    ·
      refine ⟨2919866241039074064433585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3893154988052098752578113 2919866241039074064433585)
      ·
        refine ⟨2189899680779305548325189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2919866241039074064433585 2189899680779305548325189)
        ·
          refine ⟨410606190146119790310973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2189899680779305548325189 410606190146119790310973)
          ·
            refine ⟨153977321304794921366615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 410606190146119790310973 153977321304794921366615)
            ·
              refine ⟨230965981957192382049923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153977321304794921366615 230965981957192382049923)
              ·
                refine ⟨346448972935788573074885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230965981957192382049923 346448972935788573074885)
                ·
                  refine ⟨64959182425460357451541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 346448972935788573074885 64959182425460357451541)
                  ·
                    rfl

theorem cell20_142321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_142321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142321 prefixEnd_142321 := by exact prefixLift 142321
  have htrace : WordTrace (prefixWord ++ tailWord_142321) baseStart_142321 baseEnd_142321 := by
    simpa [prefixWord, tailWord_142321, baseEnd_142321] using wordTrace_append hprefix tailTrace_142321
  have hstable : (prefixWord ++ tailWord_142321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142321).length < 2 ^ (prefixWord ++ tailWord_142321).sum := by decide
  have hdescent : baseEnd_142321 < baseStart_142321 := by decide
  rcases family_descends (prefixWord ++ tailWord_142321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142373 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 3]
def baseStart_142373 : Nat := 118140960795 + 142373 * 2 ^ 59
def prefixEnd_142373 : Nat := 4983230072969 + 3 ^ 40 * 142373 * 2
def baseEnd_142373 : Nat := 64982916642379287717995

theorem tailTrace_142373 : CollatzResearch.WordTrace tailWord_142373 prefixEnd_142373 64982916642379287717995 := by
  unfold tailWord_142373
  simp only [CollatzResearch.WordTrace]
  refine ⟨5192769913214411217663773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3461846608809607478442515 5192769913214411217663773)
  ·
    refine ⟨1947288717455404206623915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5192769913214411217663773 1947288717455404206623915)
    ·
      refine ⟨2920933076183106309935873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947288717455404206623915 2920933076183106309935873)
      ·
        refine ⟨2190699807137329732451905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2920933076183106309935873 2190699807137329732451905)
        ·
          refine ⟨1643024855352997299338929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2190699807137329732451905 1643024855352997299338929)
          ·
            refine ⟨1232268641514747974504197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1643024855352997299338929 1232268641514747974504197)
            ·
              refine ⟨231050370284015245219537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1232268641514747974504197 231050370284015245219537)
              ·
                refine ⟨173287777713011433914653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231050370284015245219537 173287777713011433914653)
                ·
                  refine ⟨64982916642379287717995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173287777713011433914653 64982916642379287717995)
                  ·
                    rfl

theorem cell20_142373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_142373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142373 prefixEnd_142373 := by exact prefixLift 142373
  have htrace : WordTrace (prefixWord ++ tailWord_142373) baseStart_142373 baseEnd_142373 := by
    simpa [prefixWord, tailWord_142373, baseEnd_142373] using wordTrace_append hprefix tailTrace_142373
  have hstable : (prefixWord ++ tailWord_142373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142373).length < 2 ^ (prefixWord ++ tailWord_142373).sum := by decide
  have hdescent : baseEnd_142373 < baseStart_142373 := by decide
  rcases family_descends (prefixWord ++ tailWord_142373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142390 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_142390 : Nat := 118140960795 + 142390 * 2 ^ 59
def prefixEnd_142390 : Nat := 4983230072969 + 3 ^ 40 * 142390 * 2
def baseEnd_142390 : Nat := 64990675905602784151259

theorem tailTrace_142390 : CollatzResearch.WordTrace tailWord_142390 prefixEnd_142390 64990675905602784151259 := by
  unfold tailWord_142390
  simp only [CollatzResearch.WordTrace]
  refine ⟨324586872134551445064539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3462259969435215414021749 324586872134551445064539)
  ·
    refine ⟨486880308201827167596809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 324586872134551445064539 486880308201827167596809)
    ·
      refine ⟨365160231151370375697607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 486880308201827167596809 365160231151370375697607)
      ·
        refine ⟨547740346727055563546411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365160231151370375697607 547740346727055563546411)
        ·
          refine ⟨821610520090583345319617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547740346727055563546411 821610520090583345319617)
          ·
            refine ⟨616207890067937508989713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821610520090583345319617 616207890067937508989713)
            ·
              refine ⟨462155917550953131742285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616207890067937508989713 462155917550953131742285)
              ·
                refine ⟨173308469081607424403357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 462155917550953131742285 173308469081607424403357)
                ·
                  refine ⟨64990675905602784151259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173308469081607424403357 64990675905602784151259)
                  ·
                    rfl

theorem cell20_142390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_142390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142390 prefixEnd_142390 := by exact prefixLift 142390
  have htrace : WordTrace (prefixWord ++ tailWord_142390) baseStart_142390 baseEnd_142390 := by
    simpa [prefixWord, tailWord_142390, baseEnd_142390] using wordTrace_append hprefix tailTrace_142390
  have hstable : (prefixWord ++ tailWord_142390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142390).length < 2 ^ (prefixWord ++ tailWord_142390).sum := by decide
  have hdescent : baseEnd_142390 < baseStart_142390 := by decide
  rcases family_descends (prefixWord ++ tailWord_142390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142432 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_142432 : Nat := 118140960795 + 142432 * 2 ^ 59
def prefixEnd_142432 : Nat := 4983230072969 + 3 ^ 40 * 142432 * 2
def baseEnd_142432 : Nat := 65009845850037304751087

theorem tailTrace_142432 : CollatzResearch.WordTrace tailWord_142432 prefixEnd_142432 65009845850037304751087 := by
  unfold tailWord_142432
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597460910000332147030775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3463281213333776196041033 2597460910000332147030775)
  ·
    refine ⟨3896191365000498220546163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2597460910000332147030775 3896191365000498220546163)
    ·
      refine ⟨5844287047500747330819245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3896191365000498220546163 5844287047500747330819245)
      ·
        refine ⟨2191607642812780249057217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5844287047500747330819245 2191607642812780249057217)
        ·
          refine ⟨1643705732109585186792913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2191607642812780249057217 1643705732109585186792913)
          ·
            refine ⟨1232779299082188890094685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1643705732109585186792913 1232779299082188890094685)
            ·
              refine ⟨462292237155820833785507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1232779299082188890094685 462292237155820833785507)
              ·
                refine ⟨693438355733731250678261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462292237155820833785507 693438355733731250678261)
                ·
                  refine ⟨65009845850037304751087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 693438355733731250678261 65009845850037304751087)
                  ·
                    rfl

theorem cell20_142432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_142432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142432 prefixEnd_142432 := by exact prefixLift 142432
  have htrace : WordTrace (prefixWord ++ tailWord_142432) baseStart_142432 baseEnd_142432 := by
    simpa [prefixWord, tailWord_142432, baseEnd_142432] using wordTrace_append hprefix tailTrace_142432
  have hstable : (prefixWord ++ tailWord_142432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142432).length < 2 ^ (prefixWord ++ tailWord_142432).sum := by decide
  have hdescent : baseEnd_142432 < baseStart_142432 := by decide
  rcases family_descends (prefixWord ++ tailWord_142432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142469 : List Nat := [1, 3, 1, 1, 7, 1, 1, 3, 2]
def baseStart_142469 : Nat := 118140960795 + 142469 * 2 ^ 59
def prefixEnd_142469 : Nat := 4983230072969 + 3 ^ 40 * 142469 * 2
def baseEnd_142469 : Nat := 65026733658229620517603

theorem tailTrace_142469 : CollatzResearch.WordTrace tailWord_142469 prefixEnd_142469 65026733658229620517603 := by
  unfold tailWord_142469
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196271320866619613158461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3464180880577746408772307 5196271320866619613158461)
  ·
    refine ⟨1948601745324982354934423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5196271320866619613158461 1948601745324982354934423)
    ·
      refine ⟨2922902617987473532401635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1948601745324982354934423 2922902617987473532401635)
      ·
        refine ⟨4384353926981210298602453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2922902617987473532401635 4384353926981210298602453)
        ·
          refine ⟨102758295163622116373495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4384353926981210298602453 102758295163622116373495)
          ·
            refine ⟨154137442745433174560243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102758295163622116373495 154137442745433174560243)
            ·
              refine ⟨231206164118149761840365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154137442745433174560243 231206164118149761840365)
              ·
                refine ⟨86702311544306160690137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231206164118149761840365 86702311544306160690137)
                ·
                  refine ⟨65026733658229620517603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86702311544306160690137 65026733658229620517603)
                  ·
                    rfl

theorem cell20_142469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_142469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142469 prefixEnd_142469 := by exact prefixLift 142469
  have htrace : WordTrace (prefixWord ++ tailWord_142469) baseStart_142469 baseEnd_142469 := by
    simpa [prefixWord, tailWord_142469, baseEnd_142469] using wordTrace_append hprefix tailTrace_142469
  have hstable : (prefixWord ++ tailWord_142469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142469).length < 2 ^ (prefixWord ++ tailWord_142469).sum := by decide
  have hdescent : baseEnd_142469 < baseStart_142469 := by decide
  rcases family_descends (prefixWord ++ tailWord_142469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142473 : List Nat := [1, 2, 1, 1, 4, 3, 3, 3, 2]
def baseStart_142473 : Nat := 118140960795 + 142473 * 2 ^ 59
def prefixEnd_142473 : Nat := 4983230072969 + 3 ^ 40 * 142473 * 2
def baseEnd_142473 : Nat := 65028559367223384384253

theorem tailTrace_142473 : CollatzResearch.WordTrace tailWord_142473 prefixEnd_142473 65028559367223384384253 := by
  unfold tailWord_142473
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196417212852128296304073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3464278141901418864202715 5196417212852128296304073)
  ·
    refine ⟨3897312909639096222228055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5196417212852128296304073 3897312909639096222228055)
    ·
      refine ⟨5845969364458644333342083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3897312909639096222228055 5845969364458644333342083)
      ·
        refine ⟨8768954046687966500013125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5845969364458644333342083 8768954046687966500013125)
        ·
          refine ⟨1644178883753993718752461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8768954046687966500013125 1644178883753993718752461)
          ·
            refine ⟨616567081407747644532173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1644178883753993718752461 616567081407747644532173)
            ·
              refine ⟨231212655527905366699565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 616567081407747644532173 231212655527905366699565)
              ·
                refine ⟨86704745822964512512337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231212655527905366699565 86704745822964512512337)
                ·
                  refine ⟨65028559367223384384253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86704745822964512512337 65028559367223384384253)
                  ·
                    rfl

theorem cell20_142473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_142473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142473 prefixEnd_142473 := by exact prefixLift 142473
  have htrace : WordTrace (prefixWord ++ tailWord_142473) baseStart_142473 baseEnd_142473 := by
    simpa [prefixWord, tailWord_142473, baseEnd_142473] using wordTrace_append hprefix tailTrace_142473
  have hstable : (prefixWord ++ tailWord_142473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142473).length < 2 ^ (prefixWord ++ tailWord_142473).sum := by decide
  have hdescent : baseEnd_142473 < baseStart_142473 := by decide
  rcases family_descends (prefixWord ++ tailWord_142473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142501 : List Nat := [1, 3, 1, 2, 1, 5, 2, 5]
def baseStart_142501 : Nat := 118140960795 + 142501 * 2 ^ 59
def prefixEnd_142501 : Nat := 4983230072969 + 3 ^ 40 * 142501 * 2
def baseEnd_142501 : Nat := 21680446443393243816935

theorem tailTrace_142501 : CollatzResearch.WordTrace tailWord_142501 prefixEnd_142501 21680446443393243816935 := by
  unfold tailWord_142501
  simp only [CollatzResearch.WordTrace]
  refine ⟨5197438456750689078323357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3464958971167126052215571 5197438456750689078323357)
  ·
    refine ⟨1949039421281508404371259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5197438456750689078323357 1949039421281508404371259)
    ·
      refine ⟨2923559131922262606556889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1949039421281508404371259 2923559131922262606556889)
      ·
        refine ⟨2192669348941696954917667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2923559131922262606556889 2192669348941696954917667)
        ·
          refine ⟨3289004023412545432376501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192669348941696954917667 3289004023412545432376501)
          ·
            refine ⟨308344127194926134285297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3289004023412545432376501 308344127194926134285297)
            ·
              refine ⟨231258095396194600713973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308344127194926134285297 231258095396194600713973)
              ·
                refine ⟨21680446443393243816935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231258095396194600713973 21680446443393243816935)
                ·
                  rfl

theorem cell20_142501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_142501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142501 prefixEnd_142501 := by exact prefixLift 142501
  have htrace : WordTrace (prefixWord ++ tailWord_142501) baseStart_142501 baseEnd_142501 := by
    simpa [prefixWord, tailWord_142501, baseEnd_142501] using wordTrace_append hprefix tailTrace_142501
  have hstable : (prefixWord ++ tailWord_142501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142501).length < 2 ^ (prefixWord ++ tailWord_142501).sum := by decide
  have hdescent : baseEnd_142501 < baseStart_142501 := by decide
  rcases family_descends (prefixWord ++ tailWord_142501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142515 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_142515 : Nat := 118140960795 + 142515 * 2 ^ 59
def prefixEnd_142515 : Nat := 4983230072969 + 3 ^ 40 * 142515 * 2
def baseEnd_142515 : Nat := 65047729311657904984081

theorem tailTrace_142515 : CollatzResearch.WordTrace tailWord_142515 prefixEnd_142515 65047729311657904984081 := by
  unfold tailWord_142515
  simp only [CollatzResearch.WordTrace]
  refine ⟨5197949078699969469332999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3465299385799979646221999 5197949078699969469332999)
  ·
    refine ⟨7796923618049954203999499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5197949078699969469332999 7796923618049954203999499)
    ·
      refine ⟨11695385427074931305999249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7796923618049954203999499 11695385427074931305999249)
      ·
        refine ⟨8771539070306198479499437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11695385427074931305999249 8771539070306198479499437)
        ·
          refine ⟨3289327151364824429812289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8771539070306198479499437 3289327151364824429812289)
          ·
            refine ⟨2466995363523618322359217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3289327151364824429812289 2466995363523618322359217)
            ·
              refine ⟨1850246522642713741769413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2466995363523618322359217 1850246522642713741769413)
              ·
                refine ⟨346921222995508826581765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1850246522642713741769413 346921222995508826581765)
                ·
                  refine ⟨65047729311657904984081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 346921222995508826581765 65047729311657904984081)
                  ·
                    rfl

theorem cell20_142515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_142515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142515 prefixEnd_142515 := by exact prefixLift 142515
  have htrace : WordTrace (prefixWord ++ tailWord_142515) baseStart_142515 baseEnd_142515 := by
    simpa [prefixWord, tailWord_142515, baseEnd_142515] using wordTrace_append hprefix tailTrace_142515
  have hstable : (prefixWord ++ tailWord_142515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142515).length < 2 ^ (prefixWord ++ tailWord_142515).sum := by decide
  have hdescent : baseEnd_142515 < baseStart_142515 := by decide
  rcases family_descends (prefixWord ++ tailWord_142515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142541 : List Nat := [1, 6, 2, 2, 1, 2, 2, 2, 2]
def baseStart_142541 : Nat := 118140960795 + 142541 * 2 ^ 59
def prefixEnd_142541 : Nat := 4983230072969 + 3 ^ 40 * 142541 * 2
def baseEnd_142541 : Nat := 65059596420117370117309

theorem tailTrace_142541 : CollatzResearch.WordTrace tailWord_142541 prefixEnd_142541 65059596420117370117309 := by
  unfold tailWord_142541
  simp only [CollatzResearch.WordTrace]
  refine ⟨5198897376605775909779477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3465931584403850606519651 5198897376605775909779477)
  ·
    refine ⟨243698314528395745770913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5198897376605775909779477 243698314528395745770913)
    ·
      refine ⟨182773735896296809328185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243698314528395745770913 182773735896296809328185)
      ·
        refine ⟨137080301922222606996139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182773735896296809328185 137080301922222606996139)
        ·
          refine ⟨205620452883333910494209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137080301922222606996139 205620452883333910494209)
          ·
            refine ⟨154215339662500432870657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205620452883333910494209 154215339662500432870657)
            ·
              refine ⟨115661504746875324652993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154215339662500432870657 115661504746875324652993)
              ·
                refine ⟨86746128560156493489745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115661504746875324652993 86746128560156493489745)
                ·
                  refine ⟨65059596420117370117309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86746128560156493489745 65059596420117370117309)
                  ·
                    rfl

theorem cell20_142541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_142541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142541 prefixEnd_142541 := by exact prefixLift 142541
  have htrace : WordTrace (prefixWord ++ tailWord_142541) baseStart_142541 baseEnd_142541 := by
    simpa [prefixWord, tailWord_142541, baseEnd_142541] using wordTrace_append hprefix tailTrace_142541
  have hstable : (prefixWord ++ tailWord_142541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142541).length < 2 ^ (prefixWord ++ tailWord_142541).sum := by decide
  have hdescent : baseEnd_142541 < baseStart_142541 := by decide
  rcases family_descends (prefixWord ++ tailWord_142541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142542 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_142542 : Nat := 118140960795 + 142542 * 2 ^ 59
def prefixEnd_142542 : Nat := 4983230072969 + 3 ^ 40 * 142542 * 2
def baseEnd_142542 : Nat := 65060052847365811083971

theorem tailTrace_142542 : CollatzResearch.WordTrace tailWord_142542 prefixEnd_142542 65060052847365811083971 := by
  unfold tailWord_142542
  simp only [CollatzResearch.WordTrace]
  refine ⟨649866731200269135070735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3465955899734768720377253 649866731200269135070735)
  ·
    refine ⟨974800096800403702606103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 649866731200269135070735 974800096800403702606103)
    ·
      refine ⟨1462200145200605553909155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 974800096800403702606103 1462200145200605553909155)
      ·
        refine ⟨2193300217800908330863733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462200145200605553909155 2193300217800908330863733)
        ·
          refine ⟨205621895418835156018475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2193300217800908330863733 205621895418835156018475)
          ·
            refine ⟨308432843128252734027713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205621895418835156018475 308432843128252734027713)
            ·
              refine ⟨231324632346189550520785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308432843128252734027713 231324632346189550520785)
              ·
                refine ⟨173493474259642162890589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231324632346189550520785 173493474259642162890589)
                ·
                  refine ⟨65060052847365811083971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173493474259642162890589 65060052847365811083971)
                  ·
                    rfl

theorem cell20_142542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_142542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142542 prefixEnd_142542 := by exact prefixLift 142542
  have htrace : WordTrace (prefixWord ++ tailWord_142542) baseStart_142542 baseEnd_142542 := by
    simpa [prefixWord, tailWord_142542, baseEnd_142542] using wordTrace_append hprefix tailTrace_142542
  have hstable : (prefixWord ++ tailWord_142542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142542).length < 2 ^ (prefixWord ++ tailWord_142542).sum := by decide
  have hdescent : baseEnd_142542 < baseStart_142542 := by decide
  rcases family_descends (prefixWord ++ tailWord_142542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142553 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_142553 : Nat := 118140960795 + 142553 * 2 ^ 59
def prefixEnd_142553 : Nat := 4983230072969 + 3 ^ 40 * 142553 * 2
def baseEnd_142553 : Nat := 65065073547098661717259

theorem tailTrace_142553 : CollatzResearch.WordTrace tailWord_142553 prefixEnd_142553 65065073547098661717259 := by
  unfold tailWord_142553
  simp only [CollatzResearch.WordTrace]
  refine ⟨5199335052562301959216313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3466223368374867972810875 5199335052562301959216313)
  ·
    refine ⟨3899501289421726469412235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5199335052562301959216313 3899501289421726469412235)
    ·
      refine ⟨5849251934132589704118353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3899501289421726469412235 5849251934132589704118353)
      ·
        refine ⟨4386938950599442278088765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5849251934132589704118353 4386938950599442278088765)
        ·
          refine ⟨1645102106474790854283287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4386938950599442278088765 1645102106474790854283287)
          ·
            refine ⟨2467653159712186281424931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645102106474790854283287 2467653159712186281424931)
            ·
              refine ⟨3701479739568279422137397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467653159712186281424931 3701479739568279422137397)
              ·
                refine ⟨347013725584526195825381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3701479739568279422137397 347013725584526195825381)
                ·
                  refine ⟨65065073547098661717259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 347013725584526195825381 65065073547098661717259)
                  ·
                    rfl

theorem cell20_142553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_142553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142553 prefixEnd_142553 := by exact prefixLift 142553
  have htrace : WordTrace (prefixWord ++ tailWord_142553) baseStart_142553 baseEnd_142553 := by
    simpa [prefixWord, tailWord_142553, baseEnd_142553] using wordTrace_append hprefix tailTrace_142553
  have hstable : (prefixWord ++ tailWord_142553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142553).length < 2 ^ (prefixWord ++ tailWord_142553).sum := by decide
  have hdescent : baseEnd_142553 < baseStart_142553 := by decide
  rcases family_descends (prefixWord ++ tailWord_142553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142570 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_142570 : Nat := 118140960795 + 142570 * 2 ^ 59
def prefixEnd_142570 : Nat := 4983230072969 + 3 ^ 40 * 142570 * 2
def baseEnd_142570 : Nat := 65072832810322158150523

theorem tailTrace_142570 : CollatzResearch.WordTrace tailWord_142570 prefixEnd_142570 65072832810322158150523 := by
  unfold tailWord_142570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1299988773375178465646291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3466636729000475908390109 1299988773375178465646291)
  ·
    refine ⟨1949983160062767698469437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1299988773375178465646291 1949983160062767698469437)
    ·
      refine ⟨731243685023537886926039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1949983160062767698469437 731243685023537886926039)
      ·
        refine ⟨1096865527535306830389059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 731243685023537886926039 1096865527535306830389059)
        ·
          refine ⟨1645298291302960245583589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096865527535306830389059 1645298291302960245583589)
          ·
            refine ⟨308493429619305046046923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1645298291302960245583589 308493429619305046046923)
            ·
              refine ⟨462740144428957569070385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308493429619305046046923 462740144428957569070385)
              ·
                refine ⟨347055108321718176802789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462740144428957569070385 347055108321718176802789)
                ·
                  refine ⟨65072832810322158150523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 347055108321718176802789 65072832810322158150523)
                  ·
                    rfl

theorem cell20_142570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_142570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142570 prefixEnd_142570 := by exact prefixLift 142570
  have htrace : WordTrace (prefixWord ++ tailWord_142570) baseStart_142570 baseEnd_142570 := by
    simpa [prefixWord, tailWord_142570, baseEnd_142570] using wordTrace_append hprefix tailTrace_142570
  have hstable : (prefixWord ++ tailWord_142570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142570).length < 2 ^ (prefixWord ++ tailWord_142570).sum := by decide
  have hdescent : baseEnd_142570 < baseStart_142570 := by decide
  rcases family_descends (prefixWord ++ tailWord_142570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142594 : List Nat := [3, 4, 1, 1, 3, 1, 7]
def baseStart_142594 : Nat := 118140960795 + 142594 * 2 ^ 59
def prefixEnd_142594 : Nat := 4983230072969 + 3 ^ 40 * 142594 * 2
def baseEnd_142594 : Nat := 7231531896031637927825

theorem tailTrace_142594 : CollatzResearch.WordTrace tailWord_142594 prefixEnd_142594 7231531896031637927825 := by
  unfold tailWord_142594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300207611353441490364709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3467220296942510640972557 1300207611353441490364709)
  ·
    refine ⟨243788927128770279443383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1300207611353441490364709 243788927128770279443383)
    ·
      refine ⟨365683390693155419165075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243788927128770279443383 365683390693155419165075)
      ·
        refine ⟨548525086039733128747613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365683390693155419165075 548525086039733128747613)
        ·
          refine ⟨205696907264899923280355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 548525086039733128747613 205696907264899923280355)
          ·
            refine ⟨308545360897349884920533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205696907264899923280355 308545360897349884920533)
            ·
              refine ⟨7231531896031637927825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 308545360897349884920533 7231531896031637927825)
              ·
                rfl

theorem cell20_142594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 7].length) (baseStart_142594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142594 prefixEnd_142594 := by exact prefixLift 142594
  have htrace : WordTrace (prefixWord ++ tailWord_142594) baseStart_142594 baseEnd_142594 := by
    simpa [prefixWord, tailWord_142594, baseEnd_142594] using wordTrace_append hprefix tailTrace_142594
  have hstable : (prefixWord ++ tailWord_142594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142594).length < 2 ^ (prefixWord ++ tailWord_142594).sum := by decide
  have hdescent : baseEnd_142594 < baseStart_142594 := by decide
  rcases family_descends (prefixWord ++ tailWord_142594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142618 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_142618 : Nat := 118140960795 + 142618 * 2 ^ 59
def prefixEnd_142618 : Nat := 4983230072969 + 3 ^ 40 * 142618 * 2
def baseEnd_142618 : Nat := 65094741318247324550327

theorem tailTrace_142618 : CollatzResearch.WordTrace tailWord_142618 prefixEnd_142618 65094741318247324550327 := by
  unfold tailWord_142618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300426449331704515083127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3467803864884545373555005 1300426449331704515083127)
  ·
    refine ⟨1950639673997556772624691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1300426449331704515083127 1950639673997556772624691)
    ·
      refine ⟨2925959510996335158937037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1950639673997556772624691 2925959510996335158937037)
      ·
        refine ⟨1097234816623625684601389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2925959510996335158937037 1097234816623625684601389)
        ·
          refine ⟨411463056233859631725521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1097234816623625684601389 411463056233859631725521)
          ·
            refine ⟨308597292175394723794141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411463056233859631725521 308597292175394723794141)
            ·
              refine ⟨115723984565773021422803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 308597292175394723794141 115723984565773021422803)
              ·
                refine ⟨173585976848659532134205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115723984565773021422803 173585976848659532134205)
                ·
                  refine ⟨65094741318247324550327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173585976848659532134205 65094741318247324550327)
                  ·
                    rfl

theorem cell20_142618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_142618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142618 prefixEnd_142618 := by exact prefixLift 142618
  have htrace : WordTrace (prefixWord ++ tailWord_142618) baseStart_142618 baseEnd_142618 := by
    simpa [prefixWord, tailWord_142618, baseEnd_142618] using wordTrace_append hprefix tailTrace_142618
  have hstable : (prefixWord ++ tailWord_142618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142618).length < 2 ^ (prefixWord ++ tailWord_142618).sum := by decide
  have hdescent : baseEnd_142618 < baseStart_142618 := by decide
  rcases family_descends (prefixWord ++ tailWord_142618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142632 : List Nat := [2, 1, 5, 1, 2, 1, 4, 4]
def baseStart_142632 : Nat := 118140960795 + 142632 * 2 ^ 59
def prefixEnd_142632 : Nat := 4983230072969 + 3 ^ 40 * 142632 * 2
def baseEnd_142632 : Nat := 21700377099908499361201

theorem tailTrace_142632 : CollatzResearch.WordTrace tailWord_142632 prefixEnd_142632 21700377099908499361201 := by
  unfold tailWord_142632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2601108209638049225671075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3468144279517398967561433 2601108209638049225671075)
  ·
    refine ⟨3901662314457073838506613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2601108209638049225671075 3901662314457073838506613)
    ·
      refine ⟨365780841980350672359995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3901662314457073838506613 365780841980350672359995)
      ·
        refine ⟨548671262970526008539993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365780841980350672359995 548671262970526008539993)
        ·
          refine ⟨411503447227894506404995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 548671262970526008539993 411503447227894506404995)
          ·
            refine ⟨617255170841841759607493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411503447227894506404995 617255170841841759607493)
            ·
              refine ⟨115735344532845329926405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 617255170841841759607493 115735344532845329926405)
              ·
                refine ⟨21700377099908499361201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115735344532845329926405 21700377099908499361201)
                ·
                  rfl

theorem cell20_142632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_142632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142632 prefixEnd_142632 := by exact prefixLift 142632
  have htrace : WordTrace (prefixWord ++ tailWord_142632) baseStart_142632 baseEnd_142632 := by
    simpa [prefixWord, tailWord_142632, baseEnd_142632] using wordTrace_append hprefix tailTrace_142632
  have hstable : (prefixWord ++ tailWord_142632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142632).length < 2 ^ (prefixWord ++ tailWord_142632).sum := by decide
  have hdescent : baseEnd_142632 < baseStart_142632 := by decide
  rcases family_descends (prefixWord ++ tailWord_142632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142642 : List Nat := [3, 2, 1, 1, 4, 3, 1, 3, 2]
def baseStart_142642 : Nat := 118140960795 + 142642 * 2 ^ 59
def prefixEnd_142642 : Nat := 4983230072969 + 3 ^ 40 * 142642 * 2
def baseEnd_142642 : Nat := 65105695572209907750229

theorem tailTrace_142642 : CollatzResearch.WordTrace tailWord_142642 prefixEnd_142642 65105695572209907750229 := by
  unfold tailWord_142642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300645287309967539801545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3468387432826580106137453 1300645287309967539801545)
  ·
    refine ⟨975483965482475654851159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1300645287309967539801545 975483965482475654851159)
    ·
      refine ⟨1463225948223713482276739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 975483965482475654851159 1463225948223713482276739)
      ·
        refine ⟨2194838922335570223415109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1463225948223713482276739 2194838922335570223415109)
        ·
          refine ⟨411532297937919416890333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2194838922335570223415109 411532297937919416890333)
          ·
            refine ⟨154324611726719781333875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 411532297937919416890333 154324611726719781333875)
            ·
              refine ⟨231486917590079672000813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154324611726719781333875 231486917590079672000813)
              ·
                refine ⟨86807594096279877000305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231486917590079672000813 86807594096279877000305)
                ·
                  refine ⟨65105695572209907750229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86807594096279877000305 65105695572209907750229)
                  ·
                    rfl

theorem cell20_142642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_142642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142642 prefixEnd_142642 := by exact prefixLift 142642
  have htrace : WordTrace (prefixWord ++ tailWord_142642) baseStart_142642 baseEnd_142642 := by
    simpa [prefixWord, tailWord_142642, baseEnd_142642] using wordTrace_append hprefix tailTrace_142642
  have hstable : (prefixWord ++ tailWord_142642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142642).length < 2 ^ (prefixWord ++ tailWord_142642).sum := by decide
  have hdescent : baseEnd_142642 < baseStart_142642 := by decide
  rcases family_descends (prefixWord ++ tailWord_142642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142669 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 3]
def baseStart_142669 : Nat := 118140960795 + 142669 * 2 ^ 59
def prefixEnd_142669 : Nat := 4983230072969 + 3 ^ 40 * 142669 * 2
def baseEnd_142669 : Nat := 65118019107917813850119

theorem tailTrace_142669 : CollatzResearch.WordTrace tailWord_142669 prefixEnd_142669 65118019107917813850119 := by
  unfold tailWord_142669
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203565920142053770439061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3469043946761369180292707 5203565920142053770439061)
  ·
    refine ⟨243917152506658770489331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5203565920142053770439061 243917152506658770489331)
    ·
      refine ⟨365875728759988155733997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243917152506658770489331 365875728759988155733997)
      ·
        refine ⟨137203398284995558400249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 365875728759988155733997 137203398284995558400249)
        ·
          refine ⟨102902548713746668800187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137203398284995558400249 102902548713746668800187)
          ·
            refine ⟨154353823070620003200281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102902548713746668800187 154353823070620003200281)
            ·
              refine ⟨115765367302965002400211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154353823070620003200281 115765367302965002400211)
              ·
                refine ⟨173648050954447503600317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115765367302965002400211 173648050954447503600317)
                ·
                  refine ⟨65118019107917813850119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173648050954447503600317 65118019107917813850119)
                  ·
                    rfl

theorem cell20_142669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_142669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142669 prefixEnd_142669 := by exact prefixLift 142669
  have htrace : WordTrace (prefixWord ++ tailWord_142669) baseStart_142669 baseEnd_142669 := by
    simpa [prefixWord, tailWord_142669, baseEnd_142669] using wordTrace_append hprefix tailTrace_142669
  have hstable : (prefixWord ++ tailWord_142669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142669).length < 2 ^ (prefixWord ++ tailWord_142669).sum := by decide
  have hdescent : baseEnd_142669 < baseStart_142669 := by decide
  rcases family_descends (prefixWord ++ tailWord_142669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142677 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 3]
def baseStart_142677 : Nat := 118140960795 + 142677 * 2 ^ 59
def prefixEnd_142677 : Nat := 4983230072969 + 3 ^ 40 * 142677 * 2
def baseEnd_142677 : Nat := 65121670525905341583419

theorem tailTrace_142677 : CollatzResearch.WordTrace tailWord_142677 prefixEnd_142677 65121670525905341583419 := by
  unfold tailWord_142677
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203857704113071136730285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3469238469408714091153523 5203857704113071136730285)
  ·
    refine ⟨1951446639042401676273857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5203857704113071136730285 1951446639042401676273857)
    ·
      refine ⟨1463584979281801257205393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1951446639042401676273857 1463584979281801257205393)
      ·
        refine ⟨1097688734461350942904045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1463584979281801257205393 1097688734461350942904045)
        ·
          refine ⟨411633275423006603589017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1097688734461350942904045 411633275423006603589017)
          ·
            refine ⟨308724956567254952691763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411633275423006603589017 308724956567254952691763)
            ·
              refine ⟨463087434850882429037645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308724956567254952691763 463087434850882429037645)
              ·
                refine ⟨173657788069080910889117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 463087434850882429037645 173657788069080910889117)
                ·
                  refine ⟨65121670525905341583419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173657788069080910889117 65121670525905341583419)
                  ·
                    rfl

theorem cell20_142677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_142677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142677 prefixEnd_142677 := by exact prefixLift 142677
  have htrace : WordTrace (prefixWord ++ tailWord_142677) baseStart_142677 baseEnd_142677 := by
    simpa [prefixWord, tailWord_142677, baseEnd_142677] using wordTrace_append hprefix tailTrace_142677
  have hstable : (prefixWord ++ tailWord_142677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142677).length < 2 ^ (prefixWord ++ tailWord_142677).sum := by decide
  have hdescent : baseEnd_142677 < baseStart_142677 := by decide
  rcases family_descends (prefixWord ++ tailWord_142677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142791 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 3]
def baseStart_142791 : Nat := 118140960795 + 142791 * 2 ^ 59
def prefixEnd_142791 : Nat := 4983230072969 + 3 ^ 40 * 142791 * 2
def baseEnd_142791 : Nat := 65173703232227611782953

theorem tailTrace_142791 : CollatzResearch.WordTrace tailWord_142791 prefixEnd_142791 65173703232227611782953 := by
  unfold tailWord_142791
  simp only [CollatzResearch.WordTrace]
  refine ⟨5208015625700068606380227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3472010417133379070920151 5208015625700068606380227)
  ·
    refine ⟨7812023438550102909570341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5208015625700068606380227 7812023438550102909570341)
    ·
      refine ⟨1464754394728144295544439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7812023438550102909570341 1464754394728144295544439)
      ·
        refine ⟨2197131592092216443316659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464754394728144295544439 2197131592092216443316659)
        ·
          refine ⟨3295697388138324664974989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197131592092216443316659 3295697388138324664974989)
          ·
            refine ⟨1235886520551871749365621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3295697388138324664974989 1235886520551871749365621)
            ·
              refine ⟨115864361301737976503027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1235886520551871749365621 115864361301737976503027)
              ·
                refine ⟨173796541952606964754541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115864361301737976503027 173796541952606964754541)
                ·
                  refine ⟨65173703232227611782953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173796541952606964754541 65173703232227611782953)
                  ·
                    rfl

theorem cell20_142791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 3].length) (baseStart_142791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142791 prefixEnd_142791 := by exact prefixLift 142791
  have htrace : WordTrace (prefixWord ++ tailWord_142791) baseStart_142791 baseEnd_142791 := by
    simpa [prefixWord, tailWord_142791, baseEnd_142791] using wordTrace_append hprefix tailTrace_142791
  have hstable : (prefixWord ++ tailWord_142791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142791).length < 2 ^ (prefixWord ++ tailWord_142791).sum := by decide
  have hdescent : baseEnd_142791 < baseStart_142791 := by decide
  rcases family_descends (prefixWord ++ tailWord_142791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142874 : List Nat := [3, 1, 1, 3, 1, 1, 1, 7, 2]
def baseStart_142874 : Nat := 118140960795 + 142874 * 2 ^ 59
def prefixEnd_142874 : Nat := 4983230072969 + 3 ^ 40 * 142874 * 2
def baseEnd_142874 : Nat := 65211586693848212015947

theorem tailTrace_142874 : CollatzResearch.WordTrace tailWord_142874 prefixEnd_142874 65211586693848212015947 := by
  unfold tailWord_142874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1302760721099843445412919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3474028589599582521101117 1302760721099843445412919)
  ·
    refine ⟨1954141081649765168119379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1302760721099843445412919 1954141081649765168119379)
    ·
      refine ⟨2931211622474647752179069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1954141081649765168119379 2931211622474647752179069)
      ·
        refine ⟨1099204358427992907067151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2931211622474647752179069 1099204358427992907067151)
        ·
          refine ⟨1648806537641989360600727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099204358427992907067151 1648806537641989360600727)
          ·
            refine ⟨2473209806462984040901091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648806537641989360600727 2473209806462984040901091)
            ·
              refine ⟨3709814709694476061351637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473209806462984040901091 3709814709694476061351637)
              ·
                refine ⟨86948782258464282687929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3709814709694476061351637 86948782258464282687929)
                ·
                  refine ⟨65211586693848212015947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86948782258464282687929 65211586693848212015947)
                  ·
                    rfl

theorem cell20_142874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_142874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142874 prefixEnd_142874 := by exact prefixLift 142874
  have htrace : WordTrace (prefixWord ++ tailWord_142874) baseStart_142874 baseEnd_142874 := by
    simpa [prefixWord, tailWord_142874, baseEnd_142874] using wordTrace_append hprefix tailTrace_142874
  have hstable : (prefixWord ++ tailWord_142874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142874).length < 2 ^ (prefixWord ++ tailWord_142874).sum := by decide
  have hdescent : baseEnd_142874 < baseStart_142874 := by decide
  rcases family_descends (prefixWord ++ tailWord_142874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142985 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_142985 : Nat := 118140960795 + 142985 * 2 ^ 59
def prefixEnd_142985 : Nat := 4983230072969 + 3 ^ 40 * 142985 * 2
def baseEnd_142985 : Nat := 65262250118425159315493

theorem tailTrace_142985 : CollatzResearch.WordTrace tailWord_142985 prefixEnd_142985 65262250118425159315493 := by
  unfold tailWord_142985
  simp only [CollatzResearch.WordTrace]
  refine ⟨5215091386997239738942409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3476727591331493159294939 5215091386997239738942409)
  ·
    refine ⟨3911318540247929804206807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5215091386997239738942409 3911318540247929804206807)
    ·
      refine ⟨5866977810371894706310211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911318540247929804206807 5866977810371894706310211)
      ·
        refine ⟨8800466715557842059465317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5866977810371894706310211 8800466715557842059465317)
        ·
          refine ⟨1650087509167095386149747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8800466715557842059465317 1650087509167095386149747)
          ·
            refine ⟨2475131263750643079224621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650087509167095386149747 2475131263750643079224621)
            ·
              refine ⟨928174223906491154709233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2475131263750643079224621 928174223906491154709233)
              ·
                refine ⟨696130667929868366031925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928174223906491154709233 696130667929868366031925)
                ·
                  refine ⟨65262250118425159315493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 696130667929868366031925 65262250118425159315493)
                  ·
                    rfl

theorem cell20_142985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_142985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142985 prefixEnd_142985 := by exact prefixLift 142985
  have htrace : WordTrace (prefixWord ++ tailWord_142985) baseStart_142985 baseEnd_142985 := by
    simpa [prefixWord, tailWord_142985, baseEnd_142985] using wordTrace_append hprefix tailTrace_142985
  have hstable : (prefixWord ++ tailWord_142985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142985).length < 2 ^ (prefixWord ++ tailWord_142985).sum := by decide
  have hdescent : baseEnd_142985 < baseStart_142985 := by decide
  rcases family_descends (prefixWord ++ tailWord_142985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142992 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_142992 : Nat := 118140960795 + 142992 * 2 ^ 59
def prefixEnd_142992 : Nat := 4983230072969 + 3 ^ 40 * 142992 * 2
def baseEnd_142992 : Nat := 65265445109164246082131

theorem tailTrace_142992 : CollatzResearch.WordTrace tailWord_142992 prefixEnd_142992 65265445109164246082131 := by
  unfold tailWord_142992
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607673348985939967223615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3476897798647919956298153 2607673348985939967223615)
  ·
    refine ⟨3911510023478909950835423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2607673348985939967223615 3911510023478909950835423)
    ·
      refine ⟨5867265035218364926253135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911510023478909950835423 5867265035218364926253135)
      ·
        refine ⟨8800897552827547389379703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5867265035218364926253135 8800897552827547389379703)
        ·
          refine ⟨13201346329241321084069555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8800897552827547389379703 13201346329241321084069555)
          ·
            refine ⟨19802019493861981626104333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13201346329241321084069555 19802019493861981626104333)
            ·
              refine ⟨7425757310198243109789125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19802019493861981626104333 7425757310198243109789125)
              ·
                refine ⟨1392329495662170583085461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7425757310198243109789125 1392329495662170583085461)
                ·
                  refine ⟨65265445109164246082131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1392329495662170583085461 65265445109164246082131)
                  ·
                    rfl

theorem cell20_142992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_142992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_142992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_142992 prefixEnd_142992 := by exact prefixLift 142992
  have htrace : WordTrace (prefixWord ++ tailWord_142992) baseStart_142992 baseEnd_142992 := by
    simpa [prefixWord, tailWord_142992, baseEnd_142992] using wordTrace_append hprefix tailTrace_142992
  have hstable : (prefixWord ++ tailWord_142992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142992).length < 2 ^ (prefixWord ++ tailWord_142992).sum := by decide
  have hdescent : baseEnd_142992 < baseStart_142992 := by decide
  rcases family_descends (prefixWord ++ tailWord_142992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143060 : List Nat := [2, 4, 1, 3, 1, 1, 4, 2, 2]
def baseStart_143060 : Nat := 118140960795 + 143060 * 2 ^ 59
def prefixEnd_143060 : Nat := 4983230072969 + 3 ^ 40 * 143060 * 2
def baseEnd_143060 : Nat := 65296482162058231815187

theorem tailTrace_143060 : CollatzResearch.WordTrace tailWord_143060 prefixEnd_143060 65296482162058231815187 := by
  unfold tailWord_143060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608913430862763773961317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3478551241150351698615089 2608913430862763773961317)
  ·
    refine ⟨489171268286768207617747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2608913430862763773961317 489171268286768207617747)
    ·
      refine ⟨733756902430152311426621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489171268286768207617747 733756902430152311426621)
      ·
        refine ⟨275158838411307116784983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 733756902430152311426621 275158838411307116784983)
        ·
          refine ⟨412738257616960675177475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275158838411307116784983 412738257616960675177475)
          ·
            refine ⟨619107386425441012766213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412738257616960675177475 619107386425441012766213)
            ·
              refine ⟨116082634954770189893665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 619107386425441012766213 116082634954770189893665)
              ·
                refine ⟨87061976216077642420249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116082634954770189893665 87061976216077642420249)
                ·
                  refine ⟨65296482162058231815187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87061976216077642420249 65296482162058231815187)
                  ·
                    rfl

theorem cell20_143060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_143060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143060 prefixEnd_143060 := by exact prefixLift 143060
  have htrace : WordTrace (prefixWord ++ tailWord_143060) baseStart_143060 baseEnd_143060 := by
    simpa [prefixWord, tailWord_143060, baseEnd_143060] using wordTrace_append hprefix tailTrace_143060
  have hstable : (prefixWord ++ tailWord_143060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143060).length < 2 ^ (prefixWord ++ tailWord_143060).sum := by decide
  have hdescent : baseEnd_143060 < baseStart_143060 := by decide
  rcases family_descends (prefixWord ++ tailWord_143060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143064 : List Nat := [2, 1, 2, 2, 3, 1, 3, 4, 2]
def baseStart_143064 : Nat := 118140960795 + 143064 * 2 ^ 59
def prefixEnd_143064 : Nat := 4983230072969 + 3 ^ 40 * 143064 * 2
def baseEnd_143064 : Nat := 65298307871051995681837

theorem tailTrace_143064 : CollatzResearch.WordTrace tailWord_143064 prefixEnd_143064 65298307871051995681837 := by
  unfold tailWord_143064
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608986376855518115534123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3478648502474024154045497 2608986376855518115534123)
  ·
    refine ⟨3913479565283277173301185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2608986376855518115534123 3913479565283277173301185)
    ·
      refine ⟨2935109673962457879975889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3913479565283277173301185 2935109673962457879975889)
      ·
        refine ⟨2201332255471843409981917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2935109673962457879975889 2201332255471843409981917)
        ·
          refine ⟨825499595801941278743219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2201332255471843409981917 825499595801941278743219)
          ·
            refine ⟨1238249393702911918114829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825499595801941278743219 1238249393702911918114829)
            ·
              refine ⟨464343522638591969293061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1238249393702911918114829 464343522638591969293061)
              ·
                refine ⟨87064410494735994242449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 464343522638591969293061 87064410494735994242449)
                ·
                  refine ⟨65298307871051995681837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87064410494735994242449 65298307871051995681837)
                  ·
                    rfl

theorem cell20_143064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_143064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143064 prefixEnd_143064 := by exact prefixLift 143064
  have htrace : WordTrace (prefixWord ++ tailWord_143064) baseStart_143064 baseEnd_143064 := by
    simpa [prefixWord, tailWord_143064, baseEnd_143064] using wordTrace_append hprefix tailTrace_143064
  have hstable : (prefixWord ++ tailWord_143064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143064).length < 2 ^ (prefixWord ++ tailWord_143064).sum := by decide
  have hdescent : baseEnd_143064 < baseStart_143064 := by decide
  rcases family_descends (prefixWord ++ tailWord_143064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143085 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_143085 : Nat := 118140960795 + 143085 * 2 ^ 59
def prefixEnd_143085 : Nat := 4983230072969 + 3 ^ 40 * 143085 * 2
def baseEnd_143085 : Nat := 65307892843269255981751

theorem tailTrace_143085 : CollatzResearch.WordTrace tailWord_143085 prefixEnd_143085 65307892843269255981751 := by
  unfold tailWord_143085
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218738686634956817582709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3479159124423304545055139 5218738686634956817582709)
  ·
    refine ⟨489256751872027201648379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5218738686634956817582709 489256751872027201648379)
    ·
      refine ⟨733885127808040802472569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489256751872027201648379 733885127808040802472569)
      ·
        refine ⟨550413845856030601854427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 733885127808040802472569 550413845856030601854427)
        ·
          refine ⟨825620768784045902781641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550413845856030601854427 825620768784045902781641)
          ·
            refine ⟨619215576588034427086231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825620768784045902781641 619215576588034427086231)
            ·
              refine ⟨928823364882051640629347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619215576588034427086231 928823364882051640629347)
              ·
                refine ⟨1393235047323077460944021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928823364882051640629347 1393235047323077460944021)
                ·
                  refine ⟨65307892843269255981751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1393235047323077460944021 65307892843269255981751)
                  ·
                    rfl

theorem cell20_143085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_143085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143085 prefixEnd_143085 := by exact prefixLift 143085
  have htrace : WordTrace (prefixWord ++ tailWord_143085) baseStart_143085 baseEnd_143085 := by
    simpa [prefixWord, tailWord_143085, baseEnd_143085] using wordTrace_append hprefix tailTrace_143085
  have hstable : (prefixWord ++ tailWord_143085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143085).length < 2 ^ (prefixWord ++ tailWord_143085).sum := by decide
  have hdescent : baseEnd_143085 < baseStart_143085 := by decide
  rcases family_descends (prefixWord ++ tailWord_143085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143116 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 3]
def baseStart_143116 : Nat := 118140960795 + 143116 * 2 ^ 59
def prefixEnd_143116 : Nat := 4983230072969 + 3 ^ 40 * 143116 * 2
def baseEnd_143116 : Nat := 65322042087970925948291

theorem tailTrace_143116 : CollatzResearch.WordTrace tailWord_143116 prefixEnd_143116 65322042087970925948291 := by
  unfold tailWord_143116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609934674761324555980601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3479912899681766074640801 2609934674761324555980601)
  ·
    refine ⟨1957451006070993416985451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2609934674761324555980601 1957451006070993416985451)
    ·
      refine ⟨2936176509106490125478177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1957451006070993416985451 2936176509106490125478177)
      ·
        refine ⟨2202132381829867594108633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2936176509106490125478177 2202132381829867594108633)
        ·
          refine ⟨1651599286372400695581475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2202132381829867594108633 1651599286372400695581475)
          ·
            refine ⟨2477398929558601043372213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651599286372400695581475 2477398929558601043372213)
            ·
              refine ⟨232256149646118847816145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2477398929558601043372213 232256149646118847816145)
              ·
                refine ⟨174192112234589135862109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232256149646118847816145 174192112234589135862109)
                ·
                  refine ⟨65322042087970925948291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174192112234589135862109 65322042087970925948291)
                  ·
                    rfl

theorem cell20_143116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_143116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143116 prefixEnd_143116 := by exact prefixLift 143116
  have htrace : WordTrace (prefixWord ++ tailWord_143116) baseStart_143116 baseEnd_143116 := by
    simpa [prefixWord, tailWord_143116, baseEnd_143116] using wordTrace_append hprefix tailTrace_143116
  have hstable : (prefixWord ++ tailWord_143116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143116).length < 2 ^ (prefixWord ++ tailWord_143116).sum := by decide
  have hdescent : baseEnd_143116 < baseStart_143116 := by decide
  rcases family_descends (prefixWord ++ tailWord_143116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143151 : List Nat := [1, 1, 2, 1, 2, 1, 2, 10]
def baseStart_143151 : Nat := 118140960795 + 143151 * 2 ^ 59
def prefixEnd_143151 : Nat := 4983230072969 + 3 ^ 40 * 143151 * 2
def baseEnd_143151 : Nat := 21779339013888786593827

theorem tailTrace_143151 : CollatzResearch.WordTrace tailWord_143151 prefixEnd_143151 21779339013888786593827 := by
  unfold tailWord_143151
  simp only [CollatzResearch.WordTrace]
  refine ⟨5221145904395850089485307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3480763936263900059656871 5221145904395850089485307)
  ·
    refine ⟨7831718856593775134227961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5221145904395850089485307 7831718856593775134227961)
    ·
      refine ⟨5873789142445331350670971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7831718856593775134227961 5873789142445331350670971)
      ·
        refine ⟨8810683713667997026006457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5873789142445331350670971 8810683713667997026006457)
        ·
          refine ⟨6608012785250997769504843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8810683713667997026006457 6608012785250997769504843)
          ·
            refine ⟨9912019177876496654257265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6608012785250997769504843 9912019177876496654257265)
            ·
              refine ⟨7434014383407372490692949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9912019177876496654257265 7434014383407372490692949)
              ·
                refine ⟨21779339013888786593827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7434014383407372490692949 21779339013888786593827)
                ·
                  rfl

theorem cell20_143151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_143151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143151 prefixEnd_143151 := by exact prefixLift 143151
  have htrace : WordTrace (prefixWord ++ tailWord_143151) baseStart_143151 baseEnd_143151 := by
    simpa [prefixWord, tailWord_143151, baseEnd_143151] using wordTrace_append hprefix tailTrace_143151
  have hstable : (prefixWord ++ tailWord_143151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143151).length < 2 ^ (prefixWord ++ tailWord_143151).sum := by decide
  have hdescent : baseEnd_143151 < baseStart_143151 := by decide
  rcases family_descends (prefixWord ++ tailWord_143151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143174 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_143174 : Nat := 118140960795 + 143174 * 2 ^ 59
def prefixEnd_143174 : Nat := 4983230072969 + 3 ^ 40 * 143174 * 2
def baseEnd_143174 : Nat := 65348514868380502014721

theorem tailTrace_143174 : CollatzResearch.WordTrace tailWord_143174 prefixEnd_143174 65348514868380502014721 := by
  unfold tailWord_143174
  simp only [CollatzResearch.WordTrace]
  refine ⟨163187024478516406799143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3481323188875016678381717 163187024478516406799143)
  ·
    refine ⟨244780536717774610198715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163187024478516406799143 244780536717774610198715)
    ·
      refine ⟨367170805076661915298073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244780536717774610198715 367170805076661915298073)
      ·
        refine ⟨275378103807496436473555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367170805076661915298073 275378103807496436473555)
        ·
          refine ⟨413067155711244654710333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275378103807496436473555 413067155711244654710333)
          ·
            refine ⟨154900183391716745516375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 413067155711244654710333 154900183391716745516375)
            ·
              refine ⟨232350275087575118274563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154900183391716745516375 232350275087575118274563)
              ·
                refine ⟨348525412631362677411845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232350275087575118274563 348525412631362677411845)
                ·
                  refine ⟨65348514868380502014721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348525412631362677411845 65348514868380502014721)
                  ·
                    rfl

theorem cell20_143174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_143174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143174 prefixEnd_143174 := by exact prefixLift 143174
  have htrace : WordTrace (prefixWord ++ tailWord_143174) baseStart_143174 baseEnd_143174 := by
    simpa [prefixWord, tailWord_143174, baseEnd_143174] using wordTrace_append hprefix tailTrace_143174
  have hstable : (prefixWord ++ tailWord_143174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143174).length < 2 ^ (prefixWord ++ tailWord_143174).sum := by decide
  have hdescent : baseEnd_143174 < baseStart_143174 := by decide
  rcases family_descends (prefixWord ++ tailWord_143174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143175 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_143175 : Nat := 118140960795 + 143175 * 2 ^ 59
def prefixEnd_143175 : Nat := 4983230072969 + 3 ^ 40 * 143175 * 2
def baseEnd_143175 : Nat := 65348971295628942981383

theorem tailTrace_143175 : CollatzResearch.WordTrace tailWord_143175 prefixEnd_143175 65348971295628942981383 := by
  unfold tailWord_143175
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222021256308902188358979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3481347504205934792239319 5222021256308902188358979)
  ·
    refine ⟨7833031884463353282538469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5222021256308902188358979 7833031884463353282538469)
    ·
      refine ⟨1468693478336878740475963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7833031884463353282538469 1468693478336878740475963)
      ·
        refine ⟨2203040217505318110713945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468693478336878740475963 2203040217505318110713945)
        ·
          refine ⟨1652280163128988583035459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2203040217505318110713945 1652280163128988583035459)
          ·
            refine ⟨2478420244693482874553189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652280163128988583035459 2478420244693482874553189)
            ·
              refine ⟨464703795880028038978723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2478420244693482874553189 464703795880028038978723)
              ·
                refine ⟨697055693820042058468085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464703795880028038978723 697055693820042058468085)
                ·
                  refine ⟨65348971295628942981383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 697055693820042058468085 65348971295628942981383)
                  ·
                    rfl

theorem cell20_143175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_143175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143175 prefixEnd_143175 := by exact prefixLift 143175
  have htrace : WordTrace (prefixWord ++ tailWord_143175) baseStart_143175 baseEnd_143175 := by
    simpa [prefixWord, tailWord_143175, baseEnd_143175] using wordTrace_append hprefix tailTrace_143175
  have hstable : (prefixWord ++ tailWord_143175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143175).length < 2 ^ (prefixWord ++ tailWord_143175).sum := by decide
  have hdescent : baseEnd_143175 < baseStart_143175 := by decide
  rcases family_descends (prefixWord ++ tailWord_143175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143188 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 3]
def baseStart_143188 : Nat := 118140960795 + 143188 * 2 ^ 59
def prefixEnd_143188 : Nat := 4983230072969 + 3 ^ 40 * 143188 * 2
def baseEnd_143188 : Nat := 65354904849858675547997

theorem tailTrace_143188 : CollatzResearch.WordTrace tailWord_143188 prefixEnd_143188 65354904849858675547997 := by
  unfold tailWord_143188
  simp only [CollatzResearch.WordTrace]
  refine ⟨2611247702630902704291109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3481663603507870272388145 2611247702630902704291109)
  ·
    refine ⟨489608944243294257054583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2611247702630902704291109 489608944243294257054583)
    ·
      refine ⟨734413416364941385581875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489608944243294257054583 734413416364941385581875)
      ·
        refine ⟨1101620124547412078372813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734413416364941385581875 1101620124547412078372813)
        ·
          refine ⟨413107546705279529389805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1101620124547412078372813 413107546705279529389805)
          ·
            refine ⟨154915330014479823521177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 413107546705279529389805 154915330014479823521177)
            ·
              refine ⟨116186497510859867640883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154915330014479823521177 116186497510859867640883)
              ·
                refine ⟨174279746266289801461325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116186497510859867640883 174279746266289801461325)
                ·
                  refine ⟨65354904849858675547997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174279746266289801461325 65354904849858675547997)
                  ·
                    rfl

theorem cell20_143188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_143188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143188 prefixEnd_143188 := by exact prefixLift 143188
  have htrace : WordTrace (prefixWord ++ tailWord_143188) baseStart_143188 baseEnd_143188 := by
    simpa [prefixWord, tailWord_143188, baseEnd_143188] using wordTrace_append hprefix tailTrace_143188
  have hstable : (prefixWord ++ tailWord_143188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143188).length < 2 ^ (prefixWord ++ tailWord_143188).sum := by decide
  have hdescent : baseEnd_143188 < baseStart_143188 := by decide
  rcases family_descends (prefixWord ++ tailWord_143188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143213 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_143213 : Nat := 118140960795 + 143213 * 2 ^ 59
def prefixEnd_143213 : Nat := 4983230072969 + 3 ^ 40 * 143213 * 2
def baseEnd_143213 : Nat := 65366315531069699714561

theorem tailTrace_143213 : CollatzResearch.WordTrace tailWord_143213 prefixEnd_143213 65366315531069699714561 := by
  unfold tailWord_143213
  simp only [CollatzResearch.WordTrace]
  refine ⟨5223407230171234678242293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3482271486780823118828195 5223407230171234678242293)
  ·
    refine ⟨489694427828553251085215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5223407230171234678242293 489694427828553251085215)
    ·
      refine ⟨734541641742829876627823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489694427828553251085215 734541641742829876627823)
      ·
        refine ⟨1101812462614244814941735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734541641742829876627823 1101812462614244814941735)
        ·
          refine ⟨1652718693921367222412603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101812462614244814941735 1652718693921367222412603)
          ·
            refine ⟨2479078040882050833618905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652718693921367222412603 2479078040882050833618905)
            ·
              refine ⟨1859308530661538125214179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2479078040882050833618905 1859308530661538125214179)
              ·
                refine ⟨2788962795992307187821269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859308530661538125214179 2788962795992307187821269)
                ·
                  refine ⟨65366315531069699714561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2788962795992307187821269 65366315531069699714561)
                  ·
                    rfl

theorem cell20_143213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_143213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143213 prefixEnd_143213 := by exact prefixLift 143213
  have htrace : WordTrace (prefixWord ++ tailWord_143213) baseStart_143213 baseEnd_143213 := by
    simpa [prefixWord, tailWord_143213, baseEnd_143213] using wordTrace_append hprefix tailTrace_143213
  have hstable : (prefixWord ++ tailWord_143213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143213).length < 2 ^ (prefixWord ++ tailWord_143213).sum := by decide
  have hdescent : baseEnd_143213 < baseStart_143213 := by decide
  rcases family_descends (prefixWord ++ tailWord_143213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143240 : List Nat := [2, 1, 3, 3, 4, 1, 1, 5]
def baseStart_143240 : Nat := 118140960795 + 143240 * 2 ^ 59
def prefixEnd_143240 : Nat := 4983230072969 + 3 ^ 40 * 143240 * 2
def baseEnd_143240 : Nat := 21792879688925868604817

theorem tailTrace_143240 : CollatzResearch.WordTrace tailWord_143240 prefixEnd_143240 21792879688925868604817 := by
  unfold tailWord_143240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2612196000536709144737587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3482928000715612192983449 2612196000536709144737587)
  ·
    refine ⟨3918294000805063717106381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2612196000536709144737587 3918294000805063717106381)
    ·
      refine ⟨1469360250301898893914893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3918294000805063717106381 1469360250301898893914893)
      ·
        refine ⟨551010093863212085218085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1469360250301898893914893 551010093863212085218085)
        ·
          refine ⟨103314392599352265978391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 551010093863212085218085 103314392599352265978391)
          ·
            refine ⟨154971588899028398967587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103314392599352265978391 154971588899028398967587)
            ·
              refine ⟨232457383348542598451381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154971588899028398967587 232457383348542598451381)
              ·
                refine ⟨21792879688925868604817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 232457383348542598451381 21792879688925868604817)
                ·
                  rfl

theorem cell20_143240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_143240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143240 prefixEnd_143240 := by exact prefixLift 143240
  have htrace : WordTrace (prefixWord ++ tailWord_143240) baseStart_143240 baseEnd_143240 := by
    simpa [prefixWord, tailWord_143240, baseEnd_143240] using wordTrace_append hprefix tailTrace_143240
  have hstable : (prefixWord ++ tailWord_143240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143240).length < 2 ^ (prefixWord ++ tailWord_143240).sum := by decide
  have hdescent : baseEnd_143240 < baseStart_143240 := by decide
  rcases family_descends (prefixWord ++ tailWord_143240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143261 : List Nat := [1, 4, 2, 1, 2, 3, 3, 4]
def baseStart_143261 : Nat := 118140960795 + 143261 * 2 ^ 59
def prefixEnd_143261 : Nat := 4983230072969 + 3 ^ 40 * 143261 * 2
def baseEnd_143261 : Nat := 21796074679664955371455

theorem tailTrace_143261 : CollatzResearch.WordTrace tailWord_143261 prefixEnd_143261 21796074679664955371455 := by
  unfold tailWord_143261
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225157933997338875989637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3483438622664892583993091 5225157933997338875989637)
  ·
    refine ⟨979717112624501039248057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5225157933997338875989637 979717112624501039248057)
    ·
      refine ⟨734787834468375779436043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 979717112624501039248057 734787834468375779436043)
      ·
        refine ⟨1102181751702563669154065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734787834468375779436043 1102181751702563669154065)
        ·
          refine ⟨826636313776922751865549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1102181751702563669154065 826636313776922751865549)
          ·
            refine ⟨309988617666346031949581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 826636313776922751865549 309988617666346031949581)
            ·
              refine ⟨116245731624879761981093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309988617666346031949581 116245731624879761981093)
              ·
                refine ⟨21796074679664955371455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116245731624879761981093 21796074679664955371455)
                ·
                  rfl

theorem cell20_143261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 4].length) (baseStart_143261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143261 prefixEnd_143261 := by exact prefixLift 143261
  have htrace : WordTrace (prefixWord ++ tailWord_143261) baseStart_143261 baseEnd_143261 := by
    simpa [prefixWord, tailWord_143261, baseEnd_143261] using wordTrace_append hprefix tailTrace_143261
  have hstable : (prefixWord ++ tailWord_143261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143261).length < 2 ^ (prefixWord ++ tailWord_143261).sum := by decide
  have hdescent : baseEnd_143261 < baseStart_143261 := by decide
  rcases family_descends (prefixWord ++ tailWord_143261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143271 : List Nat := [1, 1, 6, 1, 2, 2, 2, 3, 2]
def baseStart_143271 : Nat := 118140960795 + 143271 * 2 ^ 59
def prefixEnd_143271 : Nat := 4983230072969 + 3 ^ 40 * 143271 * 2
def baseEnd_143271 : Nat := 65392788311479275780991

theorem tailTrace_143271 : CollatzResearch.WordTrace tailWord_143271 prefixEnd_143271 65392788311479275780991 := by
  unfold tailWord_143271
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225522663961110583853667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3483681775974073722569111 5225522663961110583853667)
  ·
    refine ⟨7838283995941665875780501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5225522663961110583853667 7838283995941665875780501)
    ·
      refine ⟨367419562309765587927211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7838283995941665875780501 367419562309765587927211)
      ·
        refine ⟨551129343464648381890817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367419562309765587927211 551129343464648381890817)
        ·
          refine ⟨413347007598486286418113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551129343464648381890817 413347007598486286418113)
          ·
            refine ⟨310010255698864714813585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413347007598486286418113 310010255698864714813585)
            ·
              refine ⟨232507691774148536110189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310010255698864714813585 232507691774148536110189)
              ·
                refine ⟨87190384415305701041321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232507691774148536110189 87190384415305701041321)
                ·
                  refine ⟨65392788311479275780991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87190384415305701041321 65392788311479275780991)
                  ·
                    rfl

theorem cell20_143271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 2].length) (baseStart_143271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143271 prefixEnd_143271 := by exact prefixLift 143271
  have htrace : WordTrace (prefixWord ++ tailWord_143271) baseStart_143271 baseEnd_143271 := by
    simpa [prefixWord, tailWord_143271, baseEnd_143271] using wordTrace_append hprefix tailTrace_143271
  have hstable : (prefixWord ++ tailWord_143271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143271).length < 2 ^ (prefixWord ++ tailWord_143271).sum := by decide
  have hdescent : baseEnd_143271 < baseStart_143271 := by decide
  rcases family_descends (prefixWord ++ tailWord_143271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143285 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 3]
def baseStart_143285 : Nat := 118140960795 + 143285 * 2 ^ 59
def prefixEnd_143285 : Nat := 4983230072969 + 3 ^ 40 * 143285 * 2
def baseEnd_143285 : Nat := 65399178292957449314267

theorem tailTrace_143285 : CollatzResearch.WordTrace tailWord_143285 prefixEnd_143285 65399178292957449314267 := by
  unfold tailWord_143285
  simp only [CollatzResearch.WordTrace]
  refine ⟨5226033285910390974863309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3484022190606927316575539 5226033285910390974863309)
  ·
    refine ⟨1959762482216396615573741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5226033285910390974863309 1959762482216396615573741)
    ·
      refine ⟨734910930831148730840153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1959762482216396615573741 734910930831148730840153)
      ·
        refine ⟨551183198123361548130115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 734910930831148730840153 551183198123361548130115)
        ·
          refine ⟨826774797185042322195173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551183198123361548130115 826774797185042322195173)
          ·
            refine ⟨155020274472195435411595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 826774797185042322195173 155020274472195435411595)
            ·
              refine ⟨232530411708293153117393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155020274472195435411595 232530411708293153117393)
              ·
                refine ⟨174397808781219864838045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232530411708293153117393 174397808781219864838045)
                ·
                  refine ⟨65399178292957449314267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174397808781219864838045 65399178292957449314267)
                  ·
                    rfl

theorem cell20_143285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_143285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143285 prefixEnd_143285 := by exact prefixLift 143285
  have htrace : WordTrace (prefixWord ++ tailWord_143285) baseStart_143285 baseEnd_143285 := by
    simpa [prefixWord, tailWord_143285, baseEnd_143285] using wordTrace_append hprefix tailTrace_143285
  have hstable : (prefixWord ++ tailWord_143285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143285).length < 2 ^ (prefixWord ++ tailWord_143285).sum := by decide
  have hdescent : baseEnd_143285 < baseStart_143285 := by decide
  rcases family_descends (prefixWord ++ tailWord_143285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143289 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_143289 : Nat := 118140960795 + 143289 * 2 ^ 59
def prefixEnd_143289 : Nat := 4983230072969 + 3 ^ 40 * 143289 * 2
def baseEnd_143289 : Nat := 65401004001951213180917

theorem tailTrace_143289 : CollatzResearch.WordTrace tailWord_143289 prefixEnd_143289 65401004001951213180917 := by
  unfold tailWord_143289
  simp only [CollatzResearch.WordTrace]
  refine ⟨5226179177895899658008921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3484119451930599772005947 5226179177895899658008921)
  ·
    refine ⟨3919634383421924743506691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5226179177895899658008921 3919634383421924743506691)
    ·
      refine ⟨5879451575132887115260037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3919634383421924743506691 5879451575132887115260037)
      ·
        refine ⟨1102397170337416334111257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5879451575132887115260037 1102397170337416334111257)
        ·
          refine ⟨826797877753062250583443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1102397170337416334111257 826797877753062250583443)
          ·
            refine ⟨1240196816629593375875165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826797877753062250583443 1240196816629593375875165)
            ·
              refine ⟨465073806236097515953187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1240196816629593375875165 465073806236097515953187)
              ·
                refine ⟨697610709354146273929781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465073806236097515953187 697610709354146273929781)
                ·
                  refine ⟨65401004001951213180917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 697610709354146273929781 65401004001951213180917)
                  ·
                    rfl

theorem cell20_143289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_143289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143289 prefixEnd_143289 := by exact prefixLift 143289
  have htrace : WordTrace (prefixWord ++ tailWord_143289) baseStart_143289 baseEnd_143289 := by
    simpa [prefixWord, tailWord_143289, baseEnd_143289] using wordTrace_append hprefix tailTrace_143289
  have hstable : (prefixWord ++ tailWord_143289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143289).length < 2 ^ (prefixWord ++ tailWord_143289).sum := by decide
  have hdescent : baseEnd_143289 < baseStart_143289 := by decide
  rcases family_descends (prefixWord ++ tailWord_143289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143303 : List Nat := [1, 1, 4, 1, 1, 2, 1, 9]
def baseStart_143303 : Nat := 118140960795 + 143303 * 2 ^ 59
def prefixEnd_143303 : Nat := 4983230072969 + 3 ^ 40 * 143303 * 2
def baseEnd_143303 : Nat := 21802464661143128904731

theorem tailTrace_143303 : CollatzResearch.WordTrace tailWord_143303 prefixEnd_143303 21802464661143128904731 := by
  unfold tailWord_143303
  simp only [CollatzResearch.WordTrace]
  refine ⟨5226689799845180049018563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3484459866563453366012375 5226689799845180049018563)
  ·
    refine ⟨7840034699767770073527845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5226689799845180049018563 7840034699767770073527845)
    ·
      refine ⟨1470006506206456888786471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7840034699767770073527845 1470006506206456888786471)
      ·
        refine ⟨2205009759309685333179707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1470006506206456888786471 2205009759309685333179707)
        ·
          refine ⟨3307514638964527999769561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2205009759309685333179707 3307514638964527999769561)
          ·
            refine ⟨2480635979223395999827171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3307514638964527999769561 2480635979223395999827171)
            ·
              refine ⟨3720953968835093999740757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2480635979223395999827171 3720953968835093999740757)
              ·
                refine ⟨21802464661143128904731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3720953968835093999740757 21802464661143128904731)
                ·
                  rfl

theorem cell20_143303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_143303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143303 prefixEnd_143303 := by exact prefixLift 143303
  have htrace : WordTrace (prefixWord ++ tailWord_143303) baseStart_143303 baseEnd_143303 := by
    simpa [prefixWord, tailWord_143303, baseEnd_143303] using wordTrace_append hprefix tailTrace_143303
  have hstable : (prefixWord ++ tailWord_143303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143303).length < 2 ^ (prefixWord ++ tailWord_143303).sum := by decide
  have hdescent : baseEnd_143303 < baseStart_143303 := by decide
  rcases family_descends (prefixWord ++ tailWord_143303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143327 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_143327 : Nat := 118140960795 + 143327 * 2 ^ 59
def prefixEnd_143327 : Nat := 4983230072969 + 3 ^ 40 * 143327 * 2
def baseEnd_143327 : Nat := 65418348237391969914095

theorem tailTrace_143327 : CollatzResearch.WordTrace tailWord_143327 prefixEnd_143327 65418348237391969914095 := by
  unfold tailWord_143327
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227565151758232147892235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3485043434505488098594823 5227565151758232147892235)
  ·
    refine ⟨7841347727637348221838353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5227565151758232147892235 7841347727637348221838353)
    ·
      refine ⟨5881010795728011166378765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7841347727637348221838353 5881010795728011166378765)
      ·
        refine ⟨2205379048398004187392037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5881010795728011166378765 2205379048398004187392037)
        ·
          refine ⟨413508571574625785136007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2205379048398004187392037 413508571574625785136007)
          ·
            refine ⟨620262857361938677704011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413508571574625785136007 620262857361938677704011)
            ·
              refine ⟨930394286042908016556017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620262857361938677704011 930394286042908016556017)
              ·
                refine ⟨697795714532181012417013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930394286042908016556017 697795714532181012417013)
                ·
                  refine ⟨65418348237391969914095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 697795714532181012417013 65418348237391969914095)
                  ·
                    rfl

theorem cell20_143327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_143327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143327 prefixEnd_143327 := by exact prefixLift 143327
  have htrace : WordTrace (prefixWord ++ tailWord_143327) baseStart_143327 baseEnd_143327 := by
    simpa [prefixWord, tailWord_143327, baseEnd_143327] using wordTrace_append hprefix tailTrace_143327
  have hstable : (prefixWord ++ tailWord_143327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143327).length < 2 ^ (prefixWord ++ tailWord_143327).sum := by decide
  have hdescent : baseEnd_143327 < baseStart_143327 := by decide
  rcases family_descends (prefixWord ++ tailWord_143327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143372 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_143372 : Nat := 118140960795 + 143372 * 2 ^ 59
def prefixEnd_143372 : Nat := 4983230072969 + 3 ^ 40 * 143372 * 2
def baseEnd_143372 : Nat := 65438887463571813413911

theorem tailTrace_143372 : CollatzResearch.WordTrace tailWord_143372 prefixEnd_143372 65438887463571813413911 := by
  unfold tailWord_143372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614603218297602416640185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3486137624396803222186913 2614603218297602416640185)
  ·
    refine ⟨1960952413723201812480139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2614603218297602416640185 1960952413723201812480139)
    ·
      refine ⟨2941428620584802718720209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1960952413723201812480139 2941428620584802718720209)
      ·
        refine ⟨2206071465438602039040157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2941428620584802718720209 2206071465438602039040157)
        ·
          refine ⟨827276799539475764640059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2206071465438602039040157 827276799539475764640059)
          ·
            refine ⟨1240915199309213646960089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827276799539475764640059 1240915199309213646960089)
            ·
              refine ⟨930686399481910235220067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240915199309213646960089 930686399481910235220067)
              ·
                refine ⟨1396029599222865352830101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930686399481910235220067 1396029599222865352830101)
                ·
                  refine ⟨65438887463571813413911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1396029599222865352830101 65438887463571813413911)
                  ·
                    rfl

theorem cell20_143372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_143372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143372 prefixEnd_143372 := by exact prefixLift 143372
  have htrace : WordTrace (prefixWord ++ tailWord_143372) baseStart_143372 baseEnd_143372 := by
    simpa [prefixWord, tailWord_143372, baseEnd_143372] using wordTrace_append hprefix tailTrace_143372
  have hstable : (prefixWord ++ tailWord_143372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143372).length < 2 ^ (prefixWord ++ tailWord_143372).sum := by decide
  have hdescent : baseEnd_143372 < baseStart_143372 := by decide
  rcases family_descends (prefixWord ++ tailWord_143372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143379 : List Nat := [1, 1, 1, 2, 1, 4, 4, 6]
def baseStart_143379 : Nat := 118140960795 + 143379 * 2 ^ 59
def prefixEnd_143379 : Nat := 4983230072969 + 3 ^ 40 * 143379 * 2
def baseEnd_143379 : Nat := 21814027484770300060183

theorem tailTrace_143379 : CollatzResearch.WordTrace tailWord_143379 prefixEnd_143379 21814027484770300060183 := by
  unfold tailWord_143379
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229461747569845028785191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3486307831713230019190127 5229461747569845028785191)
  ·
    refine ⟨7844192621354767543177787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5229461747569845028785191 7844192621354767543177787)
    ·
      refine ⟨11766288932032151314766681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7844192621354767543177787 11766288932032151314766681)
      ·
        refine ⟨8824716699024113486075011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11766288932032151314766681 8824716699024113486075011)
        ·
          refine ⟨13237075048536170229112517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8824716699024113486075011 13237075048536170229112517)
          ·
            refine ⟨2481951571600531917958597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13237075048536170229112517 2481951571600531917958597)
            ·
              refine ⟨465365919675099734617237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2481951571600531917958597 465365919675099734617237)
              ·
                refine ⟨21814027484770300060183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 465365919675099734617237 21814027484770300060183)
                ·
                  rfl

theorem cell20_143379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_143379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143379 prefixEnd_143379 := by exact prefixLift 143379
  have htrace : WordTrace (prefixWord ++ tailWord_143379) baseStart_143379 baseEnd_143379 := by
    simpa [prefixWord, tailWord_143379, baseEnd_143379] using wordTrace_append hprefix tailTrace_143379
  have hstable : (prefixWord ++ tailWord_143379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143379).length < 2 ^ (prefixWord ++ tailWord_143379).sum := by decide
  have hdescent : baseEnd_143379 < baseStart_143379 := by decide
  rcases family_descends (prefixWord ++ tailWord_143379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143396 : List Nat := [2, 3, 1, 4, 2, 8]
def baseStart_143396 : Nat := 118140960795 + 143396 * 2 ^ 59
def prefixEnd_143396 : Nat := 4983230072969 + 3 ^ 40 * 143396 * 2
def baseEnd_143396 : Nat := 2424068211760533207919

theorem tailTrace_143396 : CollatzResearch.WordTrace tailWord_143396 prefixEnd_143396 2424068211760533207919 := by
  unfold tailWord_143396
  simp only [CollatzResearch.WordTrace]
  refine ⟨2615040894254128466077021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3486721192338837954769361 2615040894254128466077021)
  ·
    refine ⟨980640335345298174778883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2615040894254128466077021 980640335345298174778883)
    ·
      refine ⟨1470960503017947262168325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980640335345298174778883 1470960503017947262168325)
      ·
        refine ⟨275805094315865111656561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1470960503017947262168325 275805094315865111656561)
        ·
          refine ⟨206853820736898833742421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275805094315865111656561 206853820736898833742421)
          ·
            refine ⟨2424068211760533207919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 206853820736898833742421 2424068211760533207919)
            ·
              rfl

theorem cell20_143396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 8].length) (baseStart_143396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143396 prefixEnd_143396 := by exact prefixLift 143396
  have htrace : WordTrace (prefixWord ++ tailWord_143396) baseStart_143396 baseEnd_143396 := by
    simpa [prefixWord, tailWord_143396, baseEnd_143396] using wordTrace_append hprefix tailTrace_143396
  have hstable : (prefixWord ++ tailWord_143396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143396).length < 2 ^ (prefixWord ++ tailWord_143396).sum := by decide
  have hdescent : baseEnd_143396 < baseStart_143396 := by decide
  rcases family_descends (prefixWord ++ tailWord_143396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143402 : List Nat := [3, 1, 4, 1, 2, 3, 2, 2, 2]
def baseStart_143402 : Nat := 118140960795 + 143402 * 2 ^ 59
def prefixEnd_143402 : Nat := 4983230072969 + 3 ^ 40 * 143402 * 2
def baseEnd_143402 : Nat := 65452580281025042413789

theorem tailTrace_143402 : CollatzResearch.WordTrace tailWord_143402 prefixEnd_143402 65452580281025042413789 := by
  unfold tailWord_143402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1307575156621629989218115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3486867084324346637914973 1307575156621629989218115)
  ·
    refine ⟨1961362734932444983827173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1307575156621629989218115 1961362734932444983827173)
    ·
      refine ⟨367755512799833434467595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1961362734932444983827173 367755512799833434467595)
      ·
        refine ⟨551633269199750151701393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367755512799833434467595 551633269199750151701393)
        ·
          refine ⟨413724951899812613776045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551633269199750151701393 413724951899812613776045)
          ·
            refine ⟨155146856962429730166017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 413724951899812613776045 155146856962429730166017)
            ·
              refine ⟨116360142721822297624513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155146856962429730166017 116360142721822297624513)
              ·
                refine ⟨87270107041366723218385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116360142721822297624513 87270107041366723218385)
                ·
                  refine ⟨65452580281025042413789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87270107041366723218385 65452580281025042413789)
                  ·
                    rfl

theorem cell20_143402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_143402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143402 prefixEnd_143402 := by exact prefixLift 143402
  have htrace : WordTrace (prefixWord ++ tailWord_143402) baseStart_143402 baseEnd_143402 := by
    simpa [prefixWord, tailWord_143402, baseEnd_143402] using wordTrace_append hprefix tailTrace_143402
  have hstable : (prefixWord ++ tailWord_143402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143402).length < 2 ^ (prefixWord ++ tailWord_143402).sum := by decide
  have hdescent : baseEnd_143402 < baseStart_143402 := by decide
  rcases family_descends (prefixWord ++ tailWord_143402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143430 : List Nat := [6, 1, 1, 1, 1, 1, 5, 4]
def baseStart_143430 : Nat := 118140960795 + 143430 * 2 ^ 59
def prefixEnd_143430 : Nat := 4983230072969 + 3 ^ 40 * 143430 * 2
def baseEnd_143430 : Nat := 21821786747993796493447

theorem tailTrace_143430 : CollatzResearch.WordTrace tailWord_143430 prefixEnd_143430 21821786747993796493447 := by
  unfold tailWord_143430
  simp only [CollatzResearch.WordTrace]
  refine ⟨163478808449533773090367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3487547913590053825927829 163478808449533773090367)
  ·
    refine ⟨245218212674300659635551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163478808449533773090367 245218212674300659635551)
    ·
      refine ⟨367827319011450989453327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245218212674300659635551 367827319011450989453327)
      ·
        refine ⟨551740978517176484179991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367827319011450989453327 551740978517176484179991)
        ·
          refine ⟨827611467775764726269987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551740978517176484179991 827611467775764726269987)
          ·
            refine ⟨1241417201663647089404981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827611467775764726269987 1241417201663647089404981)
            ·
              refine ⟨116382862655966914631717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1241417201663647089404981 116382862655966914631717)
              ·
                refine ⟨21821786747993796493447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116382862655966914631717 21821786747993796493447)
                ·
                  rfl

theorem cell20_143430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_143430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143430 prefixEnd_143430 := by exact prefixLift 143430
  have htrace : WordTrace (prefixWord ++ tailWord_143430) baseStart_143430 baseEnd_143430 := by
    simpa [prefixWord, tailWord_143430, baseEnd_143430] using wordTrace_append hprefix tailTrace_143430
  have hstable : (prefixWord ++ tailWord_143430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143430).length < 2 ^ (prefixWord ++ tailWord_143430).sum := by decide
  have hdescent : baseEnd_143430 < baseStart_143430 := by decide
  rcases family_descends (prefixWord ++ tailWord_143430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143454 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_143454 : Nat := 118140960795 + 143454 * 2 ^ 59
def prefixEnd_143454 : Nat := 4983230072969 + 3 ^ 40 * 143454 * 2
def baseEnd_143454 : Nat := 65476314497943972680243

theorem tailTrace_143454 : CollatzResearch.WordTrace tailWord_143454 prefixEnd_143454 65476314497943972680243 := by
  unfold tailWord_143454
  simp only [CollatzResearch.WordTrace]
  refine ⟨654024652787266604720677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3488131481532088558510277 654024652787266604720677)
  ·
    refine ⟨122629622397612488385127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 654024652787266604720677 122629622397612488385127)
    ·
      refine ⟨183944433596418732577691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122629622397612488385127 183944433596418732577691)
      ·
        refine ⟨275916650394628098866537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183944433596418732577691 275916650394628098866537)
        ·
          refine ⟨206937487795971074149903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275916650394628098866537 206937487795971074149903)
          ·
            refine ⟨310406231693956611224855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206937487795971074149903 310406231693956611224855)
            ·
              refine ⟨465609347540934916837283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310406231693956611224855 465609347540934916837283)
              ·
                refine ⟨698414021311402375255925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465609347540934916837283 698414021311402375255925)
                ·
                  refine ⟨65476314497943972680243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 698414021311402375255925 65476314497943972680243)
                  ·
                    rfl

theorem cell20_143454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_143454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143454 prefixEnd_143454 := by exact prefixLift 143454
  have htrace : WordTrace (prefixWord ++ tailWord_143454) baseStart_143454 baseEnd_143454 := by
    simpa [prefixWord, tailWord_143454, baseEnd_143454] using wordTrace_append hprefix tailTrace_143454
  have hstable : (prefixWord ++ tailWord_143454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143454).length < 2 ^ (prefixWord ++ tailWord_143454).sum := by decide
  have hdescent : baseEnd_143454 < baseStart_143454 := by decide
  rcases family_descends (prefixWord ++ tailWord_143454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143465 : List Nat := [1, 2, 1, 1, 1, 5, 1, 6, 2]
def baseStart_143465 : Nat := 118140960795 + 143465 * 2 ^ 59
def prefixEnd_143465 : Nat := 4983230072969 + 3 ^ 40 * 143465 * 2
def baseEnd_143465 : Nat := 65481335197676823313531

theorem tailTrace_143465 : CollatzResearch.WordTrace tailWord_143465 prefixEnd_143465 65481335197676823313531 := by
  unfold tailWord_143465
  simp only [CollatzResearch.WordTrace]
  refine ⟨5232598425258281716415849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3488398950172187810943899 5232598425258281716415849)
  ·
    refine ⟨3924448818943711287311887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5232598425258281716415849 3924448818943711287311887)
    ·
      refine ⟨5886673228415566930967831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3924448818943711287311887 5886673228415566930967831)
      ·
        refine ⟨8830009842623350396451747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5886673228415566930967831 8830009842623350396451747)
        ·
          refine ⟨13245014763935025594677621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8830009842623350396451747 13245014763935025594677621)
          ·
            refine ⟨1241720134118908649501027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13245014763935025594677621 1241720134118908649501027)
            ·
              refine ⟨1862580201178362974251541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241720134118908649501027 1862580201178362974251541)
              ·
                refine ⟨87308446930235764418041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1862580201178362974251541 87308446930235764418041)
                ·
                  refine ⟨65481335197676823313531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87308446930235764418041 65481335197676823313531)
                  ·
                    rfl

theorem cell20_143465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_143465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143465 prefixEnd_143465 := by exact prefixLift 143465
  have htrace : WordTrace (prefixWord ++ tailWord_143465) baseStart_143465 baseEnd_143465 := by
    simpa [prefixWord, tailWord_143465, baseEnd_143465] using wordTrace_append hprefix tailTrace_143465
  have hstable : (prefixWord ++ tailWord_143465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143465).length < 2 ^ (prefixWord ++ tailWord_143465).sum := by decide
  have hdescent : baseEnd_143465 < baseStart_143465 := by decide
  rcases family_descends (prefixWord ++ tailWord_143465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143517 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_143517 : Nat := 118140960795 + 143517 * 2 ^ 59
def prefixEnd_143517 : Nat := 4983230072969 + 3 ^ 40 * 143517 * 2
def baseEnd_143517 : Nat := 65505069414595753579985

theorem tailTrace_143517 : CollatzResearch.WordTrace tailWord_143517 prefixEnd_143517 65505069414595753579985 := by
  unfold tailWord_143517
  simp only [CollatzResearch.WordTrace]
  refine ⟨5234495021069894597308805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3489663347379929731539203 5234495021069894597308805)
  ·
    refine ⟨981467816450605236995401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5234495021069894597308805 981467816450605236995401)
    ·
      refine ⟨736100862337953927746551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 981467816450605236995401 736100862337953927746551)
      ·
        refine ⟨1104151293506930891619827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736100862337953927746551 1104151293506930891619827)
        ·
          refine ⟨1656226940260396337429741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104151293506930891619827 1656226940260396337429741)
          ·
            refine ⟨621085102597648626536153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1656226940260396337429741 621085102597648626536153)
            ·
              refine ⟨465813826948236469902115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621085102597648626536153 465813826948236469902115)
              ·
                refine ⟨698720740422354704853173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465813826948236469902115 698720740422354704853173)
                ·
                  refine ⟨65505069414595753579985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 698720740422354704853173 65505069414595753579985)
                  ·
                    rfl

theorem cell20_143517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_143517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143517 prefixEnd_143517 := by exact prefixLift 143517
  have htrace : WordTrace (prefixWord ++ tailWord_143517) baseStart_143517 baseEnd_143517 := by
    simpa [prefixWord, tailWord_143517, baseEnd_143517] using wordTrace_append hprefix tailTrace_143517
  have hstable : (prefixWord ++ tailWord_143517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143517).length < 2 ^ (prefixWord ++ tailWord_143517).sum := by decide
  have hdescent : baseEnd_143517 < baseStart_143517 := by decide
  rcases family_descends (prefixWord ++ tailWord_143517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143527 : List Nat := [1, 1, 6, 2, 2, 1, 2, 5]
def baseStart_143527 : Nat := 118140960795 + 143527 * 2 ^ 59
def prefixEnd_143527 : Nat := 4983230072969 + 3 ^ 40 * 143527 * 2
def baseEnd_143527 : Nat := 21836544562360054415537

theorem tailTrace_143527 : CollatzResearch.WordTrace tailWord_143527 prefixEnd_143527 21836544562360054415537 := by
  unfold tailWord_143527
  simp only [CollatzResearch.WordTrace]
  refine ⟨5234859751033666305172835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3489906500689110870115223 5234859751033666305172835)
  ·
    refine ⟨7852289626550499457759253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5234859751033666305172835 7852289626550499457759253)
    ·
      refine ⟨368076076244554662082465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7852289626550499457759253 368076076244554662082465)
      ·
        refine ⟨276057057183415996561849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368076076244554662082465 276057057183415996561849)
        ·
          refine ⟨207042792887561997421387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276057057183415996561849 207042792887561997421387)
          ·
            refine ⟨310564189331342996132081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207042792887561997421387 310564189331342996132081)
            ·
              refine ⟨232923141998507247099061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310564189331342996132081 232923141998507247099061)
              ·
                refine ⟨21836544562360054415537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 232923141998507247099061 21836544562360054415537)
                ·
                  rfl

theorem cell20_143527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 5].length) (baseStart_143527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143527 prefixEnd_143527 := by exact prefixLift 143527
  have htrace : WordTrace (prefixWord ++ tailWord_143527) baseStart_143527 baseEnd_143527 := by
    simpa [prefixWord, tailWord_143527, baseEnd_143527] using wordTrace_append hprefix tailTrace_143527
  have hstable : (prefixWord ++ tailWord_143527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143527).length < 2 ^ (prefixWord ++ tailWord_143527).sum := by decide
  have hdescent : baseEnd_143527 < baseStart_143527 := by decide
  rcases family_descends (prefixWord ++ tailWord_143527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143658 : List Nat := [3, 1, 4, 2, 2, 2, 2, 4]
def baseStart_143658 : Nat := 118140960795 + 143658 * 2 ^ 59
def prefixEnd_143658 : Nat := 4983230072969 + 3 ^ 40 * 143658 * 2
def baseEnd_143658 : Nat := 21856475218875309959803

theorem tailTrace_143658 : CollatzResearch.WordTrace tailWord_143658 prefixEnd_143658 21856475218875309959803 := by
  unfold tailWord_143658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1309909428389768919547907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3493091809039383785461085 1309909428389768919547907)
  ·
    refine ⟨1964864142584653379321861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1309909428389768919547907 1964864142584653379321861)
    ·
      refine ⟨368412026734622508622849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1964864142584653379321861 368412026734622508622849)
      ·
        refine ⟨276309020050966881467137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368412026734622508622849 276309020050966881467137)
        ·
          refine ⟨207231765038225161100353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276309020050966881467137 207231765038225161100353)
          ·
            refine ⟨155423823778668870825265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207231765038225161100353 155423823778668870825265)
            ·
              refine ⟨116567867834001653118949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155423823778668870825265 116567867834001653118949)
              ·
                refine ⟨21856475218875309959803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116567867834001653118949 21856475218875309959803)
                ·
                  rfl

theorem cell20_143658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_143658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143658 prefixEnd_143658 := by exact prefixLift 143658
  have htrace : WordTrace (prefixWord ++ tailWord_143658) baseStart_143658 baseEnd_143658 := by
    simpa [prefixWord, tailWord_143658, baseEnd_143658] using wordTrace_append hprefix tailTrace_143658
  have hstable : (prefixWord ++ tailWord_143658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143658).length < 2 ^ (prefixWord ++ tailWord_143658).sum := by decide
  have hdescent : baseEnd_143658 < baseStart_143658 := by decide
  rcases family_descends (prefixWord ++ tailWord_143658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143700 : List Nat := [2, 4, 1, 1, 2, 3, 2, 5]
def baseStart_143700 : Nat := 118140960795 + 143700 * 2 ^ 59
def prefixEnd_143700 : Nat := 4983230072969 + 3 ^ 40 * 143700 * 2
def baseEnd_143700 : Nat := 21862865200353483493079

theorem tailTrace_143700 : CollatzResearch.WordTrace tailWord_143700 prefixEnd_143700 21862865200353483493079 := by
  unfold tailWord_143700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2620584789703458425610277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3494113052937944567480369 2620584789703458425610277)
  ·
    refine ⟨491359648069398454801927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2620584789703458425610277 491359648069398454801927)
    ·
      refine ⟨737039472104097682202891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 491359648069398454801927 737039472104097682202891)
      ·
        refine ⟨1105559208156146523304337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737039472104097682202891 1105559208156146523304337)
        ·
          refine ⟨829169406117109892478253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1105559208156146523304337 829169406117109892478253)
          ·
            refine ⟨310938527293916209679345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 829169406117109892478253 310938527293916209679345)
            ·
              refine ⟨233203895470437157259509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310938527293916209679345 233203895470437157259509)
              ·
                refine ⟨21862865200353483493079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 233203895470437157259509 21862865200353483493079)
                ·
                  rfl

theorem cell20_143700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_143700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143700 prefixEnd_143700 := by exact prefixLift 143700
  have htrace : WordTrace (prefixWord ++ tailWord_143700) baseStart_143700 baseEnd_143700 := by
    simpa [prefixWord, tailWord_143700, baseEnd_143700] using wordTrace_append hprefix tailTrace_143700
  have hstable : (prefixWord ++ tailWord_143700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143700).length < 2 ^ (prefixWord ++ tailWord_143700).sum := by decide
  have hdescent : baseEnd_143700 < baseStart_143700 := by decide
  rcases family_descends (prefixWord ++ tailWord_143700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143735 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_143735 : Nat := 118140960795 + 143735 * 2 ^ 59
def prefixEnd_143735 : Nat := 4983230072969 + 3 ^ 40 * 143735 * 2
def baseEnd_143735 : Nat := 65604570554755884312427

theorem tailTrace_143735 : CollatzResearch.WordTrace tailWord_143735 prefixEnd_143735 65604570554755884312427 := by
  unfold tailWord_143735
  simp only [CollatzResearch.WordTrace]
  refine ⟨5242446134280117828744659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3494964089520078552496439 5242446134280117828744659)
  ·
    refine ⟨7863669201420176743116989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5242446134280117828744659 7863669201420176743116989)
    ·
      refine ⟨2948875950532566278668871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7863669201420176743116989 2948875950532566278668871)
      ·
        refine ⟨4423313925798849418003307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2948875950532566278668871 4423313925798849418003307)
        ·
          refine ⟨6634970888698274127004961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4423313925798849418003307 6634970888698274127004961)
          ·
            refine ⟨4976228166523705595253721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6634970888698274127004961 4976228166523705595253721)
            ·
              refine ⟨3732171124892779196440291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4976228166523705595253721 3732171124892779196440291)
              ·
                refine ⟨5598256687339168794660437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732171124892779196440291 5598256687339168794660437)
                ·
                  refine ⟨65604570554755884312427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5598256687339168794660437 65604570554755884312427)
                  ·
                    rfl

theorem cell20_143735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_143735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143735 prefixEnd_143735 := by exact prefixLift 143735
  have htrace : WordTrace (prefixWord ++ tailWord_143735) baseStart_143735 baseEnd_143735 := by
    simpa [prefixWord, tailWord_143735, baseEnd_143735] using wordTrace_append hprefix tailTrace_143735
  have hstable : (prefixWord ++ tailWord_143735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143735).length < 2 ^ (prefixWord ++ tailWord_143735).sum := by decide
  have hdescent : baseEnd_143735 < baseStart_143735 := by decide
  rcases family_descends (prefixWord ++ tailWord_143735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143752 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_143752 : Nat := 118140960795 + 143752 * 2 ^ 59
def prefixEnd_143752 : Nat := 4983230072969 + 3 ^ 40 * 143752 * 2
def baseEnd_143752 : Nat := 65612329817979380745691

theorem tailTrace_143752 : CollatzResearch.WordTrace tailWord_143752 prefixEnd_143752 65612329817979380745691 := by
  unfold tailWord_143752
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621533087609264866056755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3495377450145686488075673 2621533087609264866056755)
  ·
    refine ⟨3932299631413897299085133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2621533087609264866056755 3932299631413897299085133)
    ·
      refine ⟨1474612361780211487156925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3932299631413897299085133 1474612361780211487156925)
      ·
        refine ⟨552979635667579307683847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1474612361780211487156925 552979635667579307683847)
        ·
          refine ⟨829469453501368961525771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552979635667579307683847 829469453501368961525771)
          ·
            refine ⟨1244204180252053442288657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829469453501368961525771 1244204180252053442288657)
            ·
              refine ⟨933153135189040081716493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244204180252053442288657 933153135189040081716493)
              ·
                refine ⟨349932425695890030643685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 933153135189040081716493 349932425695890030643685)
                ·
                  refine ⟨65612329817979380745691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 349932425695890030643685 65612329817979380745691)
                  ·
                    rfl

theorem cell20_143752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_143752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143752 prefixEnd_143752 := by exact prefixLift 143752
  have htrace : WordTrace (prefixWord ++ tailWord_143752) baseStart_143752 baseEnd_143752 := by
    simpa [prefixWord, tailWord_143752, baseEnd_143752] using wordTrace_append hprefix tailTrace_143752
  have hstable : (prefixWord ++ tailWord_143752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143752).length < 2 ^ (prefixWord ++ tailWord_143752).sum := by decide
  have hdescent : baseEnd_143752 < baseStart_143752 := by decide
  rcases family_descends (prefixWord ++ tailWord_143752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143776 : List Nat := [2, 1, 1, 4, 1, 4, 3, 4]
def baseStart_143776 : Nat := 118140960795 + 143776 * 2 ^ 59
def prefixEnd_143776 : Nat := 4983230072969 + 3 ^ 40 * 143776 * 2
def baseEnd_143776 : Nat := 21874428023980654648531

theorem tailTrace_143776 : CollatzResearch.WordTrace tailWord_143776 prefixEnd_143776 21874428023980654648531 := by
  unfold tailWord_143776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621970763565790915493591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3495961018087721220658121 2621970763565790915493591)
  ·
    refine ⟨3932956145348686373240387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2621970763565790915493591 3932956145348686373240387)
    ·
      refine ⟨5899434218023029559860581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3932956145348686373240387 5899434218023029559860581)
      ·
        refine ⟨1106143915879318042473859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5899434218023029559860581 1106143915879318042473859)
        ·
          refine ⟨1659215873818977063710789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106143915879318042473859 1659215873818977063710789)
          ·
            refine ⟨311102976341058199445773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1659215873818977063710789 311102976341058199445773)
            ·
              refine ⟨116663616127896824792165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 311102976341058199445773 116663616127896824792165)
              ·
                refine ⟨21874428023980654648531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116663616127896824792165 21874428023980654648531)
                ·
                  rfl

theorem cell20_143776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_143776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143776 prefixEnd_143776 := by exact prefixLift 143776
  have htrace : WordTrace (prefixWord ++ tailWord_143776) baseStart_143776 baseEnd_143776 := by
    simpa [prefixWord, tailWord_143776, baseEnd_143776] using wordTrace_append hprefix tailTrace_143776
  have hstable : (prefixWord ++ tailWord_143776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143776).length < 2 ^ (prefixWord ++ tailWord_143776).sum := by decide
  have hdescent : baseEnd_143776 < baseStart_143776 := by decide
  rcases family_descends (prefixWord ++ tailWord_143776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143873 : List Nat := [1, 2, 4, 1, 3, 1, 1, 7]
def baseStart_143873 : Nat := 118140960795 + 143873 * 2 ^ 59
def prefixEnd_143873 : Nat := 4983230072969 + 3 ^ 40 * 143873 * 2
def baseEnd_143873 : Nat := 21889185838346912570621

theorem tailTrace_143873 : CollatzResearch.WordTrace tailWord_143873 prefixEnd_143873 21889185838346912570621 := by
  unfold tailWord_143873
  simp only [CollatzResearch.WordTrace]
  refine ⟨5247479407780167397268273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3498319605186778264845515 5247479407780167397268273)
  ·
    refine ⟨3935609555835125547951205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5247479407780167397268273 3935609555835125547951205)
    ·
      refine ⟨737926791719086040240851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3935609555835125547951205 737926791719086040240851)
      ·
        refine ⟨1106890187578629060361277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737926791719086040240851 1106890187578629060361277)
        ·
          refine ⟨415083820341985897635479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1106890187578629060361277 415083820341985897635479)
          ·
            refine ⟨622625730512978846453219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415083820341985897635479 622625730512978846453219)
            ·
              refine ⟨933938595769468269679829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622625730512978846453219 933938595769468269679829)
              ·
                refine ⟨21889185838346912570621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 933938595769468269679829 21889185838346912570621)
                ·
                  rfl

theorem cell20_143873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_143873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143873 prefixEnd_143873 := by exact prefixLift 143873
  have htrace : WordTrace (prefixWord ++ tailWord_143873) baseStart_143873 baseEnd_143873 := by
    simpa [prefixWord, tailWord_143873, baseEnd_143873] using wordTrace_append hprefix tailTrace_143873
  have hstable : (prefixWord ++ tailWord_143873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143873).length < 2 ^ (prefixWord ++ tailWord_143873).sum := by decide
  have hdescent : baseEnd_143873 < baseStart_143873 := by decide
  rcases family_descends (prefixWord ++ tailWord_143873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143876 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 3]
def baseStart_143876 : Nat := 118140960795 + 143876 * 2 ^ 59
def prefixEnd_143876 : Nat := 4983230072969 + 3 ^ 40 * 143876 * 2
def baseEnd_143876 : Nat := 65668926796786060611851

theorem tailTrace_143876 : CollatzResearch.WordTrace tailWord_143876 prefixEnd_143876 65668926796786060611851 := by
  unfold tailWord_143876
  simp only [CollatzResearch.WordTrace]
  refine ⟨2623794413384649454813741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3498392551179532606418321 2623794413384649454813741)
  ·
    refine ⟨983922905019243545555153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2623794413384649454813741 983922905019243545555153)
    ·
      refine ⟨737942178764432659166365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 983922905019243545555153 737942178764432659166365)
      ·
        refine ⟨276728317036662247187387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 737942178764432659166365 276728317036662247187387)
        ·
          refine ⟨415092475554993370781081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276728317036662247187387 415092475554993370781081)
          ·
            refine ⟨311319356666245028085811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415092475554993370781081 311319356666245028085811)
            ·
              refine ⟨466979034999367542128717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311319356666245028085811 466979034999367542128717)
              ·
                refine ⟨175117138124762828298269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466979034999367542128717 175117138124762828298269)
                ·
                  refine ⟨65668926796786060611851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175117138124762828298269 65668926796786060611851)
                  ·
                    rfl

theorem cell20_143876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_143876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143876 prefixEnd_143876 := by exact prefixLift 143876
  have htrace : WordTrace (prefixWord ++ tailWord_143876) baseStart_143876 baseEnd_143876 := by
    simpa [prefixWord, tailWord_143876, baseEnd_143876] using wordTrace_append hprefix tailTrace_143876
  have hstable : (prefixWord ++ tailWord_143876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143876).length < 2 ^ (prefixWord ++ tailWord_143876).sum := by decide
  have hdescent : baseEnd_143876 < baseStart_143876 := by decide
  rcases family_descends (prefixWord ++ tailWord_143876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143914 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_143914 : Nat := 118140960795 + 143914 * 2 ^ 59
def prefixEnd_143914 : Nat := 4983230072969 + 3 ^ 40 * 143914 * 2
def baseEnd_143914 : Nat := 65686271032226817345029

theorem tailTrace_143914 : CollatzResearch.WordTrace tailWord_143914 prefixEnd_143914 65686271032226817345029 := by
  unfold tailWord_143914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312243700157907849877699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3499316533754420933007197 1312243700157907849877699)
  ·
    refine ⟨1968365550236861774816549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1312243700157907849877699 1968365550236861774816549)
    ·
      refine ⟨369068540669411582778103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1968365550236861774816549 369068540669411582778103)
      ·
        refine ⟨553602811004117374167155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369068540669411582778103 553602811004117374167155)
        ·
          refine ⟨830404216506176061250733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553602811004117374167155 830404216506176061250733)
          ·
            refine ⟨311401581189816022969025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 830404216506176061250733 311401581189816022969025)
            ·
              refine ⟨233551185892362017226769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311401581189816022969025 233551185892362017226769)
              ·
                refine ⟨175163389419271512920077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233551185892362017226769 175163389419271512920077)
                ·
                  refine ⟨65686271032226817345029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175163389419271512920077 65686271032226817345029)
                  ·
                    rfl

theorem cell20_143914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_143914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143914 prefixEnd_143914 := by exact prefixLift 143914
  have htrace : WordTrace (prefixWord ++ tailWord_143914) baseStart_143914 baseEnd_143914 := by
    simpa [prefixWord, tailWord_143914, baseEnd_143914] using wordTrace_append hprefix tailTrace_143914
  have hstable : (prefixWord ++ tailWord_143914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143914).length < 2 ^ (prefixWord ++ tailWord_143914).sum := by decide
  have hdescent : baseEnd_143914 < baseStart_143914 := by decide
  rcases family_descends (prefixWord ++ tailWord_143914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143924 : List Nat := [2, 5, 1, 3, 1, 2, 1, 5]
def baseStart_143924 : Nat := 118140960795 + 143924 * 2 ^ 59
def prefixEnd_143924 : Nat := 4983230072969 + 3 ^ 40 * 143924 * 2
def baseEnd_143924 : Nat := 21896945101570409003885

theorem tailTrace_143924 : CollatzResearch.WordTrace tailWord_143924 prefixEnd_143924 21896945101570409003885 := by
  unfold tailWord_143924
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624669765297701553687413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3499559687063602071583217 2624669765297701553687413)
  ·
    refine ⟨246062790496659520658195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2624669765297701553687413 246062790496659520658195)
    ·
      refine ⟨369094185744989280987293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246062790496659520658195 369094185744989280987293)
      ·
        refine ⟨138410319654370980370235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369094185744989280987293 138410319654370980370235)
        ·
          refine ⟨207615479481556470555353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138410319654370980370235 207615479481556470555353)
          ·
            refine ⟨155711609611167352916515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207615479481556470555353 155711609611167352916515)
            ·
              refine ⟨233567414416751029374773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155711609611167352916515 233567414416751029374773)
              ·
                refine ⟨21896945101570409003885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 233567414416751029374773 21896945101570409003885)
                ·
                  rfl

theorem cell20_143924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_143924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143924 prefixEnd_143924 := by exact prefixLift 143924
  have htrace : WordTrace (prefixWord ++ tailWord_143924) baseStart_143924 baseEnd_143924 := by
    simpa [prefixWord, tailWord_143924, baseEnd_143924] using wordTrace_append hprefix tailTrace_143924
  have hstable : (prefixWord ++ tailWord_143924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143924).length < 2 ^ (prefixWord ++ tailWord_143924).sum := by decide
  have hdescent : baseEnd_143924 < baseStart_143924 := by decide
  rcases family_descends (prefixWord ++ tailWord_143924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143959 : List Nat := [1, 1, 3, 2, 2, 2, 4, 3, 2]
def baseStart_143959 : Nat := 118140960795 + 143959 * 2 ^ 59
def prefixEnd_143959 : Nat := 4983230072969 + 3 ^ 40 * 143959 * 2
def baseEnd_143959 : Nat := 65706810258406660844845

theorem tailTrace_143959 : CollatzResearch.WordTrace tailWord_143959 prefixEnd_143959 65706810258406660844845 := by
  unfold tailWord_143959
  simp only [CollatzResearch.WordTrace]
  refine ⟨5250616085468604084898931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3500410723645736056599287 5250616085468604084898931)
  ·
    refine ⟨7875924128202906127348397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5250616085468604084898931 7875924128202906127348397)
    ·
      refine ⟨2953471548076089797755649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7875924128202906127348397 2953471548076089797755649)
      ·
        refine ⟨2215103661057067348316737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2953471548076089797755649 2215103661057067348316737)
        ·
          refine ⟨1661327745792800511237553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2215103661057067348316737 1661327745792800511237553)
          ·
            refine ⟨1245995809344600383428165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1661327745792800511237553 1245995809344600383428165)
            ·
              refine ⟨233624214252112571892781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1245995809344600383428165 233624214252112571892781)
              ·
                refine ⟨87609080344542214459793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233624214252112571892781 87609080344542214459793)
                ·
                  refine ⟨65706810258406660844845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87609080344542214459793 65706810258406660844845)
                  ·
                    rfl

theorem cell20_143959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 2].length) (baseStart_143959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143959 prefixEnd_143959 := by exact prefixLift 143959
  have htrace : WordTrace (prefixWord ++ tailWord_143959) baseStart_143959 baseEnd_143959 := by
    simpa [prefixWord, tailWord_143959, baseEnd_143959] using wordTrace_append hprefix tailTrace_143959
  have hstable : (prefixWord ++ tailWord_143959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143959).length < 2 ^ (prefixWord ++ tailWord_143959).sum := by decide
  have hdescent : baseEnd_143959 < baseStart_143959 := by decide
  rcases family_descends (prefixWord ++ tailWord_143959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143973 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 5]
def baseStart_143973 : Nat := 118140960795 + 143973 * 2 ^ 59
def prefixEnd_143973 : Nat := 4983230072969 + 3 ^ 40 * 143973 * 2
def baseEnd_143973 : Nat := 65713200239884834378121

theorem tailTrace_143973 : CollatzResearch.WordTrace tailWord_143973 prefixEnd_143973 65713200239884834378121 := by
  unfold tailWord_143973
  simp only [CollatzResearch.WordTrace]
  refine ⟨5251126707417884475908573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3500751138278589650605715 5251126707417884475908573)
  ·
    refine ⟨1969172515281706678465715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5251126707417884475908573 1969172515281706678465715)
    ·
      refine ⟨2953758772922560017698573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1969172515281706678465715 2953758772922560017698573)
      ·
        refine ⟨1107659539845960006636965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2953758772922560017698573 1107659539845960006636965)
        ·
          refine ⟨207686163721117501244431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1107659539845960006636965 207686163721117501244431)
          ·
            refine ⟨311529245581676251866647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207686163721117501244431 311529245581676251866647)
            ·
              refine ⟨467293868372514377799971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311529245581676251866647 467293868372514377799971)
              ·
                refine ⟨700940802558771566699957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467293868372514377799971 700940802558771566699957)
                ·
                  refine ⟨65713200239884834378121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 700940802558771566699957 65713200239884834378121)
                  ·
                    rfl

theorem cell20_143973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_143973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_143973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_143973 prefixEnd_143973 := by exact prefixLift 143973
  have htrace : WordTrace (prefixWord ++ tailWord_143973) baseStart_143973 baseEnd_143973 := by
    simpa [prefixWord, tailWord_143973, baseEnd_143973] using wordTrace_append hprefix tailTrace_143973
  have hstable : (prefixWord ++ tailWord_143973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143973).length < 2 ^ (prefixWord ++ tailWord_143973).sum := by decide
  have hdescent : baseEnd_143973 < baseStart_143973 := by decide
  rcases family_descends (prefixWord ++ tailWord_143973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144004 : List Nat := [2, 3, 2, 1, 3, 1, 4, 4]
def baseStart_144004 : Nat := 118140960795 + 144004 * 2 ^ 59
def prefixEnd_144004 : Nat := 4983230072969 + 3 ^ 40 * 144004 * 2
def baseEnd_144004 : Nat := 21909116494862168114887

theorem tailTrace_144004 : CollatzResearch.WordTrace tailWord_144004 prefixEnd_144004 21909116494862168114887 := by
  unfold tailWord_144004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626128685152788385143533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3501504913537051180191377 2626128685152788385143533)
  ·
    refine ⟨984798256932295644428825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2626128685152788385143533 984798256932295644428825)
    ·
      refine ⟨738598692699221733321619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 984798256932295644428825 738598692699221733321619)
      ·
        refine ⟨1107898039048832599982429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738598692699221733321619 1107898039048832599982429)
        ·
          refine ⟨415461764643312224993411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1107898039048832599982429 415461764643312224993411)
          ·
            refine ⟨623192646964968337490117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415461764643312224993411 623192646964968337490117)
            ·
              refine ⟨116848621305931563279397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 623192646964968337490117 116848621305931563279397)
              ·
                refine ⟨21909116494862168114887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116848621305931563279397 21909116494862168114887)
                ·
                  rfl

theorem cell20_144004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_144004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144004 prefixEnd_144004 := by exact prefixLift 144004
  have htrace : WordTrace (prefixWord ++ tailWord_144004) baseStart_144004 baseEnd_144004 := by
    simpa [prefixWord, tailWord_144004, baseEnd_144004] using wordTrace_append hprefix tailTrace_144004
  have hstable : (prefixWord ++ tailWord_144004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144004).length < 2 ^ (prefixWord ++ tailWord_144004).sum := by decide
  have hdescent : baseEnd_144004 < baseStart_144004 := by decide
  rcases family_descends (prefixWord ++ tailWord_144004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144045 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 3]
def baseStart_144045 : Nat := 118140960795 + 144045 * 2 ^ 59
def prefixEnd_144045 : Nat := 4983230072969 + 3 ^ 40 * 144045 * 2
def baseEnd_144045 : Nat := 65746063001772583977827

theorem tailTrace_144045 : CollatzResearch.WordTrace tailWord_144045 prefixEnd_144045 65746063001772583977827 := by
  unfold tailWord_144045
  simp only [CollatzResearch.WordTrace]
  refine ⟨5253752763157040772529589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3502501842104693848353059 5253752763157040772529589)
  ·
    refine ⟨492539321545972572424649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5253752763157040772529589 492539321545972572424649)
    ·
      refine ⟨369404491159479429318487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 492539321545972572424649 369404491159479429318487)
      ·
        refine ⟨554106736739219143977731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369404491159479429318487 554106736739219143977731)
        ·
          refine ⟨831160105108828715966597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554106736739219143977731 831160105108828715966597)
          ·
            refine ⟨155842519707905384243737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 831160105108828715966597 155842519707905384243737)
            ·
              refine ⟨116881889780929038182803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155842519707905384243737 116881889780929038182803)
              ·
                refine ⟨175322834671393557274205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116881889780929038182803 175322834671393557274205)
                ·
                  refine ⟨65746063001772583977827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175322834671393557274205 65746063001772583977827)
                  ·
                    rfl

theorem cell20_144045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_144045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144045 prefixEnd_144045 := by exact prefixLift 144045
  have htrace : WordTrace (prefixWord ++ tailWord_144045) baseStart_144045 baseEnd_144045 := by
    simpa [prefixWord, tailWord_144045, baseEnd_144045] using wordTrace_append hprefix tailTrace_144045
  have hstable : (prefixWord ++ tailWord_144045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144045).length < 2 ^ (prefixWord ++ tailWord_144045).sum := by decide
  have hdescent : baseEnd_144045 < baseStart_144045 := by decide
  rcases family_descends (prefixWord ++ tailWord_144045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144087 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 3]
def baseStart_144087 : Nat := 118140960795 + 144087 * 2 ^ 59
def prefixEnd_144087 : Nat := 4983230072969 + 3 ^ 40 * 144087 * 2
def baseEnd_144087 : Nat := 65765232946207104577655

theorem tailTrace_144087 : CollatzResearch.WordTrace tailWord_144087 prefixEnd_144087 65765232946207104577655 := by
  unfold tailWord_144087
  simp only [CollatzResearch.WordTrace]
  refine ⟨5255284629004881945558515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3503523086003254630372343 5255284629004881945558515)
  ·
    refine ⟨7882926943507322918337773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5255284629004881945558515 7882926943507322918337773)
    ·
      refine ⟨2956097603815246094376665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7882926943507322918337773 2956097603815246094376665)
      ·
        refine ⟨2217073202861434570782499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2956097603815246094376665 2217073202861434570782499)
        ·
          refine ⟨3325609804292151856173749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2217073202861434570782499 3325609804292151856173749)
          ·
            refine ⟨311775919152389236516289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3325609804292151856173749 311775919152389236516289)
            ·
              refine ⟨233831939364291927387217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311775919152389236516289 233831939364291927387217)
              ·
                refine ⟨175373954523218945540413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233831939364291927387217 175373954523218945540413)
                ·
                  refine ⟨65765232946207104577655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175373954523218945540413 65765232946207104577655)
                  ·
                    rfl

theorem cell20_144087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 3].length) (baseStart_144087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144087 prefixEnd_144087 := by exact prefixLift 144087
  have htrace : WordTrace (prefixWord ++ tailWord_144087) baseStart_144087 baseEnd_144087 := by
    simpa [prefixWord, tailWord_144087, baseEnd_144087] using wordTrace_append hprefix tailTrace_144087
  have hstable : (prefixWord ++ tailWord_144087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144087).length < 2 ^ (prefixWord ++ tailWord_144087).sum := by decide
  have hdescent : baseEnd_144087 < baseStart_144087 := by decide
  rcases family_descends (prefixWord ++ tailWord_144087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144101 : List Nat := [1, 3, 1, 4, 1, 2, 3, 5]
def baseStart_144101 : Nat := 118140960795 + 144101 * 2 ^ 59
def prefixEnd_144101 : Nat := 4983230072969 + 3 ^ 40 * 144101 * 2
def baseEnd_144101 : Nat := 21923874309228426036977

theorem tailTrace_144101 : CollatzResearch.WordTrace tailWord_144101 prefixEnd_144101 21923874309228426036977 := by
  unfold tailWord_144101
  simp only [CollatzResearch.WordTrace]
  refine ⟨5255795250954162336568157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3503863500636108224378771 5255795250954162336568157)
  ·
    refine ⟨1970923219107810876213059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5255795250954162336568157 1970923219107810876213059)
    ·
      refine ⟨2956384828661716314319589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1970923219107810876213059 2956384828661716314319589)
      ·
        refine ⟨554322155374071808934923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2956384828661716314319589 554322155374071808934923)
        ·
          refine ⟨831483233061107713402385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554322155374071808934923 831483233061107713402385)
          ·
            refine ⟨623612424795830785051789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831483233061107713402385 623612424795830785051789)
            ·
              refine ⟨233854659298436544394421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 623612424795830785051789 233854659298436544394421)
              ·
                refine ⟨21923874309228426036977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 233854659298436544394421 21923874309228426036977)
                ·
                  rfl

theorem cell20_144101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_144101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144101 prefixEnd_144101 := by exact prefixLift 144101
  have htrace : WordTrace (prefixWord ++ tailWord_144101) baseStart_144101 baseEnd_144101 := by
    simpa [prefixWord, tailWord_144101, baseEnd_144101] using wordTrace_append hprefix tailTrace_144101
  have hstable : (prefixWord ++ tailWord_144101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144101).length < 2 ^ (prefixWord ++ tailWord_144101).sum := by decide
  have hdescent : baseEnd_144101 < baseStart_144101 := by decide
  rcases family_descends (prefixWord ++ tailWord_144101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144118 : List Nat := [5, 1, 1, 1, 1, 2, 5, 4]
def baseStart_144118 : Nat := 118140960795 + 144118 * 2 ^ 59
def prefixEnd_144118 : Nat := 4983230072969 + 3 ^ 40 * 144118 * 2
def baseEnd_144118 : Nat := 21926460730302924848065

theorem tailTrace_144118 : CollatzResearch.WordTrace tailWord_144118 prefixEnd_144118 21926460730302924848065 := by
  unfold tailWord_144118
  simp only [CollatzResearch.WordTrace]
  refine ⟨328525955743285889996063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3504276861261716159958005 328525955743285889996063)
  ·
    refine ⟨492788933614928834994095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328525955743285889996063 492788933614928834994095)
    ·
      refine ⟨739183400422393252491143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492788933614928834994095 739183400422393252491143)
      ·
        refine ⟨1108775100633589878736715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739183400422393252491143 1108775100633589878736715)
        ·
          refine ⟨1663162650950384818105073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108775100633589878736715 1663162650950384818105073)
          ·
            refine ⟨1247371988212788613578805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663162650950384818105073 1247371988212788613578805)
            ·
              refine ⟨116941123894948932523013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1247371988212788613578805 116941123894948932523013)
              ·
                refine ⟨21926460730302924848065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116941123894948932523013 21926460730302924848065)
                ·
                  rfl

theorem cell20_144118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_144118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144118 prefixEnd_144118 := by exact prefixLift 144118
  have htrace : WordTrace (prefixWord ++ tailWord_144118) baseStart_144118 baseEnd_144118 := by
    simpa [prefixWord, tailWord_144118, baseEnd_144118] using wordTrace_append hprefix tailTrace_144118
  have hstable : (prefixWord ++ tailWord_144118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144118).length < 2 ^ (prefixWord ++ tailWord_144118).sum := by decide
  have hdescent : baseEnd_144118 < baseStart_144118 := by decide
  rcases family_descends (prefixWord ++ tailWord_144118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144122 : List Nat := [3, 1, 1, 1, 1, 3, 2, 8]
def baseStart_144122 : Nat := 118140960795 + 144122 * 2 ^ 59
def prefixEnd_144122 : Nat := 4983230072969 + 3 ^ 40 * 144122 * 2
def baseEnd_144122 : Nat := 21927069299967512803615

theorem tailTrace_144122 : CollatzResearch.WordTrace tailWord_144122 prefixEnd_144122 21927069299967512803615 := by
  unfold tailWord_144122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314140295969520730770655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3504374122585388615388413 1314140295969520730770655)
  ·
    refine ⟨1971210443954281096155983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1314140295969520730770655 1971210443954281096155983)
    ·
      refine ⟨2956815665931421644233975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971210443954281096155983 2956815665931421644233975)
      ·
        refine ⟨4435223498897132466350963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2956815665931421644233975 4435223498897132466350963)
        ·
          refine ⟨6652835248345698699526445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4435223498897132466350963 6652835248345698699526445)
          ·
            refine ⟨2494813218129637012322417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6652835248345698699526445 2494813218129637012322417)
            ·
              refine ⟨1871109913597227759241813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2494813218129637012322417 1871109913597227759241813)
              ·
                refine ⟨21927069299967512803615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1871109913597227759241813 21927069299967512803615)
                ·
                  rfl

theorem cell20_144122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_144122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144122 prefixEnd_144122 := by exact prefixLift 144122
  have htrace : WordTrace (prefixWord ++ tailWord_144122) baseStart_144122 baseEnd_144122 := by
    simpa [prefixWord, tailWord_144122, baseEnd_144122] using wordTrace_append hprefix tailTrace_144122
  have hstable : (prefixWord ++ tailWord_144122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144122).length < 2 ^ (prefixWord ++ tailWord_144122).sum := by decide
  have hdescent : baseEnd_144122 < baseStart_144122 := by decide
  rcases family_descends (prefixWord ++ tailWord_144122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144173 : List Nat := [1, 5, 3, 2, 1, 1, 1, 6]
def baseStart_144173 : Nat := 118140960795 + 144173 * 2 ^ 59
def prefixEnd_144173 : Nat := 4983230072969 + 3 ^ 40 * 144173 * 2
def baseEnd_144173 : Nat := 21934828563191009236879

theorem tailTrace_144173 : CollatzResearch.WordTrace tailWord_144173 prefixEnd_144173 21934828563191009236879 := by
  unfold tailWord_144173
  simp only [CollatzResearch.WordTrace]
  refine ⟨5258421306693318633189173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3505614204462212422126115 5258421306693318633189173)
  ·
    refine ⟨492976997502498621861485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5258421306693318633189173 492976997502498621861485)
    ·
      refine ⟨184866374063436983198057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 492976997502498621861485 184866374063436983198057)
      ·
        refine ⟨138649780547577737398543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184866374063436983198057 138649780547577737398543)
        ·
          refine ⟨207974670821366606097815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138649780547577737398543 207974670821366606097815)
          ·
            refine ⟨311962006232049909146723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207974670821366606097815 311962006232049909146723)
            ·
              refine ⟨467943009348074863720085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311962006232049909146723 467943009348074863720085)
              ·
                refine ⟨21934828563191009236879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 467943009348074863720085 21934828563191009236879)
                ·
                  rfl

theorem cell20_144173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 6].length) (baseStart_144173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144173 prefixEnd_144173 := by exact prefixLift 144173
  have htrace : WordTrace (prefixWord ++ tailWord_144173) baseStart_144173 baseEnd_144173 := by
    simpa [prefixWord, tailWord_144173, baseEnd_144173] using wordTrace_append hprefix tailTrace_144173
  have hstable : (prefixWord ++ tailWord_144173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144173).length < 2 ^ (prefixWord ++ tailWord_144173).sum := by decide
  have hdescent : baseEnd_144173 < baseStart_144173 := by decide
  rcases family_descends (prefixWord ++ tailWord_144173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144204 : List Nat := [2, 2, 1, 3, 3, 2, 3, 2, 2]
def baseStart_144204 : Nat := 118140960795 + 144204 * 2 ^ 59
def prefixEnd_144204 : Nat := 4983230072969 + 3 ^ 40 * 144204 * 2
def baseEnd_144204 : Nat := 65818634934274697677177

theorem tailTrace_144204 : CollatzResearch.WordTrace tailWord_144204 prefixEnd_144204 65818634934274697677177 := by
  unfold tailWord_144204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629775984790505463783833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3506367979720673951711777 2629775984790505463783833)
  ·
    refine ⟨1972331988592879097837875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2629775984790505463783833 1972331988592879097837875)
    ·
      refine ⟨2958497982889318646756813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1972331988592879097837875 2958497982889318646756813)
      ·
        refine ⟨1109436743583494492533805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2958497982889318646756813 1109436743583494492533805)
        ·
          refine ⟨416038778843810434700177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1109436743583494492533805 416038778843810434700177)
          ·
            refine ⟨312029084132857826025133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416038778843810434700177 312029084132857826025133)
            ·
              refine ⟨117010906549821684759425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 312029084132857826025133 117010906549821684759425)
              ·
                refine ⟨87758179912366263569569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117010906549821684759425 87758179912366263569569)
                ·
                  refine ⟨65818634934274697677177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87758179912366263569569 65818634934274697677177)
                  ·
                    rfl

theorem cell20_144204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_144204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144204 prefixEnd_144204 := by exact prefixLift 144204
  have htrace : WordTrace (prefixWord ++ tailWord_144204) baseStart_144204 baseEnd_144204 := by
    simpa [prefixWord, tailWord_144204, baseEnd_144204] using wordTrace_append hprefix tailTrace_144204
  have hstable : (prefixWord ++ tailWord_144204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144204).length < 2 ^ (prefixWord ++ tailWord_144204).sum := by decide
  have hdescent : baseEnd_144204 < baseStart_144204 := by decide
  rcases family_descends (prefixWord ++ tailWord_144204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144208 : List Nat := [2, 1, 1, 1, 1, 4, 2, 6, 2]
def baseStart_144208 : Nat := 118140960795 + 144208 * 2 ^ 59
def prefixEnd_144208 : Nat := 4983230072969 + 3 ^ 40 * 144208 * 2
def baseEnd_144208 : Nat := 65820460643268461543827

theorem tailTrace_144208 : CollatzResearch.WordTrace tailWord_144208 prefixEnd_144208 65820460643268461543827 := by
  unfold tailWord_144208
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629848930783259805356639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3506465241044346407142185 2629848930783259805356639)
  ·
    refine ⟨3944773396174889708034959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2629848930783259805356639 3944773396174889708034959)
    ·
      refine ⟨5917160094262334562052439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3944773396174889708034959 5917160094262334562052439)
      ·
        refine ⟨8875740141393501843078659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5917160094262334562052439 8875740141393501843078659)
        ·
          refine ⟨13313610212090252764617989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8875740141393501843078659 13313610212090252764617989)
          ·
            refine ⟨2496301914766922393365873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13313610212090252764617989 2496301914766922393365873)
            ·
              refine ⟨1872226436075191795024405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496301914766922393365873 1872226436075191795024405)
              ·
                refine ⟨87760614191024615391769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1872226436075191795024405 87760614191024615391769)
                ·
                  refine ⟨65820460643268461543827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87760614191024615391769 65820460643268461543827)
                  ·
                    rfl

theorem cell20_144208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_144208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144208 prefixEnd_144208 := by exact prefixLift 144208
  have htrace : WordTrace (prefixWord ++ tailWord_144208) baseStart_144208 baseEnd_144208 := by
    simpa [prefixWord, tailWord_144208, baseEnd_144208] using wordTrace_append hprefix tailTrace_144208
  have hstable : (prefixWord ++ tailWord_144208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144208).length < 2 ^ (prefixWord ++ tailWord_144208).sum := by decide
  have hdescent : baseEnd_144208 < baseStart_144208 := by decide
  rcases family_descends (prefixWord ++ tailWord_144208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144215 : List Nat := [1, 1, 3, 2, 4, 2, 2, 5]
def baseStart_144215 : Nat := 118140960795 + 144215 * 2 ^ 59
def prefixEnd_144215 : Nat := 4983230072969 + 3 ^ 40 * 144215 * 2
def baseEnd_144215 : Nat := 21941218544669182770155

theorem tailTrace_144215 : CollatzResearch.WordTrace tailWord_144215 prefixEnd_144215 21941218544669182770155 := by
  unfold tailWord_144215
  simp only [CollatzResearch.WordTrace]
  refine ⟨5259953172541159806218099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3506635448360773204145399 5259953172541159806218099)
  ·
    refine ⟨7889929758811739709327149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5259953172541159806218099 7889929758811739709327149)
    ·
      refine ⟨2958723659554402390997681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7889929758811739709327149 2958723659554402390997681)
      ·
        refine ⟨2219042744665801793248261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2958723659554402390997681 2219042744665801793248261)
        ·
          refine ⟨416070514624837836234049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2219042744665801793248261 416070514624837836234049)
          ·
            refine ⟨312052885968628377175537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416070514624837836234049 312052885968628377175537)
            ·
              refine ⟨234039664476471282881653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312052885968628377175537 234039664476471282881653)
              ·
                refine ⟨21941218544669182770155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234039664476471282881653 21941218544669182770155)
                ·
                  rfl

theorem cell20_144215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_144215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144215 prefixEnd_144215 := by exact prefixLift 144215
  have htrace : WordTrace (prefixWord ++ tailWord_144215) baseStart_144215 baseEnd_144215 := by
    simpa [prefixWord, tailWord_144215, baseEnd_144215] using wordTrace_append hprefix tailTrace_144215
  have hstable : (prefixWord ++ tailWord_144215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144215).length < 2 ^ (prefixWord ++ tailWord_144215).sum := by decide
  have hdescent : baseEnd_144215 < baseStart_144215 := by decide
  rcases family_descends (prefixWord ++ tailWord_144215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144218 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_144218 : Nat := 118140960795 + 144218 * 2 ^ 59
def prefixEnd_144218 : Nat := 4983230072969 + 3 ^ 40 * 144218 * 2
def baseEnd_144218 : Nat := 65825024915752871210453

theorem tailTrace_144218 : CollatzResearch.WordTrace tailWord_144218 prefixEnd_144218 65825024915752871210453 := by
  unfold tailWord_144218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315015647882572829644327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3506708394353527545718205 1315015647882572829644327)
  ·
    refine ⟨1972523471823859244466491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1315015647882572829644327 1972523471823859244466491)
    ·
      refine ⟨2958785207735788866699737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1972523471823859244466491 2958785207735788866699737)
      ·
        refine ⟨2219088905801841650024803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2958785207735788866699737 2219088905801841650024803)
        ·
          refine ⟨3328633358702762475037205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219088905801841650024803 3328633358702762475037205)
          ·
            refine ⟨156029688689191991017369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3328633358702762475037205 156029688689191991017369)
            ·
              refine ⟨117022266516893993263027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156029688689191991017369 117022266516893993263027)
              ·
                refine ⟨175533399775340989894541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117022266516893993263027 175533399775340989894541)
                ·
                  refine ⟨65825024915752871210453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175533399775340989894541 65825024915752871210453)
                  ·
                    rfl

theorem cell20_144218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_144218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144218 prefixEnd_144218 := by exact prefixLift 144218
  have htrace : WordTrace (prefixWord ++ tailWord_144218) baseStart_144218 baseEnd_144218 := by
    simpa [prefixWord, tailWord_144218, baseEnd_144218] using wordTrace_append hprefix tailTrace_144218
  have hstable : (prefixWord ++ tailWord_144218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144218).length < 2 ^ (prefixWord ++ tailWord_144218).sum := by decide
  have hdescent : baseEnd_144218 < baseStart_144218 := by decide
  rcases family_descends (prefixWord ++ tailWord_144218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144229 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_144229 : Nat := 118140960795 + 144229 * 2 ^ 59
def prefixEnd_144229 : Nat := 4983230072969 + 3 ^ 40 * 144229 * 2
def baseEnd_144229 : Nat := 65830045615485721843741

theorem tailTrace_144229 : CollatzResearch.WordTrace tailWord_144229 prefixEnd_144229 65830045615485721843741 := by
  unfold tailWord_144229
  simp only [CollatzResearch.WordTrace]
  refine ⟨5260463794490440197227741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3506975862993626798151827 5260463794490440197227741)
  ·
    refine ⟨1972673922933915073960403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5260463794490440197227741 1972673922933915073960403)
    ·
      refine ⟨2959010884400872610940605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1972673922933915073960403 2959010884400872610940605)
      ·
        refine ⟨1109629081650327229102727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2959010884400872610940605 1109629081650327229102727)
        ·
          refine ⟨1664443622475490843654091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109629081650327229102727 1664443622475490843654091)
          ·
            refine ⟨2496665433713236265481137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664443622475490843654091 2496665433713236265481137)
            ·
              refine ⟨1872499075284927199110853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496665433713236265481137 1872499075284927199110853)
              ·
                refine ⟨351093576615923849833285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1872499075284927199110853 351093576615923849833285)
                ·
                  refine ⟨65830045615485721843741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351093576615923849833285 65830045615485721843741)
                  ·
                    rfl

theorem cell20_144229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_144229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144229 prefixEnd_144229 := by exact prefixLift 144229
  have htrace : WordTrace (prefixWord ++ tailWord_144229) baseStart_144229 baseEnd_144229 := by
    simpa [prefixWord, tailWord_144229, baseEnd_144229] using wordTrace_append hprefix tailTrace_144229
  have hstable : (prefixWord ++ tailWord_144229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144229).length < 2 ^ (prefixWord ++ tailWord_144229).sum := by decide
  have hdescent : baseEnd_144229 < baseStart_144229 := by decide
  rcases family_descends (prefixWord ++ tailWord_144229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144236 : List Nat := [2, 2, 1, 1, 4, 1, 1, 8]
def baseStart_144236 : Nat := 118140960795 + 144236 * 2 ^ 59
def prefixEnd_144236 : Nat := 4983230072969 + 3 ^ 40 * 144236 * 2
def baseEnd_144236 : Nat := 21944413535408269536793

theorem tailTrace_144236 : CollatzResearch.WordTrace tailWord_144236 prefixEnd_144236 21944413535408269536793 := by
  unfold tailWord_144236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2630359552732540196366281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3507146070310053595155041 2630359552732540196366281)
  ·
    refine ⟨1972769664549405147274711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2630359552732540196366281 1972769664549405147274711)
    ·
      refine ⟨2959154496824107720912067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1972769664549405147274711 2959154496824107720912067)
      ·
        refine ⟨4438731745236161581368101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2959154496824107720912067 4438731745236161581368101)
        ·
          refine ⟨832262202231780296506519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4438731745236161581368101 832262202231780296506519)
          ·
            refine ⟨1248393303347670444759779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832262202231780296506519 1248393303347670444759779)
            ·
              refine ⟨1872589955021505667139669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248393303347670444759779 1872589955021505667139669)
              ·
                refine ⟨21944413535408269536793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1872589955021505667139669 21944413535408269536793)
                ·
                  rfl

theorem cell20_144236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_144236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144236 prefixEnd_144236 := by exact prefixLift 144236
  have htrace : WordTrace (prefixWord ++ tailWord_144236) baseStart_144236 baseEnd_144236 := by
    simpa [prefixWord, tailWord_144236, baseEnd_144236] using wordTrace_append hprefix tailTrace_144236
  have hstable : (prefixWord ++ tailWord_144236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144236).length < 2 ^ (prefixWord ++ tailWord_144236).sum := by decide
  have hdescent : baseEnd_144236 < baseStart_144236 := by decide
  rcases family_descends (prefixWord ++ tailWord_144236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144243 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_144243 : Nat := 118140960795 + 144243 * 2 ^ 59
def prefixEnd_144243 : Nat := 4983230072969 + 3 ^ 40 * 144243 * 2
def baseEnd_144243 : Nat := 65836435596963895377017

theorem tailTrace_144243 : CollatzResearch.WordTrace tailWord_144243 prefixEnd_144243 65836435596963895377017 := by
  unfold tailWord_144243
  simp only [CollatzResearch.WordTrace]
  refine ⟨5260974416439720588237383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3507316277626480392158255 5260974416439720588237383)
  ·
    refine ⟨7891461624659580882356075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5260974416439720588237383 7891461624659580882356075)
    ·
      refine ⟨11837192436989371323534113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7891461624659580882356075 11837192436989371323534113)
      ·
        refine ⟨8877894327742028492650585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11837192436989371323534113 8877894327742028492650585)
        ·
          refine ⟨6658420745806521369487939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8877894327742028492650585 6658420745806521369487939)
          ·
            refine ⟨9987631118709782054231909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6658420745806521369487939 9987631118709782054231909)
            ·
              refine ⟨1872680834758084135168483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9987631118709782054231909 1872680834758084135168483)
              ·
                refine ⟨2809021252137126202752725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872680834758084135168483 2809021252137126202752725)
                ·
                  refine ⟨65836435596963895377017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2809021252137126202752725 65836435596963895377017)
                  ·
                    rfl

theorem cell20_144243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_144243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144243 prefixEnd_144243 := by exact prefixLift 144243
  have htrace : WordTrace (prefixWord ++ tailWord_144243) baseStart_144243 baseEnd_144243 := by
    simpa [prefixWord, tailWord_144243, baseEnd_144243] using wordTrace_append hprefix tailTrace_144243
  have hstable : (prefixWord ++ tailWord_144243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144243).length < 2 ^ (prefixWord ++ tailWord_144243).sum := by decide
  have hdescent : baseEnd_144243 < baseStart_144243 := by decide
  rcases family_descends (prefixWord ++ tailWord_144243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144263 : List Nat := [1, 1, 4, 2, 3, 2, 1, 4, 2]
def baseStart_144263 : Nat := 118140960795 + 144263 * 2 ^ 59
def prefixEnd_144263 : Nat := 4983230072969 + 3 ^ 40 * 144263 * 2
def baseEnd_144263 : Nat := 65845564141932714710269

theorem tailTrace_144263 : CollatzResearch.WordTrace tailWord_144263 prefixEnd_144263 65845564141932714710269 := by
  unfold tailWord_144263
  simp only [CollatzResearch.WordTrace]
  refine ⟨5261703876367264003965443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3507802584244842669310295 5261703876367264003965443)
  ·
    refine ⟨7892555814550896005948165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5261703876367264003965443 7892555814550896005948165)
    ·
      refine ⟨1479854215228293001115281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7892555814550896005948165 1479854215228293001115281)
      ·
        refine ⟨1109890661421219750836461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479854215228293001115281 1109890661421219750836461)
        ·
          refine ⟨416208998032957406563673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1109890661421219750836461 416208998032957406563673)
          ·
            refine ⟨312156748524718054922755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416208998032957406563673 312156748524718054922755)
            ·
              refine ⟨468235122787077082384133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312156748524718054922755 468235122787077082384133)
              ·
                refine ⟨87794085522576952947025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 468235122787077082384133 87794085522576952947025)
                ·
                  refine ⟨65845564141932714710269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87794085522576952947025 65845564141932714710269)
                  ·
                    rfl

theorem cell20_144263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 2].length) (baseStart_144263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144263 prefixEnd_144263 := by exact prefixLift 144263
  have htrace : WordTrace (prefixWord ++ tailWord_144263) baseStart_144263 baseEnd_144263 := by
    simpa [prefixWord, tailWord_144263, baseEnd_144263] using wordTrace_append hprefix tailTrace_144263
  have hstable : (prefixWord ++ tailWord_144263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144263).length < 2 ^ (prefixWord ++ tailWord_144263).sum := by decide
  have hdescent : baseEnd_144263 < baseStart_144263 := by decide
  rcases family_descends (prefixWord ++ tailWord_144263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144281 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_144281 : Nat := 118140960795 + 144281 * 2 ^ 59
def prefixEnd_144281 : Nat := 4983230072969 + 3 ^ 40 * 144281 * 2
def baseEnd_144281 : Nat := 65853779832404652110195

theorem tailTrace_144281 : CollatzResearch.WordTrace tailWord_144281 prefixEnd_144281 65853779832404652110195 := by
  unfold tailWord_144281
  simp only [CollatzResearch.WordTrace]
  refine ⟨5262360390302053078120697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3508240260201368718747131 5262360390302053078120697)
  ·
    refine ⟨3946770292726539808590523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5262360390302053078120697 3946770292726539808590523)
    ·
      refine ⟨5920155439089809712885785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3946770292726539808590523 5920155439089809712885785)
      ·
        refine ⟨4440116579317357284664339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5920155439089809712885785 4440116579317357284664339)
        ·
          refine ⟨6660174868976035926996509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4440116579317357284664339 6660174868976035926996509)
          ·
            refine ⟨2497565575866013472623691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6660174868976035926996509 2497565575866013472623691)
            ·
              refine ⟨3746348363799020208935537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497565575866013472623691 3746348363799020208935537)
              ·
                refine ⟨2809761272849265156701653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3746348363799020208935537 2809761272849265156701653)
                ·
                  refine ⟨65853779832404652110195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2809761272849265156701653 65853779832404652110195)
                  ·
                    rfl

theorem cell20_144281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_144281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144281 prefixEnd_144281 := by exact prefixLift 144281
  have htrace : WordTrace (prefixWord ++ tailWord_144281) baseStart_144281 baseEnd_144281 := by
    simpa [prefixWord, tailWord_144281, baseEnd_144281] using wordTrace_append hprefix tailTrace_144281
  have hstable : (prefixWord ++ tailWord_144281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144281).length < 2 ^ (prefixWord ++ tailWord_144281).sum := by decide
  have hdescent : baseEnd_144281 < baseStart_144281 := by decide
  rcases family_descends (prefixWord ++ tailWord_144281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144308 : List Nat := [2, 5, 2, 1, 1, 2, 7]
def baseStart_144308 : Nat := 118140960795 + 144308 * 2 ^ 59
def prefixEnd_144308 : Nat := 4983230072969 + 3 ^ 40 * 144308 * 2
def baseEnd_144308 : Nat := 7318455929790284245565

theorem tailTrace_144308 : CollatzResearch.WordTrace tailWord_144308 prefixEnd_144308 7318455929790284245565 := by
  unfold tailWord_144308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2631672580602118344676789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3508896774136157792902385 2631672580602118344676789)
  ·
    refine ⟨246719304431448594813449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2631672580602118344676789 246719304431448594813449)
    ·
      refine ⟨185039478323586446110087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246719304431448594813449 185039478323586446110087)
      ·
        refine ⟨277559217485379669165131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185039478323586446110087 277559217485379669165131)
        ·
          refine ⟨416338826228069503747697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277559217485379669165131 416338826228069503747697)
          ·
            refine ⟨312254119671052127810773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416338826228069503747697 312254119671052127810773)
            ·
              refine ⟨7318455929790284245565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 312254119671052127810773 7318455929790284245565)
              ·
                rfl

theorem cell20_144308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 7].length) (baseStart_144308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144308 prefixEnd_144308 := by exact prefixLift 144308
  have htrace : WordTrace (prefixWord ++ tailWord_144308) baseStart_144308 baseEnd_144308 := by
    simpa [prefixWord, tailWord_144308, baseEnd_144308] using wordTrace_append hprefix tailTrace_144308
  have hstable : (prefixWord ++ tailWord_144308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144308).length < 2 ^ (prefixWord ++ tailWord_144308).sum := by decide
  have hdescent : baseEnd_144308 < baseStart_144308 := by decide
  rcases family_descends (prefixWord ++ tailWord_144308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144312 : List Nat := [2, 1, 2, 1, 2, 5, 7]
def baseStart_144312 : Nat := 118140960795 + 144312 * 2 ^ 59
def prefixEnd_144312 : Nat := 4983230072969 + 3 ^ 40 * 144312 * 2
def baseEnd_144312 : Nat := 7318658786345146897415

theorem tailTrace_144312 : CollatzResearch.WordTrace tailWord_144312 prefixEnd_144312 7318658786345146897415 := by
  unfold tailWord_144312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2631745526594872686249595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3508994035459830248332793 2631745526594872686249595)
  ·
    refine ⟨3947618289892309029374393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2631745526594872686249595 3947618289892309029374393)
    ·
      refine ⟨2960713717419231772030795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3947618289892309029374393 2960713717419231772030795)
      ·
        refine ⟨4441070576128847658046193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960713717419231772030795 4441070576128847658046193)
        ·
          refine ⟨3330802932096635743534645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4441070576128847658046193 3330802932096635743534645)
          ·
            refine ⟨312262774884059600956373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3330802932096635743534645 312262774884059600956373)
            ·
              refine ⟨7318658786345146897415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 312262774884059600956373 7318658786345146897415)
              ·
                rfl

theorem cell20_144312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 7].length) (baseStart_144312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144312 prefixEnd_144312 := by exact prefixLift 144312
  have htrace : WordTrace (prefixWord ++ tailWord_144312) baseStart_144312 baseEnd_144312 := by
    simpa [prefixWord, tailWord_144312, baseEnd_144312] using wordTrace_append hprefix tailTrace_144312
  have hstable : (prefixWord ++ tailWord_144312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144312).length < 2 ^ (prefixWord ++ tailWord_144312).sum := by decide
  have hdescent : baseEnd_144312 < baseStart_144312 := by decide
  rcases family_descends (prefixWord ++ tailWord_144312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144346 : List Nat := [3, 1, 1, 2, 4, 3, 2, 4]
def baseStart_144346 : Nat := 118140960795 + 144346 * 2 ^ 59
def prefixEnd_144346 : Nat := 4983230072969 + 3 ^ 40 * 144346 * 2
def baseEnd_144346 : Nat := 21961149201184438314421

theorem tailTrace_144346 : CollatzResearch.WordTrace tailWord_144346 prefixEnd_144346 21961149201184438314421 := by
  unfold tailWord_144346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316182783766642294809223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3509820756711046119491261 1316182783766642294809223)
  ·
    refine ⟨1974274175649963442213835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316182783766642294809223 1974274175649963442213835)
    ·
      refine ⟨2961411263474945163320753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1974274175649963442213835 2961411263474945163320753)
      ·
        refine ⟨2221058447606208872490565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2961411263474945163320753 2221058447606208872490565)
        ·
          refine ⟨416448458926164163591981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2221058447606208872490565 416448458926164163591981)
          ·
            refine ⟨156168172097311561346993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 416448458926164163591981 156168172097311561346993)
            ·
              refine ⟨117126129072983671010245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156168172097311561346993 117126129072983671010245)
              ·
                refine ⟨21961149201184438314421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117126129072983671010245 21961149201184438314421)
                ·
                  rfl

theorem cell20_144346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_144346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144346 prefixEnd_144346 := by exact prefixLift 144346
  have htrace : WordTrace (prefixWord ++ tailWord_144346) baseStart_144346 baseEnd_144346 := by
    simpa [prefixWord, tailWord_144346, baseEnd_144346] using wordTrace_append hprefix tailTrace_144346
  have hstable : (prefixWord ++ tailWord_144346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144346).length < 2 ^ (prefixWord ++ tailWord_144346).sum := by decide
  have hdescent : baseEnd_144346 < baseStart_144346 := by decide
  rcases family_descends (prefixWord ++ tailWord_144346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144373 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 4]
def baseStart_144373 : Nat := 118140960795 + 144373 * 2 ^ 59
def prefixEnd_144373 : Nat := 4983230072969 + 3 ^ 40 * 144373 * 2
def baseEnd_144373 : Nat := 65895771139261221043153

theorem tailTrace_144373 : CollatzResearch.WordTrace tailWord_144373 prefixEnd_144373 65895771139261221043153 := by
  unfold tailWord_144373
  simp only [CollatzResearch.WordTrace]
  refine ⟨5265715905968752790469773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3510477270645835193646515 5265715905968752790469773)
  ·
    refine ⟨1974643464738282296426165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5265715905968752790469773 1974643464738282296426165)
    ·
      refine ⟨185122824819213965289953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1974643464738282296426165 185122824819213965289953)
      ·
        refine ⟨138842118614410473967465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185122824819213965289953 138842118614410473967465)
        ·
          refine ⟨104131588960807855475599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138842118614410473967465 104131588960807855475599)
          ·
            refine ⟨156197383441211783213399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104131588960807855475599 156197383441211783213399)
            ·
              refine ⟨234296075161817674820099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156197383441211783213399 234296075161817674820099)
              ·
                refine ⟨351444112742726512230149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234296075161817674820099 351444112742726512230149)
                ·
                  refine ⟨65895771139261221043153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351444112742726512230149 65895771139261221043153)
                  ·
                    rfl

theorem cell20_144373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_144373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144373 prefixEnd_144373 := by exact prefixLift 144373
  have htrace : WordTrace (prefixWord ++ tailWord_144373) baseStart_144373 baseEnd_144373 := by
    simpa [prefixWord, tailWord_144373, baseEnd_144373] using wordTrace_append hprefix tailTrace_144373
  have hstable : (prefixWord ++ tailWord_144373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144373).length < 2 ^ (prefixWord ++ tailWord_144373).sum := by decide
  have hdescent : baseEnd_144373 < baseStart_144373 := by decide
  rcases family_descends (prefixWord ++ tailWord_144373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144377 : List Nat := [1, 2, 1, 3, 1, 3, 5, 2, 2]
def baseStart_144377 : Nat := 118140960795 + 144377 * 2 ^ 59
def prefixEnd_144377 : Nat := 4983230072969 + 3 ^ 40 * 144377 * 2
def baseEnd_144377 : Nat := 65897596848254984909803

theorem tailTrace_144377 : CollatzResearch.WordTrace tailWord_144377 prefixEnd_144377 65897596848254984909803 := by
  unfold tailWord_144377
  simp only [CollatzResearch.WordTrace]
  refine ⟨5265861797954261473615385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3510574531969507649076923 5265861797954261473615385)
  ·
    refine ⟨3949396348465696105211539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5265861797954261473615385 3949396348465696105211539)
    ·
      refine ⟨5924094522698544157817309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3949396348465696105211539 5924094522698544157817309)
      ·
        refine ⟨2221535446011954059181491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5924094522698544157817309 2221535446011954059181491)
        ·
          refine ⟨3332303169017931088772237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221535446011954059181491 3332303169017931088772237)
          ·
            refine ⟨1249613688381724158289589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3332303169017931088772237 1249613688381724158289589)
            ·
              refine ⟨117151283285786639839649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1249613688381724158289589 117151283285786639839649)
              ·
                refine ⟨87863462464339979879737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117151283285786639839649 87863462464339979879737)
                ·
                  refine ⟨65897596848254984909803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87863462464339979879737 65897596848254984909803)
                  ·
                    rfl

theorem cell20_144377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_144377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144377 prefixEnd_144377 := by exact prefixLift 144377
  have htrace : WordTrace (prefixWord ++ tailWord_144377) baseStart_144377 baseEnd_144377 := by
    simpa [prefixWord, tailWord_144377, baseEnd_144377] using wordTrace_append hprefix tailTrace_144377
  have hstable : (prefixWord ++ tailWord_144377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144377).length < 2 ^ (prefixWord ++ tailWord_144377).sum := by decide
  have hdescent : baseEnd_144377 < baseStart_144377 := by decide
  rcases family_descends (prefixWord ++ tailWord_144377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144426 : List Nat := [3, 1, 4, 1, 11]
def baseStart_144426 : Nat := 118140960795 + 144426 * 2 ^ 59
def prefixEnd_144426 : Nat := 4983230072969 + 3 ^ 40 * 144426 * 2
def baseEnd_144426 : Nat := 813826688684303608349

theorem tailTrace_144426 : CollatzResearch.WordTrace tailWord_144426 prefixEnd_144426 813826688684303608349 := by
  unfold tailWord_144426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316912243694185710537283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3511765983184495228099421 1316912243694185710537283)
  ·
    refine ⟨1975368365541278565805925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316912243694185710537283 1975368365541278565805925)
    ·
      refine ⟨370381568538989731088611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1975368365541278565805925 370381568538989731088611)
      ·
        refine ⟨555572352808484596632917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370381568538989731088611 555572352808484596632917)
        ·
          refine ⟨813826688684303608349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 555572352808484596632917 813826688684303608349)
          ·
            rfl

theorem cell20_144426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 11].length) (baseStart_144426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144426 prefixEnd_144426 := by exact prefixLift 144426
  have htrace : WordTrace (prefixWord ++ tailWord_144426) baseStart_144426 baseEnd_144426 := by
    simpa [prefixWord, tailWord_144426, baseEnd_144426] using wordTrace_append hprefix tailTrace_144426
  have hstable : (prefixWord ++ tailWord_144426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144426).length < 2 ^ (prefixWord ++ tailWord_144426).sum := by decide
  have hdescent : baseEnd_144426 < baseStart_144426 := by decide
  rcases family_descends (prefixWord ++ tailWord_144426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144471 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_144471 : Nat := 118140960795 + 144471 * 2 ^ 59
def prefixEnd_144471 : Nat := 4983230072969 + 3 ^ 40 * 144471 * 2
def baseEnd_144471 : Nat := 65940501009608435776085

theorem tailTrace_144471 : CollatzResearch.WordTrace tailWord_144471 prefixEnd_144471 65940501009608435776085 := by
  unfold tailWord_144471
  simp only [CollatzResearch.WordTrace]
  refine ⟨5269290259613715527537267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3512860173075810351691511 5269290259613715527537267)
  ·
    refine ⟨7903935389420573291305901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5269290259613715527537267 7903935389420573291305901)
    ·
      refine ⟨2963975771032714984239713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7903935389420573291305901 2963975771032714984239713)
      ·
        refine ⟨2222981828274536238179785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2963975771032714984239713 2222981828274536238179785)
        ·
          refine ⟨1667236371205902178634839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2222981828274536238179785 1667236371205902178634839)
          ·
            refine ⟨2500854556808853267952259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667236371205902178634839 2500854556808853267952259)
            ·
              refine ⟨3751281835213279901928389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500854556808853267952259 3751281835213279901928389)
              ·
                refine ⟨703365344102489981611573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3751281835213279901928389 703365344102489981611573)
                ·
                  refine ⟨65940501009608435776085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 703365344102489981611573 65940501009608435776085)
                  ·
                    rfl

theorem cell20_144471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_144471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144471 prefixEnd_144471 := by exact prefixLift 144471
  have htrace : WordTrace (prefixWord ++ tailWord_144471) baseStart_144471 baseEnd_144471 := by
    simpa [prefixWord, tailWord_144471, baseEnd_144471] using wordTrace_append hprefix tailTrace_144471
  have hstable : (prefixWord ++ tailWord_144471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144471).length < 2 ^ (prefixWord ++ tailWord_144471).sum := by decide
  have hdescent : baseEnd_144471 < baseStart_144471 := by decide
  rcases family_descends (prefixWord ++ tailWord_144471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144495 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 4]
def baseStart_144495 : Nat := 118140960795 + 144495 * 2 ^ 59
def prefixEnd_144495 : Nat := 4983230072969 + 3 ^ 40 * 144495 * 2
def baseEnd_144495 : Nat := 65951455263571018975987

theorem tailTrace_144495 : CollatzResearch.WordTrace tailWord_144495 prefixEnd_144495 65951455263571018975987 := by
  unfold tailWord_144495
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270165611526767626410939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3513443741017845084273959 5270165611526767626410939)
  ·
    refine ⟨7905248417290151439616409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5270165611526767626410939 7905248417290151439616409)
    ·
      refine ⟨5928936312967613579712307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7905248417290151439616409 5928936312967613579712307)
      ·
        refine ⟨8893404469451420369568461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5928936312967613579712307 8893404469451420369568461)
        ·
          refine ⟨3335026676044282638588173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8893404469451420369568461 3335026676044282638588173)
          ·
            refine ⟨1250635003516605989470565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3335026676044282638588173 1250635003516605989470565)
            ·
              refine ⟨234494063159363623025731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1250635003516605989470565 234494063159363623025731)
              ·
                refine ⟨351741094739045434538597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234494063159363623025731 351741094739045434538597)
                ·
                  refine ⟨65951455263571018975987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351741094739045434538597 65951455263571018975987)
                  ·
                    rfl

theorem cell20_144495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_144495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144495 prefixEnd_144495 := by exact prefixLift 144495
  have htrace : WordTrace (prefixWord ++ tailWord_144495) baseStart_144495 baseEnd_144495 := by
    simpa [prefixWord, tailWord_144495, baseEnd_144495] using wordTrace_append hprefix tailTrace_144495
  have hstable : (prefixWord ++ tailWord_144495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144495).length < 2 ^ (prefixWord ++ tailWord_144495).sum := by decide
  have hdescent : baseEnd_144495 < baseStart_144495 := by decide
  rcases family_descends (prefixWord ++ tailWord_144495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144501 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 3]
def baseStart_144501 : Nat := 118140960795 + 144501 * 2 ^ 59
def prefixEnd_144501 : Nat := 4983230072969 + 3 ^ 40 * 144501 * 2
def baseEnd_144501 : Nat := 65954193827061664775963

theorem tailTrace_144501 : CollatzResearch.WordTrace tailWord_144501 prefixEnd_144501 65954193827061664775963 := by
  unfold tailWord_144501
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270384449505030651129357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3513589633003353767419571 5270384449505030651129357)
  ·
    refine ⟨1976394168564386494173509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5270384449505030651129357 1976394168564386494173509)
    ·
      refine ⟨370573906605822467657533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1976394168564386494173509 370573906605822467657533)
      ·
        refine ⟨138965214977183425371575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 370573906605822467657533 138965214977183425371575)
        ·
          refine ⟨208447822465775138057363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138965214977183425371575 208447822465775138057363)
          ·
            refine ⟨312671733698662707086045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208447822465775138057363 312671733698662707086045)
            ·
              refine ⟨117251900136998515157267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 312671733698662707086045 117251900136998515157267)
              ·
                refine ⟨175877850205497772735901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117251900136998515157267 175877850205497772735901)
                ·
                  refine ⟨65954193827061664775963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175877850205497772735901 65954193827061664775963)
                  ·
                    rfl

theorem cell20_144501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_144501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144501 prefixEnd_144501 := by exact prefixLift 144501
  have htrace : WordTrace (prefixWord ++ tailWord_144501) baseStart_144501 baseEnd_144501 := by
    simpa [prefixWord, tailWord_144501, baseEnd_144501] using wordTrace_append hprefix tailTrace_144501
  have hstable : (prefixWord ++ tailWord_144501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144501).length < 2 ^ (prefixWord ++ tailWord_144501).sum := by decide
  have hdescent : baseEnd_144501 < baseStart_144501 := by decide
  rcases family_descends (prefixWord ++ tailWord_144501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144526 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_144526 : Nat := 118140960795 + 144526 * 2 ^ 59
def prefixEnd_144526 : Nat := 4983230072969 + 3 ^ 40 * 144526 * 2
def baseEnd_144526 : Nat := 65965604508272688942527

theorem tailTrace_144526 : CollatzResearch.WordTrace tailWord_144526 prefixEnd_144526 65965604508272688942527 := by
  unfold tailWord_144526
  simp only [CollatzResearch.WordTrace]
  refine ⟨658912034301807490098679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3514197516276306613859621 658912034301807490098679)
  ·
    refine ⟨988368051452711235148019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 658912034301807490098679 988368051452711235148019)
    ·
      refine ⟨1482552077179066852722029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988368051452711235148019 1482552077179066852722029)
      ·
        refine ⟨555957028942150069770761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1482552077179066852722029 555957028942150069770761)
        ·
          refine ⟨416967771706612552328071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555957028942150069770761 416967771706612552328071)
          ·
            refine ⟨625451657559918828492107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416967771706612552328071 625451657559918828492107)
            ·
              refine ⟨938177486339878242738161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625451657559918828492107 938177486339878242738161)
              ·
                refine ⟨703633114754908682053621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938177486339878242738161 703633114754908682053621)
                ·
                  refine ⟨65965604508272688942527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 703633114754908682053621 65965604508272688942527)
                  ·
                    rfl

theorem cell20_144526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_144526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144526 prefixEnd_144526 := by exact prefixLift 144526
  have htrace : WordTrace (prefixWord ++ tailWord_144526) baseStart_144526 baseEnd_144526 := by
    simpa [prefixWord, tailWord_144526, baseEnd_144526] using wordTrace_append hprefix tailTrace_144526
  have hstable : (prefixWord ++ tailWord_144526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144526).length < 2 ^ (prefixWord ++ tailWord_144526).sum := by decide
  have hdescent : baseEnd_144526 < baseStart_144526 := by decide
  rcases family_descends (prefixWord ++ tailWord_144526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144540 : List Nat := [2, 2, 3, 2, 1, 2, 8]
def baseStart_144540 : Nat := 118140960795 + 144540 * 2 ^ 59
def prefixEnd_144540 : Nat := 4983230072969 + 3 ^ 40 * 144540 * 2
def baseEnd_144540 : Nat := 7330221609972318052867

theorem tailTrace_144540 : CollatzResearch.WordTrace tailWord_144540 prefixEnd_144540 7330221609972318052867 := by
  unfold tailWord_144540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635903448181870155899537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3514537930909160207866049 2635903448181870155899537)
  ·
    refine ⟨1976927586136402616924653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2635903448181870155899537 1976927586136402616924653)
    ·
      refine ⟨741347844801150981346745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1976927586136402616924653 741347844801150981346745)
      ·
        refine ⟨556010883600863236010059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 741347844801150981346745 556010883600863236010059)
        ·
          refine ⟨834016325401294854015089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556010883600863236010059 834016325401294854015089)
          ·
            refine ⟨625512244050971140511317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834016325401294854015089 625512244050971140511317)
            ·
              refine ⟨7330221609972318052867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 625512244050971140511317 7330221609972318052867)
              ·
                rfl

theorem cell20_144540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 8].length) (baseStart_144540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144540 prefixEnd_144540 := by exact prefixLift 144540
  have htrace : WordTrace (prefixWord ++ tailWord_144540) baseStart_144540 baseEnd_144540 := by
    simpa [prefixWord, tailWord_144540, baseEnd_144540] using wordTrace_append hprefix tailTrace_144540
  have hstable : (prefixWord ++ tailWord_144540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144540).length < 2 ^ (prefixWord ++ tailWord_144540).sum := by decide
  have hdescent : baseEnd_144540 < baseStart_144540 := by decide
  rcases family_descends (prefixWord ++ tailWord_144540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144546 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 4]
def baseStart_144546 : Nat := 118140960795 + 144546 * 2 ^ 59
def prefixEnd_144546 : Nat := 4983230072969 + 3 ^ 40 * 144546 * 2
def baseEnd_144546 : Nat := 65974733053241508275779

theorem tailTrace_144546 : CollatzResearch.WordTrace tailWord_144546 prefixEnd_144546 65974733053241508275779 := by
  unfold tailWord_144546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318006433585500834129373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3514683822894668891011661 1318006433585500834129373)
  ·
    refine ⟨494252412594562812798515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1318006433585500834129373 494252412594562812798515)
    ·
      refine ⟨741378618891844219197773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494252412594562812798515 741378618891844219197773)
      ·
        refine ⟨278016982084441582199165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 741378618891844219197773 278016982084441582199165)
        ·
          refine ⟨104256368281665593324687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278016982084441582199165 104256368281665593324687)
          ·
            refine ⟨156384552422498389987031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104256368281665593324687 156384552422498389987031)
            ·
              refine ⟨234576828633747584980547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156384552422498389987031 234576828633747584980547)
              ·
                refine ⟨351865242950621377470821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234576828633747584980547 351865242950621377470821)
                ·
                  refine ⟨65974733053241508275779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 351865242950621377470821 65974733053241508275779)
                  ·
                    rfl

theorem cell20_144546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_144546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144546 prefixEnd_144546 := by exact prefixLift 144546
  have htrace : WordTrace (prefixWord ++ tailWord_144546) baseStart_144546 baseEnd_144546 := by
    simpa [prefixWord, tailWord_144546, baseEnd_144546] using wordTrace_append hprefix tailTrace_144546
  have hstable : (prefixWord ++ tailWord_144546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144546).length < 2 ^ (prefixWord ++ tailWord_144546).sum := by decide
  have hdescent : baseEnd_144546 < baseStart_144546 := by decide
  rcases family_descends (prefixWord ++ tailWord_144546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144626 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_144626 : Nat := 118140960795 + 144626 * 2 ^ 59
def prefixEnd_144626 : Nat := 4983230072969 + 3 ^ 40 * 144626 * 2
def baseEnd_144626 : Nat := 66011247233116785608785

theorem tailTrace_144626 : CollatzResearch.WordTrace tailWord_144626 prefixEnd_144626 66011247233116785608785 := by
  unfold tailWord_144626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318735893513044249857433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3516629049368117999619821 1318735893513044249857433)
  ·
    refine ⟨989051920134783187393075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1318735893513044249857433 989051920134783187393075)
    ·
      refine ⟨1483577880202174781089613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989051920134783187393075 1483577880202174781089613)
      ·
        refine ⟨556341705075815542908605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1483577880202174781089613 556341705075815542908605)
        ·
          refine ⟨208628139403430828590727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 556341705075815542908605 208628139403430828590727)
          ·
            refine ⟨312942209105146242886091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208628139403430828590727 312942209105146242886091)
            ·
              refine ⟨469413313657719364329137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312942209105146242886091 469413313657719364329137)
              ·
                refine ⟨352059985243289523246853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469413313657719364329137 352059985243289523246853)
                ·
                  refine ⟨66011247233116785608785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352059985243289523246853 66011247233116785608785)
                  ·
                    rfl

theorem cell20_144626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_144626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144626 prefixEnd_144626 := by exact prefixLift 144626
  have htrace : WordTrace (prefixWord ++ tailWord_144626) baseStart_144626 baseEnd_144626 := by
    simpa [prefixWord, tailWord_144626, baseEnd_144626] using wordTrace_append hprefix tailTrace_144626
  have hstable : (prefixWord ++ tailWord_144626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144626).length < 2 ^ (prefixWord ++ tailWord_144626).sum := by decide
  have hdescent : baseEnd_144626 < baseStart_144626 := by decide
  rcases family_descends (prefixWord ++ tailWord_144626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144654 : List Nat := [4, 1, 1, 2, 1, 4, 7]
def baseStart_144654 : Nat := 118140960795 + 144654 * 2 ^ 59
def prefixEnd_144654 : Nat := 4983230072969 + 3 ^ 40 * 144654 * 2
def baseEnd_144654 : Nat := 7336003021785903630593

theorem tailTrace_144654 : CollatzResearch.WordTrace tailWord_144654 prefixEnd_144654 7336003021785903630593 := by
  unfold tailWord_144654
  simp only [CollatzResearch.WordTrace]
  refine ⟨659495602243842222681127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3517309878633825187632677 659495602243842222681127)
  ·
    refine ⟨989243403365763334021691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 659495602243842222681127 989243403365763334021691)
    ·
      refine ⟨1483865105048645001032537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989243403365763334021691 1483865105048645001032537)
      ·
        refine ⟨1112898828786483750774403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1483865105048645001032537 1112898828786483750774403)
        ·
          refine ⟨1669348243179725626161605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112898828786483750774403 1669348243179725626161605)
          ·
            refine ⟨313002795596198554905301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1669348243179725626161605 313002795596198554905301)
            ·
              refine ⟨7336003021785903630593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 313002795596198554905301 7336003021785903630593)
              ·
                rfl

theorem cell20_144654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 7].length) (baseStart_144654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144654 prefixEnd_144654 := by exact prefixLift 144654
  have htrace : WordTrace (prefixWord ++ tailWord_144654) baseStart_144654 baseEnd_144654 := by
    simpa [prefixWord, tailWord_144654, baseEnd_144654] using wordTrace_append hprefix tailTrace_144654
  have hstable : (prefixWord ++ tailWord_144654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144654).length < 2 ^ (prefixWord ++ tailWord_144654).sum := by decide
  have hdescent : baseEnd_144654 < baseStart_144654 := by decide
  rcases family_descends (prefixWord ++ tailWord_144654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144664 : List Nat := [2, 1, 2, 3, 1, 3, 2, 4, 2]
def baseStart_144664 : Nat := 118140960795 + 144664 * 2 ^ 59
def prefixEnd_144664 : Nat := 4983230072969 + 3 ^ 40 * 144664 * 2
def baseEnd_144664 : Nat := 66028591468557542341963

theorem tailTrace_144664 : CollatzResearch.WordTrace tailWord_144664 prefixEnd_144664 66028591468557542341963 := by
  unfold tailWord_144664
  simp only [CollatzResearch.WordTrace]
  refine ⟨2638164773957254744656523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3517553031943006326208697 2638164773957254744656523)
  ·
    refine ⟨3957247160935882116984785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2638164773957254744656523 3957247160935882116984785)
    ·
      refine ⟨2967935370701911587738589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3957247160935882116984785 2967935370701911587738589)
      ·
        refine ⟨1112975764013216845401971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2967935370701911587738589 1112975764013216845401971)
        ·
          refine ⟨1669463646019825268102957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112975764013216845401971 1669463646019825268102957)
          ·
            refine ⟨626048867257434475538609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1669463646019825268102957 626048867257434475538609)
            ·
              refine ⟨469536650443075856653957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626048867257434475538609 469536650443075856653957)
              ·
                refine ⟨88038121958076723122617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469536650443075856653957 88038121958076723122617)
                ·
                  refine ⟨66028591468557542341963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88038121958076723122617 66028591468557542341963)
                  ·
                    rfl

theorem cell20_144664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_144664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144664 prefixEnd_144664 := by exact prefixLift 144664
  have htrace : WordTrace (prefixWord ++ tailWord_144664) baseStart_144664 baseEnd_144664 := by
    simpa [prefixWord, tailWord_144664, baseEnd_144664] using wordTrace_append hprefix tailTrace_144664
  have hstable : (prefixWord ++ tailWord_144664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144664).length < 2 ^ (prefixWord ++ tailWord_144664).sum := by decide
  have hdescent : baseEnd_144664 < baseStart_144664 := by decide
  rcases family_descends (prefixWord ++ tailWord_144664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144674 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_144674 : Nat := 118140960795 + 144674 * 2 ^ 59
def prefixEnd_144674 : Nat := 4983230072969 + 3 ^ 40 * 144674 * 2
def baseEnd_144674 : Nat := 66033155741041952008589

theorem tailTrace_144674 : CollatzResearch.WordTrace tailWord_144674 prefixEnd_144674 66033155741041952008589 := by
  unfold tailWord_144674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319173569469570299294269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3517796185252187464784717 1319173569469570299294269)
  ·
    refine ⟨494690088551088862235351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1319173569469570299294269 494690088551088862235351)
    ·
      refine ⟨742035132826633293353027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494690088551088862235351 742035132826633293353027)
      ·
        refine ⟨1113052699239949940029541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742035132826633293353027 1113052699239949940029541)
        ·
          refine ⟨208697381107490613755539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1113052699239949940029541 208697381107490613755539)
          ·
            refine ⟨313046071661235920633309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208697381107490613755539 313046071661235920633309)
            ·
              refine ⟨117392276872963470237491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 313046071661235920633309 117392276872963470237491)
              ·
                refine ⟨176088415309445205356237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117392276872963470237491 176088415309445205356237)
                ·
                  refine ⟨66033155741041952008589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176088415309445205356237 66033155741041952008589)
                  ·
                    rfl

theorem cell20_144674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_144674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144674 prefixEnd_144674 := by exact prefixLift 144674
  have htrace : WordTrace (prefixWord ++ tailWord_144674) baseStart_144674 baseEnd_144674 := by
    simpa [prefixWord, tailWord_144674, baseEnd_144674] using wordTrace_append hprefix tailTrace_144674
  have hstable : (prefixWord ++ tailWord_144674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144674).length < 2 ^ (prefixWord ++ tailWord_144674).sum := by decide
  have hdescent : baseEnd_144674 < baseStart_144674 := by decide
  rcases family_descends (prefixWord ++ tailWord_144674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144694 : List Nat := [5, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_144694 : Nat := 118140960795 + 144694 * 2 ^ 59
def prefixEnd_144694 : Nat := 4983230072969 + 3 ^ 40 * 144694 * 2
def baseEnd_144694 : Nat := 66042284286010771341841

theorem tailTrace_144694 : CollatzResearch.WordTrace tailWord_144694 prefixEnd_144694 66042284286010771341841 := by
  unfold tailWord_144694
  simp only [CollatzResearch.WordTrace]
  refine ⟨329838983612864038306571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3518282491870549741936757 329838983612864038306571)
  ·
    refine ⟨494758475419296057459857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 329838983612864038306571 494758475419296057459857)
    ·
      refine ⟨371068856564472043094893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 494758475419296057459857 371068856564472043094893)
      ·
        refine ⟨139150821211677016160585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371068856564472043094893 139150821211677016160585)
        ·
          refine ⟨104363115908757762120439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139150821211677016160585 104363115908757762120439)
          ·
            refine ⟨156544673863136643180659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104363115908757762120439 156544673863136643180659)
            ·
              refine ⟨234817010794704964770989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156544673863136643180659 234817010794704964770989)
              ·
                refine ⟨88056379048014361789121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234817010794704964770989 88056379048014361789121)
                ·
                  refine ⟨66042284286010771341841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88056379048014361789121 66042284286010771341841)
                  ·
                    rfl

theorem cell20_144694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_144694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144694 prefixEnd_144694 := by exact prefixLift 144694
  have htrace : WordTrace (prefixWord ++ tailWord_144694) baseStart_144694 baseEnd_144694 := by
    simpa [prefixWord, tailWord_144694, baseEnd_144694] using wordTrace_append hprefix tailTrace_144694
  have hstable : (prefixWord ++ tailWord_144694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144694).length < 2 ^ (prefixWord ++ tailWord_144694).sum := by decide
  have hdescent : baseEnd_144694 < baseStart_144694 := by decide
  rcases family_descends (prefixWord ++ tailWord_144694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144713 : List Nat := [1, 2, 1, 1, 2, 3, 10]
def baseStart_144713 : Nat := 118140960795 + 144713 * 2 ^ 59
def prefixEnd_144713 : Nat := 4983230072969 + 3 ^ 40 * 144713 * 2
def baseEnd_144713 : Nat := 7338995155970127745381

theorem tailTrace_144713 : CollatzResearch.WordTrace tailWord_144713 prefixEnd_144713 7338995155970127745381 := by
  unfold tailWord_144713
  simp only [CollatzResearch.WordTrace]
  refine ⟨5278116724736990857846793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3518744483157993905231195 5278116724736990857846793)
  ·
    refine ⟨3958587543552743143385095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5278116724736990857846793 3958587543552743143385095)
    ·
      refine ⟨5937881315329114715077643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3958587543552743143385095 5937881315329114715077643)
      ·
        refine ⟨8906821972993672072616465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5937881315329114715077643 8906821972993672072616465)
        ·
          refine ⟨6680116479745254054462349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8906821972993672072616465 6680116479745254054462349)
          ·
            refine ⟨2505043679904470270423381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6680116479745254054462349 2505043679904470270423381)
            ·
              refine ⟨7338995155970127745381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2505043679904470270423381 7338995155970127745381)
              ·
                rfl

theorem cell20_144713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 10].length) (baseStart_144713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144713 prefixEnd_144713 := by exact prefixLift 144713
  have htrace : WordTrace (prefixWord ++ tailWord_144713) baseStart_144713 baseEnd_144713 := by
    simpa [prefixWord, tailWord_144713, baseEnd_144713] using wordTrace_append hprefix tailTrace_144713
  have hstable : (prefixWord ++ tailWord_144713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144713).length < 2 ^ (prefixWord ++ tailWord_144713).sum := by decide
  have hdescent : baseEnd_144713 < baseStart_144713 := by decide
  rcases family_descends (prefixWord ++ tailWord_144713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144751 : List Nat := [1, 1, 2, 1, 3, 1, 3, 8]
def baseStart_144751 : Nat := 118140960795 + 144751 * 2 ^ 59
def prefixEnd_144751 : Nat := 4983230072969 + 3 ^ 40 * 144751 * 2
def baseEnd_144751 : Nat := 22022766879723968813869

theorem tailTrace_144751 : CollatzResearch.WordTrace tailWord_144751 prefixEnd_144751 22022766879723968813869 := by
  unfold tailWord_144751
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279502698599323347730107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3519668465732882231820071 5279502698599323347730107)
  ·
    refine ⟨7919254047898985021595161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5279502698599323347730107 7919254047898985021595161)
    ·
      refine ⟨5939440535924238766196371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7919254047898985021595161 5939440535924238766196371)
      ·
        refine ⟨8909160803886358149294557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5939440535924238766196371 8909160803886358149294557)
        ·
          refine ⟨3340935301457384305985459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8909160803886358149294557 3340935301457384305985459)
          ·
            refine ⟨5011402952186076458978189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3340935301457384305985459 5011402952186076458978189)
            ·
              refine ⟨1879276107069778672116821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5011402952186076458978189 1879276107069778672116821)
              ·
                refine ⟨22022766879723968813869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1879276107069778672116821 22022766879723968813869)
                ·
                  rfl

theorem cell20_144751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_144751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144751 prefixEnd_144751 := by exact prefixLift 144751
  have htrace : WordTrace (prefixWord ++ tailWord_144751) baseStart_144751 baseEnd_144751 := by
    simpa [prefixWord, tailWord_144751, baseEnd_144751] using wordTrace_append hprefix tailTrace_144751
  have hstable : (prefixWord ++ tailWord_144751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144751).length < 2 ^ (prefixWord ++ tailWord_144751).sum := by decide
  have hdescent : baseEnd_144751 < baseStart_144751 := by decide
  rcases family_descends (prefixWord ++ tailWord_144751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144799 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 4]
def baseStart_144799 : Nat := 118140960795 + 144799 * 2 ^ 59
def prefixEnd_144799 : Nat := 4983230072969 + 3 ^ 40 * 144799 * 2
def baseEnd_144799 : Nat := 66090209147097072841411

theorem tailTrace_144799 : CollatzResearch.WordTrace tailWord_144799 prefixEnd_144799 66090209147097072841411 := by
  unfold tailWord_144799
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281253402425427545477451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3520835601616951696984967 5281253402425427545477451)
  ·
    refine ⟨7921880103638141318216177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5281253402425427545477451 7921880103638141318216177)
    ·
      refine ⟨5941410077728605988662133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7921880103638141318216177 5941410077728605988662133)
      ·
        refine ⟨557007194787056811437075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5941410077728605988662133 557007194787056811437075)
        ·
          refine ⟨835510792180585217155613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557007194787056811437075 835510792180585217155613)
          ·
            refine ⟨313316547067719456433355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 835510792180585217155613 313316547067719456433355)
            ·
              refine ⟨469974820601579184650033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313316547067719456433355 469974820601579184650033)
              ·
                refine ⟨352481115451184388487525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469974820601579184650033 352481115451184388487525)
                ·
                  refine ⟨66090209147097072841411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352481115451184388487525 66090209147097072841411)
                  ·
                    rfl

theorem cell20_144799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_144799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144799 prefixEnd_144799 := by exact prefixLift 144799
  have htrace : WordTrace (prefixWord ++ tailWord_144799) baseStart_144799 baseEnd_144799 := by
    simpa [prefixWord, tailWord_144799, baseEnd_144799] using wordTrace_append hprefix tailTrace_144799
  have hstable : (prefixWord ++ tailWord_144799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144799).length < 2 ^ (prefixWord ++ tailWord_144799).sum := by decide
  have hdescent : baseEnd_144799 < baseStart_144799 := by decide
  rcases family_descends (prefixWord ++ tailWord_144799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144854 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_144854 : Nat := 118140960795 + 144854 * 2 ^ 59
def prefixEnd_144854 : Nat := 4983230072969 + 3 ^ 40 * 144854 * 2
def baseEnd_144854 : Nat := 66115312645761326007853

theorem tailTrace_144854 : CollatzResearch.WordTrace tailWord_144854 prefixEnd_144854 66115312645761326007853 := by
  unfold tailWord_144854
  simp only [CollatzResearch.WordTrace]
  refine ⟨330203713576635746170601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3522172944817447959153077 330203713576635746170601)
  ·
    refine ⟨247652785182476809627951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 330203713576635746170601 247652785182476809627951)
    ·
      refine ⟨371479177773715214441927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247652785182476809627951 371479177773715214441927)
      ·
        refine ⟨557218766660572821662891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371479177773715214441927 557218766660572821662891)
        ·
          refine ⟨835828149990859232494337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557218766660572821662891 835828149990859232494337)
          ·
            refine ⟨626871112493144424370753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835828149990859232494337 626871112493144424370753)
            ·
              refine ⟨470153334369858318278065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626871112493144424370753 470153334369858318278065)
              ·
                refine ⟨352615000777393738708549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470153334369858318278065 352615000777393738708549)
                ·
                  refine ⟨66115312645761326007853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352615000777393738708549 66115312645761326007853)
                  ·
                    rfl

theorem cell20_144854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_144854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144854 prefixEnd_144854 := by exact prefixLift 144854
  have htrace : WordTrace (prefixWord ++ tailWord_144854) baseStart_144854 baseEnd_144854 := by
    simpa [prefixWord, tailWord_144854, baseEnd_144854] using wordTrace_append hprefix tailTrace_144854
  have hstable : (prefixWord ++ tailWord_144854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144854).length < 2 ^ (prefixWord ++ tailWord_144854).sum := by decide
  have hdescent : baseEnd_144854 < baseStart_144854 := by decide
  rcases family_descends (prefixWord ++ tailWord_144854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144861 : List Nat := [1, 4, 3, 1, 1, 2, 4, 4]
def baseStart_144861 : Nat := 118140960795 + 144861 * 2 ^ 59
def prefixEnd_144861 : Nat := 4983230072969 + 3 ^ 40 * 144861 * 2
def baseEnd_144861 : Nat := 22039502545500137591497

theorem tailTrace_144861 : CollatzResearch.WordTrace tailWord_144861 prefixEnd_144861 22039502545500137591497 := by
  unfold tailWord_144861
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283514728200812134234437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3522343152133874756156291 5283514728200812134234437)
  ·
    refine ⟨990659011537652275168957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5283514728200812134234437 990659011537652275168957)
    ·
      refine ⟨371497129326619603188359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 990659011537652275168957 371497129326619603188359)
      ·
        refine ⟨557245693989929404782539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371497129326619603188359 557245693989929404782539)
        ·
          refine ⟨835868540984894107173809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557245693989929404782539 835868540984894107173809)
          ·
            refine ⟨626901405738670580380357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835868540984894107173809 626901405738670580380357)
            ·
              refine ⟨117544013576000733821317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 626901405738670580380357 117544013576000733821317)
              ·
                refine ⟨22039502545500137591497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117544013576000733821317 22039502545500137591497)
                ·
                  rfl

theorem cell20_144861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 4].length) (baseStart_144861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144861 prefixEnd_144861 := by exact prefixLift 144861
  have htrace : WordTrace (prefixWord ++ tailWord_144861) baseStart_144861 baseEnd_144861 := by
    simpa [prefixWord, tailWord_144861, baseEnd_144861] using wordTrace_append hprefix tailTrace_144861
  have hstable : (prefixWord ++ tailWord_144861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144861).length < 2 ^ (prefixWord ++ tailWord_144861).sum := by decide
  have hdescent : baseEnd_144861 < baseStart_144861 := by decide
  rcases family_descends (prefixWord ++ tailWord_144861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144871 : List Nat := [1, 1, 5, 2, 1, 4, 1, 3, 2]
def baseStart_144871 : Nat := 118140960795 + 144871 * 2 ^ 59
def prefixEnd_144871 : Nat := 4983230072969 + 3 ^ 40 * 144871 * 2
def baseEnd_144871 : Nat := 66123071908984822441117

theorem tailTrace_144871 : CollatzResearch.WordTrace tailWord_144871 prefixEnd_144871 66123071908984822441117 := by
  unfold tailWord_144871
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283879458164583842098467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3522586305443055894732311 5283879458164583842098467)
  ·
    refine ⟨7925819187246875763147701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5283879458164583842098467 7925819187246875763147701)
    ·
      refine ⟨743045548804394602795097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7925819187246875763147701 743045548804394602795097)
      ·
        refine ⟨557284161603295952096323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743045548804394602795097 557284161603295952096323)
        ·
          refine ⟨835926242404943928144485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557284161603295952096323 835926242404943928144485)
          ·
            refine ⟨156736170450926986527091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 835926242404943928144485 156736170450926986527091)
            ·
              refine ⟨235104255676390479790637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156736170450926986527091 235104255676390479790637)
              ·
                refine ⟨88164095878646429921489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235104255676390479790637 88164095878646429921489)
                ·
                  refine ⟨66123071908984822441117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88164095878646429921489 66123071908984822441117)
                  ·
                    rfl

theorem cell20_144871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 2].length) (baseStart_144871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144871 prefixEnd_144871 := by exact prefixLift 144871
  have htrace : WordTrace (prefixWord ++ tailWord_144871) baseStart_144871 baseEnd_144871 := by
    simpa [prefixWord, tailWord_144871, baseEnd_144871] using wordTrace_append hprefix tailTrace_144871
  have hstable : (prefixWord ++ tailWord_144871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144871).length < 2 ^ (prefixWord ++ tailWord_144871).sum := by decide
  have hdescent : baseEnd_144871 < baseStart_144871 := by decide
  rcases family_descends (prefixWord ++ tailWord_144871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144875 : List Nat := [1, 1, 1, 1, 2, 3, 2, 7, 2]
def baseStart_144875 : Nat := 118140960795 + 144875 * 2 ^ 59
def prefixEnd_144875 : Nat := 4983230072969 + 3 ^ 40 * 144875 * 2
def baseEnd_144875 : Nat := 66124897617978586307767

theorem tailTrace_144875 : CollatzResearch.WordTrace tailWord_144875 prefixEnd_144875 66124897617978586307767 := by
  unfold tailWord_144875
  simp only [CollatzResearch.WordTrace]
  refine ⟨5284025350150092525244079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3522683566766728350162719 5284025350150092525244079)
  ·
    refine ⟨7926038025225138787866119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5284025350150092525244079 7926038025225138787866119)
    ·
      refine ⟨11889057037837708181799179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7926038025225138787866119 11889057037837708181799179)
      ·
        refine ⟨17833585556756562272698769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11889057037837708181799179 17833585556756562272698769)
        ·
          refine ⟨13375189167567421704524077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17833585556756562272698769 13375189167567421704524077)
          ·
            refine ⟨5015695937837783139196529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13375189167567421704524077 5015695937837783139196529)
            ·
              refine ⟨3761771953378337354397397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5015695937837783139196529 3761771953378337354397397)
              ·
                refine ⟨88166530157304781743689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3761771953378337354397397 88166530157304781743689)
                ·
                  refine ⟨66124897617978586307767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88166530157304781743689 66124897617978586307767)
                  ·
                    rfl

theorem cell20_144875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 2].length) (baseStart_144875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144875 prefixEnd_144875 := by exact prefixLift 144875
  have htrace : WordTrace (prefixWord ++ tailWord_144875) baseStart_144875 baseEnd_144875 := by
    simpa [prefixWord, tailWord_144875, baseEnd_144875] using wordTrace_append hprefix tailTrace_144875
  have hstable : (prefixWord ++ tailWord_144875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144875).length < 2 ^ (prefixWord ++ tailWord_144875).sum := by decide
  have hdescent : baseEnd_144875 < baseStart_144875 := by decide
  rcases family_descends (prefixWord ++ tailWord_144875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144882 : List Nat := [3, 2, 1, 4, 1, 1, 8]
def baseStart_144882 : Nat := 118140960795 + 144882 * 2 ^ 59
def prefixEnd_144882 : Nat := 4983230072969 + 3 ^ 40 * 144882 * 2
def baseEnd_144882 : Nat := 7347565845413074786045

theorem tailTrace_144882 : CollatzResearch.WordTrace tailWord_144882 prefixEnd_144882 7347565845413074786045 := by
  unfold tailWord_144882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1321070165281183180187225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3522853774083155147165933 1321070165281183180187225)
  ·
    refine ⟨990802623960887385140419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1321070165281183180187225 990802623960887385140419)
    ·
      refine ⟨1486203935941331077710629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 990802623960887385140419 1486203935941331077710629)
      ·
        refine ⟨278663237988999577070743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1486203935941331077710629 278663237988999577070743)
        ·
          refine ⟨417994856983499365606115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278663237988999577070743 417994856983499365606115)
          ·
            refine ⟨626992285475249048409173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417994856983499365606115 626992285475249048409173)
            ·
              refine ⟨7347565845413074786045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 626992285475249048409173 7347565845413074786045)
              ·
                rfl

theorem cell20_144882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 8].length) (baseStart_144882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144882 prefixEnd_144882 := by exact prefixLift 144882
  have htrace : WordTrace (prefixWord ++ tailWord_144882) baseStart_144882 baseEnd_144882 := by
    simpa [prefixWord, tailWord_144882, baseEnd_144882] using wordTrace_append hprefix tailTrace_144882
  have hstable : (prefixWord ++ tailWord_144882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144882).length < 2 ^ (prefixWord ++ tailWord_144882).sum := by decide
  have hdescent : baseEnd_144882 < baseStart_144882 := by decide
  rcases family_descends (prefixWord ++ tailWord_144882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144889 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 3]
def baseStart_144889 : Nat := 118140960795 + 144889 * 2 ^ 59
def prefixEnd_144889 : Nat := 4983230072969 + 3 ^ 40 * 144889 * 2
def baseEnd_144889 : Nat := 66131287599456759841043

theorem tailTrace_144889 : CollatzResearch.WordTrace tailWord_144889 prefixEnd_144889 66131287599456759841043 := by
  unfold tailWord_144889
  simp only [CollatzResearch.WordTrace]
  refine ⟨5284535972099372916253721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3523023981399581944169147 5284535972099372916253721)
  ·
    refine ⟨3963401979074529687190291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5284535972099372916253721 3963401979074529687190291)
    ·
      refine ⟨5945102968611794530785437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3963401979074529687190291 5945102968611794530785437)
      ·
        refine ⟨2229413613229422949044539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5945102968611794530785437 2229413613229422949044539)
        ·
          refine ⟨3344120419844134423566809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2229413613229422949044539 3344120419844134423566809)
          ·
            refine ⟨2508090314883100817675107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3344120419844134423566809 2508090314883100817675107)
            ·
              refine ⟨3762135472324651226512661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508090314883100817675107 3762135472324651226512661)
              ·
                refine ⟨176350100265218026242781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3762135472324651226512661 176350100265218026242781)
                ·
                  refine ⟨66131287599456759841043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176350100265218026242781 66131287599456759841043)
                  ·
                    rfl

theorem cell20_144889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_144889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144889 prefixEnd_144889 := by exact prefixLift 144889
  have htrace : WordTrace (prefixWord ++ tailWord_144889) baseStart_144889 baseEnd_144889 := by
    simpa [prefixWord, tailWord_144889, baseEnd_144889] using wordTrace_append hprefix tailTrace_144889
  have hstable : (prefixWord ++ tailWord_144889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144889).length < 2 ^ (prefixWord ++ tailWord_144889).sum := by decide
  have hdescent : baseEnd_144889 < baseStart_144889 := by decide
  rcases family_descends (prefixWord ++ tailWord_144889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144906 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_144906 : Nat := 118140960795 + 144906 * 2 ^ 59
def prefixEnd_144906 : Nat := 4983230072969 + 3 ^ 40 * 144906 * 2
def baseEnd_144906 : Nat := 66139046862680256274307

theorem tailTrace_144906 : CollatzResearch.WordTrace tailWord_144906 prefixEnd_144906 66139046862680256274307 := by
  unfold tailWord_144906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1321289003259446204905643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3523437342025189879748381 1321289003259446204905643)
  ·
    refine ⟨1981933504889169307358465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1321289003259446204905643 1981933504889169307358465)
    ·
      refine ⟨1486450128666876980518849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1981933504889169307358465 1486450128666876980518849)
      ·
        refine ⟨1114837596500157735389137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1486450128666876980518849 1114837596500157735389137)
        ·
          refine ⟨836128197375118301541853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1114837596500157735389137 836128197375118301541853)
          ·
            refine ⟨313548074015669363078195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 836128197375118301541853 313548074015669363078195)
            ·
              refine ⟨470322111023504044617293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313548074015669363078195 470322111023504044617293)
              ·
                refine ⟨176370791633814016731485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 470322111023504044617293 176370791633814016731485)
                ·
                  refine ⟨66139046862680256274307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176370791633814016731485 66139046862680256274307)
                  ·
                    rfl

theorem cell20_144906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_144906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144906 prefixEnd_144906 := by exact prefixLift 144906
  have htrace : WordTrace (prefixWord ++ tailWord_144906) baseStart_144906 baseEnd_144906 := by
    simpa [prefixWord, tailWord_144906, baseEnd_144906] using wordTrace_append hprefix tailTrace_144906
  have hstable : (prefixWord ++ tailWord_144906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144906).length < 2 ^ (prefixWord ++ tailWord_144906).sum := by decide
  have hdescent : baseEnd_144906 < baseStart_144906 := by decide
  rcases family_descends (prefixWord ++ tailWord_144906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144947 : List Nat := [1, 1, 1, 2, 4, 5, 2, 2, 2]
def baseStart_144947 : Nat := 118140960795 + 144947 * 2 ^ 59
def prefixEnd_144947 : Nat := 4983230072969 + 3 ^ 40 * 144947 * 2
def baseEnd_144947 : Nat := 66157760379866335907473

theorem tailTrace_144947 : CollatzResearch.WordTrace tailWord_144947 prefixEnd_144947 66157760379866335907473 := by
  unfold tailWord_144947
  simp only [CollatzResearch.WordTrace]
  refine ⟨5286651405889248821865095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3524434270592832547910063 5286651405889248821865095)
  ·
    refine ⟨7929977108833873232797643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5286651405889248821865095 7929977108833873232797643)
    ·
      refine ⟨11894965663250809849196465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7929977108833873232797643 11894965663250809849196465)
      ·
        refine ⟨8921224247438107386897349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11894965663250809849196465 8921224247438107386897349)
        ·
          refine ⟨1672729546394645135043253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8921224247438107386897349 1672729546394645135043253)
          ·
            refine ⟨156818394974497981410305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1672729546394645135043253 156818394974497981410305)
            ·
              refine ⟨117613796230873486057729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156818394974497981410305 117613796230873486057729)
              ·
                refine ⟨88210347173155114543297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117613796230873486057729 88210347173155114543297)
                ·
                  refine ⟨66157760379866335907473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88210347173155114543297 66157760379866335907473)
                  ·
                    rfl

theorem cell20_144947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 2].length) (baseStart_144947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144947 prefixEnd_144947 := by exact prefixLift 144947
  have htrace : WordTrace (prefixWord ++ tailWord_144947) baseStart_144947 baseEnd_144947 := by
    simpa [prefixWord, tailWord_144947, baseEnd_144947] using wordTrace_append hprefix tailTrace_144947
  have hstable : (prefixWord ++ tailWord_144947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144947).length < 2 ^ (prefixWord ++ tailWord_144947).sum := by decide
  have hdescent : baseEnd_144947 < baseStart_144947 := by decide
  rcases family_descends (prefixWord ++ tailWord_144947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144965 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 3]
def baseStart_144965 : Nat := 118140960795 + 144965 * 2 ^ 59
def prefixEnd_144965 : Nat := 4983230072969 + 3 ^ 40 * 144965 * 2
def baseEnd_144965 : Nat := 66165976070338273307399

theorem tailTrace_144965 : CollatzResearch.WordTrace tailWord_144965 prefixEnd_144965 66165976070338273307399 := by
  unfold tailWord_144965
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287307919824037896020349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3524871946549358597346899 5287307919824037896020349)
  ·
    refine ⟨1982740469934014211007631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5287307919824037896020349 1982740469934014211007631)
    ·
      refine ⟨2974110704901021316511447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982740469934014211007631 2974110704901021316511447)
      ·
        refine ⟨4461166057351531974767171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974110704901021316511447 4461166057351531974767171)
        ·
          refine ⟨6691749086027297962150757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4461166057351531974767171 6691749086027297962150757)
          ·
            refine ⟨1254702953630118367903267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6691749086027297962150757 1254702953630118367903267)
            ·
              refine ⟨1882054430445177551854901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254702953630118367903267 1882054430445177551854901)
              ·
                refine ⟨176442602854235395486397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1882054430445177551854901 176442602854235395486397)
                ·
                  refine ⟨66165976070338273307399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176442602854235395486397 66165976070338273307399)
                  ·
                    rfl

theorem cell20_144965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_144965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144965 prefixEnd_144965 := by exact prefixLift 144965
  have htrace : WordTrace (prefixWord ++ tailWord_144965) baseStart_144965 baseEnd_144965 := by
    simpa [prefixWord, tailWord_144965, baseEnd_144965] using wordTrace_append hprefix tailTrace_144965
  have hstable : (prefixWord ++ tailWord_144965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144965).length < 2 ^ (prefixWord ++ tailWord_144965).sum := by decide
  have hdescent : baseEnd_144965 < baseStart_144965 := by decide
  rcases family_descends (prefixWord ++ tailWord_144965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144972 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_144972 : Nat := 118140960795 + 144972 * 2 ^ 59
def prefixEnd_144972 : Nat := 4983230072969 + 3 ^ 40 * 144972 * 2
def baseEnd_144972 : Nat := 66169171061077360074037

theorem tailTrace_144972 : CollatzResearch.WordTrace tailWord_144972 prefixEnd_144972 66169171061077360074037 := by
  unfold tailWord_144972
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643781615399339045762585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3525042153865785394350113 2643781615399339045762585)
  ·
    refine ⟨1982836211549504284321939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2643781615399339045762585 1982836211549504284321939)
    ·
      refine ⟨2974254317324256426482909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982836211549504284321939 2974254317324256426482909)
      ·
        refine ⟨1115345368996596159931091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2974254317324256426482909 1115345368996596159931091)
        ·
          refine ⟨1673018053494894239896637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115345368996596159931091 1673018053494894239896637)
          ·
            refine ⟨627381770060585339961239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1673018053494894239896637 627381770060585339961239)
            ·
              refine ⟨941072655090878009941859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627381770060585339961239 941072655090878009941859)
              ·
                refine ⟨1411608982636317014912789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941072655090878009941859 1411608982636317014912789)
                ·
                  refine ⟨66169171061077360074037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1411608982636317014912789 66169171061077360074037)
                  ·
                    rfl

theorem cell20_144972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_144972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_144972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_144972 prefixEnd_144972 := by exact prefixLift 144972
  have htrace : WordTrace (prefixWord ++ tailWord_144972) baseStart_144972 baseEnd_144972 := by
    simpa [prefixWord, tailWord_144972, baseEnd_144972] using wordTrace_append hprefix tailTrace_144972
  have hstable : (prefixWord ++ tailWord_144972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144972).length < 2 ^ (prefixWord ++ tailWord_144972).sum := by decide
  have hdescent : baseEnd_144972 < baseStart_144972 := by decide
  rcases family_descends (prefixWord ++ tailWord_144972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145006 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_145006 : Nat := 118140960795 + 145006 * 2 ^ 59
def prefixEnd_145006 : Nat := 4983230072969 + 3 ^ 40 * 145006 * 2
def baseEnd_145006 : Nat := 66184689587524352940565

theorem tailTrace_145006 : CollatzResearch.WordTrace tailWord_145006 prefixEnd_145006 66184689587524352940565 := by
  unfold tailWord_145006
  simp only [CollatzResearch.WordTrace]
  refine ⟨661100414084437737282859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3525868875117001265508581 661100414084437737282859)
  ·
    refine ⟨991650621126656605924289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 661100414084437737282859 991650621126656605924289)
    ·
      refine ⟨743737965844992454443217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 991650621126656605924289 743737965844992454443217)
      ·
        refine ⟨557803474383744340832413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743737965844992454443217 557803474383744340832413)
        ·
          refine ⟨209176302893904127812155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 557803474383744340832413 209176302893904127812155)
          ·
            refine ⟨313764454340856191718233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209176302893904127812155 313764454340856191718233)
            ·
              refine ⟨235323340755642143788675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313764454340856191718233 235323340755642143788675)
              ·
                refine ⟨352985011133463215683013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235323340755642143788675 352985011133463215683013)
                ·
                  refine ⟨66184689587524352940565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 352985011133463215683013 66184689587524352940565)
                  ·
                    rfl

theorem cell20_145006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_145006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145006 prefixEnd_145006 := by exact prefixLift 145006
  have htrace : WordTrace (prefixWord ++ tailWord_145006) baseStart_145006 baseEnd_145006 := by
    simpa [prefixWord, tailWord_145006, baseEnd_145006] using wordTrace_append hprefix tailTrace_145006
  have hstable : (prefixWord ++ tailWord_145006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145006).length < 2 ^ (prefixWord ++ tailWord_145006).sum := by decide
  have hdescent : baseEnd_145006 < baseStart_145006 := by decide
  rcases family_descends (prefixWord ++ tailWord_145006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145017 : List Nat := [1, 2, 1, 3, 3, 1, 2, 7]
def baseStart_145017 : Nat := 118140960795 + 145017 * 2 ^ 59
def prefixEnd_145017 : Nat := 4983230072969 + 3 ^ 40 * 145017 * 2
def baseEnd_145017 : Nat := 22063236762419067857951

theorem tailTrace_145017 : CollatzResearch.WordTrace tailWord_145017 prefixEnd_145017 22063236762419067857951 := by
  unfold tailWord_145017
  simp only [CollatzResearch.WordTrace]
  refine ⟨5289204515635650776913305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3526136343757100517942203 5289204515635650776913305)
  ·
    refine ⟨3966903386726738082684979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5289204515635650776913305 3966903386726738082684979)
    ·
      refine ⟨5950355080090107124027469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3966903386726738082684979 5950355080090107124027469)
      ·
        refine ⟨2231383155033790171510301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5950355080090107124027469 2231383155033790171510301)
        ·
          refine ⟨836768683137671314316363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2231383155033790171510301 836768683137671314316363)
          ·
            refine ⟨1255153024706506971474545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836768683137671314316363 1255153024706506971474545)
            ·
              refine ⟨941364768529880228605909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255153024706506971474545 941364768529880228605909)
              ·
                refine ⟨22063236762419067857951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 941364768529880228605909 22063236762419067857951)
                ·
                  rfl

theorem cell20_145017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_145017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145017 prefixEnd_145017 := by exact prefixLift 145017
  have htrace : WordTrace (prefixWord ++ tailWord_145017) baseStart_145017 baseEnd_145017 := by
    simpa [prefixWord, tailWord_145017, baseEnd_145017] using wordTrace_append hprefix tailTrace_145017
  have hstable : (prefixWord ++ tailWord_145017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145017).length < 2 ^ (prefixWord ++ tailWord_145017).sum := by decide
  have hdescent : baseEnd_145017 < baseStart_145017 := by decide
  rcases family_descends (prefixWord ++ tailWord_145017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145034 : List Nat := [3, 1, 2, 3, 2, 2, 1, 6]
def baseStart_145034 : Nat := 118140960795 + 145034 * 2 ^ 59
def prefixEnd_145034 : Nat := 4983230072969 + 3 ^ 40 * 145034 * 2
def baseEnd_145034 : Nat := 22065823183493566669039

theorem tailTrace_145034 : CollatzResearch.WordTrace tailWord_145034 prefixEnd_145034 22065823183493566669039 := by
  unfold tailWord_145034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322456139143515670070539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3526549704382708453521437 1322456139143515670070539)
  ·
    refine ⟨1983684208715273505105809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1322456139143515670070539 1983684208715273505105809)
    ·
      refine ⟨1487763156536455128829357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1983684208715273505105809 1487763156536455128829357)
      ·
        refine ⟨557911183701170673311009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1487763156536455128829357 557911183701170673311009)
        ·
          refine ⟨418433387775878004983257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557911183701170673311009 418433387775878004983257)
          ·
            refine ⟨313825040831908503737443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418433387775878004983257 313825040831908503737443)
            ·
              refine ⟨470737561247862755606165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313825040831908503737443 470737561247862755606165)
              ·
                refine ⟨22065823183493566669039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 470737561247862755606165 22065823183493566669039)
                ·
                  rfl

theorem cell20_145034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_145034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145034 prefixEnd_145034 := by exact prefixLift 145034
  have htrace : WordTrace (prefixWord ++ tailWord_145034) baseStart_145034 baseEnd_145034 := by
    simpa [prefixWord, tailWord_145034, baseEnd_145034] using wordTrace_append hprefix tailTrace_145034
  have hstable : (prefixWord ++ tailWord_145034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145034).length < 2 ^ (prefixWord ++ tailWord_145034).sum := by decide
  have hdescent : baseEnd_145034 < baseStart_145034 := by decide
  rcases family_descends (prefixWord ++ tailWord_145034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145120 : List Nat := [2, 1, 1, 3, 1, 2, 6, 2, 2]
def baseStart_145120 : Nat := 118140960795 + 145120 * 2 ^ 59
def prefixEnd_145120 : Nat := 4983230072969 + 3 ^ 40 * 145120 * 2
def baseEnd_145120 : Nat := 66236722293846623140099

theorem tailTrace_145120 : CollatzResearch.WordTrace tailWord_145120 prefixEnd_145120 66236722293846623140099 := by
  unfold tailWord_145120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646480617131249683956407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3528640822841666245275209 2646480617131249683956407)
  ·
    refine ⟨3969720925696874525934611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2646480617131249683956407 3969720925696874525934611)
    ·
      refine ⟨5954581388545311788901917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3969720925696874525934611 5954581388545311788901917)
      ·
        refine ⟨2232968020704491920838219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5954581388545311788901917 2232968020704491920838219)
        ·
          refine ⟨3349452031056737881257329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232968020704491920838219 3349452031056737881257329)
          ·
            refine ⟨2512089023292553410942997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3349452031056737881257329 2512089023292553410942997)
            ·
              refine ⟨117754172966838441137953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2512089023292553410942997 117754172966838441137953)
              ·
                refine ⟨88315629725128830853465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117754172966838441137953 88315629725128830853465)
                ·
                  refine ⟨66236722293846623140099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88315629725128830853465 66236722293846623140099)
                  ·
                    rfl

theorem cell20_145120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_145120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145120 prefixEnd_145120 := by exact prefixLift 145120
  have htrace : WordTrace (prefixWord ++ tailWord_145120) baseStart_145120 baseEnd_145120 := by
    simpa [prefixWord, tailWord_145120, baseEnd_145120] using wordTrace_append hprefix tailTrace_145120
  have hstable : (prefixWord ++ tailWord_145120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145120).length < 2 ^ (prefixWord ++ tailWord_145120).sum := by decide
  have hdescent : baseEnd_145120 < baseStart_145120 := by decide
  rcases family_descends (prefixWord ++ tailWord_145120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145124 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_145124 : Nat := 118140960795 + 145124 * 2 ^ 59
def prefixEnd_145124 : Nat := 4983230072969 + 3 ^ 40 * 145124 * 2
def baseEnd_145124 : Nat := 66238548002840387006749

theorem tailTrace_145124 : CollatzResearch.WordTrace tailWord_145124 prefixEnd_145124 66238548002840387006749 := by
  unfold tailWord_145124
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646553563124004025529213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3528738084165338700705617 2646553563124004025529213)
  ·
    refine ⟨992457586171501509573455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2646553563124004025529213 992457586171501509573455)
    ·
      refine ⟨1488686379257252264360183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 992457586171501509573455 1488686379257252264360183)
      ·
        refine ⟨2233029568885878396540275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488686379257252264360183 2233029568885878396540275)
        ·
          refine ⟨3349544353328817594810413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233029568885878396540275 3349544353328817594810413)
          ·
            refine ⟨1256079132498306598053905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3349544353328817594810413 1256079132498306598053905)
            ·
              refine ⟨942059349373729948540429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256079132498306598053905 942059349373729948540429)
              ·
                refine ⟨353272256015148730702661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 942059349373729948540429 353272256015148730702661)
                ·
                  refine ⟨66238548002840387006749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 353272256015148730702661 66238548002840387006749)
                  ·
                    rfl

theorem cell20_145124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_145124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145124 prefixEnd_145124 := by exact prefixLift 145124
  have htrace : WordTrace (prefixWord ++ tailWord_145124) baseStart_145124 baseEnd_145124 := by
    simpa [prefixWord, tailWord_145124, baseEnd_145124] using wordTrace_append hprefix tailTrace_145124
  have hstable : (prefixWord ++ tailWord_145124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145124).length < 2 ^ (prefixWord ++ tailWord_145124).sum := by decide
  have hdescent : baseEnd_145124 < baseStart_145124 := by decide
  rcases family_descends (prefixWord ++ tailWord_145124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145131 : List Nat := [1, 1, 1, 1, 2, 4, 5, 5]
def baseStart_145131 : Nat := 118140960795 + 145131 * 2 ^ 59
def prefixEnd_145131 : Nat := 4983230072969 + 3 ^ 40 * 145131 * 2
def baseEnd_145131 : Nat := 22080580997859824591129

theorem tailTrace_145131 : CollatzResearch.WordTrace tailWord_145131 prefixEnd_145131 22080580997859824591129 := by
  unfold tailWord_145131
  simp only [CollatzResearch.WordTrace]
  refine ⟨5293362437222648246563247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3528908291481765497708831 5293362437222648246563247)
  ·
    refine ⟨7940043655833972369844871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5293362437222648246563247 7940043655833972369844871)
    ·
      refine ⟨11910065483750958554767307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7940043655833972369844871 11910065483750958554767307)
      ·
        refine ⟨17865098225626437832150961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11910065483750958554767307 17865098225626437832150961)
        ·
          refine ⟨13398823669219828374113221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17865098225626437832150961 13398823669219828374113221)
          ·
            refine ⟨2512279437978717820146229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13398823669219828374113221 2512279437978717820146229)
            ·
              refine ⟨235526197310504795638709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2512279437978717820146229 235526197310504795638709)
              ·
                refine ⟨22080580997859824591129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 235526197310504795638709 22080580997859824591129)
                ·
                  rfl

theorem cell20_145131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_145131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145131 prefixEnd_145131 := by exact prefixLift 145131
  have htrace : WordTrace (prefixWord ++ tailWord_145131) baseStart_145131 baseEnd_145131 := by
    simpa [prefixWord, tailWord_145131, baseEnd_145131] using wordTrace_append hprefix tailTrace_145131
  have hstable : (prefixWord ++ tailWord_145131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145131).length < 2 ^ (prefixWord ++ tailWord_145131).sum := by decide
  have hdescent : baseEnd_145131 < baseStart_145131 := by decide
  rcases family_descends (prefixWord ++ tailWord_145131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145148 : List Nat := [2, 2, 2, 1, 3, 1, 5, 4]
def baseStart_145148 : Nat := 118140960795 + 145148 * 2 ^ 59
def prefixEnd_145148 : Nat := 4983230072969 + 3 ^ 40 * 145148 * 2
def baseEnd_145148 : Nat := 22083167418934323402217

theorem tailTrace_145148 : CollatzResearch.WordTrace tailWord_145148 prefixEnd_145148 22083167418934323402217 := by
  unfold tailWord_145148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646991239080530074966049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3529321652107373433288065 2646991239080530074966049)
  ·
    refine ⟨1985243429310397556224537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2646991239080530074966049 1985243429310397556224537)
    ·
      refine ⟨1488932571982798167168403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1985243429310397556224537 1488932571982798167168403)
      ·
        refine ⟨2233398857974197250752605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488932571982798167168403 2233398857974197250752605)
        ·
          refine ⟨837524571740323969032227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2233398857974197250752605 837524571740323969032227)
          ·
            refine ⟨1256286857610485953548341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837524571740323969032227 1256286857610485953548341)
            ·
              refine ⟨117776892900983058145157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1256286857610485953548341 117776892900983058145157)
              ·
                refine ⟨22083167418934323402217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117776892900983058145157 22083167418934323402217)
                ·
                  rfl

theorem cell20_145148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_145148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145148 prefixEnd_145148 := by exact prefixLift 145148
  have htrace : WordTrace (prefixWord ++ tailWord_145148) baseStart_145148 baseEnd_145148 := by
    simpa [prefixWord, tailWord_145148, baseEnd_145148] using wordTrace_append hprefix tailTrace_145148
  have hstable : (prefixWord ++ tailWord_145148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145148).length < 2 ^ (prefixWord ++ tailWord_145148).sum := by decide
  have hdescent : baseEnd_145148 < baseStart_145148 := by decide
  rcases family_descends (prefixWord ++ tailWord_145148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145203 : List Nat := [1, 1, 1, 2, 7, 2, 2, 4]
def baseStart_145203 : Nat := 118140960795 + 145203 * 2 ^ 59
def prefixEnd_145203 : Nat := 4983230072969 + 3 ^ 40 * 145203 * 2
def baseEnd_145203 : Nat := 22091535251822407791031

theorem tailTrace_145203 : CollatzResearch.WordTrace tailWord_145203 prefixEnd_145203 22091535251822407791031 := by
  unfold tailWord_145203
  simp only [CollatzResearch.WordTrace]
  refine ⟨5295988492961804543184263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3530658995307869695456175 5295988492961804543184263)
  ·
    refine ⟨7943982739442706814776395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5295988492961804543184263 7943982739442706814776395)
    ·
      refine ⟨11915974109164060222164593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7943982739442706814776395 11915974109164060222164593)
      ·
        refine ⟨8936980581873045166623445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11915974109164060222164593 8936980581873045166623445)
        ·
          refine ⟨209460482387649496092737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8936980581873045166623445 209460482387649496092737)
          ·
            refine ⟨157095361790737122069553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209460482387649496092737 157095361790737122069553)
            ·
              refine ⟨117821521343052841552165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157095361790737122069553 117821521343052841552165)
              ·
                refine ⟨22091535251822407791031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117821521343052841552165 22091535251822407791031)
                ·
                  rfl

theorem cell20_145203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 4].length) (baseStart_145203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145203 prefixEnd_145203 := by exact prefixLift 145203
  have htrace : WordTrace (prefixWord ++ tailWord_145203) baseStart_145203 baseEnd_145203 := by
    simpa [prefixWord, tailWord_145203, baseEnd_145203] using wordTrace_append hprefix tailTrace_145203
  have hstable : (prefixWord ++ tailWord_145203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145203).length < 2 ^ (prefixWord ++ tailWord_145203).sum := by decide
  have hdescent : baseEnd_145203 < baseStart_145203 := by decide
  rcases family_descends (prefixWord ++ tailWord_145203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145213 : List Nat := [1, 4, 1, 4, 1, 3, 1, 3, 2]
def baseStart_145213 : Nat := 118140960795 + 145213 * 2 ^ 59
def prefixEnd_145213 : Nat := 4983230072969 + 3 ^ 40 * 145213 * 2
def baseEnd_145213 : Nat := 66279170027951633039719

theorem tailTrace_145213 : CollatzResearch.WordTrace tailWord_145213 prefixEnd_145213 66279170027951633039719 := by
  unfold tailWord_145213
  simp only [CollatzResearch.WordTrace]
  refine ⟨5296353222925576251048293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3530902148617050834032195 5296353222925576251048293)
  ·
    refine ⟨993066229298545547071555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5296353222925576251048293 993066229298545547071555)
    ·
      refine ⟨1489599343947818320607333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993066229298545547071555 1489599343947818320607333)
      ·
        refine ⟨279299876990215935113875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1489599343947818320607333 279299876990215935113875)
        ·
          refine ⟨418949815485323902670813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279299876990215935113875 418949815485323902670813)
          ·
            refine ⟨157106180806996463501555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418949815485323902670813 157106180806996463501555)
            ·
              refine ⟨235659271210494695252333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157106180806996463501555 235659271210494695252333)
              ·
                refine ⟨88372226703935510719625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235659271210494695252333 88372226703935510719625)
                ·
                  refine ⟨66279170027951633039719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88372226703935510719625 66279170027951633039719)
                  ·
                    rfl

theorem cell20_145213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_145213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145213 prefixEnd_145213 := by exact prefixLift 145213
  have htrace : WordTrace (prefixWord ++ tailWord_145213) baseStart_145213 baseEnd_145213 := by
    simpa [prefixWord, tailWord_145213, baseEnd_145213] using wordTrace_append hprefix tailTrace_145213
  have hstable : (prefixWord ++ tailWord_145213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145213).length < 2 ^ (prefixWord ++ tailWord_145213).sum := by decide
  have hdescent : baseEnd_145213 < baseStart_145213 := by decide
  rcases family_descends (prefixWord ++ tailWord_145213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145244 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 3]
def baseStart_145244 : Nat := 118140960795 + 145244 * 2 ^ 59
def prefixEnd_145244 : Nat := 4983230072969 + 3 ^ 40 * 145244 * 2
def baseEnd_145244 : Nat := 66293319272653303006259

theorem tailTrace_145244 : CollatzResearch.WordTrace tailWord_145244 prefixEnd_145244 66293319272653303006259 := by
  unfold tailWord_145244
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648741942906634272713393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3531655923875512363617857 2648741942906634272713393)
  ·
    refine ⟨1986556457179975704535045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2648741942906634272713393 1986556457179975704535045)
    ·
      refine ⟨372479335721245444600321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1986556457179975704535045 372479335721245444600321)
      ·
        refine ⟨279359501790934083450241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372479335721245444600321 279359501790934083450241)
        ·
          refine ⟨209519626343200562587681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279359501790934083450241 209519626343200562587681)
          ·
            refine ⟨157139719757400421940761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209519626343200562587681 157139719757400421940761)
            ·
              refine ⟨117854789818050316455571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157139719757400421940761 117854789818050316455571)
              ·
                refine ⟨176782184727075474683357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117854789818050316455571 176782184727075474683357)
                ·
                  refine ⟨66293319272653303006259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176782184727075474683357 66293319272653303006259)
                  ·
                    rfl

theorem cell20_145244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_145244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145244 prefixEnd_145244 := by exact prefixLift 145244
  have htrace : WordTrace (prefixWord ++ tailWord_145244) baseStart_145244 baseEnd_145244 := by
    simpa [prefixWord, tailWord_145244, baseEnd_145244] using wordTrace_append hprefix tailTrace_145244
  have hstable : (prefixWord ++ tailWord_145244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145244).length < 2 ^ (prefixWord ++ tailWord_145244).sum := by decide
  have hdescent : baseEnd_145244 < baseStart_145244 := by decide
  rcases family_descends (prefixWord ++ tailWord_145244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145248 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 3]
def baseStart_145248 : Nat := 118140960795 + 145248 * 2 ^ 59
def prefixEnd_145248 : Nat := 4983230072969 + 3 ^ 40 * 145248 * 2
def baseEnd_145248 : Nat := 66295144981647066872909

theorem tailTrace_145248 : CollatzResearch.WordTrace tailWord_145248 prefixEnd_145248 66295144981647066872909 := by
  unfold tailWord_145248
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648814888899388614286199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3531753185199184819048265 2648814888899388614286199)
  ·
    refine ⟨3973222333349082921429299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2648814888899388614286199 3973222333349082921429299)
    ·
      refine ⟨5959833500023624382143949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3973222333349082921429299 5959833500023624382143949)
      ·
        refine ⟨2234937562508859143303981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5959833500023624382143949 2234937562508859143303981)
        ·
          refine ⟨838101585940822178738993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2234937562508859143303981 838101585940822178738993)
          ·
            refine ⟨628576189455616634054245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 838101585940822178738993 628576189455616634054245)
            ·
              refine ⟨117858035522928118885171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 628576189455616634054245 117858035522928118885171)
              ·
                refine ⟨176787053284392178327757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117858035522928118885171 176787053284392178327757)
                ·
                  refine ⟨66295144981647066872909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176787053284392178327757 66295144981647066872909)
                  ·
                    rfl

theorem cell20_145248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_145248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145248 prefixEnd_145248 := by exact prefixLift 145248
  have htrace : WordTrace (prefixWord ++ tailWord_145248) baseStart_145248 baseEnd_145248 := by
    simpa [prefixWord, tailWord_145248, baseEnd_145248] using wordTrace_append hprefix tailTrace_145248
  have hstable : (prefixWord ++ tailWord_145248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145248).length < 2 ^ (prefixWord ++ tailWord_145248).sum := by decide
  have hdescent : baseEnd_145248 < baseStart_145248 := by decide
  rcases family_descends (prefixWord ++ tailWord_145248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145259 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_145259 : Nat := 118140960795 + 145259 * 2 ^ 59
def prefixEnd_145259 : Nat := 4983230072969 + 3 ^ 40 * 145259 * 2
def baseEnd_145259 : Nat := 66300165681379917506197

theorem tailTrace_145259 : CollatzResearch.WordTrace tailWord_145259 prefixEnd_145259 66300165681379917506197 := by
  unfold tailWord_145259
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298030980758926107222831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3532020653839284071481887 5298030980758926107222831)
  ·
    refine ⟨7947046471138389160834247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5298030980758926107222831 7947046471138389160834247)
    ·
      refine ⟨11920569706707583741251371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7947046471138389160834247 11920569706707583741251371)
      ·
        refine ⟨17880854560061375611877057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11920569706707583741251371 17880854560061375611877057)
        ·
          refine ⟨13410640920046031708907793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17880854560061375611877057 13410640920046031708907793)
          ·
            refine ⟨10057980690034523781680845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13410640920046031708907793 10057980690034523781680845)
            ·
              refine ⟨3771742758762946418130317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10057980690034523781680845 3771742758762946418130317)
              ·
                refine ⟨1414403534536104906798869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3771742758762946418130317 1414403534536104906798869)
                ·
                  refine ⟨66300165681379917506197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1414403534536104906798869 66300165681379917506197)
                  ·
                    rfl

theorem cell20_145259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_145259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145259 prefixEnd_145259 := by exact prefixLift 145259
  have htrace : WordTrace (prefixWord ++ tailWord_145259) baseStart_145259 baseEnd_145259 := by
    simpa [prefixWord, tailWord_145259, baseEnd_145259] using wordTrace_append hprefix tailTrace_145259
  have hstable : (prefixWord ++ tailWord_145259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145259).length < 2 ^ (prefixWord ++ tailWord_145259).sum := by decide
  have hdescent : baseEnd_145259 < baseStart_145259 := by decide
  rcases family_descends (prefixWord ++ tailWord_145259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145262 : List Nat := [4, 1, 2, 3, 1, 1, 2, 6]
def baseStart_145262 : Nat := 118140960795 + 145262 * 2 ^ 59
def prefixEnd_145262 : Nat := 4983230072969 + 3 ^ 40 * 145262 * 2
def baseEnd_145262 : Nat := 22100511654375080135395

theorem tailTrace_145262 : CollatzResearch.WordTrace tailWord_145262 prefixEnd_145262 22100511654375080135395 := by
  unfold tailWord_145262
  simp only [CollatzResearch.WordTrace]
  refine ⟨662267549968507202447755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3532093599832038413054693 662267549968507202447755)
  ·
    refine ⟨993401324952760803671633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662267549968507202447755 993401324952760803671633)
    ·
      refine ⟨745050993714570602753725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 993401324952760803671633 745050993714570602753725)
      ·
        refine ⟨279394122642963976032647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 745050993714570602753725 279394122642963976032647)
        ·
          refine ⟨419091183964445964048971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279394122642963976032647 419091183964445964048971)
          ·
            refine ⟨628636775946668946073457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419091183964445964048971 628636775946668946073457)
            ·
              refine ⟨471477581960001709555093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628636775946668946073457 471477581960001709555093)
              ·
                refine ⟨22100511654375080135395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 471477581960001709555093 22100511654375080135395)
                ·
                  rfl

theorem cell20_145262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_145262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145262 prefixEnd_145262 := by exact prefixLift 145262
  have htrace : WordTrace (prefixWord ++ tailWord_145262) baseStart_145262 baseEnd_145262 := by
    simpa [prefixWord, tailWord_145262, baseEnd_145262] using wordTrace_append hprefix tailTrace_145262
  have hstable : (prefixWord ++ tailWord_145262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145262).length < 2 ^ (prefixWord ++ tailWord_145262).sum := by decide
  have hdescent : baseEnd_145262 < baseStart_145262 := by decide
  rcases family_descends (prefixWord ++ tailWord_145262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145300 : List Nat := [2, 4, 2, 1, 1, 2, 3, 5]
def baseStart_145300 : Nat := 118140960795 + 145300 * 2 ^ 59
def prefixEnd_145300 : Nat := 4983230072969 + 3 ^ 40 * 145300 * 2
def baseEnd_145300 : Nat := 22106293066188665713121

theorem tailTrace_145300 : CollatzResearch.WordTrace tailWord_145300 prefixEnd_145300 22106293066188665713121 := by
  unfold tailWord_145300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2649763186805195054732677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3533017582406926739643569 2649763186805195054732677)
  ·
    refine ⟨496830597525974072762377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2649763186805195054732677 496830597525974072762377)
    ·
      refine ⟨372622948144480554571783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 496830597525974072762377 372622948144480554571783)
      ·
        refine ⟨558934422216720831857675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372622948144480554571783 558934422216720831857675)
        ·
          refine ⟨838401633325081247786513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558934422216720831857675 838401633325081247786513)
          ·
            refine ⟨628801224993810935839885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 838401633325081247786513 628801224993810935839885)
            ·
              refine ⟨235800459372679100939957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 628801224993810935839885 235800459372679100939957)
              ·
                refine ⟨22106293066188665713121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 235800459372679100939957 22106293066188665713121)
                ·
                  rfl

theorem cell20_145300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_145300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145300 prefixEnd_145300 := by exact prefixLift 145300
  have htrace : WordTrace (prefixWord ++ tailWord_145300) baseStart_145300 baseEnd_145300 := by
    simpa [prefixWord, tailWord_145300, baseEnd_145300] using wordTrace_append hprefix tailTrace_145300
  have hstable : (prefixWord ++ tailWord_145300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145300).length < 2 ^ (prefixWord ++ tailWord_145300).sum := by decide
  have hdescent : baseEnd_145300 < baseStart_145300 := by decide
  rcases family_descends (prefixWord ++ tailWord_145300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145331 : List Nat := [1, 1, 1, 2, 3, 1, 6, 3, 2]
def baseStart_145331 : Nat := 118140960795 + 145331 * 2 ^ 59
def prefixEnd_145331 : Nat := 4983230072969 + 3 ^ 40 * 145331 * 2
def baseEnd_145331 : Nat := 66333028443267667105903

theorem tailTrace_145331 : CollatzResearch.WordTrace tailWord_145331 prefixEnd_145331 66333028443267667105903 := by
  unfold tailWord_145331
  simp only [CollatzResearch.WordTrace]
  refine ⟨5300657036498082403843847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3533771357665388269229231 5300657036498082403843847)
  ·
    refine ⟨7950985554747123605765771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5300657036498082403843847 7950985554747123605765771)
    ·
      refine ⟨11926478332120685408648657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7950985554747123605765771 11926478332120685408648657)
      ·
        refine ⟨8944858749090514056486493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11926478332120685408648657 8944858749090514056486493)
        ·
          refine ⟨3354322030908942771182435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8944858749090514056486493 3354322030908942771182435)
          ·
            refine ⟨5031483046363414156773653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354322030908942771182435 5031483046363414156773653)
            ·
              refine ⟨235850767798285038598765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5031483046363414156773653 235850767798285038598765)
              ·
                refine ⟨88444037924356889474537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235850767798285038598765 88444037924356889474537)
                ·
                  refine ⟨66333028443267667105903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88444037924356889474537 66333028443267667105903)
                  ·
                    rfl

theorem cell20_145331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 2].length) (baseStart_145331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145331 prefixEnd_145331 := by exact prefixLift 145331
  have htrace : WordTrace (prefixWord ++ tailWord_145331) baseStart_145331 baseEnd_145331 := by
    simpa [prefixWord, tailWord_145331, baseEnd_145331] using wordTrace_append hprefix tailTrace_145331
  have hstable : (prefixWord ++ tailWord_145331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145331).length < 2 ^ (prefixWord ++ tailWord_145331).sum := by decide
  have hdescent : baseEnd_145331 < baseStart_145331 := by decide
  rcases family_descends (prefixWord ++ tailWord_145331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145335 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_145335 : Nat := 118140960795 + 145335 * 2 ^ 59
def prefixEnd_145335 : Nat := 4983230072969 + 3 ^ 40 * 145335 * 2
def baseEnd_145335 : Nat := 66334854152261430972553

theorem tailTrace_145335 : CollatzResearch.WordTrace tailWord_145335 prefixEnd_145335 66334854152261430972553 := by
  unfold tailWord_145335
  simp only [CollatzResearch.WordTrace]
  refine ⟨5300802928483591086989459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3533868618989060724659639 5300802928483591086989459)
  ·
    refine ⟨7951204392725386630484189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5300802928483591086989459 7951204392725386630484189)
    ·
      refine ⟨2981701647272019986431571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7951204392725386630484189 2981701647272019986431571)
      ·
        refine ⟨4472552470908029979647357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2981701647272019986431571 4472552470908029979647357)
        ·
          refine ⟨1677207176590511242367759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4472552470908029979647357 1677207176590511242367759)
          ·
            refine ⟨2515810764885766863551639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677207176590511242367759 2515810764885766863551639)
            ·
              refine ⟨3773716147328650295327459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515810764885766863551639 3773716147328650295327459)
              ·
                refine ⟨5660574220992975442991189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3773716147328650295327459 5660574220992975442991189)
                ·
                  refine ⟨66334854152261430972553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5660574220992975442991189 66334854152261430972553)
                  ·
                    rfl

theorem cell20_145335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_145335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145335 prefixEnd_145335 := by exact prefixLift 145335
  have htrace : WordTrace (prefixWord ++ tailWord_145335) baseStart_145335 baseEnd_145335 := by
    simpa [prefixWord, tailWord_145335, baseEnd_145335] using wordTrace_append hprefix tailTrace_145335
  have hstable : (prefixWord ++ tailWord_145335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145335).length < 2 ^ (prefixWord ++ tailWord_145335).sum := by decide
  have hdescent : baseEnd_145335 < baseStart_145335 := by decide
  rcases family_descends (prefixWord ++ tailWord_145335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145352 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_145352 : Nat := 118140960795 + 145352 * 2 ^ 59
def prefixEnd_145352 : Nat := 4983230072969 + 3 ^ 40 * 145352 * 2
def baseEnd_145352 : Nat := 66342613415484927405817

theorem tailTrace_145352 : CollatzResearch.WordTrace tailWord_145352 prefixEnd_145352 66342613415484927405817 := by
  unfold tailWord_145352
  simp only [CollatzResearch.WordTrace]
  refine ⟨2650711484711001495179155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3534281979614668660238873 2650711484711001495179155)
  ·
    refine ⟨3976067227066502242768733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2650711484711001495179155 3976067227066502242768733)
    ·
      refine ⟨1491025210149938341038275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3976067227066502242768733 1491025210149938341038275)
      ·
        refine ⟨2236537815224907511557413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491025210149938341038275 2236537815224907511557413)
        ·
          refine ⟨419350840354670158417015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2236537815224907511557413 419350840354670158417015)
          ·
            refine ⟨629026260532005237625523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419350840354670158417015 629026260532005237625523)
            ·
              refine ⟨943539390798007856438285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629026260532005237625523 943539390798007856438285)
              ·
                refine ⟨353827271549252946164357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 943539390798007856438285 353827271549252946164357)
                ·
                  refine ⟨66342613415484927405817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 353827271549252946164357 66342613415484927405817)
                  ·
                    rfl

theorem cell20_145352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_145352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145352 prefixEnd_145352 := by exact prefixLift 145352
  have htrace : WordTrace (prefixWord ++ tailWord_145352) baseStart_145352 baseEnd_145352 := by
    simpa [prefixWord, tailWord_145352, baseEnd_145352] using wordTrace_append hprefix tailTrace_145352
  have hstable : (prefixWord ++ tailWord_145352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145352).length < 2 ^ (prefixWord ++ tailWord_145352).sum := by decide
  have hdescent : baseEnd_145352 < baseStart_145352 := by decide
  rcases family_descends (prefixWord ++ tailWord_145352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145372 : List Nat := [2, 2, 6, 1, 1, 1, 1, 6]
def baseStart_145372 : Nat := 118140960795 + 145372 * 2 ^ 59
def prefixEnd_145372 : Nat := 4983230072969 + 3 ^ 40 * 145372 * 2
def baseEnd_145372 : Nat := 22117247320151248913023

theorem tailTrace_145372 : CollatzResearch.WordTrace tailWord_145372 prefixEnd_145372 22117247320151248913023 := by
  unfold tailWord_145372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2651076214674773203043185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3534768286233030937390913 2651076214674773203043185)
  ·
    refine ⟨1988307161006079902282389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2651076214674773203043185 1988307161006079902282389)
    ·
      refine ⟨93201898172159995419487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1988307161006079902282389 93201898172159995419487)
      ·
        refine ⟨139802847258239993129231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93201898172159995419487 139802847258239993129231)
        ·
          refine ⟨209704270887359989693847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139802847258239993129231 209704270887359989693847)
          ·
            refine ⟨314556406331039984540771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209704270887359989693847 314556406331039984540771)
            ·
              refine ⟨471834609496559976811157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314556406331039984540771 471834609496559976811157)
              ·
                refine ⟨22117247320151248913023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 471834609496559976811157 22117247320151248913023)
                ·
                  rfl

theorem cell20_145372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_145372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145372 prefixEnd_145372 := by exact prefixLift 145372
  have htrace : WordTrace (prefixWord ++ tailWord_145372) baseStart_145372 baseEnd_145372 := by
    simpa [prefixWord, tailWord_145372, baseEnd_145372] using wordTrace_append hprefix tailTrace_145372
  have hstable : (prefixWord ++ tailWord_145372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145372).length < 2 ^ (prefixWord ++ tailWord_145372).sum := by decide
  have hdescent : baseEnd_145372 < baseStart_145372 := by decide
  rcases family_descends (prefixWord ++ tailWord_145372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145404 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_145404 : Nat := 118140960795 + 145404 * 2 ^ 59
def prefixEnd_145404 : Nat := 4983230072969 + 3 ^ 40 * 145404 * 2
def baseEnd_145404 : Nat := 66366347632403857672271

theorem tailTrace_145404 : CollatzResearch.WordTrace tailWord_145404 prefixEnd_145404 66366347632403857672271 := by
  unfold tailWord_145404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2651659782616807935625633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3535546376822410580834177 2651659782616807935625633)
  ·
    refine ⟨1988744836962605951719225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2651659782616807935625633 1988744836962605951719225)
    ·
      refine ⟨1491558627721954463789419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1988744836962605951719225 1491558627721954463789419)
      ·
        refine ⟨2237337941582931695684129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491558627721954463789419 2237337941582931695684129)
        ·
          refine ⟨1678003456187198771763097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2237337941582931695684129 1678003456187198771763097)
          ·
            refine ⟨1258502592140399078822323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1678003456187198771763097 1258502592140399078822323)
            ·
              refine ⟨1887753888210598618233485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258502592140399078822323 1887753888210598618233485)
              ·
                refine ⟨707907708078974481837557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1887753888210598618233485 707907708078974481837557)
                ·
                  refine ⟨66366347632403857672271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 707907708078974481837557 66366347632403857672271)
                  ·
                    rfl

theorem cell20_145404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_145404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145404 prefixEnd_145404 := by exact prefixLift 145404
  have htrace : WordTrace (prefixWord ++ tailWord_145404) baseStart_145404 baseEnd_145404 := by
    simpa [prefixWord, tailWord_145404, baseEnd_145404] using wordTrace_append hprefix tailTrace_145404
  have hstable : (prefixWord ++ tailWord_145404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145404).length < 2 ^ (prefixWord ++ tailWord_145404).sum := by decide
  have hdescent : baseEnd_145404 < baseStart_145404 := by decide
  rcases family_descends (prefixWord ++ tailWord_145404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145456 : List Nat := [2, 1, 1, 1, 2, 13]
def baseStart_145456 : Nat := 118140960795 + 145456 * 2 ^ 59
def prefixEnd_145456 : Nat := 4983230072969 + 3 ^ 40 * 145456 * 2
def baseEnd_145456 : Nat := 2458891920345288442175

theorem tailTrace_145456 : CollatzResearch.WordTrace tailWord_145456 prefixEnd_145456 2458891920345288442175 := by
  unfold tailWord_145456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652608080522614376072111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3536810774030152501429481 2652608080522614376072111)
  ·
    refine ⟨3978912120783921564108167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2652608080522614376072111 3978912120783921564108167)
    ·
      refine ⟨5968368181175882346162251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3978912120783921564108167 5968368181175882346162251)
      ·
        refine ⟨8952552271763823519243377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5968368181175882346162251 8952552271763823519243377)
        ·
          refine ⟨6714414203822867639432533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8952552271763823519243377 6714414203822867639432533)
          ·
            refine ⟨2458891920345288442175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 6714414203822867639432533 2458891920345288442175)
            ·
              rfl

theorem cell20_145456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 13].length) (baseStart_145456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145456 prefixEnd_145456 := by exact prefixLift 145456
  have htrace : WordTrace (prefixWord ++ tailWord_145456) baseStart_145456 baseEnd_145456 := by
    simpa [prefixWord, tailWord_145456, baseEnd_145456] using wordTrace_append hprefix tailTrace_145456
  have hstable : (prefixWord ++ tailWord_145456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145456).length < 2 ^ (prefixWord ++ tailWord_145456).sum := by decide
  have hdescent : baseEnd_145456 < baseStart_145456 := by decide
  rcases family_descends (prefixWord ++ tailWord_145456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145462 : List Nat := [5, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_145462 : Nat := 118140960795 + 145462 * 2 ^ 59
def prefixEnd_145462 : Nat := 4983230072969 + 3 ^ 40 * 145462 * 2
def baseEnd_145462 : Nat := 66392820412813433738701

theorem tailTrace_145462 : CollatzResearch.WordTrace tailWord_145462 prefixEnd_145462 66392820412813433738701 := by
  unfold tailWord_145462
  simp only [CollatzResearch.WordTrace]
  refine ⟨331589687438968236053915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3536956666015661184575093 331589687438968236053915)
  ·
    refine ⟨497384531158452354080873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 331589687438968236053915 497384531158452354080873)
    ·
      refine ⟨373038398368839265560655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 497384531158452354080873 373038398368839265560655)
      ·
        refine ⟨559557597553258898340983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373038398368839265560655 559557597553258898340983)
        ·
          refine ⟨839336396329888347511475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559557597553258898340983 839336396329888347511475)
          ·
            refine ⟨1259004594494832521267213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839336396329888347511475 1259004594494832521267213)
            ·
              refine ⟨472126722935562195475205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1259004594494832521267213 472126722935562195475205)
              ·
                refine ⟨88523760550417911651601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472126722935562195475205 88523760550417911651601)
                ·
                  refine ⟨66392820412813433738701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88523760550417911651601 66392820412813433738701)
                  ·
                    rfl

theorem cell20_145462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_145462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145462 prefixEnd_145462 := by exact prefixLift 145462
  have htrace : WordTrace (prefixWord ++ tailWord_145462) baseStart_145462 baseEnd_145462 := by
    simpa [prefixWord, tailWord_145462, baseEnd_145462] using wordTrace_append hprefix tailTrace_145462
  have hstable : (prefixWord ++ tailWord_145462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145462).length < 2 ^ (prefixWord ++ tailWord_145462).sum := by decide
  have hdescent : baseEnd_145462 < baseStart_145462 := by decide
  rcases family_descends (prefixWord ++ tailWord_145462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145487 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_145487 : Nat := 118140960795 + 145487 * 2 ^ 59
def prefixEnd_145487 : Nat := 4983230072969 + 3 ^ 40 * 145487 * 2
def baseEnd_145487 : Nat := 66404231094024457905265

theorem tailTrace_145487 : CollatzResearch.WordTrace tailWord_145487 prefixEnd_145487 66404231094024457905265 := by
  unfold tailWord_145487
  simp only [CollatzResearch.WordTrace]
  refine ⟨5306346823932921046522715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3537564549288614031015143 5306346823932921046522715)
  ·
    refine ⟨7959520235899381569784073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5306346823932921046522715 7959520235899381569784073)
    ·
      refine ⟨5969640176924536177338055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7959520235899381569784073 5969640176924536177338055)
      ·
        refine ⟨8954460265386804266007083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5969640176924536177338055 8954460265386804266007083)
        ·
          refine ⟨13431690398080206399010625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8954460265386804266007083 13431690398080206399010625)
          ·
            refine ⟨10073767798560154799257969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13431690398080206399010625 10073767798560154799257969)
            ·
              refine ⟨7555325848920116099443477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10073767798560154799257969 7555325848920116099443477)
              ·
                refine ⟨354155899168130442161413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7555325848920116099443477 354155899168130442161413)
                ·
                  refine ⟨66404231094024457905265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354155899168130442161413 66404231094024457905265)
                  ·
                    rfl

theorem cell20_145487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_145487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145487 prefixEnd_145487 := by exact prefixLift 145487
  have htrace : WordTrace (prefixWord ++ tailWord_145487) baseStart_145487 baseEnd_145487 := by
    simpa [prefixWord, tailWord_145487, baseEnd_145487] using wordTrace_append hprefix tailTrace_145487
  have hstable : (prefixWord ++ tailWord_145487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145487).length < 2 ^ (prefixWord ++ tailWord_145487).sum := by decide
  have hdescent : baseEnd_145487 < baseStart_145487 := by decide
  rcases family_descends (prefixWord ++ tailWord_145487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145500 : List Nat := [2, 2, 4, 1, 1, 3, 2, 3, 2]
def baseStart_145500 : Nat := 118140960795 + 145500 * 2 ^ 59
def prefixEnd_145500 : Nat := 4983230072969 + 3 ^ 40 * 145500 * 2
def baseEnd_145500 : Nat := 66410164648254190471879

theorem tailTrace_145500 : CollatzResearch.WordTrace tailWord_145500 prefixEnd_145500 66410164648254190471879 := by
  unfold tailWord_145500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653410486442912133372977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3537880648590549511163969 2653410486442912133372977)
  ·
    refine ⟨1990057864832184100029733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2653410486442912133372977 1990057864832184100029733)
    ·
      refine ⟨373135849656034518755575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1990057864832184100029733 373135849656034518755575)
      ·
        refine ⟨559703774484051778133363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373135849656034518755575 559703774484051778133363)
        ·
          refine ⟨839555661726077667200045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559703774484051778133363 839555661726077667200045)
          ·
            refine ⟨314833373147279125200017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 839555661726077667200045 314833373147279125200017)
            ·
              refine ⟨236125029860459343900013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314833373147279125200017 236125029860459343900013)
              ·
                refine ⟨88546886197672253962505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236125029860459343900013 88546886197672253962505)
                ·
                  refine ⟨66410164648254190471879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88546886197672253962505 66410164648254190471879)
                  ·
                    rfl

theorem cell20_145500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_145500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145500 prefixEnd_145500 := by exact prefixLift 145500
  have htrace : WordTrace (prefixWord ++ tailWord_145500) baseStart_145500 baseEnd_145500 := by
    simpa [prefixWord, tailWord_145500, baseEnd_145500] using wordTrace_append hprefix tailTrace_145500
  have hstable : (prefixWord ++ tailWord_145500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145500).length < 2 ^ (prefixWord ++ tailWord_145500).sum := by decide
  have hdescent : baseEnd_145500 < baseStart_145500 := by decide
  rcases family_descends (prefixWord ++ tailWord_145500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145558 : List Nat := [5, 3, 2, 1, 2, 1, 6]
def baseStart_145558 : Nat := 118140960795 + 145558 * 2 ^ 59
def prefixEnd_145558 : Nat := 4983230072969 + 3 ^ 40 * 145558 * 2
def baseEnd_145558 : Nat := 7381848603184862948701

theorem tailTrace_145558 : CollatzResearch.WordTrace tailWord_145558 prefixEnd_145558 7381848603184862948701 := by
  unfold tailWord_145558
  simp only [CollatzResearch.WordTrace]
  refine ⟨331808525417231260772333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3539290937783800114904885 331808525417231260772333)
  ·
    refine ⟨124428197031461722789625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 331808525417231260772333 124428197031461722789625)
    ·
      refine ⟨93321147773596292092219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124428197031461722789625 93321147773596292092219)
      ·
        refine ⟨139981721660394438138329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93321147773596292092219 139981721660394438138329)
        ·
          refine ⟨104986291245295828603747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139981721660394438138329 104986291245295828603747)
          ·
            refine ⟨157479436867943742905621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104986291245295828603747 157479436867943742905621)
            ·
              refine ⟨7381848603184862948701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157479436867943742905621 7381848603184862948701)
              ·
                rfl

theorem cell20_145558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 6].length) (baseStart_145558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145558 prefixEnd_145558 := by exact prefixLift 145558
  have htrace : WordTrace (prefixWord ++ tailWord_145558) baseStart_145558 baseEnd_145558 := by
    simpa [prefixWord, tailWord_145558, baseEnd_145558] using wordTrace_append hprefix tailTrace_145558
  have hstable : (prefixWord ++ tailWord_145558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145558).length < 2 ^ (prefixWord ++ tailWord_145558).sum := by decide
  have hdescent : baseEnd_145558 < baseStart_145558 := by decide
  rcases family_descends (prefixWord ++ tailWord_145558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145663 : List Nat := [1, 1, 2, 2, 1, 4, 5, 4]
def baseStart_145663 : Nat := 118140960795 + 145663 * 2 ^ 59
def prefixEnd_145663 : Nat := 4983230072969 + 3 ^ 40 * 145663 * 2
def baseEnd_145663 : Nat := 22161520763250022679293

theorem tailTrace_145663 : CollatzResearch.WordTrace tailWord_145663 prefixEnd_145663 22161520763250022679293 := by
  unfold tailWord_145663
  simp only [CollatzResearch.WordTrace]
  refine ⟨5312766071295303104929643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3541844047530202069953095 5312766071295303104929643)
  ·
    refine ⟨7969149106942954657394465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5312766071295303104929643 7969149106942954657394465)
    ·
      refine ⟨5976861830207215993045849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7969149106942954657394465 5976861830207215993045849)
      ·
        refine ⟨4482646372655411994784387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5976861830207215993045849 4482646372655411994784387)
        ·
          refine ⟨6723969558983117992176581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4482646372655411994784387 6723969558983117992176581)
          ·
            refine ⟨1260744292309334623533109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6723969558983117992176581 1260744292309334623533109)
            ·
              refine ⟨118194777404000120956229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1260744292309334623533109 118194777404000120956229)
              ·
                refine ⟨22161520763250022679293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118194777404000120956229 22161520763250022679293)
                ·
                  rfl

theorem cell20_145663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 4].length) (baseStart_145663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145663 prefixEnd_145663 := by exact prefixLift 145663
  have htrace : WordTrace (prefixWord ++ tailWord_145663) baseStart_145663 baseEnd_145663 := by
    simpa [prefixWord, tailWord_145663, baseEnd_145663] using wordTrace_append hprefix tailTrace_145663
  have hstable : (prefixWord ++ tailWord_145663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145663).length < 2 ^ (prefixWord ++ tailWord_145663).sum := by decide
  have hdescent : baseEnd_145663 < baseStart_145663 := by decide
  rcases family_descends (prefixWord ++ tailWord_145663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145673 : List Nat := [1, 2, 1, 1, 3, 5, 2, 3, 2]
def baseStart_145673 : Nat := 118140960795 + 145673 * 2 ^ 59
def prefixEnd_145673 : Nat := 4983230072969 + 3 ^ 40 * 145673 * 2
def baseEnd_145673 : Nat := 66489126562234477704505

theorem tailTrace_145673 : CollatzResearch.WordTrace tailWord_145673 prefixEnd_145673 66489126562234477704505 := by
  unfold tailWord_145673
  simp only [CollatzResearch.WordTrace]
  refine ⟨5313130801259074812793673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3542087200839383208529115 5313130801259074812793673)
  ·
    refine ⟨3984848100944306109595255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5313130801259074812793673 3984848100944306109595255)
    ·
      refine ⟨5977272151416459164392883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3984848100944306109595255 5977272151416459164392883)
      ·
        refine ⟨8965908227124688746589325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5977272151416459164392883 8965908227124688746589325)
        ·
          refine ⟨3362215585171758279970997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8965908227124688746589325 3362215585171758279970997)
          ·
            refine ⟨315207711109852338747281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3362215585171758279970997 315207711109852338747281)
            ·
              refine ⟨236405783332389254060461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315207711109852338747281 236405783332389254060461)
              ·
                refine ⟨88652168749645970272673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236405783332389254060461 88652168749645970272673)
                ·
                  refine ⟨66489126562234477704505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88652168749645970272673 66489126562234477704505)
                  ·
                    rfl

theorem cell20_145673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_145673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145673 prefixEnd_145673 := by exact prefixLift 145673
  have htrace : WordTrace (prefixWord ++ tailWord_145673) baseStart_145673 baseEnd_145673 := by
    simpa [prefixWord, tailWord_145673, baseEnd_145673] using wordTrace_append hprefix tailTrace_145673
  have hstable : (prefixWord ++ tailWord_145673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145673).length < 2 ^ (prefixWord ++ tailWord_145673).sum := by decide
  have hdescent : baseEnd_145673 < baseStart_145673 := by decide
  rcases family_descends (prefixWord ++ tailWord_145673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145687 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 3]
def baseStart_145687 : Nat := 118140960795 + 145687 * 2 ^ 59
def prefixEnd_145687 : Nat := 4983230072969 + 3 ^ 40 * 145687 * 2
def baseEnd_145687 : Nat := 66495516543712651237781

theorem tailTrace_145687 : CollatzResearch.WordTrace tailWord_145687 prefixEnd_145687 66495516543712651237781 := by
  unfold tailWord_145687
  simp only [CollatzResearch.WordTrace]
  refine ⟨5313641423208355203803315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3542427615472236802535543 5313641423208355203803315)
  ·
    refine ⟨7970462134812532805704973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5313641423208355203803315 7970462134812532805704973)
    ·
      refine ⟨2988923300554699802139365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7970462134812532805704973 2988923300554699802139365)
      ·
        refine ⟨560423118854006212901131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2988923300554699802139365 560423118854006212901131)
        ·
          refine ⟨840634678281009319351697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560423118854006212901131 840634678281009319351697)
          ·
            refine ⟨630476008710756989513773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 840634678281009319351697 630476008710756989513773)
            ·
              refine ⟨236428503266533871067665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 630476008710756989513773 236428503266533871067665)
              ·
                refine ⟨177321377449900403300749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236428503266533871067665 177321377449900403300749)
                ·
                  refine ⟨66495516543712651237781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177321377449900403300749 66495516543712651237781)
                  ·
                    rfl

theorem cell20_145687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 3].length) (baseStart_145687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145687 prefixEnd_145687 := by exact prefixLift 145687
  have htrace : WordTrace (prefixWord ++ tailWord_145687) baseStart_145687 baseEnd_145687 := by
    simpa [prefixWord, tailWord_145687, baseEnd_145687] using wordTrace_append hprefix tailTrace_145687
  have hstable : (prefixWord ++ tailWord_145687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145687).length < 2 ^ (prefixWord ++ tailWord_145687).sum := by decide
  have hdescent : baseEnd_145687 < baseStart_145687 := by decide
  rcases family_descends (prefixWord ++ tailWord_145687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145708 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 3]
def baseStart_145708 : Nat := 118140960795 + 145708 * 2 ^ 59
def prefixEnd_145708 : Nat := 4983230072969 + 3 ^ 40 * 145708 * 2
def baseEnd_145708 : Nat := 66505101515929911537695

theorem tailTrace_145708 : CollatzResearch.WordTrace tailWord_145708 prefixEnd_145708 66505101515929911537695 := by
  unfold tailWord_145708
  simp only [CollatzResearch.WordTrace]
  refine ⟨2657203678066137895158889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3542938237421517193545185 2657203678066137895158889)
  ·
    refine ⟨1992902758549603421369167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2657203678066137895158889 1992902758549603421369167)
    ·
      refine ⟨2989354137824405132053751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1992902758549603421369167 2989354137824405132053751)
      ·
        refine ⟨4484031206736607698080627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2989354137824405132053751 4484031206736607698080627)
        ·
          refine ⟨6726046810104911547120941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4484031206736607698080627 6726046810104911547120941)
          ·
            refine ⟨2522267553789341830170353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6726046810104911547120941 2522267553789341830170353)
            ·
              refine ⟨1891700665342006372627765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2522267553789341830170353 1891700665342006372627765)
              ·
                refine ⟨177346937375813097433853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1891700665342006372627765 177346937375813097433853)
                ·
                  refine ⟨66505101515929911537695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177346937375813097433853 66505101515929911537695)
                  ·
                    rfl

theorem cell20_145708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_145708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145708 prefixEnd_145708 := by exact prefixLift 145708
  have htrace : WordTrace (prefixWord ++ tailWord_145708) baseStart_145708 baseEnd_145708 := by
    simpa [prefixWord, tailWord_145708, baseEnd_145708] using wordTrace_append hprefix tailTrace_145708
  have hstable : (prefixWord ++ tailWord_145708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145708).length < 2 ^ (prefixWord ++ tailWord_145708).sum := by decide
  have hdescent : baseEnd_145708 < baseStart_145708 := by decide
  rcases family_descends (prefixWord ++ tailWord_145708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145715 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_145715 : Nat := 118140960795 + 145715 * 2 ^ 59
def prefixEnd_145715 : Nat := 4983230072969 + 3 ^ 40 * 145715 * 2
def baseEnd_145715 : Nat := 66508296506668998304333

theorem tailTrace_145715 : CollatzResearch.WordTrace tailWord_145715 prefixEnd_145715 66508296506668998304333 := by
  unfold tailWord_145715
  simp only [CollatzResearch.WordTrace]
  refine ⟨5314662667106915985822599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3543108444737943990548399 5314662667106915985822599)
  ·
    refine ⟨7971994000660373978733899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5314662667106915985822599 7971994000660373978733899)
    ·
      refine ⟨11957991000990560968100849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7971994000660373978733899 11957991000990560968100849)
      ·
        refine ⟨8968493250742920726075637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11957991000990560968100849 8968493250742920726075637)
        ·
          refine ⟨840796242257148818069591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8968493250742920726075637 840796242257148818069591)
          ·
            refine ⟨1261194363385723227104387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840796242257148818069591 1261194363385723227104387)
            ·
              refine ⟨1891791545078584840656581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261194363385723227104387 1891791545078584840656581)
              ·
                refine ⟨354710914702234657623109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1891791545078584840656581 354710914702234657623109)
                ·
                  refine ⟨66508296506668998304333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354710914702234657623109 66508296506668998304333)
                  ·
                    rfl

theorem cell20_145715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_145715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145715 prefixEnd_145715 := by exact prefixLift 145715
  have htrace : WordTrace (prefixWord ++ tailWord_145715) baseStart_145715 baseEnd_145715 := by
    simpa [prefixWord, tailWord_145715, baseEnd_145715] using wordTrace_append hprefix tailTrace_145715
  have hstable : (prefixWord ++ tailWord_145715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145715).length < 2 ^ (prefixWord ++ tailWord_145715).sum := by decide
  have hdescent : baseEnd_145715 < baseStart_145715 := by decide
  rcases family_descends (prefixWord ++ tailWord_145715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145746 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_145746 : Nat := 118140960795 + 145746 * 2 ^ 59
def prefixEnd_145746 : Nat := 4983230072969 + 3 ^ 40 * 145746 * 2
def baseEnd_145746 : Nat := 66522445751370668270873

theorem tailTrace_145746 : CollatzResearch.WordTrace tailWord_145746 prefixEnd_145746 66522445751370668270873 := by
  unfold tailWord_145746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1328948332498652070050273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3543862219996405520134061 1328948332498652070050273)
  ·
    refine ⟨996711249373989052537705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1328948332498652070050273 996711249373989052537705)
    ·
      refine ⟨747533437030491789403279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 996711249373989052537705 747533437030491789403279)
      ·
        refine ⟨1121300155545737684104919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 747533437030491789403279 1121300155545737684104919)
        ·
          refine ⟨1681950233318606526157379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1121300155545737684104919 1681950233318606526157379)
          ·
            refine ⟨2522925349977909789236069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681950233318606526157379 2522925349977909789236069)
            ·
              refine ⟨473048503120858085481763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2522925349977909789236069 473048503120858085481763)
              ·
                refine ⟨709572754681287128222645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473048503120858085481763 709572754681287128222645)
                ·
                  refine ⟨66522445751370668270873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 709572754681287128222645 66522445751370668270873)
                  ·
                    rfl

theorem cell20_145746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_145746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145746 prefixEnd_145746 := by exact prefixLift 145746
  have htrace : WordTrace (prefixWord ++ tailWord_145746) baseStart_145746 baseEnd_145746 := by
    simpa [prefixWord, tailWord_145746, baseEnd_145746] using wordTrace_append hprefix tailTrace_145746
  have hstable : (prefixWord ++ tailWord_145746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145746).length < 2 ^ (prefixWord ++ tailWord_145746).sum := by decide
  have hdescent : baseEnd_145746 < baseStart_145746 := by decide
  rcases family_descends (prefixWord ++ tailWord_145746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145749 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 4]
def baseStart_145749 : Nat := 118140960795 + 145749 * 2 ^ 59
def prefixEnd_145749 : Nat := 4983230072969 + 3 ^ 40 * 145749 * 2
def baseEnd_145749 : Nat := 66523815033115991170861

theorem tailTrace_145749 : CollatzResearch.WordTrace tailWord_145749 prefixEnd_145749 66523815033115991170861 := by
  unfold tailWord_145749
  simp only [CollatzResearch.WordTrace]
  refine ⟨5315902748983739792560301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3543935165989159861706867 5315902748983739792560301)
  ·
    refine ⟨1993463530868902422210113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5315902748983739792560301 1993463530868902422210113)
    ·
      refine ⟨1495097648151676816657585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1993463530868902422210113 1495097648151676816657585)
      ·
        refine ⟨1121323236113757612493189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1495097648151676816657585 1121323236113757612493189)
        ·
          refine ⟨210248106771329552342473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1121323236113757612493189 210248106771329552342473)
          ·
            refine ⟨157686080078497164256855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210248106771329552342473 157686080078497164256855)
            ·
              refine ⟨236529120117745746385283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157686080078497164256855 236529120117745746385283)
              ·
                refine ⟨354793680176618619577925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236529120117745746385283 354793680176618619577925)
                ·
                  refine ⟨66523815033115991170861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354793680176618619577925 66523815033115991170861)
                  ·
                    rfl

theorem cell20_145749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_145749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145749 prefixEnd_145749 := by exact prefixLift 145749
  have htrace : WordTrace (prefixWord ++ tailWord_145749) baseStart_145749 baseEnd_145749 := by
    simpa [prefixWord, tailWord_145749, baseEnd_145749] using wordTrace_append hprefix tailTrace_145749
  have hstable : (prefixWord ++ tailWord_145749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145749).length < 2 ^ (prefixWord ++ tailWord_145749).sum := by decide
  have hdescent : baseEnd_145749 < baseStart_145749 := by decide
  rcases family_descends (prefixWord ++ tailWord_145749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145794 : List Nat := [3, 4, 2, 1, 2, 8]
def baseStart_145794 : Nat := 118140960795 + 145794 * 2 ^ 59
def prefixEnd_145794 : Nat := 4983230072969 + 3 ^ 40 * 145794 * 2
def baseEnd_145794 : Nat := 2464605713307253135951

theorem tailTrace_145794 : CollatzResearch.WordTrace tailWord_145794 prefixEnd_145794 2464605713307253135951 := by
  unfold tailWord_145794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329386008455178119487109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3545029355880474985298957 1329386008455178119487109)
  ·
    refine ⟨249259876585345897403833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1329386008455178119487109 249259876585345897403833)
    ·
      refine ⟨186944907439009423052875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249259876585345897403833 186944907439009423052875)
      ·
        refine ⟨280417361158514134579313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186944907439009423052875 280417361158514134579313)
        ·
          refine ⟨210313020868885600934485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280417361158514134579313 210313020868885600934485)
          ·
            refine ⟨2464605713307253135951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 210313020868885600934485 2464605713307253135951)
            ·
              rfl

theorem cell20_145794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 8].length) (baseStart_145794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145794 prefixEnd_145794 := by exact prefixLift 145794
  have htrace : WordTrace (prefixWord ++ tailWord_145794) baseStart_145794 baseEnd_145794 := by
    simpa [prefixWord, tailWord_145794, baseEnd_145794] using wordTrace_append hprefix tailTrace_145794
  have hstable : (prefixWord ++ tailWord_145794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145794).length < 2 ^ (prefixWord ++ tailWord_145794).sum := by decide
  have hdescent : baseEnd_145794 < baseStart_145794 := by decide
  rcases family_descends (prefixWord ++ tailWord_145794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145801 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 3]
def baseStart_145801 : Nat := 118140960795 + 145801 * 2 ^ 59
def prefixEnd_145801 : Nat := 4983230072969 + 3 ^ 40 * 145801 * 2
def baseEnd_145801 : Nat := 66547549250034921437315

theorem tailTrace_145801 : CollatzResearch.WordTrace tailWord_145801 prefixEnd_145801 66547549250034921437315 := by
  unfold tailWord_145801
  simp only [CollatzResearch.WordTrace]
  refine ⟨5317799344795352673453257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3545199563196901782302171 5317799344795352673453257)
  ·
    refine ⟨3988349508596514505089943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5317799344795352673453257 3988349508596514505089943)
    ·
      refine ⟨5982524262894771757634915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3988349508596514505089943 5982524262894771757634915)
      ·
        refine ⟨8973786394342157636452373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5982524262894771757634915 8973786394342157636452373)
        ·
          refine ⟨420646237234788639208705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8973786394342157636452373 420646237234788639208705)
          ·
            refine ⟨315484677926091479406529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420646237234788639208705 315484677926091479406529)
            ·
              refine ⟨236613508444568609554897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315484677926091479406529 236613508444568609554897)
              ·
                refine ⟨177460131333426457166173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236613508444568609554897 177460131333426457166173)
                ·
                  refine ⟨66547549250034921437315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177460131333426457166173 66547549250034921437315)
                  ·
                    rfl

theorem cell20_145801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_145801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145801 prefixEnd_145801 := by exact prefixLift 145801
  have htrace : WordTrace (prefixWord ++ tailWord_145801) baseStart_145801 baseEnd_145801 := by
    simpa [prefixWord, tailWord_145801, baseEnd_145801] using wordTrace_append hprefix tailTrace_145801
  have hstable : (prefixWord ++ tailWord_145801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145801).length < 2 ^ (prefixWord ++ tailWord_145801).sum := by decide
  have hdescent : baseEnd_145801 < baseStart_145801 := by decide
  rcases family_descends (prefixWord ++ tailWord_145801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145804 : List Nat := [2, 2, 1, 2, 1, 6, 2, 2, 2]
def baseStart_145804 : Nat := 118140960795 + 145804 * 2 ^ 59
def prefixEnd_145804 : Nat := 4983230072969 + 3 ^ 40 * 145804 * 2
def baseEnd_145804 : Nat := 66548918531780244337303

theorem tailTrace_145804 : CollatzResearch.WordTrace tailWord_145804 prefixEnd_145804 66548918531780244337303 := by
  unfold tailWord_145804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2658954381892242092906233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3545272509189656123874977 2658954381892242092906233)
  ·
    refine ⟨1994215786419181569679675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2658954381892242092906233 1994215786419181569679675)
    ·
      refine ⟨2991323679628772354519513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1994215786419181569679675 2991323679628772354519513)
      ·
        refine ⟨2243492759721579265889635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2991323679628772354519513 2243492759721579265889635)
        ·
          refine ⟨3365239139582368898834453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243492759721579265889635 3365239139582368898834453)
          ·
            refine ⟨157745584667923542132865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3365239139582368898834453 157745584667923542132865)
            ·
              refine ⟨118309188500942656599649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157745584667923542132865 118309188500942656599649)
              ·
                refine ⟨88731891375706992449737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118309188500942656599649 88731891375706992449737)
                ·
                  refine ⟨66548918531780244337303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88731891375706992449737 66548918531780244337303)
                  ·
                    rfl

theorem cell20_145804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_145804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145804 prefixEnd_145804 := by exact prefixLift 145804
  have htrace : WordTrace (prefixWord ++ tailWord_145804) baseStart_145804 baseEnd_145804 := by
    simpa [prefixWord, tailWord_145804, baseEnd_145804] using wordTrace_append hprefix tailTrace_145804
  have hstable : (prefixWord ++ tailWord_145804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145804).length < 2 ^ (prefixWord ++ tailWord_145804).sum := by decide
  have hdescent : baseEnd_145804 < baseStart_145804 := by decide
  rcases family_descends (prefixWord ++ tailWord_145804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145825 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 4]
def baseStart_145825 : Nat := 118140960795 + 145825 * 2 ^ 59
def prefixEnd_145825 : Nat := 4983230072969 + 3 ^ 40 * 145825 * 2
def baseEnd_145825 : Nat := 66558503503997504637217

theorem tailTrace_145825 : CollatzResearch.WordTrace tailWord_145825 prefixEnd_145825 66558503503997504637217 := by
  unfold tailWord_145825
  simp only [CollatzResearch.WordTrace]
  refine ⟨5318674696708404772326929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3545783131138936514884619 5318674696708404772326929)
  ·
    refine ⟨3989006022531303579245197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5318674696708404772326929 3989006022531303579245197)
    ·
      refine ⟨1495877258449238842216949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3989006022531303579245197 1495877258449238842216949)
      ·
        refine ⟨140238492979616141457839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1495877258449238842216949 140238492979616141457839)
        ·
          refine ⟨210357739469424212186759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140238492979616141457839 210357739469424212186759)
          ·
            refine ⟨315536609204136318280139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210357739469424212186759 315536609204136318280139)
            ·
              refine ⟨473304913806204477420209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315536609204136318280139 473304913806204477420209)
              ·
                refine ⟨354978685354653358065157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473304913806204477420209 354978685354653358065157)
                ·
                  refine ⟨66558503503997504637217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354978685354653358065157 66558503503997504637217)
                  ·
                    rfl

theorem cell20_145825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_145825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145825 prefixEnd_145825 := by exact prefixLift 145825
  have htrace : WordTrace (prefixWord ++ tailWord_145825) baseStart_145825 baseEnd_145825 := by
    simpa [prefixWord, tailWord_145825, baseEnd_145825] using wordTrace_append hprefix tailTrace_145825
  have hstable : (prefixWord ++ tailWord_145825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145825).length < 2 ^ (prefixWord ++ tailWord_145825).sum := by decide
  have hdescent : baseEnd_145825 < baseStart_145825 := by decide
  rcases family_descends (prefixWord ++ tailWord_145825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145829 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_145829 : Nat := 118140960795 + 145829 * 2 ^ 59
def prefixEnd_145829 : Nat := 4983230072969 + 3 ^ 40 * 145829 * 2
def baseEnd_145829 : Nat := 66560329212991268503867

theorem tailTrace_145829 : CollatzResearch.WordTrace tailWord_145829 prefixEnd_145829 66560329212991268503867 := by
  unfold tailWord_145829
  simp only [CollatzResearch.WordTrace]
  refine ⟨5318820588693913455472541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3545880392462608970315027 5318820588693913455472541)
  ·
    refine ⟨1994557720760217545802203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5318820588693913455472541 1994557720760217545802203)
    ·
      refine ⟨2991836581140326318703305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1994557720760217545802203 2991836581140326318703305)
      ·
        refine ⟨2243877435855244739027479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2991836581140326318703305 2243877435855244739027479)
        ·
          refine ⟨3365816153782867108541219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243877435855244739027479 3365816153782867108541219)
          ·
            refine ⟨5048724230674300662811829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365816153782867108541219 5048724230674300662811829)
            ·
              refine ⟨473317896625715687138609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5048724230674300662811829 473317896625715687138609)
              ·
                refine ⟨354988422469286765353957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473317896625715687138609 354988422469286765353957)
                ·
                  refine ⟨66560329212991268503867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354988422469286765353957 66560329212991268503867)
                  ·
                    rfl

theorem cell20_145829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_145829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145829 prefixEnd_145829 := by exact prefixLift 145829
  have htrace : WordTrace (prefixWord ++ tailWord_145829) baseStart_145829 baseEnd_145829 := by
    simpa [prefixWord, tailWord_145829, baseEnd_145829] using wordTrace_append hprefix tailTrace_145829
  have hstable : (prefixWord ++ tailWord_145829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145829).length < 2 ^ (prefixWord ++ tailWord_145829).sum := by decide
  have hdescent : baseEnd_145829 < baseStart_145829 := by decide
  rcases family_descends (prefixWord ++ tailWord_145829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145891 : List Nat := [1, 1, 1, 6, 3, 1, 1, 6]
def baseStart_145891 : Nat := 118140960795 + 145891 * 2 ^ 59
def prefixEnd_145891 : Nat := 4983230072969 + 3 ^ 40 * 145891 * 2
def baseEnd_145891 : Nat := 22196209234131536145649

theorem tailTrace_145891 : CollatzResearch.WordTrace tailWord_145891 prefixEnd_145891 22196209234131536145649 := by
  unfold tailWord_145891
  simp only [CollatzResearch.WordTrace]
  refine ⟨5321081914469298044229527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3547387942979532029486351 5321081914469298044229527)
  ·
    refine ⟨7981622871703947066344291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5321081914469298044229527 7981622871703947066344291)
    ·
      refine ⟨11972434307555920599516437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7981622871703947066344291 11972434307555920599516437)
      ·
        refine ⟨561207858166683778102333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11972434307555920599516437 561207858166683778102333)
        ·
          refine ⟨210452946812506416788375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 561207858166683778102333 210452946812506416788375)
          ·
            refine ⟨315679420218759625182563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210452946812506416788375 315679420218759625182563)
            ·
              refine ⟨473519130328139437773845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315679420218759625182563 473519130328139437773845)
              ·
                refine ⟨22196209234131536145649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 473519130328139437773845 22196209234131536145649)
                ·
                  rfl

theorem cell20_145891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 6].length) (baseStart_145891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145891 prefixEnd_145891 := by exact prefixLift 145891
  have htrace : WordTrace (prefixWord ++ tailWord_145891) baseStart_145891 baseEnd_145891 := by
    simpa [prefixWord, tailWord_145891, baseEnd_145891] using wordTrace_append hprefix tailTrace_145891
  have hstable : (prefixWord ++ tailWord_145891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145891).length < 2 ^ (prefixWord ++ tailWord_145891).sum := by decide
  have hdescent : baseEnd_145891 < baseStart_145891 := by decide
  rcases family_descends (prefixWord ++ tailWord_145891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145898 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_145898 : Nat := 118140960795 + 145898 * 2 ^ 59
def prefixEnd_145898 : Nat := 4983230072969 + 3 ^ 40 * 145898 * 2
def baseEnd_145898 : Nat := 66591822693133695203585

theorem tailTrace_145898 : CollatzResearch.WordTrace tailWord_145898 prefixEnd_145898 66591822693133695203585 := by
  unfold tailWord_145898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1330334306360984559933587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3547558150295958826489565 1330334306360984559933587)
  ·
    refine ⟨1995501459541476839900381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1330334306360984559933587 1995501459541476839900381)
    ·
      refine ⟨748313047328053814962643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1995501459541476839900381 748313047328053814962643)
      ·
        refine ⟨1122469570992080722443965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748313047328053814962643 1122469570992080722443965)
        ·
          refine ⟨420926089122030270916487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1122469570992080722443965 420926089122030270916487)
          ·
            refine ⟨631389133683045406374731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420926089122030270916487 631389133683045406374731)
            ·
              refine ⟨947083700524568109562097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631389133683045406374731 947083700524568109562097)
              ·
                refine ⟨710312775393426082171573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947083700524568109562097 710312775393426082171573)
                ·
                  refine ⟨66591822693133695203585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 710312775393426082171573 66591822693133695203585)
                  ·
                    rfl

theorem cell20_145898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_145898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145898 prefixEnd_145898 := by exact prefixLift 145898
  have htrace : WordTrace (prefixWord ++ tailWord_145898) baseStart_145898 baseEnd_145898 := by
    simpa [prefixWord, tailWord_145898, baseEnd_145898] using wordTrace_append hprefix tailTrace_145898
  have hstable : (prefixWord ++ tailWord_145898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145898).length < 2 ^ (prefixWord ++ tailWord_145898).sum := by decide
  have hdescent : baseEnd_145898 < baseStart_145898 := by decide
  rcases family_descends (prefixWord ++ tailWord_145898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145919 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_145919 : Nat := 118140960795 + 145919 * 2 ^ 59
def prefixEnd_145919 : Nat := 4983230072969 + 3 ^ 40 * 145919 * 2
def baseEnd_145919 : Nat := 66601407665350955503499

theorem tailTrace_145919 : CollatzResearch.WordTrace tailWord_145919 prefixEnd_145919 66601407665350955503499 := by
  unfold tailWord_145919
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322103158367858826248811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3548068772245239217499207 5322103158367858826248811)
  ·
    refine ⟨7983154737551788239373217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5322103158367858826248811 7983154737551788239373217)
    ·
      refine ⟨5987366053163841179529913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7983154737551788239373217 5987366053163841179529913)
      ·
        refine ⟨4490524539872880884647435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5987366053163841179529913 4490524539872880884647435)
        ·
          refine ⟨6735786809809321326971153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4490524539872880884647435 6735786809809321326971153)
          ·
            refine ⟨5051840107356990995228365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6735786809809321326971153 5051840107356990995228365)
            ·
              refine ⟨1894440040258871623210637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5051840107356990995228365 1894440040258871623210637)
              ·
                refine ⟨710415015097076858703989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1894440040258871623210637 710415015097076858703989)
                ·
                  refine ⟨66601407665350955503499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 710415015097076858703989 66601407665350955503499)
                  ·
                    rfl

theorem cell20_145919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_145919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145919 prefixEnd_145919 := by exact prefixLift 145919
  have htrace : WordTrace (prefixWord ++ tailWord_145919) baseStart_145919 baseEnd_145919 := by
    simpa [prefixWord, tailWord_145919, baseEnd_145919] using wordTrace_append hprefix tailTrace_145919
  have hstable : (prefixWord ++ tailWord_145919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145919).length < 2 ^ (prefixWord ++ tailWord_145919).sum := by decide
  have hdescent : baseEnd_145919 < baseStart_145919 := by decide
  rcases family_descends (prefixWord ++ tailWord_145919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145932 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 3]
def baseStart_145932 : Nat := 118140960795 + 145932 * 2 ^ 59
def prefixEnd_145932 : Nat := 4983230072969 + 3 ^ 40 * 145932 * 2
def baseEnd_145932 : Nat := 66607341219580688070113

theorem tailTrace_145932 : CollatzResearch.WordTrace tailWord_145932 prefixEnd_145932 66607341219580688070113 := by
  unfold tailWord_145932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2661288653660381023236025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3548384871547174697648033 2661288653660381023236025)
  ·
    refine ⟨1995966490245285767427019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2661288653660381023236025 1995966490245285767427019)
    ·
      refine ⟨2993949735367928651140529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1995966490245285767427019 2993949735367928651140529)
      ·
        refine ⟨2245462301525946488355397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2993949735367928651140529 2245462301525946488355397)
        ·
          refine ⟨421024181536114966566637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2245462301525946488355397 421024181536114966566637)
          ·
            refine ⟨157884068076043112462489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421024181536114966566637 157884068076043112462489)
            ·
              refine ⟨118413051057032334346867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157884068076043112462489 118413051057032334346867)
              ·
                refine ⟨177619576585548501520301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118413051057032334346867 177619576585548501520301)
                ·
                  refine ⟨66607341219580688070113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177619576585548501520301 66607341219580688070113)
                  ·
                    rfl

theorem cell20_145932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_145932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145932 prefixEnd_145932 := by exact prefixLift 145932
  have htrace : WordTrace (prefixWord ++ tailWord_145932) baseStart_145932 baseEnd_145932 := by
    simpa [prefixWord, tailWord_145932, baseEnd_145932] using wordTrace_append hprefix tailTrace_145932
  have hstable : (prefixWord ++ tailWord_145932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145932).length < 2 ^ (prefixWord ++ tailWord_145932).sum := by decide
  have hdescent : baseEnd_145932 < baseStart_145932 := by decide
  rcases family_descends (prefixWord ++ tailWord_145932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145957 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_145957 : Nat := 118140960795 + 145957 * 2 ^ 59
def prefixEnd_145957 : Nat := 4983230072969 + 3 ^ 40 * 145957 * 2
def baseEnd_145957 : Nat := 66618751900791712236677

theorem tailTrace_145957 : CollatzResearch.WordTrace tailWord_145957 prefixEnd_145957 66618751900791712236677 := by
  unfold tailWord_145957
  simp only [CollatzResearch.WordTrace]
  refine ⟨5323489132230191316132125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3548992754820127544088083 5323489132230191316132125)
  ·
    refine ⟨1996308424586321743549547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5323489132230191316132125 1996308424586321743549547)
    ·
      refine ⟨2994462636879482615324321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996308424586321743549547 2994462636879482615324321)
      ·
        refine ⟨2245846977659611961493241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2994462636879482615324321 2245846977659611961493241)
        ·
          refine ⟨1684385233244708971119931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2245846977659611961493241 1684385233244708971119931)
          ·
            refine ⟨2526577849867063456679897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684385233244708971119931 2526577849867063456679897)
            ·
              refine ⟨1894933387400297592509923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2526577849867063456679897 1894933387400297592509923)
              ·
                refine ⟨2842400081100446388764885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894933387400297592509923 2842400081100446388764885)
                ·
                  refine ⟨66618751900791712236677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2842400081100446388764885 66618751900791712236677)
                  ·
                    rfl

theorem cell20_145957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_145957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_145957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_145957 prefixEnd_145957 := by exact prefixLift 145957
  have htrace : WordTrace (prefixWord ++ tailWord_145957) baseStart_145957 baseEnd_145957 := by
    simpa [prefixWord, tailWord_145957, baseEnd_145957] using wordTrace_append hprefix tailTrace_145957
  have hstable : (prefixWord ++ tailWord_145957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145957).length < 2 ^ (prefixWord ++ tailWord_145957).sum := by decide
  have hdescent : baseEnd_145957 < baseStart_145957 := by decide
  rcases family_descends (prefixWord ++ tailWord_145957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146026 : List Nat := [3, 1, 3, 2, 1, 1, 9]
def baseStart_146026 : Nat := 118140960795 + 146026 * 2 ^ 59
def prefixEnd_146026 : Nat := 4983230072969 + 3 ^ 40 * 146026 * 2
def baseEnd_146026 : Nat := 7405582820103793215155

theorem tailTrace_146026 : CollatzResearch.WordTrace tailWord_146026 prefixEnd_146026 7405582820103793215155 := by
  unfold tailWord_146026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1331501442245054025098483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3550670512653477400262621 1331501442245054025098483)
  ·
    refine ⟨1997252163367581037647725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1331501442245054025098483 1997252163367581037647725)
    ·
      refine ⟨748969561262842889117897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1997252163367581037647725 748969561262842889117897)
      ·
        refine ⟨561727170947132166838423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 748969561262842889117897 561727170947132166838423)
        ·
          refine ⟨842590756420698250257635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561727170947132166838423 842590756420698250257635)
          ·
            refine ⟨1263886134631047375386453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842590756420698250257635 1263886134631047375386453)
            ·
              refine ⟨7405582820103793215155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1263886134631047375386453 7405582820103793215155)
              ·
                rfl

theorem cell20_146026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 9].length) (baseStart_146026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146026 prefixEnd_146026 := by exact prefixLift 146026
  have htrace : WordTrace (prefixWord ++ tailWord_146026) baseStart_146026 baseEnd_146026 := by
    simpa [prefixWord, tailWord_146026, baseEnd_146026] using wordTrace_append hprefix tailTrace_146026
  have hstable : (prefixWord ++ tailWord_146026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146026).length < 2 ^ (prefixWord ++ tailWord_146026).sum := by decide
  have hdescent : baseEnd_146026 < baseStart_146026 := by decide
  rcases family_descends (prefixWord ++ tailWord_146026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146029 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 3]
def baseStart_146029 : Nat := 118140960795 + 146029 * 2 ^ 59
def prefixEnd_146029 : Nat := 4983230072969 + 3 ^ 40 * 146029 * 2
def baseEnd_146029 : Nat := 66651614662679461836383

theorem tailTrace_146029 : CollatzResearch.WordTrace tailWord_146029 prefixEnd_146029 66651614662679461836383 := by
  unfold tailWord_146029
  simp only [CollatzResearch.WordTrace]
  refine ⟨5326115187969347612753141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3550743458646231741835427 5326115187969347612753141)
  ·
    refine ⟨499323298872126338695607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5326115187969347612753141 499323298872126338695607)
    ·
      refine ⟨748984948308189508043411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499323298872126338695607 748984948308189508043411)
      ·
        refine ⟨1123477422462284262065117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748984948308189508043411 1123477422462284262065117)
        ·
          refine ⟨421304033423356598274419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1123477422462284262065117 421304033423356598274419)
          ·
            refine ⟨631956050135034897411629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421304033423356598274419 631956050135034897411629)
            ·
              refine ⟨236983518800638086529361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 631956050135034897411629 236983518800638086529361)
              ·
                refine ⟨177737639100478564897021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236983518800638086529361 177737639100478564897021)
                ·
                  refine ⟨66651614662679461836383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177737639100478564897021 66651614662679461836383)
                  ·
                    rfl

theorem cell20_146029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_146029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146029 prefixEnd_146029 := by exact prefixLift 146029
  have htrace : WordTrace (prefixWord ++ tailWord_146029) baseStart_146029 baseEnd_146029 := by
    simpa [prefixWord, tailWord_146029, baseEnd_146029] using wordTrace_append hprefix tailTrace_146029
  have hstable : (prefixWord ++ tailWord_146029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146029).length < 2 ^ (prefixWord ++ tailWord_146029).sum := by decide
  have hdescent : baseEnd_146029 < baseStart_146029 := by decide
  rcases family_descends (prefixWord ++ tailWord_146029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146040 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_146040 : Nat := 118140960795 + 146040 * 2 ^ 59
def prefixEnd_146040 : Nat := 4983230072969 + 3 ^ 40 * 146040 * 2
def baseEnd_146040 : Nat := 66656635362412312469671

theorem tailTrace_146040 : CollatzResearch.WordTrace tailWord_146040 prefixEnd_146040 66656635362412312469671 := by
  unfold tailWord_146040
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663258195464748245701787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3551010927286330994269049 2663258195464748245701787)
  ·
    refine ⟨3994887293197122368552681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2663258195464748245701787 3994887293197122368552681)
    ·
      refine ⟨2996165469897841776414511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3994887293197122368552681 2996165469897841776414511)
      ·
        refine ⟨4494248204846762664621767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2996165469897841776414511 4494248204846762664621767)
        ·
          refine ⟨6741372307270143996932651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4494248204846762664621767 6741372307270143996932651)
          ·
            refine ⟨10112058460905215995398977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6741372307270143996932651 10112058460905215995398977)
            ·
              refine ⟨7584043845678911996549233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10112058460905215995398977 7584043845678911996549233)
              ·
                refine ⟨5688032884259183997411925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7584043845678911996549233 5688032884259183997411925)
                ·
                  refine ⟨66656635362412312469671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5688032884259183997411925 66656635362412312469671)
                  ·
                    rfl

theorem cell20_146040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_146040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146040 prefixEnd_146040 := by exact prefixLift 146040
  have htrace : WordTrace (prefixWord ++ tailWord_146040) baseStart_146040 baseEnd_146040 := by
    simpa [prefixWord, tailWord_146040, baseEnd_146040] using wordTrace_append hprefix tailTrace_146040
  have hstable : (prefixWord ++ tailWord_146040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146040).length < 2 ^ (prefixWord ++ tailWord_146040).sum := by decide
  have hdescent : baseEnd_146040 < baseStart_146040 := by decide
  rcases family_descends (prefixWord ++ tailWord_146040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146071 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_146071 : Nat := 118140960795 + 146071 * 2 ^ 59
def prefixEnd_146071 : Nat := 4983230072969 + 3 ^ 40 * 146071 * 2
def baseEnd_146071 : Nat := 66670784607113982436211

theorem tailTrace_146071 : CollatzResearch.WordTrace tailWord_146071 prefixEnd_146071 66670784607113982436211 := by
  unfold tailWord_146071
  simp only [CollatzResearch.WordTrace]
  refine ⟨5327647053817188785782067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3551764702544792523854711 5327647053817188785782067)
  ·
    refine ⟨7991470580725783178673101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5327647053817188785782067 7991470580725783178673101)
    ·
      refine ⟨2996801467772168692002413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7991470580725783178673101 2996801467772168692002413)
      ·
        refine ⟨1123800550414563259500905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2996801467772168692002413 1123800550414563259500905)
        ·
          refine ⟨842850412810922444625679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1123800550414563259500905 842850412810922444625679)
          ·
            refine ⟨1264275619216383666938519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842850412810922444625679 1264275619216383666938519)
            ·
              refine ⟨1896413428824575500407779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264275619216383666938519 1896413428824575500407779)
              ·
                refine ⟨2844620143236863250611669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896413428824575500407779 2844620143236863250611669)
                ·
                  refine ⟨66670784607113982436211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2844620143236863250611669 66670784607113982436211)
                  ·
                    rfl

theorem cell20_146071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_146071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146071 prefixEnd_146071 := by exact prefixLift 146071
  have htrace : WordTrace (prefixWord ++ tailWord_146071) baseStart_146071 baseEnd_146071 := by
    simpa [prefixWord, tailWord_146071, baseEnd_146071] using wordTrace_append hprefix tailTrace_146071
  have hstable : (prefixWord ++ tailWord_146071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146071).length < 2 ^ (prefixWord ++ tailWord_146071).sum := by decide
  have hdescent : baseEnd_146071 < baseStart_146071 := by decide
  rcases family_descends (prefixWord ++ tailWord_146071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146081 : List Nat := [1, 2, 3, 3, 3, 2, 6]
def baseStart_146081 : Nat := 118140960795 + 146081 * 2 ^ 59
def prefixEnd_146081 : Nat := 4983230072969 + 3 ^ 40 * 146081 * 2
def baseEnd_146081 : Nat := 7408372097733154678093

theorem tailTrace_146081 : CollatzResearch.WordTrace tailWord_146081 prefixEnd_146081 7408372097733154678093 := by
  unfold tailWord_146081
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328011783780960493646097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3552007855853973662430731 5328011783780960493646097)
  ·
    refine ⟨3996008837835720370234573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5328011783780960493646097 3996008837835720370234573)
    ·
      refine ⟨1498503314188395138837965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3996008837835720370234573 1498503314188395138837965)
      ·
        refine ⟨561938742820648177064237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1498503314188395138837965 561938742820648177064237)
        ·
          refine ⟨210727028557743066399089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 561938742820648177064237 210727028557743066399089)
          ·
            refine ⟨158045271418307299799317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210727028557743066399089 158045271418307299799317)
            ·
              refine ⟨7408372097733154678093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158045271418307299799317 7408372097733154678093)
              ·
                rfl

theorem cell20_146081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 6].length) (baseStart_146081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146081 prefixEnd_146081 := by exact prefixLift 146081
  have htrace : WordTrace (prefixWord ++ tailWord_146081) baseStart_146081 baseEnd_146081 := by
    simpa [prefixWord, tailWord_146081, baseEnd_146081] using wordTrace_append hprefix tailTrace_146081
  have hstable : (prefixWord ++ tailWord_146081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146081).length < 2 ^ (prefixWord ++ tailWord_146081).sum := by decide
  have hdescent : baseEnd_146081 < baseStart_146081 := by decide
  rcases family_descends (prefixWord ++ tailWord_146081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146087 : List Nat := [1, 1, 6, 3, 1, 1, 3, 2, 2]
def baseStart_146087 : Nat := 118140960795 + 146087 * 2 ^ 59
def prefixEnd_146087 : Nat := 4983230072969 + 3 ^ 40 * 146087 * 2
def baseEnd_146087 : Nat := 66678087443089037902813

theorem tailTrace_146087 : CollatzResearch.WordTrace tailWord_146087 prefixEnd_146087 66678087443089037902813 := by
  unfold tailWord_146087
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328230621759223518364515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3552153747839482345576343 5328230621759223518364515)
  ·
    refine ⟨7992345932638835277546773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5328230621759223518364515 7992345932638835277546773)
    ·
      refine ⟨374641215592445403635005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7992345932638835277546773 374641215592445403635005)
      ·
        refine ⟨140490455847167026363127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 374641215592445403635005 140490455847167026363127)
        ·
          refine ⟨210735683770750539544691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140490455847167026363127 210735683770750539544691)
          ·
            refine ⟨316103525656125809317037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210735683770750539544691 316103525656125809317037)
            ·
              refine ⟨118538822121047178493889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316103525656125809317037 118538822121047178493889)
              ·
                refine ⟨88904116590785383870417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118538822121047178493889 88904116590785383870417)
                ·
                  refine ⟨66678087443089037902813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88904116590785383870417 66678087443089037902813)
                  ·
                    rfl

theorem cell20_146087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 2].length) (baseStart_146087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146087 prefixEnd_146087 := by exact prefixLift 146087
  have htrace : WordTrace (prefixWord ++ tailWord_146087) baseStart_146087 baseEnd_146087 := by
    simpa [prefixWord, tailWord_146087, baseEnd_146087] using wordTrace_append hprefix tailTrace_146087
  have hstable : (prefixWord ++ tailWord_146087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146087).length < 2 ^ (prefixWord ++ tailWord_146087).sum := by decide
  have hdescent : baseEnd_146087 < baseStart_146087 := by decide
  rcases family_descends (prefixWord ++ tailWord_146087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146095 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 4]
def baseStart_146095 : Nat := 118140960795 + 146095 * 2 ^ 59
def prefixEnd_146095 : Nat := 4983230072969 + 3 ^ 40 * 146095 * 2
def baseEnd_146095 : Nat := 66681738861076565636113

theorem tailTrace_146095 : CollatzResearch.WordTrace tailWord_146095 prefixEnd_146095 66681738861076565636113 := by
  unfold tailWord_146095
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328522405730240884655739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3552348270486827256437159 5328522405730240884655739)
  ·
    refine ⟨7992783608595361326983609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5328522405730240884655739 7992783608595361326983609)
    ·
      refine ⟨5994587706446520995237707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7992783608595361326983609 5994587706446520995237707)
      ·
        refine ⟨8991881559669781492856561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5994587706446520995237707 8991881559669781492856561)
        ·
          refine ⟨6743911169752336119642421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8991881559669781492856561 6743911169752336119642421)
          ·
            refine ⟨632241672164281511216477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6743911169752336119642421 632241672164281511216477)
            ·
              refine ⟨237090627061605566706179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 632241672164281511216477 237090627061605566706179)
              ·
                refine ⟨355635940592408350059269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237090627061605566706179 355635940592408350059269)
                ·
                  refine ⟨66681738861076565636113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355635940592408350059269 66681738861076565636113)
                  ·
                    rfl

theorem cell20_146095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_146095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146095 prefixEnd_146095 := by exact prefixLift 146095
  have htrace : WordTrace (prefixWord ++ tailWord_146095) baseStart_146095 baseEnd_146095 := by
    simpa [prefixWord, tailWord_146095, baseEnd_146095] using wordTrace_append hprefix tailTrace_146095
  have hstable : (prefixWord ++ tailWord_146095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146095).length < 2 ^ (prefixWord ++ tailWord_146095).sum := by decide
  have hdescent : baseEnd_146095 < baseStart_146095 := by decide
  rcases family_descends (prefixWord ++ tailWord_146095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146174 : List Nat := [4, 2, 2, 1, 2, 2, 3, 4]
def baseStart_146174 : Nat := 118140960795 + 146174 * 2 ^ 59
def prefixEnd_146174 : Nat := 4983230072969 + 3 ^ 40 * 146174 * 2
def baseEnd_146174 : Nat := 22239265537901134000819

theorem tailTrace_146174 : CollatzResearch.WordTrace tailWord_146174 prefixEnd_146174 22239265537901134000819 := by
  unfold tailWord_146174
  simp only [CollatzResearch.WordTrace]
  refine ⟨666425471555504672097697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3554269181629358251187717 666425471555504672097697)
  ·
    refine ⟨499819103666628504073273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 666425471555504672097697 499819103666628504073273)
    ·
      refine ⟨374864327749971378054955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 499819103666628504073273 374864327749971378054955)
      ·
        refine ⟨562296491624957067082433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374864327749971378054955 562296491624957067082433)
        ·
          refine ⟨421722368718717800311825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562296491624957067082433 421722368718717800311825)
          ·
            refine ⟨316291776539038350233869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421722368718717800311825 316291776539038350233869)
            ·
              refine ⟨118609416202139381337701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316291776539038350233869 118609416202139381337701)
              ·
                refine ⟨22239265537901134000819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118609416202139381337701 22239265537901134000819)
                ·
                  rfl

theorem cell20_146174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_146174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146174 prefixEnd_146174 := by exact prefixLift 146174
  have htrace : WordTrace (prefixWord ++ tailWord_146174) baseStart_146174 baseEnd_146174 := by
    simpa [prefixWord, tailWord_146174, baseEnd_146174] using wordTrace_append hprefix tailTrace_146174
  have hstable : (prefixWord ++ tailWord_146174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146174).length < 2 ^ (prefixWord ++ tailWord_146174).sum := by decide
  have hdescent : baseEnd_146174 < baseStart_146174 := by decide
  rcases family_descends (prefixWord ++ tailWord_146174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146205 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 4]
def baseStart_146205 : Nat := 118140960795 + 146205 * 2 ^ 59
def prefixEnd_146205 : Nat := 4983230072969 + 3 ^ 40 * 146205 * 2
def baseEnd_146205 : Nat := 66731945858405071968997

theorem tailTrace_146205 : CollatzResearch.WordTrace tailWord_146205 prefixEnd_146205 66731945858405071968997 := by
  unfold tailWord_146205
  simp only [CollatzResearch.WordTrace]
  refine ⟨5332534435331729671160069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3555022956887819780773379 5332534435331729671160069)
  ·
    refine ⟨999850206624699313342513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5332534435331729671160069 999850206624699313342513)
    ·
      refine ⟨749887654968524485006885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 999850206624699313342513 749887654968524485006885)
      ·
        refine ⟨140603935306598340938791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 749887654968524485006885 140603935306598340938791)
        ·
          refine ⟨210905902959897511408187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140603935306598340938791 210905902959897511408187)
          ·
            refine ⟨316358854439846267112281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210905902959897511408187 316358854439846267112281)
            ·
              refine ⟨237269140829884700334211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316358854439846267112281 237269140829884700334211)
              ·
                refine ⟨355903711244827050501317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237269140829884700334211 355903711244827050501317)
                ·
                  refine ⟨66731945858405071968997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355903711244827050501317 66731945858405071968997)
                  ·
                    rfl

theorem cell20_146205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_146205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146205 prefixEnd_146205 := by exact prefixLift 146205
  have htrace : WordTrace (prefixWord ++ tailWord_146205) baseStart_146205 baseEnd_146205 := by
    simpa [prefixWord, tailWord_146205, baseEnd_146205] using wordTrace_append hprefix tailTrace_146205
  have hstable : (prefixWord ++ tailWord_146205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146205).length < 2 ^ (prefixWord ++ tailWord_146205).sum := by decide
  have hdescent : baseEnd_146205 < baseStart_146205 := by decide
  rcases family_descends (prefixWord ++ tailWord_146205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146209 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 4]
def baseStart_146209 : Nat := 118140960795 + 146209 * 2 ^ 59
def prefixEnd_146209 : Nat := 4983230072969 + 3 ^ 40 * 146209 * 2
def baseEnd_146209 : Nat := 66733771567398835835647

theorem tailTrace_146209 : CollatzResearch.WordTrace tailWord_146209 prefixEnd_146209 66733771567398835835647 := by
  unfold tailWord_146209
  simp only [CollatzResearch.WordTrace]
  refine ⟨5332680327317238354305681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3555120218211492236203787 5332680327317238354305681)
  ·
    refine ⟨3999510245487928765729261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5332680327317238354305681 3999510245487928765729261)
    ·
      refine ⟨1499816342057973287148473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3999510245487928765729261 1499816342057973287148473)
      ·
        refine ⟨1124862256543479965361355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1499816342057973287148473 1124862256543479965361355)
        ·
          refine ⟨1687293384815219948042033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124862256543479965361355 1687293384815219948042033)
          ·
            refine ⟨1265470038611414961031525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687293384815219948042033 1265470038611414961031525)
            ·
              refine ⟨237275632239640305193411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1265470038611414961031525 237275632239640305193411)
              ·
                refine ⟨355913448359460457790117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237275632239640305193411 355913448359460457790117)
                ·
                  refine ⟨66733771567398835835647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355913448359460457790117 66733771567398835835647)
                  ·
                    rfl

theorem cell20_146209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_146209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146209 prefixEnd_146209 := by exact prefixLift 146209
  have htrace : WordTrace (prefixWord ++ tailWord_146209) baseStart_146209 baseEnd_146209 := by
    simpa [prefixWord, tailWord_146209, baseEnd_146209] using wordTrace_append hprefix tailTrace_146209
  have hstable : (prefixWord ++ tailWord_146209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146209).length < 2 ^ (prefixWord ++ tailWord_146209).sum := by decide
  have hdescent : baseEnd_146209 < baseStart_146209 := by decide
  rcases family_descends (prefixWord ++ tailWord_146209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146216 : List Nat := [2, 1, 5, 1, 1, 1, 2, 7]
def baseStart_146216 : Nat := 118140960795 + 146216 * 2 ^ 59
def prefixEnd_146216 : Nat := 4983230072969 + 3 ^ 40 * 146216 * 2
def baseEnd_146216 : Nat := 22245655519379307534095

theorem tailTrace_146216 : CollatzResearch.WordTrace tailWord_146216 prefixEnd_146216 22245655519379307534095 := by
  unfold tailWord_146216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2666467819145939274905251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3555290425527919033207001 2666467819145939274905251)
  ·
    refine ⟨3999701728718908912357877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2666467819145939274905251 3999701728718908912357877)
    ·
      refine ⟨374972037067397710533551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3999701728718908912357877 374972037067397710533551)
      ·
        refine ⟨562458055601096565800327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374972037067397710533551 562458055601096565800327)
        ·
          refine ⟨843687083401644848700491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562458055601096565800327 843687083401644848700491)
          ·
            refine ⟨1265530625102467273050737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843687083401644848700491 1265530625102467273050737)
            ·
              refine ⟨949147968826850454788053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265530625102467273050737 949147968826850454788053)
              ·
                refine ⟨22245655519379307534095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 949147968826850454788053 22245655519379307534095)
                ·
                  rfl

theorem cell20_146216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_146216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146216 prefixEnd_146216 := by exact prefixLift 146216
  have htrace : WordTrace (prefixWord ++ tailWord_146216) baseStart_146216 baseEnd_146216 := by
    simpa [prefixWord, tailWord_146216, baseEnd_146216] using wordTrace_append hprefix tailTrace_146216
  have hstable : (prefixWord ++ tailWord_146216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146216).length < 2 ^ (prefixWord ++ tailWord_146216).sum := by decide
  have hdescent : baseEnd_146216 < baseStart_146216 := by decide
  rcases family_descends (prefixWord ++ tailWord_146216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146260 : List Nat := [2, 4, 1, 1, 4, 1, 3, 2, 2]
def baseStart_146260 : Nat := 118140960795 + 146260 * 2 ^ 59
def prefixEnd_146260 : Nat := 4983230072969 + 3 ^ 40 * 146260 * 2
def baseEnd_146260 : Nat := 66757049357069325135439

theorem tailTrace_146260 : CollatzResearch.WordTrace tailWord_146260 prefixEnd_146260 66757049357069325135439 := by
  unfold tailWord_146260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667270225066237032206117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3556360300088316042941489 2667270225066237032206117)
  ·
    refine ⟨500113167199919443538647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2667270225066237032206117 500113167199919443538647)
    ·
      refine ⟨750169750799879165307971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 500113167199919443538647 750169750799879165307971)
      ·
        refine ⟨1125254626199818747961957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 750169750799879165307971 1125254626199818747961957)
        ·
          refine ⟨210985242412466015242867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1125254626199818747961957 210985242412466015242867)
          ·
            refine ⟨316477863618699022864301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210985242412466015242867 316477863618699022864301)
            ·
              refine ⟨118679198857012133574113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316477863618699022864301 118679198857012133574113)
              ·
                refine ⟨89009399142759100180585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118679198857012133574113 89009399142759100180585)
                ·
                  refine ⟨66757049357069325135439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89009399142759100180585 66757049357069325135439)
                  ·
                    rfl

theorem cell20_146260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_146260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146260 prefixEnd_146260 := by exact prefixLift 146260
  have htrace : WordTrace (prefixWord ++ tailWord_146260) baseStart_146260 baseEnd_146260 := by
    simpa [prefixWord, tailWord_146260, baseEnd_146260] using wordTrace_append hprefix tailTrace_146260
  have hstable : (prefixWord ++ tailWord_146260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146260).length < 2 ^ (prefixWord ++ tailWord_146260).sum := by decide
  have hdescent : baseEnd_146260 < baseStart_146260 := by decide
  rcases family_descends (prefixWord ++ tailWord_146260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146261 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_146261 : Nat := 118140960795 + 146261 * 2 ^ 59
def prefixEnd_146261 : Nat := 4983230072969 + 3 ^ 40 * 146261 * 2
def baseEnd_146261 : Nat := 66757505784317766102101

theorem tailTrace_146261 : CollatzResearch.WordTrace tailWord_146261 prefixEnd_146261 66757505784317766102101 := by
  unfold tailWord_146261
  simp only [CollatzResearch.WordTrace]
  refine ⟨5334576923128851235198637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3556384615419234156799091 5334576923128851235198637)
  ·
    refine ⟨2000466346173319213199489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5334576923128851235198637 2000466346173319213199489)
    ·
      refine ⟨1500349759629989409899617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2000466346173319213199489 1500349759629989409899617)
      ·
        refine ⟨1125262319722492057424713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1500349759629989409899617 1125262319722492057424713)
        ·
          refine ⟨843946739791869043068535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1125262319722492057424713 843946739791869043068535)
          ·
            refine ⟨1265920109687803564602803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843946739791869043068535 1265920109687803564602803)
            ·
              refine ⟨1898880164531705346904205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265920109687803564602803 1898880164531705346904205)
              ·
                refine ⟨712080061699389505089077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898880164531705346904205 712080061699389505089077)
                ·
                  refine ⟨66757505784317766102101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 712080061699389505089077 66757505784317766102101)
                  ·
                    rfl

theorem cell20_146261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_146261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146261 prefixEnd_146261 := by exact prefixLift 146261
  have htrace : WordTrace (prefixWord ++ tailWord_146261) baseStart_146261 baseEnd_146261 := by
    simpa [prefixWord, tailWord_146261, baseEnd_146261] using wordTrace_append hprefix tailTrace_146261
  have hstable : (prefixWord ++ tailWord_146261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146261).length < 2 ^ (prefixWord ++ tailWord_146261).sum := by decide
  have hdescent : baseEnd_146261 < baseStart_146261 := by decide
  rcases family_descends (prefixWord ++ tailWord_146261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146313 : List Nat := [1, 2, 1, 1, 5, 10]
def baseStart_146313 : Nat := 118140960795 + 146313 * 2 ^ 59
def prefixEnd_146313 : Nat := 4983230072969 + 3 ^ 40 * 146313 * 2
def baseEnd_146313 : Nat := 2473379259305062828465

theorem tailTrace_146313 : CollatzResearch.WordTrace tailWord_146313 prefixEnd_146313 2473379259305062828465 := by
  unfold tailWord_146313
  simp only [CollatzResearch.WordTrace]
  refine ⟨5336473518940464116091593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3557649012626976077394395 5336473518940464116091593)
  ·
    refine ⟨4002355139205348087068695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5336473518940464116091593 4002355139205348087068695)
    ·
      refine ⟨6003532708808022130603043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4002355139205348087068695 6003532708808022130603043)
      ·
        refine ⟨9005299063212033195904565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6003532708808022130603043 9005299063212033195904565)
        ·
          refine ⟨844246787176128112116053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9005299063212033195904565 844246787176128112116053)
          ·
            refine ⟨2473379259305062828465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 844246787176128112116053 2473379259305062828465)
            ·
              rfl

theorem cell20_146313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 10].length) (baseStart_146313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_146313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_146313 prefixEnd_146313 := by exact prefixLift 146313
  have htrace : WordTrace (prefixWord ++ tailWord_146313) baseStart_146313 baseEnd_146313 := by
    simpa [prefixWord, tailWord_146313, baseEnd_146313] using wordTrace_append hprefix tailTrace_146313
  have hstable : (prefixWord ++ tailWord_146313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146313).length < 2 ^ (prefixWord ++ tailWord_146313).sum := by decide
  have hdescent : baseEnd_146313 < baseStart_146313 := by decide
  rcases family_descends (prefixWord ++ tailWord_146313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
