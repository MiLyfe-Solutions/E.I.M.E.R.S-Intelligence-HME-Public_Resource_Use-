import V185TrunkScan19Chunk041

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_421958 : List Nat := [6, 1, 1, 1, 1, 1, 4, 4]
def baseStart_421958 : Nat := 118140960795 + 421958 * 2 ^ 59
def prefixEnd_421958 : Nat := 4983230072969 + 3 ^ 40 * 421958 * 2
def baseEnd_421958 : Nat := 128395419265164634716715

theorem tailTrace_421958 : CollatzResearch.WordTrace tailWord_421958 prefixEnd_421958 128395419265164634716715 := by
  unfold tailWord_421958
  simp only [CollatzResearch.WordTrace]
  refine ⟨480939768916428297942079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10260048403550470356097685 480939768916428297942079)
  ·
    refine ⟨721409653374642446913119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 480939768916428297942079 721409653374642446913119)
    ·
      refine ⟨1082114480061963670369679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 721409653374642446913119 1082114480061963670369679)
      ·
        refine ⟨1623171720092945505554519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082114480061963670369679 1623171720092945505554519)
        ·
          refine ⟨2434757580139418258331779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623171720092945505554519 2434757580139418258331779)
          ·
            refine ⟨3652136370209127387497669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434757580139418258331779 3652136370209127387497669)
            ·
              refine ⟨684775569414211385155813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3652136370209127387497669 684775569414211385155813)
              ·
                refine ⟨128395419265164634716715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 684775569414211385155813 128395419265164634716715)
                ·
                  rfl

theorem cell19_421958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_421958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_421958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_421958 prefixEnd_421958 := by exact prefixLift 421958
  have htrace : WordTrace (prefixWord ++ tailWord_421958) baseStart_421958 baseEnd_421958 := by
    simpa [prefixWord, tailWord_421958, baseEnd_421958] using wordTrace_append hprefix tailTrace_421958
  have hstable : (prefixWord ++ tailWord_421958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421958).length < 2 ^ (prefixWord ++ tailWord_421958).sum := by decide
  have hdescent : baseEnd_421958 < baseStart_421958 := by decide
  rcases family_descends (prefixWord ++ tailWord_421958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422019 : List Nat := [1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_422019 : Nat := 118140960795 + 422019 * 2 ^ 59
def prefixEnd_422019 : Nat := 4983230072969 + 3 ^ 40 * 422019 * 2
def baseEnd_422019 : Nat := 128413980639934567360993

theorem tailTrace_422019 : CollatzResearch.WordTrace tailWord_422019 prefixEnd_422019 128413980639934567360993 := by
  unfold tailWord_422019
  simp only [CollatzResearch.WordTrace]
  refine ⟨15392297458104712952117111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10261531638736475301411407 15392297458104712952117111)
  ·
    refine ⟨23088446187157069428175667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15392297458104712952117111 23088446187157069428175667)
    ·
      refine ⟨34632669280735604142263501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23088446187157069428175667 34632669280735604142263501)
      ·
        refine ⟨12987250980275851553348813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34632669280735604142263501 12987250980275851553348813)
        ·
          refine ⟨4870219117603444332505805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12987250980275851553348813 4870219117603444332505805)
          ·
            refine ⟨1826332169101291624689677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4870219117603444332505805 1826332169101291624689677)
            ·
              refine ⟨684874563412984359258629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1826332169101291624689677 684874563412984359258629)
              ·
                refine ⟨128413980639934567360993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 684874563412984359258629 128413980639934567360993)
                ·
                  rfl

theorem cell19_422019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_422019 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422019 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422019 prefixEnd_422019 := by exact prefixLift 422019
  have htrace : WordTrace (prefixWord ++ tailWord_422019) baseStart_422019 baseEnd_422019 := by
    simpa [prefixWord, tailWord_422019, baseEnd_422019] using wordTrace_append hprefix tailTrace_422019
  have hstable : (prefixWord ++ tailWord_422019).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422019).length < 2 ^ (prefixWord ++ tailWord_422019).sum := by decide
  have hdescent : baseEnd_422019 < baseStart_422019 := by decide
  rcases family_descends (prefixWord ++ tailWord_422019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422055 : List Nat := [1, 1, 6, 2, 2, 1, 6]
def baseStart_422055 : Nat := 118140960795 + 422055 * 2 ^ 59
def prefixEnd_422055 : Nat := 4983230072969 + 3 ^ 40 * 422055 * 2
def baseEnd_422055 : Nat := 42808311631299050186965

theorem tailTrace_422055 : CollatzResearch.WordTrace tailWord_422055 prefixEnd_422055 42808311631299050186965 := by
  unfold tailWord_422055
  simp only [CollatzResearch.WordTrace]
  refine ⟨15393610485974291100427619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10262406990649527400285079 15393610485974291100427619)
  ·
    refine ⟨23090415728961436650641429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15393610485974291100427619 23090415728961436650641429)
    ·
      refine ⟨1082363237295067342998817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23090415728961436650641429 1082363237295067342998817)
      ·
        refine ⟨811772427971300507249113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1082363237295067342998817 811772427971300507249113)
        ·
          refine ⟨608829320978475380436835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 811772427971300507249113 608829320978475380436835)
          ·
            refine ⟨913243981467713070655253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608829320978475380436835 913243981467713070655253)
            ·
              refine ⟨42808311631299050186965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 913243981467713070655253 42808311631299050186965)
              ·
                rfl

theorem cell19_422055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_422055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422055 prefixEnd_422055 := by exact prefixLift 422055
  have htrace : WordTrace (prefixWord ++ tailWord_422055) baseStart_422055 baseEnd_422055 := by
    simpa [prefixWord, tailWord_422055, baseEnd_422055] using wordTrace_append hprefix tailTrace_422055
  have hstable : (prefixWord ++ tailWord_422055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422055).length < 2 ^ (prefixWord ++ tailWord_422055).sum := by decide
  have hdescent : baseEnd_422055 < baseStart_422055 := by decide
  rcases family_descends (prefixWord ++ tailWord_422055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422108 : List Nat := [2, 2, 5, 2, 2, 1, 5]
def baseStart_422108 : Nat := 118140960795 + 422108 * 2 ^ 59
def prefixEnd_422108 : Nat := 4983230072969 + 3 ^ 40 * 422108 * 2
def baseEnd_422108 : Nat := 42813687330002910460991

theorem tailTrace_422108 : CollatzResearch.WordTrace tailWord_422108 prefixEnd_422108 42813687330002910460991 := by
  unfold tailWord_422108
  simp only [CollatzResearch.WordTrace]
  refine ⟨7697771777391140576053489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10263695703188187434737985 7697771777391140576053489)
  ·
    refine ⟨5773328833043355432040117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7697771777391140576053489 5773328833043355432040117)
    ·
      refine ⟨541249578097814571753761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5773328833043355432040117 541249578097814571753761)
      ·
        refine ⟨405937183573360928815321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541249578097814571753761 405937183573360928815321)
        ·
          refine ⟨304452887680020696611491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405937183573360928815321 304452887680020696611491)
          ·
            refine ⟨456679331520031044917237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304452887680020696611491 456679331520031044917237)
            ·
              refine ⟨42813687330002910460991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 456679331520031044917237 42813687330002910460991)
              ·
                rfl

theorem cell19_422108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 5].length) (baseStart_422108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422108 prefixEnd_422108 := by exact prefixLift 422108
  have htrace : WordTrace (prefixWord ++ tailWord_422108) baseStart_422108 baseEnd_422108 := by
    simpa [prefixWord, tailWord_422108, baseEnd_422108] using wordTrace_append hprefix tailTrace_422108
  have hstable : (prefixWord ++ tailWord_422108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422108).length < 2 ^ (prefixWord ++ tailWord_422108).sum := by decide
  have hdescent : baseEnd_422108 < baseStart_422108 := by decide
  rcases family_descends (prefixWord ++ tailWord_422108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422152 : List Nat := [2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_422152 : Nat := 118140960795 + 422152 * 2 ^ 59
def prefixEnd_422152 : Nat := 4983230072969 + 3 ^ 40 * 422152 * 2
def baseEnd_422152 : Nat := 128454450522629666405075

theorem tailTrace_422152 : CollatzResearch.WordTrace tailWord_422152 prefixEnd_422152 128454450522629666405075 := by
  unfold tailWord_422152
  simp only [CollatzResearch.WordTrace]
  refine ⟨7698574183311438333354355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10264765577748584444472473 7698574183311438333354355)
  ·
    refine ⟨11547861274967157500031533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7698574183311438333354355 11547861274967157500031533)
    ·
      refine ⟨4330447978112684062511825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11547861274967157500031533 4330447978112684062511825)
      ·
        refine ⟨3247835983584513046883869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4330447978112684062511825 3247835983584513046883869)
        ·
          refine ⟨1217938493844192392581451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3247835983584513046883869 1217938493844192392581451)
          ·
            refine ⟨1826907740766288588872177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217938493844192392581451 1826907740766288588872177)
            ·
              refine ⟨1370180805574716441654133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826907740766288588872177 1370180805574716441654133)
              ·
                refine ⟨128454450522629666405075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1370180805574716441654133 128454450522629666405075)
                ·
                  rfl

theorem cell19_422152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_422152 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422152 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422152 prefixEnd_422152 := by exact prefixLift 422152
  have htrace : WordTrace (prefixWord ++ tailWord_422152) baseStart_422152 baseEnd_422152 := by
    simpa [prefixWord, tailWord_422152, baseEnd_422152] using wordTrace_append hprefix tailTrace_422152
  have hstable : (prefixWord ++ tailWord_422152).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422152).length < 2 ^ (prefixWord ++ tailWord_422152).sum := by decide
  have hdescent : baseEnd_422152 < baseStart_422152 := by decide
  rcases family_descends (prefixWord ++ tailWord_422152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422186 : List Nat := [3, 1, 4, 2, 2, 2, 1, 4]
def baseStart_422186 : Nat := 118140960795 + 422186 * 2 ^ 59
def prefixEnd_422186 : Nat := 4983230072969 + 3 ^ 40 * 422186 * 2
def baseEnd_422186 : Nat := 128464796206927661649427

theorem tailTrace_422186 : CollatzResearch.WordTrace tailWord_422186 prefixEnd_422186 128464796206927661649427 := by
  unfold tailWord_422186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849597112124925118361603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10265592298999800315630941 3849597112124925118361603)
  ·
    refine ⟨5774395668187387677542405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3849597112124925118361603 5774395668187387677542405)
    ·
      refine ⟨1082699187785135189539201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5774395668187387677542405 1082699187785135189539201)
      ·
        refine ⟨812024390838851392154401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1082699187785135189539201 812024390838851392154401)
        ·
          refine ⟨609018293129138544115801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812024390838851392154401 609018293129138544115801)
          ·
            refine ⟨456763719846853908086851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609018293129138544115801 456763719846853908086851)
            ·
              refine ⟨685145579770280862130277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456763719846853908086851 685145579770280862130277)
              ·
                refine ⟨128464796206927661649427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685145579770280862130277 128464796206927661649427)
                ·
                  rfl

theorem cell19_422186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_422186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422186 prefixEnd_422186 := by exact prefixLift 422186
  have htrace : WordTrace (prefixWord ++ tailWord_422186) baseStart_422186 baseEnd_422186 := by
    simpa [prefixWord, tailWord_422186, baseEnd_422186] using wordTrace_append hprefix tailTrace_422186
  have hstable : (prefixWord ++ tailWord_422186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422186).length < 2 ^ (prefixWord ++ tailWord_422186).sum := by decide
  have hdescent : baseEnd_422186 < baseStart_422186 := by decide
  rcases family_descends (prefixWord ++ tailWord_422186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422192 : List Nat := [2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_422192 : Nat := 118140960795 + 422192 * 2 ^ 59
def prefixEnd_422192 : Nat := 4983230072969 + 3 ^ 40 * 422192 * 2
def baseEnd_422192 : Nat := 128466621915921425516077

theorem tailTrace_422192 : CollatzResearch.WordTrace tailWord_422192 prefixEnd_422192 128466621915921425516077 := by
  unfold tailWord_422192
  simp only [CollatzResearch.WordTrace]
  refine ⟨7699303643238981749082415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10265738190985308998776553 7699303643238981749082415)
  ·
    refine ⟨11548955464858472623623623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7699303643238981749082415 11548955464858472623623623)
    ·
      refine ⟨17323433197287708935435435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11548955464858472623623623 17323433197287708935435435)
      ·
        refine ⟨25985149795931563403153153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17323433197287708935435435 25985149795931563403153153)
        ·
          refine ⟨19488862346948672552364865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25985149795931563403153153 19488862346948672552364865)
          ·
            refine ⟨14616646760211504414273649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19488862346948672552364865 14616646760211504414273649)
            ·
              refine ⟨10962485070158628310705237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14616646760211504414273649 10962485070158628310705237)
              ·
                refine ⟨128466621915921425516077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10962485070158628310705237 128466621915921425516077)
                ·
                  rfl

theorem cell19_422192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_422192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422192 prefixEnd_422192 := by exact prefixLift 422192
  have htrace : WordTrace (prefixWord ++ tailWord_422192) baseStart_422192 baseEnd_422192 := by
    simpa [prefixWord, tailWord_422192, baseEnd_422192] using wordTrace_append hprefix tailTrace_422192
  have hstable : (prefixWord ++ tailWord_422192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422192).length < 2 ^ (prefixWord ++ tailWord_422192).sum := by decide
  have hdescent : baseEnd_422192 < baseStart_422192 := by decide
  rcases family_descends (prefixWord ++ tailWord_422192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422211 : List Nat := [1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_422211 : Nat := 118140960795 + 422211 * 2 ^ 59
def prefixEnd_422211 : Nat := 4983230072969 + 3 ^ 40 * 422211 * 2
def baseEnd_422211 : Nat := 128472403327735011093803

theorem tailTrace_422211 : CollatzResearch.WordTrace tailWord_422211 prefixEnd_422211 128472403327735011093803 := by
  unfold tailWord_422211
  simp only [CollatzResearch.WordTrace]
  refine ⟨15399300273409129743106487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10266200182272753162070991 15399300273409129743106487)
  ·
    refine ⟨23098950410113694614659731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15399300273409129743106487 23098950410113694614659731)
    ·
      refine ⟨34648425615170541921989597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23098950410113694614659731 34648425615170541921989597)
      ·
        refine ⟨12993159605688953220746099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34648425615170541921989597 12993159605688953220746099)
        ·
          refine ⟨19489739408533429831119149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12993159605688953220746099 19489739408533429831119149)
          ·
            refine ⟨7308652278200036186669681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19489739408533429831119149 7308652278200036186669681)
            ·
              refine ⟨5481489208650027140002261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7308652278200036186669681 5481489208650027140002261)
              ·
                refine ⟨128472403327735011093803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5481489208650027140002261 128472403327735011093803)
                ·
                  rfl

theorem cell19_422211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_422211 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422211 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422211 prefixEnd_422211 := by exact prefixLift 422211
  have htrace : WordTrace (prefixWord ++ tailWord_422211) baseStart_422211 baseEnd_422211 := by
    simpa [prefixWord, tailWord_422211, baseEnd_422211] using wordTrace_append hprefix tailTrace_422211
  have hstable : (prefixWord ++ tailWord_422211).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422211).length < 2 ^ (prefixWord ++ tailWord_422211).sum := by decide
  have hdescent : baseEnd_422211 < baseStart_422211 := by decide
  rcases family_descends (prefixWord ++ tailWord_422211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422228 : List Nat := [2, 4, 1, 1, 2, 3, 6]
def baseStart_422228 : Nat := 118140960795 + 422228 * 2 ^ 59
def prefixEnd_422228 : Nat := 4983230072969 + 3 ^ 40 * 422228 * 2
def baseEnd_422228 : Nat := 42825858723294669571993

theorem tailTrace_422228 : CollatzResearch.WordTrace tailWord_422228 prefixEnd_422228 42825858723294669571993 := by
  unfold tailWord_422228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7699960157173770823237669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10266613542898361097650225 7699960157173770823237669)
  ·
    refine ⟨1443742529470082029357063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7699960157173770823237669 1443742529470082029357063)
    ·
      refine ⟨2165613794205123044035595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443742529470082029357063 2165613794205123044035595)
      ·
        refine ⟨3248420691307684566053393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165613794205123044035595 3248420691307684566053393)
        ·
          refine ⟨2436315518480763424540045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3248420691307684566053393 2436315518480763424540045)
          ·
            refine ⟨913618319430286284202517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2436315518480763424540045 913618319430286284202517)
            ·
              refine ⟨42825858723294669571993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 913618319430286284202517 42825858723294669571993)
              ·
                rfl

theorem cell19_422228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_422228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422228 prefixEnd_422228 := by exact prefixLift 422228
  have htrace : WordTrace (prefixWord ++ tailWord_422228) baseStart_422228 baseEnd_422228 := by
    simpa [prefixWord, tailWord_422228, baseEnd_422228] using wordTrace_append hprefix tailTrace_422228
  have hstable : (prefixWord ++ tailWord_422228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422228).length < 2 ^ (prefixWord ++ tailWord_422228).sum := by decide
  have hdescent : baseEnd_422228 < baseStart_422228 := by decide
  rcases family_descends (prefixWord ++ tailWord_422228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422249 : List Nat := [1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_422249 : Nat := 118140960795 + 422249 * 2 ^ 59
def prefixEnd_422249 : Nat := 4983230072969 + 3 ^ 40 * 422249 * 2
def baseEnd_422249 : Nat := 128483966151362182249255

theorem tailTrace_422249 : CollatzResearch.WordTrace tailWord_422249 prefixEnd_422249 128483966151362182249255 := by
  unfold tailWord_422249
  simp only [CollatzResearch.WordTrace]
  refine ⟨15400686247271462232989801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10267124164847641488659867 15400686247271462232989801)
  ·
    refine ⟨11550514685453596674742351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15400686247271462232989801 11550514685453596674742351)
    ·
      refine ⟨17325772028180395012113527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11550514685453596674742351 17325772028180395012113527)
      ·
        refine ⟨25988658042270592518170291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17325772028180395012113527 25988658042270592518170291)
        ·
          refine ⟨38982987063405888777255437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25988658042270592518170291 38982987063405888777255437)
          ·
            refine ⟨14618620148777208291470789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38982987063405888777255437 14618620148777208291470789)
            ·
              refine ⟨2740991277895726554650773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14618620148777208291470789 2740991277895726554650773)
              ·
                refine ⟨128483966151362182249255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2740991277895726554650773 128483966151362182249255)
                ·
                  rfl

theorem cell19_422249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_422249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422249 prefixEnd_422249 := by exact prefixLift 422249
  have htrace : WordTrace (prefixWord ++ tailWord_422249) baseStart_422249 baseEnd_422249 := by
    simpa [prefixWord, tailWord_422249, baseEnd_422249] using wordTrace_append hprefix tailTrace_422249
  have hstable : (prefixWord ++ tailWord_422249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422249).length < 2 ^ (prefixWord ++ tailWord_422249).sum := by decide
  have hdescent : baseEnd_422249 < baseStart_422249 := by decide
  rcases family_descends (prefixWord ++ tailWord_422249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422262 : List Nat := [5, 1, 1, 4, 1, 1, 1, 5]
def baseStart_422262 : Nat := 118140960795 + 422262 * 2 ^ 59
def prefixEnd_422262 : Nat := 4983230072969 + 3 ^ 40 * 422262 * 2
def baseEnd_422262 : Nat := 128487921854182003960331

theorem tailTrace_422262 : CollatzResearch.WordTrace tailWord_422262 prefixEnd_422262 128487921854182003960331 := by
  unfold tailWord_422262
  simp only [CollatzResearch.WordTrace]
  refine ⟨962572524764022840825815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10267440264149576968808693 962572524764022840825815)
  ·
    refine ⟨1443858787146034261238723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962572524764022840825815 1443858787146034261238723)
    ·
      refine ⟨2165788180719051391858085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443858787146034261238723 2165788180719051391858085)
      ·
        refine ⟨406085283884822135973391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2165788180719051391858085 406085283884822135973391)
        ·
          refine ⟨609127925827233203960087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406085283884822135973391 609127925827233203960087)
          ·
            refine ⟨913691888740849805940131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609127925827233203960087 913691888740849805940131)
            ·
              refine ⟨1370537833111274708910197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913691888740849805940131 1370537833111274708910197)
              ·
                refine ⟨128487921854182003960331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1370537833111274708910197 128487921854182003960331)
                ·
                  rfl

theorem cell19_422262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_422262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422262 prefixEnd_422262 := by exact prefixLift 422262
  have htrace : WordTrace (prefixWord ++ tailWord_422262) baseStart_422262 baseEnd_422262 := by
    simpa [prefixWord, tailWord_422262, baseEnd_422262] using wordTrace_append hprefix tailTrace_422262
  have hstable : (prefixWord ++ tailWord_422262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422262).length < 2 ^ (prefixWord ++ tailWord_422262).sum := by decide
  have hdescent : baseEnd_422262 < baseStart_422262 := by decide
  rcases family_descends (prefixWord ++ tailWord_422262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422302 : List Nat := [4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_422302 : Nat := 118140960795 + 422302 * 2 ^ 59
def prefixEnd_422302 : Nat := 4983230072969 + 3 ^ 40 * 422302 * 2
def baseEnd_422302 : Nat := 128500093247473763071333

theorem tailTrace_422302 : CollatzResearch.WordTrace tailWord_422302 prefixEnd_422302 128500093247473763071333 := by
  unfold tailWord_422302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925327414509931535583645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10268412877386301523112773 1925327414509931535583645)
  ·
    refine ⟨721997780441224325843867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1925327414509931535583645 721997780441224325843867)
    ·
      refine ⟨1082996670661836488765801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 721997780441224325843867 1082996670661836488765801)
      ·
        refine ⟨812247502996377366574351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1082996670661836488765801 812247502996377366574351)
        ·
          refine ⟨1218371254494566049861527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812247502996377366574351 1218371254494566049861527)
          ·
            refine ⟨1827556881741849074792291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218371254494566049861527 1827556881741849074792291)
            ·
              refine ⟨2741335322612773612188437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827556881741849074792291 2741335322612773612188437)
              ·
                refine ⟨128500093247473763071333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2741335322612773612188437 128500093247473763071333)
                ·
                  rfl

theorem cell19_422302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_422302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422302 prefixEnd_422302 := by exact prefixLift 422302
  have htrace : WordTrace (prefixWord ++ tailWord_422302) baseStart_422302 baseEnd_422302 := by
    simpa [prefixWord, tailWord_422302, baseEnd_422302] using wordTrace_append hprefix tailTrace_422302
  have hstable : (prefixWord ++ tailWord_422302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422302).length < 2 ^ (prefixWord ++ tailWord_422302).sum := by decide
  have hdescent : baseEnd_422302 < baseStart_422302 := by decide
  rcases family_descends (prefixWord ++ tailWord_422302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422304 : List Nat := [2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_422304 : Nat := 118140960795 + 422304 * 2 ^ 59
def prefixEnd_422304 : Nat := 4983230072969 + 3 ^ 40 * 422304 * 2
def baseEnd_422304 : Nat := 128500701817138351026883

theorem tailTrace_422304 : CollatzResearch.WordTrace tailWord_422304 prefixEnd_422304 128500701817138351026883 := by
  unfold tailWord_422304
  simp only [CollatzResearch.WordTrace]
  refine ⟨7701346131036103313120983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10268461508048137750827977 7701346131036103313120983)
  ·
    refine ⟨11552019196554154969681475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7701346131036103313120983 11552019196554154969681475)
    ·
      refine ⟨17328028794831232454522213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11552019196554154969681475 17328028794831232454522213)
      ·
        refine ⟨3249005399030856085222915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17328028794831232454522213 3249005399030856085222915)
        ·
          refine ⟨4873508098546284127834373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3249005399030856085222915 4873508098546284127834373)
          ·
            refine ⟨913782768477428273968945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4873508098546284127834373 913782768477428273968945)
            ·
              refine ⟨685337076358071205476709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913782768477428273968945 685337076358071205476709)
              ·
                refine ⟨128500701817138351026883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685337076358071205476709 128500701817138351026883)
                ·
                  rfl

theorem cell19_422304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_422304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422304 prefixEnd_422304 := by exact prefixLift 422304
  have htrace : WordTrace (prefixWord ++ tailWord_422304) baseStart_422304 baseEnd_422304 := by
    simpa [prefixWord, tailWord_422304, baseEnd_422304] using wordTrace_append hprefix tailTrace_422304
  have hstable : (prefixWord ++ tailWord_422304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422304).length < 2 ^ (prefixWord ++ tailWord_422304).sum := by decide
  have hdescent : baseEnd_422304 < baseStart_422304 := by decide
  rcases family_descends (prefixWord ++ tailWord_422304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422340 : List Nat := [2, 3, 3, 2, 3, 6]
def baseStart_422340 : Nat := 118140960795 + 422340 * 2 ^ 59
def prefixEnd_422340 : Nat := 4983230072969 + 3 ^ 40 * 422340 * 2
def baseEnd_422340 : Nat := 14279072896788992691865

theorem tailTrace_422340 : CollatzResearch.WordTrace tailWord_422340 prefixEnd_422340 14279072896788992691865 := by
  unfold tailWord_422340
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702002644970892387276237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10269336859961189849701649 7702002644970892387276237)
  ·
    refine ⟨2888250991864084645228589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7702002644970892387276237 2888250991864084645228589)
    ·
      refine ⟨1083094121949031741960721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2888250991864084645228589 1083094121949031741960721)
      ·
        refine ⟨812320591461773806470541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1083094121949031741960721 812320591461773806470541)
        ·
          refine ⟨304620221798165177426453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 812320591461773806470541 304620221798165177426453)
          ·
            refine ⟨14279072896788992691865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 304620221798165177426453 14279072896788992691865)
            ·
              rfl

theorem cell19_422340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 6].length) (baseStart_422340 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422340 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422340 prefixEnd_422340 := by exact prefixLift 422340
  have htrace : WordTrace (prefixWord ++ tailWord_422340) baseStart_422340 baseEnd_422340 := by
    simpa [prefixWord, tailWord_422340, baseEnd_422340] using wordTrace_append hprefix tailTrace_422340
  have hstable : (prefixWord ++ tailWord_422340).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422340).length < 2 ^ (prefixWord ++ tailWord_422340).sum := by decide
  have hdescent : baseEnd_422340 < baseStart_422340 := by decide
  rcases family_descends (prefixWord ++ tailWord_422340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422342 : List Nat := [6, 1, 12]
def baseStart_422342 : Nat := 118140960795 + 422342 * 2 ^ 59
def prefixEnd_422342 : Nat := 4983230072969 + 3 ^ 40 * 422342 * 2
def baseEnd_422342 : Nat := 528857056134837539845

theorem tailTrace_422342 : CollatzResearch.WordTrace tailWord_422342 prefixEnd_422342 528857056134837539845 := by
  unfold tailWord_422342
  simp only [CollatzResearch.WordTrace]
  refine ⟨481377444872954347378915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10269385490623026077416853 481377444872954347378915)
  ·
    refine ⟨722066167309431521068373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 481377444872954347378915 722066167309431521068373)
    ·
      refine ⟨528857056134837539845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 722066167309431521068373 528857056134837539845)
      ·
        rfl

theorem cell19_422342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 12].length) (baseStart_422342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422342 prefixEnd_422342 := by exact prefixLift 422342
  have htrace : WordTrace (prefixWord ++ tailWord_422342) baseStart_422342 baseEnd_422342 := by
    simpa [prefixWord, tailWord_422342, baseEnd_422342] using wordTrace_append hprefix tailTrace_422342
  have hstable : (prefixWord ++ tailWord_422342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422342).length < 2 ^ (prefixWord ++ tailWord_422342).sum := by decide
  have hdescent : baseEnd_422342 < baseStart_422342 := by decide
  rcases family_descends (prefixWord ++ tailWord_422342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422344 : List Nat := [2, 1, 3, 1, 3, 9]
def baseStart_422344 : Nat := 118140960795 + 422344 * 2 ^ 59
def prefixEnd_422344 : Nat := 4983230072969 + 3 ^ 40 * 422344 * 2
def baseEnd_422344 : Nat := 14279208134492234459765

theorem tailTrace_422344 : CollatzResearch.WordTrace tailWord_422344 prefixEnd_422344 14279208134492234459765 := by
  unfold tailWord_422344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702075590963646728849043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10269434121284862305132057 7702075590963646728849043)
  ·
    refine ⟨11553113386445470093273565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7702075590963646728849043 11553113386445470093273565)
    ·
      refine ⟨4332417519917051284977587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11553113386445470093273565 4332417519917051284977587)
      ·
        refine ⟨6498626279875576927466381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4332417519917051284977587 6498626279875576927466381)
        ·
          refine ⟨2436984854953341347799893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6498626279875576927466381 2436984854953341347799893)
          ·
            refine ⟨14279208134492234459765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2436984854953341347799893 14279208134492234459765)
            ·
              rfl

theorem cell19_422344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 9].length) (baseStart_422344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422344 prefixEnd_422344 := by exact prefixLift 422344
  have htrace : WordTrace (prefixWord ++ tailWord_422344) baseStart_422344 baseEnd_422344 := by
    simpa [prefixWord, tailWord_422344, baseEnd_422344] using wordTrace_append hprefix tailTrace_422344
  have hstable : (prefixWord ++ tailWord_422344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422344).length < 2 ^ (prefixWord ++ tailWord_422344).sum := by decide
  have hdescent : baseEnd_422344 < baseStart_422344 := by decide
  rcases family_descends (prefixWord ++ tailWord_422344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422378 : List Nat := [3, 1, 3, 1, 3, 2, 3, 3]
def baseStart_422378 : Nat := 118140960795 + 422378 * 2 ^ 59
def prefixEnd_422378 : Nat := 4983230072969 + 3 ^ 40 * 422378 * 2
def baseEnd_422378 : Nat := 128523218894728105382237

theorem tailTrace_422378 : CollatzResearch.WordTrace tailWord_422378 prefixEnd_422378 128523218894728105382237 := by
  unfold tailWord_422378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3851347815951029316108947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10270260842536078176290525 3851347815951029316108947)
  ·
    refine ⟨5777021723926543974163421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3851347815951029316108947 5777021723926543974163421)
    ·
      refine ⟨2166383146472453990311283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5777021723926543974163421 2166383146472453990311283)
      ·
        refine ⟨3249574719708680985466925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2166383146472453990311283 3249574719708680985466925)
        ·
          refine ⟨1218590519890755369550097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3249574719708680985466925 1218590519890755369550097)
          ·
            refine ⟨913942889918066527162573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218590519890755369550097 913942889918066527162573)
            ·
              refine ⟨342728583719274947685965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 913942889918066527162573 342728583719274947685965)
              ·
                refine ⟨128523218894728105382237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342728583719274947685965 128523218894728105382237)
                ·
                  rfl

theorem cell19_422378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_422378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422378 prefixEnd_422378 := by exact prefixLift 422378
  have htrace : WordTrace (prefixWord ++ tailWord_422378) baseStart_422378 baseEnd_422378 := by
    simpa [prefixWord, tailWord_422378, baseEnd_422378] using wordTrace_append hprefix tailTrace_422378
  have hstable : (prefixWord ++ tailWord_422378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422378).length < 2 ^ (prefixWord ++ tailWord_422378).sum := by decide
  have hdescent : baseEnd_422378 < baseStart_422378 := by decide
  rcases family_descends (prefixWord ++ tailWord_422378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422380 : List Nat := [2, 2, 1, 1, 2, 1, 7, 3]
def baseStart_422380 : Nat := 118140960795 + 422380 * 2 ^ 59
def prefixEnd_422380 : Nat := 4983230072969 + 3 ^ 40 * 422380 * 2
def baseEnd_422380 : Nat := 128523827464392693337787

theorem tailTrace_422380 : CollatzResearch.WordTrace tailWord_422380 prefixEnd_422380 128523827464392693337787 := by
  unfold tailWord_422380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702732104898435803004297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10270309473197914404005729 7702732104898435803004297)
  ·
    refine ⟨5777049078673826852253223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7702732104898435803004297 5777049078673826852253223)
    ·
      refine ⟨8665573618010740278379835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5777049078673826852253223 8665573618010740278379835)
      ·
        refine ⟨12998360427016110417569753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8665573618010740278379835 12998360427016110417569753)
        ·
          refine ⟨9748770320262082813177315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12998360427016110417569753 9748770320262082813177315)
          ·
            refine ⟨14623155480393124219765973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9748770320262082813177315 14623155480393124219765973)
            ·
              refine ⟨342730206571713848900765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14623155480393124219765973 342730206571713848900765)
              ·
                refine ⟨128523827464392693337787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342730206571713848900765 128523827464392693337787)
                ·
                  rfl

theorem cell19_422380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_422380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422380 prefixEnd_422380 := by exact prefixLift 422380
  have htrace : WordTrace (prefixWord ++ tailWord_422380) baseStart_422380 baseEnd_422380 := by
    simpa [prefixWord, tailWord_422380, baseEnd_422380] using wordTrace_append hprefix tailTrace_422380
  have hstable : (prefixWord ++ tailWord_422380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422380).length < 2 ^ (prefixWord ++ tailWord_422380).sum := by decide
  have hdescent : baseEnd_422380 < baseStart_422380 := by decide
  rcases family_descends (prefixWord ++ tailWord_422380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422435 : List Nat := [1, 1, 1, 4, 4, 3, 2, 3]
def baseStart_422435 : Nat := 118140960795 + 422435 * 2 ^ 59
def prefixEnd_422435 : Nat := 4983230072969 + 3 ^ 40 * 422435 * 2
def baseEnd_422435 : Nat := 128540563130168862115415

theorem tailTrace_422435 : CollatzResearch.WordTrace tailWord_422435 prefixEnd_422435 128540563130168862115415 := by
  unfold tailWord_422435
  simp only [CollatzResearch.WordTrace]
  refine ⟨15407470224597615999260759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10271646816398410666173839 15407470224597615999260759)
  ·
    refine ⟨23111205336896423998891139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15407470224597615999260759 23111205336896423998891139)
    ·
      refine ⟨34666808005344635998336709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23111205336896423998891139 34666808005344635998336709)
      ·
        refine ⟨6500026501002119249688133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34666808005344635998336709 6500026501002119249688133)
        ·
          refine ⟨1218754968937897359316525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6500026501002119249688133 1218754968937897359316525)
          ·
            refine ⟨457033113351711509743697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1218754968937897359316525 457033113351711509743697)
            ·
              refine ⟨342774835013783632307773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457033113351711509743697 342774835013783632307773)
              ·
                refine ⟨128540563130168862115415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342774835013783632307773 128540563130168862115415)
                ·
                  rfl

theorem cell19_422435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 3].length) (baseStart_422435 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422435 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422435 prefixEnd_422435 := by exact prefixLift 422435
  have htrace : WordTrace (prefixWord ++ tailWord_422435) baseStart_422435 baseEnd_422435 := by
    simpa [prefixWord, tailWord_422435, baseEnd_422435] using wordTrace_append hprefix tailTrace_422435
  have hstable : (prefixWord ++ tailWord_422435).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422435).length < 2 ^ (prefixWord ++ tailWord_422435).sum := by decide
  have hdescent : baseEnd_422435 < baseStart_422435 := by decide
  rcases family_descends (prefixWord ++ tailWord_422435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422437 : List Nat := [1, 3, 1, 2, 2, 1, 6, 3]
def baseStart_422437 : Nat := 118140960795 + 422437 * 2 ^ 59
def prefixEnd_422437 : Nat := 4983230072969 + 3 ^ 40 * 422437 * 2
def baseEnd_422437 : Nat := 128541171699833450070965

theorem tailTrace_422437 : CollatzResearch.WordTrace tailWord_422437 prefixEnd_422437 128541171699833450070965 := by
  unfold tailWord_422437
  simp only [CollatzResearch.WordTrace]
  refine ⟨15407543170590370340833565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10271695447060246893889043 15407543170590370340833565)
  ·
    refine ⟨5777828688971388877812587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15407543170590370340833565 5777828688971388877812587)
    ·
      refine ⟨8666743033457083316718881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5777828688971388877812587 8666743033457083316718881)
      ·
        refine ⟨6500057275092812487539161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8666743033457083316718881 6500057275092812487539161)
        ·
          refine ⟨4875042956319609365654371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6500057275092812487539161 4875042956319609365654371)
          ·
            refine ⟨7312564434479414048481557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4875042956319609365654371 7312564434479414048481557)
            ·
              refine ⟨342776457866222533522573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7312564434479414048481557 342776457866222533522573)
              ·
                refine ⟨128541171699833450070965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342776457866222533522573 128541171699833450070965)
                ·
                  rfl

theorem cell19_422437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 3].length) (baseStart_422437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422437 prefixEnd_422437 := by exact prefixLift 422437
  have htrace : WordTrace (prefixWord ++ tailWord_422437) baseStart_422437 baseEnd_422437 := by
    simpa [prefixWord, tailWord_422437, baseEnd_422437] using wordTrace_append hprefix tailTrace_422437
  have hstable : (prefixWord ++ tailWord_422437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422437).length < 2 ^ (prefixWord ++ tailWord_422437).sum := by decide
  have hdescent : baseEnd_422437 < baseStart_422437 := by decide
  rcases family_descends (prefixWord ++ tailWord_422437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422452 : List Nat := [2, 5, 1, 3, 1, 2, 5]
def baseStart_422452 : Nat := 118140960795 + 422452 * 2 ^ 59
def prefixEnd_422452 : Nat := 4983230072969 + 3 ^ 40 * 422452 * 2
def baseEnd_422452 : Nat := 42848578657439286579197

theorem tailTrace_422452 : CollatzResearch.WordTrace tailWord_422452 prefixEnd_422452 42848578657439286579197 := by
  unfold tailWord_422452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7704045132768013951314805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10272060177024018601753073 7704045132768013951314805)
  ·
    refine ⟨722254231197001307935763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7704045132768013951314805 722254231197001307935763)
    ·
      refine ⟨1083381346795501961903645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722254231197001307935763 1083381346795501961903645)
      ·
        refine ⟨406268005048313235713867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1083381346795501961903645 406268005048313235713867)
        ·
          refine ⟨609402007572469853570801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406268005048313235713867 609402007572469853570801)
          ·
            refine ⟨457051505679352390178101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609402007572469853570801 457051505679352390178101)
            ·
              refine ⟨42848578657439286579197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 457051505679352390178101 42848578657439286579197)
              ·
                rfl

theorem cell19_422452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 5].length) (baseStart_422452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422452 prefixEnd_422452 := by exact prefixLift 422452
  have htrace : WordTrace (prefixWord ++ tailWord_422452) baseStart_422452 baseEnd_422452 := by
    simpa [prefixWord, tailWord_422452, baseEnd_422452] using wordTrace_append hprefix tailTrace_422452
  have hstable : (prefixWord ++ tailWord_422452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422452).length < 2 ^ (prefixWord ++ tailWord_422452).sum := by decide
  have hdescent : baseEnd_422452 < baseStart_422452 := by decide
  rcases family_descends (prefixWord ++ tailWord_422452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422454 : List Nat := [5, 1, 2, 1, 2, 3, 5]
def baseStart_422454 : Nat := 118140960795 + 422454 * 2 ^ 59
def prefixEnd_422454 : Nat := 4983230072969 + 3 ^ 40 * 422454 * 2
def baseEnd_422454 : Nat := 42848781513994149231047

theorem tailTrace_422454 : CollatzResearch.WordTrace tailWord_422454 prefixEnd_422454 42848781513994149231047 := by
  unfold tailWord_422454
  simp only [CollatzResearch.WordTrace]
  refine ⟨963010200720548890262651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10272108807685854829468277 963010200720548890262651)
  ·
    refine ⟨1444515301080823335393977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 963010200720548890262651 1444515301080823335393977)
    ·
      refine ⟨1083386475810617501545483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1444515301080823335393977 1083386475810617501545483)
      ·
        refine ⟨1625079713715926252318225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1083386475810617501545483 1625079713715926252318225)
        ·
          refine ⟨1218809785286944689238669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1625079713715926252318225 1218809785286944689238669)
          ·
            refine ⟨457053669482604258464501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1218809785286944689238669 457053669482604258464501)
            ·
              refine ⟨42848781513994149231047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 457053669482604258464501 42848781513994149231047)
              ·
                rfl

theorem cell19_422454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_422454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422454 prefixEnd_422454 := by exact prefixLift 422454
  have htrace : WordTrace (prefixWord ++ tailWord_422454) baseStart_422454 baseEnd_422454 := by
    simpa [prefixWord, tailWord_422454, baseEnd_422454] using wordTrace_append hprefix tailTrace_422454
  have hstable : (prefixWord ++ tailWord_422454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422454).length < 2 ^ (prefixWord ++ tailWord_422454).sum := by decide
  have hdescent : baseEnd_422454 < baseStart_422454 := by decide
  rcases family_descends (prefixWord ++ tailWord_422454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422458 : List Nat := [3, 1, 1, 1, 3, 3, 7]
def baseStart_422458 : Nat := 118140960795 + 422458 * 2 ^ 59
def prefixEnd_422458 : Nat := 4983230072969 + 3 ^ 40 * 422458 * 2
def baseEnd_422458 : Nat := 42849187227103874534747

theorem tailTrace_422458 : CollatzResearch.WordTrace tailWord_422458 prefixEnd_422458 42849187227103874534747 := by
  unfold tailWord_422458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3852077275878572731837007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10272206069009527284898685 3852077275878572731837007)
  ·
    refine ⟨5778115913817859097755511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3852077275878572731837007 5778115913817859097755511)
    ·
      refine ⟨8667173870726788646633267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5778115913817859097755511 8667173870726788646633267)
      ·
        refine ⟨13000760806090182969949901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667173870726788646633267 13000760806090182969949901)
        ·
          refine ⟨4875285302283818613731213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13000760806090182969949901 4875285302283818613731213)
          ·
            refine ⟨1828231988356431980149205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4875285302283818613731213 1828231988356431980149205)
            ·
              refine ⟨42849187227103874534747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1828231988356431980149205 42849187227103874534747)
              ·
                rfl

theorem cell19_422458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_422458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422458 prefixEnd_422458 := by exact prefixLift 422458
  have htrace : WordTrace (prefixWord ++ tailWord_422458) baseStart_422458 baseEnd_422458 := by
    simpa [prefixWord, tailWord_422458, baseEnd_422458] using wordTrace_append hprefix tailTrace_422458
  have hstable : (prefixWord ++ tailWord_422458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422458).length < 2 ^ (prefixWord ++ tailWord_422458).sum := by decide
  have hdescent : baseEnd_422458 < baseStart_422458 := by decide
  rcases family_descends (prefixWord ++ tailWord_422458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422496 : List Nat := [2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_422496 : Nat := 118140960795 + 422496 * 2 ^ 59
def prefixEnd_422496 : Nat := 4983230072969 + 3 ^ 40 * 422496 * 2
def baseEnd_422496 : Nat := 128559124504938794759693

theorem tailTrace_422496 : CollatzResearch.WordTrace tailWord_422496 prefixEnd_422496 128559124504938794759693 := by
  unfold tailWord_422496
  simp only [CollatzResearch.WordTrace]
  refine ⟨7704847538688311708615671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10273130051584415611487561 7704847538688311708615671)
  ·
    refine ⟨11557271308032467562923507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7704847538688311708615671 11557271308032467562923507)
    ·
      refine ⟨17335906962048701344385261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11557271308032467562923507 17335906962048701344385261)
      ·
        refine ⟨6500965110768263004144473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17335906962048701344385261 6500965110768263004144473)
        ·
          refine ⟨4875723833076197253108355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6500965110768263004144473 4875723833076197253108355)
          ·
            refine ⟨7313585749614295879662533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4875723833076197253108355 7313585749614295879662533)
            ·
              refine ⟨1371297328052680477436725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7313585749614295879662533 1371297328052680477436725)
              ·
                refine ⟨128559124504938794759693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1371297328052680477436725 128559124504938794759693)
                ·
                  rfl

theorem cell19_422496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_422496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422496 prefixEnd_422496 := by exact prefixLift 422496
  have htrace : WordTrace (prefixWord ++ tailWord_422496) baseStart_422496 baseEnd_422496 := by
    simpa [prefixWord, tailWord_422496, baseEnd_422496] using wordTrace_append hprefix tailTrace_422496
  have hstable : (prefixWord ++ tailWord_422496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422496).length < 2 ^ (prefixWord ++ tailWord_422496).sum := by decide
  have hdescent : baseEnd_422496 < baseStart_422496 := by decide
  rcases family_descends (prefixWord ++ tailWord_422496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422532 : List Nat := [2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_422532 : Nat := 118140960795 + 422532 * 2 ^ 59
def prefixEnd_422532 : Nat := 4983230072969 + 3 ^ 40 * 422532 * 2
def baseEnd_422532 : Nat := 128570078758901377959595

theorem tailTrace_422532 : CollatzResearch.WordTrace tailWord_422532 prefixEnd_422532 128570078758901377959595 := by
  unfold tailWord_422532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7705504052623100782770925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10274005403497467710361233 7705504052623100782770925)
  ·
    refine ⟨2889564019733662793539097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7705504052623100782770925 2889564019733662793539097)
    ·
      refine ⟨2167173014800247095154323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2889564019733662793539097 2167173014800247095154323)
      ·
        refine ⟨3250759522200370642731485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167173014800247095154323 3250759522200370642731485)
        ·
          refine ⟨1219034820825138991024307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3250759522200370642731485 1219034820825138991024307)
          ·
            refine ⟨1828552231237708486536461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219034820825138991024307 1828552231237708486536461)
            ·
              refine ⟨685707086714140682451173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1828552231237708486536461 685707086714140682451173)
              ·
                refine ⟨128570078758901377959595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685707086714140682451173 128570078758901377959595)
                ·
                  rfl

theorem cell19_422532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_422532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422532 prefixEnd_422532 := by exact prefixLift 422532
  have htrace : WordTrace (prefixWord ++ tailWord_422532) baseStart_422532 baseEnd_422532 := by
    simpa [prefixWord, tailWord_422532, baseEnd_422532] using wordTrace_append hprefix tailTrace_422532
  have hstable : (prefixWord ++ tailWord_422532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422532).length < 2 ^ (prefixWord ++ tailWord_422532).sum := by decide
  have hdescent : baseEnd_422532 < baseStart_422532 := by decide
  rcases family_descends (prefixWord ++ tailWord_422532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422551 : List Nat := [1, 1, 3, 3, 2, 1, 5, 3]
def baseStart_422551 : Nat := 118140960795 + 422551 * 2 ^ 59
def prefixEnd_422551 : Nat := 4983230072969 + 3 ^ 40 * 422551 * 2
def baseEnd_422551 : Nat := 128575860170714963537321

theorem tailTrace_422551 : CollatzResearch.WordTrace tailWord_422551 prefixEnd_422551 128575860170714963537321 := by
  unfold tailWord_422551
  simp only [CollatzResearch.WordTrace]
  refine ⟨15411701092177367810483507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10274467394784911873655671 15411701092177367810483507)
  ·
    refine ⟨23117551638266051715725261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15411701092177367810483507 23117551638266051715725261)
    ·
      refine ⟨8669081864349769393396973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23117551638266051715725261 8669081864349769393396973)
      ·
        refine ⟨3250905699131163522523865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8669081864349769393396973 3250905699131163522523865)
        ·
          refine ⟨2438179274348372641892899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3250905699131163522523865 2438179274348372641892899)
          ·
            refine ⟨3657268911522558962839349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438179274348372641892899 3657268911522558962839349)
            ·
              refine ⟨342868960455239902766189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3657268911522558962839349 342868960455239902766189)
              ·
                refine ⟨128575860170714963537321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342868960455239902766189 128575860170714963537321)
                ·
                  rfl

theorem cell19_422551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 3].length) (baseStart_422551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422551 prefixEnd_422551 := by exact prefixLift 422551
  have htrace : WordTrace (prefixWord ++ tailWord_422551) baseStart_422551 baseEnd_422551 := by
    simpa [prefixWord, tailWord_422551, baseEnd_422551] using wordTrace_append hprefix tailTrace_422551
  have hstable : (prefixWord ++ tailWord_422551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422551).length < 2 ^ (prefixWord ++ tailWord_422551).sum := by decide
  have hdescent : baseEnd_422551 < baseStart_422551 := by decide
  rcases family_descends (prefixWord ++ tailWord_422551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422606 : List Nat := [4, 1, 1, 1, 3, 4, 2, 3]
def baseStart_422606 : Nat := 118140960795 + 422606 * 2 ^ 59
def prefixEnd_422606 : Nat := 4983230072969 + 3 ^ 40 * 422606 * 2
def baseEnd_422606 : Nat := 128592595836491132314949

theorem tailTrace_422606 : CollatzResearch.WordTrace tailWord_422606 prefixEnd_422606 128592595836491132314949 := by
  unfold tailWord_422606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926713388372264025466959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10275804737985408135823781 1926713388372264025466959)
  ·
    refine ⟨2890070082558396038200439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1926713388372264025466959 2890070082558396038200439)
    ·
      refine ⟨4335105123837594057300659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2890070082558396038200439 4335105123837594057300659)
      ·
        refine ⟨6502657685756391085950989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4335105123837594057300659 6502657685756391085950989)
        ·
          refine ⟨2438496632158646657231621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6502657685756391085950989 2438496632158646657231621)
          ·
            refine ⟨457218118529746248230929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2438496632158646657231621 457218118529746248230929)
            ·
              refine ⟨342913588897309686173197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457218118529746248230929 342913588897309686173197)
              ·
                refine ⟨128592595836491132314949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342913588897309686173197 128592595836491132314949)
                ·
                  rfl

theorem cell19_422606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_422606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422606 prefixEnd_422606 := by exact prefixLift 422606
  have htrace : WordTrace (prefixWord ++ tailWord_422606) baseStart_422606 baseEnd_422606 := by
    simpa [prefixWord, tailWord_422606, baseEnd_422606] using wordTrace_append hprefix tailTrace_422606
  have hstable : (prefixWord ++ tailWord_422606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422606).length < 2 ^ (prefixWord ++ tailWord_422606).sum := by decide
  have hdescent : baseEnd_422606 < baseStart_422606 := by decide
  rcases family_descends (prefixWord ++ tailWord_422606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422627 : List Nat := [1, 1, 1, 7, 1, 3, 5]
def baseStart_422627 : Nat := 118140960795 + 422627 * 2 ^ 59
def prefixEnd_422627 : Nat := 4983230072969 + 3 ^ 40 * 422627 * 2
def baseEnd_422627 : Nat := 42866328605989768616075

theorem tailTrace_422627 : CollatzResearch.WordTrace tailWord_422627 prefixEnd_422627 42866328605989768616075 := by
  unfold tailWord_422627
  simp only [CollatzResearch.WordTrace]
  refine ⟨15414473039902032790250135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10276315359934688526833423 15414473039902032790250135)
  ·
    refine ⟨23121709559853049185375203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15414473039902032790250135 23121709559853049185375203)
    ·
      refine ⟨34682564339779573778062805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23121709559853049185375203 34682564339779573778062805)
      ·
        refine ⟨812872601713583760423347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 34682564339779573778062805 812872601713583760423347)
        ·
          refine ⟨1219308902570375640635021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812872601713583760423347 1219308902570375640635021)
          ·
            refine ⟨457240838463890865238133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1219308902570375640635021 457240838463890865238133)
            ·
              refine ⟨42866328605989768616075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 457240838463890865238133 42866328605989768616075)
              ·
                rfl

theorem cell19_422627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_422627 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422627 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422627 prefixEnd_422627 := by exact prefixLift 422627
  have htrace : WordTrace (prefixWord ++ tailWord_422627) baseStart_422627 baseEnd_422627 := by
    simpa [prefixWord, tailWord_422627, baseEnd_422627] using wordTrace_append hprefix tailTrace_422627
  have hstable : (prefixWord ++ tailWord_422627).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422627).length < 2 ^ (prefixWord ++ tailWord_422627).sum := by decide
  have hdescent : baseEnd_422627 < baseStart_422627 := by decide
  rcases family_descends (prefixWord ++ tailWord_422627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422629 : List Nat := [1, 3, 1, 4, 1, 2, 7]
def baseStart_422629 : Nat := 118140960795 + 422629 * 2 ^ 59
def prefixEnd_422629 : Nat := 4983230072969 + 3 ^ 40 * 422629 * 2
def baseEnd_422629 : Nat := 42866531462544631267925

theorem tailTrace_422629 : CollatzResearch.WordTrace tailWord_422629 prefixEnd_422629 42866531462544631267925 := by
  unfold tailWord_422629
  simp only [CollatzResearch.WordTrace]
  refine ⟨15414545985894787131822941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10276363990596524754548627 15414545985894787131822941)
  ·
    refine ⟨5780454744710545174433603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15414545985894787131822941 5780454744710545174433603)
    ·
      refine ⟨8670682117065817761650405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5780454744710545174433603 8670682117065817761650405)
      ·
        refine ⟨1625752896949840830309451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8670682117065817761650405 1625752896949840830309451)
        ·
          refine ⟨2438629345424761245464177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625752896949840830309451 2438629345424761245464177)
          ·
            refine ⟨1828972009068570934098133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2438629345424761245464177 1828972009068570934098133)
            ·
              refine ⟨42866531462544631267925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1828972009068570934098133 42866531462544631267925)
              ·
                rfl

theorem cell19_422629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_422629 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422629 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422629 prefixEnd_422629 := by exact prefixLift 422629
  have htrace : WordTrace (prefixWord ++ tailWord_422629) baseStart_422629 baseEnd_422629 := by
    simpa [prefixWord, tailWord_422629, baseEnd_422629] using wordTrace_append hprefix tailTrace_422629
  have hstable : (prefixWord ++ tailWord_422629).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422629).length < 2 ^ (prefixWord ++ tailWord_422629).sum := by decide
  have hdescent : baseEnd_422629 < baseStart_422629 := by decide
  rcases family_descends (prefixWord ++ tailWord_422629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422646 : List Nat := [5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_422646 : Nat := 118140960795 + 422646 * 2 ^ 59
def prefixEnd_422646 : Nat := 4983230072969 + 3 ^ 40 * 422646 * 2
def baseEnd_422646 : Nat := 128604767229782891425951

theorem tailTrace_422646 : CollatzResearch.WordTrace tailWord_422646 prefixEnd_422646 128604767229782891425951 := by
  unfold tailWord_422646
  simp only [CollatzResearch.WordTrace]
  refine ⟨963447876677074939699487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10276777351222132690127861 963447876677074939699487)
  ·
    refine ⟨1445171815015612409549231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 963447876677074939699487 1445171815015612409549231)
    ·
      refine ⟨2167757722523418614323847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1445171815015612409549231 2167757722523418614323847)
      ·
        refine ⟨3251636583785127921485771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167757722523418614323847 3251636583785127921485771)
        ·
          refine ⟨4877454875677691882228657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251636583785127921485771 4877454875677691882228657)
          ·
            refine ⟨3658091156758268911671493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4877454875677691882228657 3658091156758268911671493)
            ·
              refine ⟨685892091892175420938405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3658091156758268911671493 685892091892175420938405)
              ·
                refine ⟨128604767229782891425951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685892091892175420938405 128604767229782891425951)
                ·
                  rfl

theorem cell19_422646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_422646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422646 prefixEnd_422646 := by exact prefixLift 422646
  have htrace : WordTrace (prefixWord ++ tailWord_422646) baseStart_422646 baseEnd_422646 := by
    simpa [prefixWord, tailWord_422646, baseEnd_422646] using wordTrace_append hprefix tailTrace_422646
  have hstable : (prefixWord ++ tailWord_422646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422646).length < 2 ^ (prefixWord ++ tailWord_422646).sum := by decide
  have hdescent : baseEnd_422646 < baseStart_422646 := by decide
  rcases family_descends (prefixWord ++ tailWord_422646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422648 : List Nat := [2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_422648 : Nat := 118140960795 + 422648 * 2 ^ 59
def prefixEnd_422648 : Nat := 4983230072969 + 3 ^ 40 * 422648 * 2
def baseEnd_422648 : Nat := 128605375799447479381501

theorem tailTrace_422648 : CollatzResearch.WordTrace tailWord_422648 prefixEnd_422648 128605375799447479381501 := by
  unfold tailWord_422648
  simp only [CollatzResearch.WordTrace]
  refine ⟨7707619486412976688382299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10276825981883968917843065 7707619486412976688382299)
  ·
    refine ⟨11561429229619465032573449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7707619486412976688382299 11561429229619465032573449)
    ·
      refine ⟨8671071922214598774430087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11561429229619465032573449 8671071922214598774430087)
      ·
        refine ⟨13006607883321898161645131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8671071922214598774430087 13006607883321898161645131)
        ·
          refine ⟨19509911824982847242467697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13006607883321898161645131 19509911824982847242467697)
          ·
            refine ⟨14632433868737135431850773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19509911824982847242467697 14632433868737135431850773)
            ·
              refine ⟨685895337597053223368005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14632433868737135431850773 685895337597053223368005)
              ·
                refine ⟨128605375799447479381501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685895337597053223368005 128605375799447479381501)
                ·
                  rfl

theorem cell19_422648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_422648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422648 prefixEnd_422648 := by exact prefixLift 422648
  have htrace : WordTrace (prefixWord ++ tailWord_422648) baseStart_422648 baseEnd_422648 := by
    simpa [prefixWord, tailWord_422648, baseEnd_422648] using wordTrace_append hprefix tailTrace_422648
  have hstable : (prefixWord ++ tailWord_422648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422648).length < 2 ^ (prefixWord ++ tailWord_422648).sum := by decide
  have hdescent : baseEnd_422648 < baseStart_422648 := by decide
  rcases family_descends (prefixWord ++ tailWord_422648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422743 : List Nat := [1, 1, 3, 2, 4, 2, 6]
def baseStart_422743 : Nat := 118140960795 + 422743 * 2 ^ 59
def prefixEnd_422743 : Nat := 4983230072969 + 3 ^ 40 * 422743 * 2
def baseEnd_422743 : Nat := 42878094286171802423377

theorem tailTrace_422743 : CollatzResearch.WordTrace tailWord_422743 prefixEnd_422743 42878094286171802423377 := by
  unfold tailWord_422743
  simp only [CollatzResearch.WordTrace]
  refine ⟨15418703907481784601472883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10279135938321189734315255 15418703907481784601472883)
  ·
    refine ⟨23128055861222676902209325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15418703907481784601472883 23128055861222676902209325)
    ·
      refine ⟨8673020947958503838328497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23128055861222676902209325 8673020947958503838328497)
      ·
        refine ⟨6504765710968877878746373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8673020947958503838328497 6504765710968877878746373)
        ·
          refine ⟨1219643570806664602264945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6504765710968877878746373 1219643570806664602264945)
          ·
            refine ⟨914732678104998451698709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219643570806664602264945 914732678104998451698709)
            ·
              refine ⟨42878094286171802423377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 914732678104998451698709 42878094286171802423377)
              ·
                rfl

theorem cell19_422743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_422743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422743 prefixEnd_422743 := by exact prefixLift 422743
  have htrace : WordTrace (prefixWord ++ tailWord_422743) baseStart_422743 baseEnd_422743 := by
    simpa [prefixWord, tailWord_422743, baseEnd_422743] using wordTrace_append hprefix tailTrace_422743
  have hstable : (prefixWord ++ tailWord_422743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422743).length < 2 ^ (prefixWord ++ tailWord_422743).sum := by decide
  have hdescent : baseEnd_422743 < baseStart_422743 := by decide
  rcases family_descends (prefixWord ++ tailWord_422743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422817 : List Nat := [1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_422817 : Nat := 118140960795 + 422817 * 2 ^ 59
def prefixEnd_422817 : Nat := 4983230072969 + 3 ^ 40 * 422817 * 2
def baseEnd_422817 : Nat := 128656799936105161625485

theorem tailTrace_422817 : CollatzResearch.WordTrace tailWord_422817 prefixEnd_422817 128656799936105161625485 := by
  unfold tailWord_422817
  simp only [CollatzResearch.WordTrace]
  refine ⟨15421402909213695239666705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10280935272809130159777803 15421402909213695239666705)
  ·
    refine ⟨11566052181910271429750029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15421402909213695239666705 11566052181910271429750029)
    ·
      refine ⟨4337269568216351786156261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11566052181910271429750029 4337269568216351786156261)
      ·
        refine ⟨813238044040565959904299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4337269568216351786156261 813238044040565959904299)
        ·
          refine ⟨1219857066060848939856449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813238044040565959904299 1219857066060848939856449)
          ·
            refine ⟨914892799545636704892337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219857066060848939856449 914892799545636704892337)
            ·
              refine ⟨686169599659227528669253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914892799545636704892337 686169599659227528669253)
              ·
                refine ⟨128656799936105161625485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 686169599659227528669253 128656799936105161625485)
                ·
                  rfl

theorem cell19_422817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_422817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422817 prefixEnd_422817 := by exact prefixLift 422817
  have htrace : WordTrace (prefixWord ++ tailWord_422817) baseStart_422817 baseEnd_422817 := by
    simpa [prefixWord, tailWord_422817, baseEnd_422817] using wordTrace_append hprefix tailTrace_422817
  have hstable : (prefixWord ++ tailWord_422817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422817).length < 2 ^ (prefixWord ++ tailWord_422817).sum := by decide
  have hdescent : baseEnd_422817 < baseStart_422817 := by decide
  rcases family_descends (prefixWord ++ tailWord_422817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422859 : List Nat := [1, 1, 1, 1, 3, 12]
def baseStart_422859 : Nat := 118140960795 + 422859 * 2 ^ 59
def prefixEnd_422859 : Nat := 4983230072969 + 3 ^ 40 * 422859 * 2
def baseEnd_422859 : Nat := 14296619988784612076893

theorem tailTrace_422859 : CollatzResearch.WordTrace tailWord_422859 prefixEnd_422859 14296619988784612076893 := by
  unfold tailWord_422859
  simp only [CollatzResearch.WordTrace]
  refine ⟨15422934775061536412695631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10281956516707690941797087 15422934775061536412695631)
  ·
    refine ⟨23134402162592304619043447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15422934775061536412695631 23134402162592304619043447)
    ·
      refine ⟨34701603243888456928565171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23134402162592304619043447 34701603243888456928565171)
      ·
        refine ⟨52052404865832685392847757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34701603243888456928565171 52052404865832685392847757)
        ·
          refine ⟨19519651824687257022317909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52052404865832685392847757 19519651824687257022317909)
          ·
            refine ⟨14296619988784612076893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19519651824687257022317909 14296619988784612076893)
            ·
              rfl

theorem cell19_422859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 12].length) (baseStart_422859 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422859 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422859 prefixEnd_422859 := by exact prefixLift 422859
  have htrace : WordTrace (prefixWord ++ tailWord_422859) baseStart_422859 baseEnd_422859 := by
    simpa [prefixWord, tailWord_422859, baseEnd_422859] using wordTrace_append hprefix tailTrace_422859
  have hstable : (prefixWord ++ tailWord_422859).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422859).length < 2 ^ (prefixWord ++ tailWord_422859).sum := by decide
  have hdescent : baseEnd_422859 < baseStart_422859 := by decide
  rcases family_descends (prefixWord ++ tailWord_422859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422874 : List Nat := [3, 1, 1, 2, 4, 3, 1, 4]
def baseStart_422874 : Nat := 118140960795 + 422874 * 2 ^ 59
def prefixEnd_422874 : Nat := 4983230072969 + 3 ^ 40 * 422874 * 2
def baseEnd_422874 : Nat := 128674144171545918358663

theorem tailTrace_422874 : CollatzResearch.WordTrace tailWord_422874 prefixEnd_422874 128674144171545918358663 := by
  unfold tailWord_422874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3855870467501798493622919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10282321246671462649661117 3855870467501798493622919)
  ·
    refine ⟨5783805701252697740434379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3855870467501798493622919 5783805701252697740434379)
    ·
      refine ⟨8675708551879046610651569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5783805701252697740434379 8675708551879046610651569)
      ·
        refine ⟨6506781413909284957988677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8675708551879046610651569 6506781413909284957988677)
        ·
          refine ⟨1220021515107990929622877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6506781413909284957988677 1220021515107990929622877)
          ·
            refine ⟨457508068165496598608579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1220021515107990929622877 457508068165496598608579)
            ·
              refine ⟨686262102248244897912869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457508068165496598608579 686262102248244897912869)
              ·
                refine ⟨128674144171545918358663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 686262102248244897912869 128674144171545918358663)
                ·
                  rfl

theorem cell19_422874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_422874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422874 prefixEnd_422874 := by exact prefixLift 422874
  have htrace : WordTrace (prefixWord ++ tailWord_422874) baseStart_422874 baseEnd_422874 := by
    simpa [prefixWord, tailWord_422874, baseEnd_422874] using wordTrace_append hprefix tailTrace_422874
  have hstable : (prefixWord ++ tailWord_422874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422874).length < 2 ^ (prefixWord ++ tailWord_422874).sum := by decide
  have hdescent : baseEnd_422874 < baseStart_422874 := by decide
  rcases family_descends (prefixWord ++ tailWord_422874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422948 : List Nat := [2, 3, 1, 4, 1, 3, 2, 3]
def baseStart_422948 : Nat := 118140960795 + 422948 * 2 ^ 59
def prefixEnd_422948 : Nat := 4983230072969 + 3 ^ 40 * 422948 * 2
def baseEnd_422948 : Nat := 128696661249135672714017

theorem tailTrace_422948 : CollatzResearch.WordTrace tailWord_422948 prefixEnd_422948 128696661249135672714017 := by
  unfold tailWord_422948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7713090435869552306342749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10284120581159403075123665 7713090435869552306342749)
  ·
    refine ⟨2892408913451082114878531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7713090435869552306342749 2892408913451082114878531)
    ·
      refine ⟨4338613370176623172317797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2892408913451082114878531 4338613370176623172317797)
      ·
        refine ⟨813490006908116844809587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4338613370176623172317797 813490006908116844809587)
        ·
          refine ⟨1220235010362175267214381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813490006908116844809587 1220235010362175267214381)
          ·
            refine ⟨457588128885815725205393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1220235010362175267214381 457588128885815725205393)
            ·
              refine ⟨343191096664361793904045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457588128885815725205393 343191096664361793904045)
              ·
                refine ⟨128696661249135672714017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343191096664361793904045 128696661249135672714017)
                ·
                  rfl

theorem cell19_422948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_422948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422948 prefixEnd_422948 := by exact prefixLift 422948
  have htrace : WordTrace (prefixWord ++ tailWord_422948) baseStart_422948 baseEnd_422948 := by
    simpa [prefixWord, tailWord_422948, baseEnd_422948] using wordTrace_append hprefix tailTrace_422948
  have hstable : (prefixWord ++ tailWord_422948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422948).length < 2 ^ (prefixWord ++ tailWord_422948).sum := by decide
  have hdescent : baseEnd_422948 < baseStart_422948 := by decide
  rcases family_descends (prefixWord ++ tailWord_422948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422990 : List Nat := [4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_422990 : Nat := 118140960795 + 422990 * 2 ^ 59
def prefixEnd_422990 : Nat := 4983230072969 + 3 ^ 40 * 422990 * 2
def baseEnd_422990 : Nat := 128709441212092019780569

theorem tailTrace_422990 : CollatzResearch.WordTrace tailWord_422990 prefixEnd_422990 128709441212092019780569 := by
  unfold tailWord_422990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928464092198368223214303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10285141825057963857142949 1928464092198368223214303)
  ·
    refine ⟨2892696138297552334821455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1928464092198368223214303 2892696138297552334821455)
    ·
      refine ⟨4339044207446328502232183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2892696138297552334821455 4339044207446328502232183)
      ·
        refine ⟨6508566311169492753348275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4339044207446328502232183 6508566311169492753348275)
        ·
          refine ⟨9762849466754239130022413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6508566311169492753348275 9762849466754239130022413)
          ·
            refine ⟨3661068550032839673758405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9762849466754239130022413 3661068550032839673758405)
            ·
              refine ⟨686450353131157438829701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3661068550032839673758405 686450353131157438829701)
              ·
                refine ⟨128709441212092019780569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 686450353131157438829701 128709441212092019780569)
                ·
                  rfl

theorem cell19_422990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_422990 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_422990 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_422990 prefixEnd_422990 := by exact prefixLift 422990
  have htrace : WordTrace (prefixWord ++ tailWord_422990) baseStart_422990 baseEnd_422990 := by
    simpa [prefixWord, tailWord_422990, baseEnd_422990] using wordTrace_append hprefix tailTrace_422990
  have hstable : (prefixWord ++ tailWord_422990).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422990).length < 2 ^ (prefixWord ++ tailWord_422990).sum := by decide
  have hdescent : baseEnd_422990 < baseStart_422990 := by decide
  rcases family_descends (prefixWord ++ tailWord_422990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423045 : List Nat := [1, 3, 1, 1, 6, 2, 1, 4]
def baseStart_423045 : Nat := 118140960795 + 423045 * 2 ^ 59
def prefixEnd_423045 : Nat := 4983230072969 + 3 ^ 40 * 423045 * 2
def baseEnd_423045 : Nat := 128726176877868188558197

theorem tailTrace_423045 : CollatzResearch.WordTrace tailWord_423045 prefixEnd_423045 128726176877868188558197 := by
  unfold tailWord_423045
  simp only [CollatzResearch.WordTrace]
  refine ⟨15429718752387690178966589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10286479168258460119311059 15429718752387690178966589)
  ·
    refine ⟨5786144532145383817112471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15429718752387690178966589 5786144532145383817112471)
    ·
      refine ⟨8679216798218075725668707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5786144532145383817112471 8679216798218075725668707)
      ·
        refine ⟨13018825197327113588503061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8679216798218075725668707 13018825197327113588503061)
        ·
          refine ⟨610257431124708449461081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13018825197327113588503061 610257431124708449461081)
          ·
            refine ⟨457693073343531337095811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610257431124708449461081 457693073343531337095811)
            ·
              refine ⟨686539610015297005643717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457693073343531337095811 686539610015297005643717)
              ·
                refine ⟨128726176877868188558197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 686539610015297005643717 128726176877868188558197)
                ·
                  rfl

theorem cell19_423045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_423045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423045 prefixEnd_423045 := by exact prefixLift 423045
  have htrace : WordTrace (prefixWord ++ tailWord_423045) baseStart_423045 baseEnd_423045 := by
    simpa [prefixWord, tailWord_423045, baseEnd_423045] using wordTrace_append hprefix tailTrace_423045
  have hstable : (prefixWord ++ tailWord_423045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423045).length < 2 ^ (prefixWord ++ tailWord_423045).sum := by decide
  have hdescent : baseEnd_423045 < baseStart_423045 := by decide
  rcases family_descends (prefixWord ++ tailWord_423045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423064 : List Nat := [2, 1, 2, 4, 2, 2, 3, 3]
def baseStart_423064 : Nat := 118140960795 + 423064 * 2 ^ 59
def prefixEnd_423064 : Nat := 4983230072969 + 3 ^ 40 * 423064 * 2
def baseEnd_423064 : Nat := 128731958289681774135923

theorem tailTrace_423064 : CollatzResearch.WordTrace tailWord_423064 prefixEnd_423064 128731958289681774135923 := by
  unfold tailWord_423064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7715205869659428211954123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10286941159545904282605497 7715205869659428211954123)
  ·
    refine ⟨11572808804489142317931185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7715205869659428211954123 11572808804489142317931185)
    ·
      refine ⟨8679606603366856738448389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11572808804489142317931185 8679606603366856738448389)
      ·
        refine ⟨1627426238131285638459073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8679606603366856738448389 1627426238131285638459073)
        ·
          refine ⟨1220569678598464228844305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1627426238131285638459073 1220569678598464228844305)
          ·
            refine ⟨915427258948848171633229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220569678598464228844305 915427258948848171633229)
            ·
              refine ⟨343285222105818064362461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 915427258948848171633229 343285222105818064362461)
              ·
                refine ⟨128731958289681774135923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343285222105818064362461 128731958289681774135923)
                ·
                  rfl

theorem cell19_423064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_423064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423064 prefixEnd_423064 := by exact prefixLift 423064
  have htrace : WordTrace (prefixWord ++ tailWord_423064) baseStart_423064 baseEnd_423064 := by
    simpa [prefixWord, tailWord_423064, baseEnd_423064] using wordTrace_append hprefix tailTrace_423064
  have hstable : (prefixWord ++ tailWord_423064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423064).length < 2 ^ (prefixWord ++ tailWord_423064).sum := by decide
  have hdescent : baseEnd_423064 < baseStart_423064 := by decide
  rcases family_descends (prefixWord ++ tailWord_423064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423199 : List Nat := [1, 1, 2, 4, 5, 6]
def baseStart_423199 : Nat := 118140960795 + 423199 * 2 ^ 59
def prefixEnd_423199 : Nat := 4983230072969 + 3 ^ 40 * 423199 * 2
def baseEnd_423199 : Nat := 14308115193560162348395

theorem tailTrace_423199 : CollatzResearch.WordTrace tailWord_423199 prefixEnd_423199 14308115193560162348395 := by
  unfold tailWord_423199
  simp only [CollatzResearch.WordTrace]
  refine ⟨15435335593829774480072651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10290223729219849653381767 15435335593829774480072651)
  ·
    refine ⟨23153003390744661720108977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15435335593829774480072651 23153003390744661720108977)
    ·
      refine ⟨17364752543058496290081733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23153003390744661720108977 17364752543058496290081733)
      ·
        refine ⟨3255891101823468054390325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17364752543058496290081733 3255891101823468054390325)
        ·
          refine ⟨305239790795950130099093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3255891101823468054390325 305239790795950130099093)
          ·
            refine ⟨14308115193560162348395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 305239790795950130099093 14308115193560162348395)
            ·
              rfl

theorem cell19_423199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 6].length) (baseStart_423199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423199 prefixEnd_423199 := by exact prefixLift 423199
  have htrace : WordTrace (prefixWord ++ tailWord_423199) baseStart_423199 baseEnd_423199 := by
    simpa [prefixWord, tailWord_423199, baseEnd_423199] using wordTrace_append hprefix tailTrace_423199
  have hstable : (prefixWord ++ tailWord_423199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423199).length < 2 ^ (prefixWord ++ tailWord_423199).sum := by decide
  have hdescent : baseEnd_423199 < baseStart_423199 := by decide
  rcases family_descends (prefixWord ++ tailWord_423199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423218 : List Nat := [3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_423218 : Nat := 118140960795 + 423218 * 2 ^ 59
def prefixEnd_423218 : Nat := 4983230072969 + 3 ^ 40 * 423218 * 2
def baseEnd_423218 : Nat := 128778818153855046713281

theorem tailTrace_423218 : CollatzResearch.WordTrace tailWord_423218 prefixEnd_423218 128778818153855046713281 := by
  unfold tailWord_423218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3859007145190235181253577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10290685720507293816676205 3859007145190235181253577)
  ·
    refine ⟨2894255358892676385940183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3859007145190235181253577 2894255358892676385940183)
    ·
      refine ⟨4341383038339014578910275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2894255358892676385940183 4341383038339014578910275)
      ·
        refine ⟨6512074557508521868365413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4341383038339014578910275 6512074557508521868365413)
        ·
          refine ⟨1221013979532847850318515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6512074557508521868365413 1221013979532847850318515)
          ·
            refine ⟨1831520969299271775477773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221013979532847850318515 1831520969299271775477773)
            ·
              refine ⟨686820363487226915804165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1831520969299271775477773 686820363487226915804165)
              ·
                refine ⟨128778818153855046713281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 686820363487226915804165 128778818153855046713281)
                ·
                  rfl

theorem cell19_423218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_423218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423218 prefixEnd_423218 := by exact prefixLift 423218
  have htrace : WordTrace (prefixWord ++ tailWord_423218) baseStart_423218 baseEnd_423218 := by
    simpa [prefixWord, tailWord_423218, baseEnd_423218] using wordTrace_append hprefix tailTrace_423218
  have hstable : (prefixWord ++ tailWord_423218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423218).length < 2 ^ (prefixWord ++ tailWord_423218).sum := by decide
  have hdescent : baseEnd_423218 < baseStart_423218 := by decide
  rcases family_descends (prefixWord ++ tailWord_423218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423372 : List Nat := [2, 2, 1, 4, 2, 8]
def baseStart_423372 : Nat := 118140960795 + 423372 * 2 ^ 59
def prefixEnd_423372 : Nat := 4983230072969 + 3 ^ 40 * 423372 * 2
def baseEnd_423372 : Nat := 14313964224225368810071

theorem tailTrace_423372 : CollatzResearch.WordTrace tailWord_423372 prefixEnd_423372 14313964224225368810071 := by
  unfold tailWord_423372
  simp only [CollatzResearch.WordTrace]
  refine ⟨7720822711101512513060185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10294430281468683350746913 7720822711101512513060185)
  ·
    refine ⟨5790617033326134384795139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7720822711101512513060185 5790617033326134384795139)
    ·
      refine ⟨8685925549989201577192709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5790617033326134384795139 8685925549989201577192709)
      ·
        refine ⟨1628611040622975295723633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8685925549989201577192709 1628611040622975295723633)
        ·
          refine ⟨1221458280467231471792725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1628611040622975295723633 1221458280467231471792725)
          ·
            refine ⟨14313964224225368810071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1221458280467231471792725 14313964224225368810071)
            ·
              rfl

theorem cell19_423372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 8].length) (baseStart_423372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423372 prefixEnd_423372 := by exact prefixLift 423372
  have htrace : WordTrace (prefixWord ++ tailWord_423372) baseStart_423372 baseEnd_423372 := by
    simpa [prefixWord, tailWord_423372, baseEnd_423372] using wordTrace_append hprefix tailTrace_423372
  have hstable : (prefixWord ++ tailWord_423372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423372).length < 2 ^ (prefixWord ++ tailWord_423372).sum := by decide
  have hdescent : baseEnd_423372 < baseStart_423372 := by decide
  rcases family_descends (prefixWord ++ tailWord_423372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423389 : List Nat := [1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_423389 : Nat := 118140960795 + 423389 * 2 ^ 59
def prefixEnd_423389 : Nat := 4983230072969 + 3 ^ 40 * 423389 * 2
def baseEnd_423389 : Nat := 128830850860177316912815

theorem tailTrace_423389 : CollatzResearch.WordTrace tailWord_423389 prefixEnd_423389 128830850860177316912815 := by
  unfold tailWord_423389
  simp only [CollatzResearch.WordTrace]
  refine ⟨15442265463141436929489221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10294843642094291286326147 15442265463141436929489221)
  ·
    refine ⟨2895424774339019424279229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15442265463141436929489221 2895424774339019424279229)
    ·
      refine ⟨1085784290377132284104711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2895424774339019424279229 1085784290377132284104711)
      ·
        refine ⟨1628676435565698426157067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1085784290377132284104711 1628676435565698426157067)
        ·
          refine ⟨2443014653348547639235601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628676435565698426157067 2443014653348547639235601)
          ·
            refine ⟨1832260990011410729426701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2443014653348547639235601 1832260990011410729426701)
            ·
              refine ⟨687097871254279023535013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1832260990011410729426701 687097871254279023535013)
              ·
                refine ⟨128830850860177316912815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 687097871254279023535013 128830850860177316912815)
                ·
                  rfl

theorem cell19_423389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_423389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423389 prefixEnd_423389 := by exact prefixLift 423389
  have htrace : WordTrace (prefixWord ++ tailWord_423389) baseStart_423389 baseEnd_423389 := by
    simpa [prefixWord, tailWord_423389, baseEnd_423389] using wordTrace_append hprefix tailTrace_423389
  have hstable : (prefixWord ++ tailWord_423389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423389).length < 2 ^ (prefixWord ++ tailWord_423389).sum := by decide
  have hdescent : baseEnd_423389 < baseStart_423389 := by decide
  rcases family_descends (prefixWord ++ tailWord_423389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423408 : List Nat := [2, 1, 1, 1, 3, 5, 3, 3]
def baseStart_423408 : Nat := 118140960795 + 423408 * 2 ^ 59
def prefixEnd_423408 : Nat := 4983230072969 + 3 ^ 40 * 423408 * 2
def baseEnd_423408 : Nat := 128836632271990902490541

theorem tailTrace_423408 : CollatzResearch.WordTrace tailWord_423408 prefixEnd_423408 128836632271990902490541 := by
  unfold tailWord_423408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721479225036301587215439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10295305633381735449620585 7721479225036301587215439)
  ·
    refine ⟨11582218837554452380823159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7721479225036301587215439 11582218837554452380823159)
    ·
      refine ⟨17373328256331678571234739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11582218837554452380823159 17373328256331678571234739)
      ·
        refine ⟨26059992384497517856852109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17373328256331678571234739 26059992384497517856852109)
        ·
          refine ⟨9772497144186569196319541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26059992384497517856852109 9772497144186569196319541)
          ·
            refine ⟨916171607267490862154957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9772497144186569196319541 916171607267490862154957)
            ·
              refine ⟨343564352725309073308109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 916171607267490862154957 343564352725309073308109)
              ·
                refine ⟨128836632271990902490541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343564352725309073308109 128836632271990902490541)
                ·
                  rfl

theorem cell19_423408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_423408 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423408 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423408 prefixEnd_423408 := by exact prefixLift 423408
  have htrace : WordTrace (prefixWord ++ tailWord_423408) baseStart_423408 baseEnd_423408 := by
    simpa [prefixWord, tailWord_423408, baseEnd_423408] using wordTrace_append hprefix tailTrace_423408
  have hstable : (prefixWord ++ tailWord_423408).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423408).length < 2 ^ (prefixWord ++ tailWord_423408).sum := by decide
  have hdescent : baseEnd_423408 < baseStart_423408 := by decide
  rcases family_descends (prefixWord ++ tailWord_423408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423484 : List Nat := [2, 2, 2, 2, 4, 2, 5]
def baseStart_423484 : Nat := 118140960795 + 423484 * 2 ^ 59
def prefixEnd_423484 : Nat := 4983230072969 + 3 ^ 40 * 423484 * 2
def baseEnd_423484 : Nat := 42953252639748414933815

theorem tailTrace_423484 : CollatzResearch.WordTrace tailWord_423484 prefixEnd_423484 42953252639748414933815 := by
  unfold tailWord_423484
  simp only [CollatzResearch.WordTrace]
  refine ⟨7722865198898634077098753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10297153598531512102798337 7722865198898634077098753)
  ·
    refine ⟨5792148899173975557824065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7722865198898634077098753 5792148899173975557824065)
    ·
      refine ⟨4344111674380481668368049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5792148899173975557824065 4344111674380481668368049)
      ·
        refine ⟨3258083755785361251276037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4344111674380481668368049 3258083755785361251276037)
        ·
          refine ⟨610890704209755234614257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3258083755785361251276037 610890704209755234614257)
          ·
            refine ⟨458168028157316425960693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610890704209755234614257 458168028157316425960693)
            ·
              refine ⟨42953252639748414933815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 458168028157316425960693 42953252639748414933815)
              ·
                rfl

theorem cell19_423484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_423484 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423484 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423484 prefixEnd_423484 := by exact prefixLift 423484
  have htrace : WordTrace (prefixWord ++ tailWord_423484) baseStart_423484 baseEnd_423484 := by
    simpa [prefixWord, tailWord_423484, baseEnd_423484] using wordTrace_append hprefix tailTrace_423484
  have hstable : (prefixWord ++ tailWord_423484).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423484).length < 2 ^ (prefixWord ++ tailWord_423484).sum := by decide
  have hdescent : baseEnd_423484 < baseStart_423484 := by decide
  rcases family_descends (prefixWord ++ tailWord_423484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423501 : List Nat := [1, 6, 1, 1, 3, 1, 2, 4]
def baseStart_423501 : Nat := 118140960795 + 423501 * 2 ^ 59
def prefixEnd_423501 : Nat := 4983230072969 + 3 ^ 40 * 423501 * 2
def baseEnd_423501 : Nat := 128864930761394242423621

theorem tailTrace_423501 : CollatzResearch.WordTrace tailWord_423501 prefixEnd_423501 128864930761394242423621 := by
  unfold tailWord_423501
  simp only [CollatzResearch.WordTrace]
  refine ⟨15446350438735680057566357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10297566959157120038377571 15446350438735680057566357)
  ·
    refine ⟨724047676815735002698423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15446350438735680057566357 724047676815735002698423)
    ·
      refine ⟨1086071515223602504047635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724047676815735002698423 1086071515223602504047635)
      ·
        refine ⟨1629107272835403756071453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086071515223602504047635 1629107272835403756071453)
        ·
          refine ⟨610915227313276408526795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1629107272835403756071453 610915227313276408526795)
          ·
            refine ⟨916372840969914612790193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610915227313276408526795 916372840969914612790193)
            ·
              refine ⟨687279630727435959592645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916372840969914612790193 687279630727435959592645)
              ·
                refine ⟨128864930761394242423621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 687279630727435959592645 128864930761394242423621)
                ·
                  rfl

theorem cell19_423501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_423501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423501 prefixEnd_423501 := by exact prefixLift 423501
  have htrace : WordTrace (prefixWord ++ tailWord_423501) baseStart_423501 baseEnd_423501 := by
    simpa [prefixWord, tailWord_423501, baseEnd_423501] using wordTrace_append hprefix tailTrace_423501
  have hstable : (prefixWord ++ tailWord_423501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423501).length < 2 ^ (prefixWord ++ tailWord_423501).sum := by decide
  have hdescent : baseEnd_423501 < baseStart_423501 := by decide
  rcases family_descends (prefixWord ++ tailWord_423501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423505 : List Nat := [1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_423505 : Nat := 118140960795 + 423505 * 2 ^ 59
def prefixEnd_423505 : Nat := 4983230072969 + 3 ^ 40 * 423505 * 2
def baseEnd_423505 : Nat := 128866147900723418334721

theorem tailTrace_423505 : CollatzResearch.WordTrace tailWord_423505 prefixEnd_423505 128866147900723418334721 := by
  unfold tailWord_423505
  simp only [CollatzResearch.WordTrace]
  refine ⟨15446496330721188740711969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10297664220480792493807979 15446496330721188740711969)
  ·
    refine ⟨11584872248040891555533977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15446496330721188740711969 11584872248040891555533977)
    ·
      refine ⟨8688654186030668666650483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11584872248040891555533977 8688654186030668666650483)
      ·
        refine ⟨13032981279046002999975725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8688654186030668666650483 13032981279046002999975725)
        ·
          refine ⟨4887367979642251124990897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13032981279046002999975725 4887367979642251124990897)
          ·
            refine ⟨3665525984731688343743173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4887367979642251124990897 3665525984731688343743173)
            ·
              refine ⟨687286122137191564451845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3665525984731688343743173 687286122137191564451845)
              ·
                refine ⟨128866147900723418334721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 687286122137191564451845 128866147900723418334721)
                ·
                  rfl

theorem cell19_423505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_423505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423505 prefixEnd_423505 := by exact prefixLift 423505
  have htrace : WordTrace (prefixWord ++ tailWord_423505) baseStart_423505 baseEnd_423505 := by
    simpa [prefixWord, tailWord_423505, baseEnd_423505] using wordTrace_append hprefix tailTrace_423505
  have hstable : (prefixWord ++ tailWord_423505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423505).length < 2 ^ (prefixWord ++ tailWord_423505).sum := by decide
  have hdescent : baseEnd_423505 < baseStart_423505 := by decide
  rcases family_descends (prefixWord ++ tailWord_423505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423524 : List Nat := [2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_423524 : Nat := 118140960795 + 423524 * 2 ^ 59
def prefixEnd_423524 : Nat := 4983230072969 + 3 ^ 40 * 423524 * 2
def baseEnd_423524 : Nat := 128871929312537003912447

theorem tailTrace_423524 : CollatzResearch.WordTrace tailWord_423524 prefixEnd_423524 128871929312537003912447 := by
  unfold tailWord_423524
  simp only [CollatzResearch.WordTrace]
  refine ⟨7723594658826177492826813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10298126211768236657102417 7723594658826177492826813)
  ·
    refine ⟨2896347997059816559810055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7723594658826177492826813 2896347997059816559810055)
    ·
      refine ⟨4344521995589724839715083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2896347997059816559810055 4344521995589724839715083)
      ·
        refine ⟨6516782993384587259572625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4344521995589724839715083 6516782993384587259572625)
        ·
          refine ⟨4887587245038440444679469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6516782993384587259572625 4887587245038440444679469)
          ·
            refine ⟨1832845216889415166754801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4887587245038440444679469 1832845216889415166754801)
            ·
              refine ⟨1374633912667061375066101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832845216889415166754801 1374633912667061375066101)
              ·
                refine ⟨128871929312537003912447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1374633912667061375066101 128871929312537003912447)
                ·
                  rfl

theorem cell19_423524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_423524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423524 prefixEnd_423524 := by exact prefixLift 423524
  have htrace : WordTrace (prefixWord ++ tailWord_423524) baseStart_423524 baseEnd_423524 := by
    simpa [prefixWord, tailWord_423524, baseEnd_423524] using wordTrace_append hprefix tailTrace_423524
  have hstable : (prefixWord ++ tailWord_423524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423524).length < 2 ^ (prefixWord ++ tailWord_423524).sum := by decide
  have hdescent : baseEnd_423524 < baseStart_423524 := by decide
  rcases family_descends (prefixWord ++ tailWord_423524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423634 : List Nat := [3, 2, 2, 2, 2, 3, 2, 3]
def baseStart_423634 : Nat := 118140960795 + 423634 * 2 ^ 59
def prefixEnd_423634 : Nat := 4983230072969 + 3 ^ 40 * 423634 * 2
def baseEnd_423634 : Nat := 128905400644089341467703

theorem tailTrace_423634 : CollatzResearch.WordTrace tailWord_423634 prefixEnd_423634 128905400644089341467703 := by
  unfold tailWord_423634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3862800336813460943039489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10300800898169229181438637 3862800336813460943039489)
  ·
    refine ⟨2897100252610095707279617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3862800336813460943039489 2897100252610095707279617)
    ·
      refine ⟨2172825189457571780459713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2897100252610095707279617 2172825189457571780459713)
      ·
        refine ⟨1629618892093178835344785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2172825189457571780459713 1629618892093178835344785)
        ·
          refine ⟨1222214169069884126508589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1629618892093178835344785 1222214169069884126508589)
          ·
            refine ⟨458330313401206547440721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1222214169069884126508589 458330313401206547440721)
            ·
              refine ⟨343747735050904910580541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458330313401206547440721 343747735050904910580541)
              ·
                refine ⟨128905400644089341467703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343747735050904910580541 128905400644089341467703)
                ·
                  rfl

theorem cell19_423634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_423634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423634 prefixEnd_423634 := by exact prefixLift 423634
  have htrace : WordTrace (prefixWord ++ tailWord_423634) baseStart_423634 baseEnd_423634 := by
    simpa [prefixWord, tailWord_423634, baseEnd_423634] using wordTrace_append hprefix tailTrace_423634
  have hstable : (prefixWord ++ tailWord_423634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423634).length < 2 ^ (prefixWord ++ tailWord_423634).sum := by decide
  have hdescent : baseEnd_423634 < baseStart_423634 := by decide
  rcases family_descends (prefixWord ++ tailWord_423634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423636 : List Nat := [2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_423636 : Nat := 118140960795 + 423636 * 2 ^ 59
def prefixEnd_423636 : Nat := 4983230072969 + 3 ^ 40 * 423636 * 2
def baseEnd_423636 : Nat := 128906009213753929423253

theorem tailTrace_423636 : CollatzResearch.WordTrace tailWord_423636 prefixEnd_423636 128906009213753929423253 := by
  unfold tailWord_423636
  simp only [CollatzResearch.WordTrace]
  refine ⟨7725637146623299056865381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10300849528831065409153841 7725637146623299056865381)
  ·
    refine ⟨1448556964991868573162259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7725637146623299056865381 1448556964991868573162259)
    ·
      refine ⟨2172835447487802859743389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448556964991868573162259 2172835447487802859743389)
      ·
        refine ⟨814813292807926072403771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2172835447487802859743389 814813292807926072403771)
        ·
          refine ⟨1222219939211889108605657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814813292807926072403771 1222219939211889108605657)
          ·
            refine ⟨916664954408916831454243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1222219939211889108605657 916664954408916831454243)
            ·
              refine ⟨1374997431613375247181365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916664954408916831454243 1374997431613375247181365)
              ·
                refine ⟨128906009213753929423253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1374997431613375247181365 128906009213753929423253)
                ·
                  rfl

theorem cell19_423636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_423636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423636 prefixEnd_423636 := by exact prefixLift 423636
  have htrace : WordTrace (prefixWord ++ tailWord_423636) baseStart_423636 baseEnd_423636 := by
    simpa [prefixWord, tailWord_423636, baseEnd_423636] using wordTrace_append hprefix tailTrace_423636
  have hstable : (prefixWord ++ tailWord_423636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423636).length < 2 ^ (prefixWord ++ tailWord_423636).sum := by decide
  have hdescent : baseEnd_423636 < baseStart_423636 := by decide
  rcases family_descends (prefixWord ++ tailWord_423636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423659 : List Nat := [1, 1, 1, 1, 2, 4, 9]
def baseStart_423659 : Nat := 118140960795 + 423659 * 2 ^ 59
def prefixEnd_423659 : Nat := 4983230072969 + 3 ^ 40 * 423659 * 2
def baseEnd_423659 : Nat := 42971002588298896970693

theorem tailTrace_423659 : CollatzResearch.WordTrace tailWord_423659 prefixEnd_423659 42971002588298896970693 := by
  unfold tailWord_423659
  simp only [CollatzResearch.WordTrace]
  refine ⟨15452113172163273041818031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10301408781442182027878687 15452113172163273041818031)
  ·
    refine ⟨23178169758244909562727047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15452113172163273041818031 23178169758244909562727047)
    ·
      refine ⟨34767254637367364344090571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23178169758244909562727047 34767254637367364344090571)
      ·
        refine ⟨52150881956051046516135857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34767254637367364344090571 52150881956051046516135857)
        ·
          refine ⟨39113161467038284887101893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52150881956051046516135857 39113161467038284887101893)
          ·
            refine ⟨7333717775069678416331605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39113161467038284887101893 7333717775069678416331605)
            ·
              refine ⟨42971002588298896970693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7333717775069678416331605 42971002588298896970693)
              ·
                rfl

theorem cell19_423659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_423659 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423659 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423659 prefixEnd_423659 := by exact prefixLift 423659
  have htrace : WordTrace (prefixWord ++ tailWord_423659) baseStart_423659 baseEnd_423659 := by
    simpa [prefixWord, tailWord_423659, baseEnd_423659] using wordTrace_append hprefix tailTrace_423659
  have hstable : (prefixWord ++ tailWord_423659).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423659).length < 2 ^ (prefixWord ++ tailWord_423659).sum := by decide
  have hdescent : baseEnd_423659 < baseStart_423659 := by decide
  rcases family_descends (prefixWord ++ tailWord_423659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423676 : List Nat := [2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_423676 : Nat := 118140960795 + 423676 * 2 ^ 59
def prefixEnd_423676 : Nat := 4983230072969 + 3 ^ 40 * 423676 * 2
def baseEnd_423676 : Nat := 128918180607045688534255

theorem tailTrace_423676 : CollatzResearch.WordTrace tailWord_423676 prefixEnd_423676 128918180607045688534255 := by
  unfold tailWord_423676
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726366606550842472593441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10301822142067789963457921 7726366606550842472593441)
  ·
    refine ⟨5794774954913131854445081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7726366606550842472593441 5794774954913131854445081)
    ·
      refine ⟨4346081216184848890833811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5794774954913131854445081 4346081216184848890833811)
      ·
        refine ⟨6519121824277273336250717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346081216184848890833811 6519121824277273336250717)
        ·
          refine ⟨2444670684103977501094019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6519121824277273336250717 2444670684103977501094019)
          ·
            refine ⟨3667006026155966251641029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444670684103977501094019 3667006026155966251641029)
            ·
              refine ⟨687563629904243672182693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3667006026155966251641029 687563629904243672182693)
              ·
                refine ⟨128918180607045688534255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 687563629904243672182693 128918180607045688534255)
                ·
                  rfl

theorem cell19_423676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_423676 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423676 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423676 prefixEnd_423676 := by exact prefixLift 423676
  have htrace : WordTrace (prefixWord ++ tailWord_423676) baseStart_423676 baseEnd_423676 := by
    simpa [prefixWord, tailWord_423676, baseEnd_423676] using wordTrace_append hprefix tailTrace_423676
  have hstable : (prefixWord ++ tailWord_423676).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423676).length < 2 ^ (prefixWord ++ tailWord_423676).sum := by decide
  have hdescent : baseEnd_423676 < baseStart_423676 := by decide
  rcases family_descends (prefixWord ++ tailWord_423676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423710 : List Nat := [4, 3, 2, 2, 1, 7]
def baseStart_423710 : Nat := 118140960795 + 423710 * 2 ^ 59
def prefixEnd_423710 : Nat := 4983230072969 + 3 ^ 40 * 423710 * 2
def baseEnd_423710 : Nat := 14325391810149298197623

theorem tailTrace_423710 : CollatzResearch.WordTrace tailWord_423710 prefixEnd_423710 14325391810149298197623 := by
  unfold tailWord_423710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1931746661872313593990573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10302648863319005834616389 1931746661872313593990573)
  ·
    refine ⟨724404998202117597746465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1931746661872313593990573 724404998202117597746465)
    ·
      refine ⟨543303748651588198309849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 724404998202117597746465 543303748651588198309849)
      ·
        refine ⟨407477811488691148732387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543303748651588198309849 407477811488691148732387)
        ·
          refine ⟨611216717233036723098581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407477811488691148732387 611216717233036723098581)
          ·
            refine ⟨14325391810149298197623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 611216717233036723098581 14325391810149298197623)
            ·
              rfl

theorem cell19_423710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 7].length) (baseStart_423710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423710 prefixEnd_423710 := by exact prefixLift 423710
  have htrace : WordTrace (prefixWord ++ tailWord_423710) baseStart_423710 baseEnd_423710 := by
    simpa [prefixWord, tailWord_423710, baseEnd_423710] using wordTrace_append hprefix tailTrace_423710
  have hstable : (prefixWord ++ tailWord_423710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423710).length < 2 ^ (prefixWord ++ tailWord_423710).sum := by decide
  have hdescent : baseEnd_423710 < baseStart_423710 := by decide
  rcases family_descends (prefixWord ++ tailWord_423710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423731 : List Nat := [1, 1, 1, 2, 7, 2, 1, 4]
def baseStart_423731 : Nat := 118140960795 + 423731 * 2 ^ 59
def prefixEnd_423731 : Nat := 4983230072969 + 3 ^ 40 * 423731 * 2
def baseEnd_423731 : Nat := 128934916272821857311883

theorem tailTrace_423731 : CollatzResearch.WordTrace tailWord_423731 prefixEnd_423731 128934916272821857311883 := by
  unfold tailWord_423731
  simp only [CollatzResearch.WordTrace]
  refine ⟨15454739227902429338439047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10303159485268286225626031 15454739227902429338439047)
  ·
    refine ⟨23182108841853644007658571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15454739227902429338439047 23182108841853644007658571)
    ·
      refine ⟨34773163262780466011487857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23182108841853644007658571 34773163262780466011487857)
      ·
        refine ⟨26079872447085349508615893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34773163262780466011487857 26079872447085349508615893)
        ·
          refine ⟨611247010478562879108185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26079872447085349508615893 611247010478562879108185)
          ·
            refine ⟨458435257858922159331139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611247010478562879108185 458435257858922159331139)
            ·
              refine ⟨687652886788383238996709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458435257858922159331139 687652886788383238996709)
              ·
                refine ⟨128934916272821857311883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 687652886788383238996709 128934916272821857311883)
                ·
                  rfl

theorem cell19_423731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_423731 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423731 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423731 prefixEnd_423731 := by exact prefixLift 423731
  have htrace : WordTrace (prefixWord ++ tailWord_423731) baseStart_423731 baseEnd_423731 := by
    simpa [prefixWord, tailWord_423731, baseEnd_423731] using wordTrace_append hprefix tailTrace_423731
  have hstable : (prefixWord ++ tailWord_423731).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423731).length < 2 ^ (prefixWord ++ tailWord_423731).sum := by decide
  have hdescent : baseEnd_423731 < baseStart_423731 := by decide
  rcases family_descends (prefixWord ++ tailWord_423731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423735 : List Nat := [1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_423735 : Nat := 118140960795 + 423735 * 2 ^ 59
def prefixEnd_423735 : Nat := 4983230072969 + 3 ^ 40 * 423735 * 2
def baseEnd_423735 : Nat := 128936133412151033222983

theorem tailTrace_423735 : CollatzResearch.WordTrace tailWord_423735 prefixEnd_423735 128936133412151033222983 := by
  unfold tailWord_423735
  simp only [CollatzResearch.WordTrace]
  refine ⟨15454885119887938021584659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10303256746591958681056439 15454885119887938021584659)
  ·
    refine ⟨23182327679831907032376989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15454885119887938021584659 23182327679831907032376989)
    ·
      refine ⟨8693372879936965137141371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23182327679831907032376989 8693372879936965137141371)
      ·
        refine ⟨13040059319905447705712057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8693372879936965137141371 13040059319905447705712057)
        ·
          refine ⟨9780044489929085779284043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13040059319905447705712057 9780044489929085779284043)
          ·
            refine ⟨14670066734893628668926065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9780044489929085779284043 14670066734893628668926065)
            ·
              refine ⟨11002550051170221501694549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14670066734893628668926065 11002550051170221501694549)
              ·
                refine ⟨128936133412151033222983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11002550051170221501694549 128936133412151033222983)
                ·
                  rfl

theorem cell19_423735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_423735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423735 prefixEnd_423735 := by exact prefixLift 423735
  have htrace : WordTrace (prefixWord ++ tailWord_423735) baseStart_423735 baseEnd_423735 := by
    simpa [prefixWord, tailWord_423735, baseEnd_423735] using wordTrace_append hprefix tailTrace_423735
  have hstable : (prefixWord ++ tailWord_423735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423735).length < 2 ^ (prefixWord ++ tailWord_423735).sum := by decide
  have hdescent : baseEnd_423735 < baseStart_423735 := by decide
  rcases family_descends (prefixWord ++ tailWord_423735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423792 : List Nat := [2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_423792 : Nat := 118140960795 + 423792 * 2 ^ 59
def prefixEnd_423792 : Nat := 4983230072969 + 3 ^ 40 * 423792 * 2
def baseEnd_423792 : Nat := 128953477647591789956161

theorem tailTrace_423792 : CollatzResearch.WordTrace tailWord_423792 prefixEnd_423792 128953477647591789956161 := by
  unfold tailWord_423792
  simp only [CollatzResearch.WordTrace]
  refine ⟨7728482040340718378204815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10304642720454291170939753 7728482040340718378204815)
  ·
    refine ⟨11592723060511077567307223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7728482040340718378204815 11592723060511077567307223)
    ·
      refine ⟨17389084590766616350960835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11592723060511077567307223 17389084590766616350960835)
      ·
        refine ⟨26083626886149924526441253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17389084590766616350960835 26083626886149924526441253)
        ·
          refine ⟨4890680041153110848707735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26083626886149924526441253 4890680041153110848707735)
          ·
            refine ⟨7336020061729666273061603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890680041153110848707735 7336020061729666273061603)
            ·
              refine ⟨11004030092594499409592405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7336020061729666273061603 11004030092594499409592405)
              ·
                refine ⟨128953477647591789956161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11004030092594499409592405 128953477647591789956161)
                ·
                  rfl

theorem cell19_423792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_423792 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423792 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423792 prefixEnd_423792 := by exact prefixLift 423792
  have htrace : WordTrace (prefixWord ++ tailWord_423792) baseStart_423792 baseEnd_423792 := by
    simpa [prefixWord, tailWord_423792, baseEnd_423792] using wordTrace_append hprefix tailTrace_423792
  have hstable : (prefixWord ++ tailWord_423792).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423792).length < 2 ^ (prefixWord ++ tailWord_423792).sum := by decide
  have hdescent : baseEnd_423792 < baseStart_423792 := by decide
  rcases family_descends (prefixWord ++ tailWord_423792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423826 : List Nat := [3, 2, 3, 2, 1, 3, 5]
def baseStart_423826 : Nat := 118140960795 + 423826 * 2 ^ 59
def prefixEnd_423826 : Nat := 4983230072969 + 3 ^ 40 * 423826 * 2
def baseEnd_423826 : Nat := 42987941110629928400171

theorem tailTrace_423826 : CollatzResearch.WordTrace tailWord_423826 prefixEnd_423826 42987941110629928400171 := by
  unfold tailWord_423826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3864551040639565140786833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10305469441705507042098221 3864551040639565140786833)
  ·
    refine ⟨2898413280479673855590125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3864551040639565140786833 2898413280479673855590125)
    ·
      refine ⟨1086904980179877695846297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2898413280479673855590125 1086904980179877695846297)
      ·
        refine ⟨815178735134908271884723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1086904980179877695846297 815178735134908271884723)
        ·
          refine ⟨1222768102702362407827085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815178735134908271884723 1222768102702362407827085)
          ·
            refine ⟨458538038513385902935157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1222768102702362407827085 458538038513385902935157)
            ·
              refine ⟨42987941110629928400171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 458538038513385902935157 42987941110629928400171)
              ·
                rfl

theorem cell19_423826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_423826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423826 prefixEnd_423826 := by exact prefixLift 423826
  have htrace : WordTrace (prefixWord ++ tailWord_423826) baseStart_423826 baseEnd_423826 := by
    simpa [prefixWord, tailWord_423826, baseEnd_423826] using wordTrace_append hprefix tailTrace_423826
  have hstable : (prefixWord ++ tailWord_423826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423826).length < 2 ^ (prefixWord ++ tailWord_423826).sum := by decide
  have hdescent : baseEnd_423826 < baseStart_423826 := by decide
  rcases family_descends (prefixWord ++ tailWord_423826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423828 : List Nat := [2, 4, 2, 1, 1, 2, 7]
def baseStart_423828 : Nat := 118140960795 + 423828 * 2 ^ 59
def prefixEnd_423828 : Nat := 4983230072969 + 3 ^ 40 * 423828 * 2
def baseEnd_423828 : Nat := 42988143967184791052021

theorem tailTrace_423828 : CollatzResearch.WordTrace tailWord_423828 prefixEnd_423828 42988143967184791052021 := by
  unfold tailWord_423828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729138554275507452360069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10305518072367343269813425 7729138554275507452360069)
  ·
    refine ⟨1449213478926657647317513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7729138554275507452360069 1449213478926657647317513)
    ·
      refine ⟨1086910109194993235488135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1449213478926657647317513 1086910109194993235488135)
      ·
        refine ⟨1630365163792489853232203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086910109194993235488135 1630365163792489853232203)
        ·
          refine ⟨2445547745688734779848305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1630365163792489853232203 2445547745688734779848305)
          ·
            refine ⟨1834160809266551084886229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2445547745688734779848305 1834160809266551084886229)
            ·
              refine ⟨42988143967184791052021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1834160809266551084886229 42988143967184791052021)
              ·
                rfl

theorem cell19_423828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_423828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423828 prefixEnd_423828 := by exact prefixLift 423828
  have htrace : WordTrace (prefixWord ++ tailWord_423828) baseStart_423828 baseEnd_423828 := by
    simpa [prefixWord, tailWord_423828, baseEnd_423828] using wordTrace_append hprefix tailTrace_423828
  have hstable : (prefixWord ++ tailWord_423828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423828).length < 2 ^ (prefixWord ++ tailWord_423828).sum := by decide
  have hdescent : baseEnd_423828 < baseStart_423828 := by decide
  rcases family_descends (prefixWord ++ tailWord_423828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423847 : List Nat := [1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_423847 : Nat := 118140960795 + 423847 * 2 ^ 59
def prefixEnd_423847 : Nat := 4983230072969 + 3 ^ 40 * 423847 * 2
def baseEnd_423847 : Nat := 128970213313367958733789

theorem tailTrace_423847 : CollatzResearch.WordTrace tailWord_423847 prefixEnd_423847 128970213313367958733789 := by
  unfold tailWord_423847
  simp only [CollatzResearch.WordTrace]
  refine ⟨15458970095482181149661795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10305980063654787433107863 15458970095482181149661795)
  ·
    refine ⟨23188455143223271724492693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15458970095482181149661795 23188455143223271724492693)
    ·
      refine ⟨1086958834838590862085595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23188455143223271724492693 1086958834838590862085595)
      ·
        refine ⟨1630438252257886293128393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086958834838590862085595 1630438252257886293128393)
        ·
          refine ⟨1222828689193414719846295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1630438252257886293128393 1222828689193414719846295)
          ·
            refine ⟨1834243033790122079769443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222828689193414719846295 1834243033790122079769443)
            ·
              refine ⟨2751364550685183119654165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1834243033790122079769443 2751364550685183119654165)
              ·
                refine ⟨128970213313367958733789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2751364550685183119654165 128970213313367958733789)
                ·
                  rfl

theorem cell19_423847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_423847 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423847 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423847 prefixEnd_423847 := by exact prefixLift 423847
  have htrace : WordTrace (prefixWord ++ tailWord_423847) baseStart_423847 baseEnd_423847 := by
    simpa [prefixWord, tailWord_423847, baseEnd_423847] using wordTrace_append hprefix tailTrace_423847
  have hstable : (prefixWord ++ tailWord_423847).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423847).length < 2 ^ (prefixWord ++ tailWord_423847).sum := by decide
  have hdescent : baseEnd_423847 < baseStart_423847 := by decide
  rcases family_descends (prefixWord ++ tailWord_423847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423921 : List Nat := [1, 2, 2, 2, 5, 1, 3, 3]
def baseStart_423921 : Nat := 118140960795 + 423921 * 2 ^ 59
def prefixEnd_423921 : Nat := 4983230072969 + 3 ^ 40 * 423921 * 2
def baseEnd_423921 : Nat := 128992730390957713089143

theorem tailTrace_423921 : CollatzResearch.WordTrace tailWord_423921 prefixEnd_423921 128992730390957713089143 := by
  unfold tailWord_423921
  simp only [CollatzResearch.WordTrace]
  refine ⟨15461669097214091787855617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10307779398142727858570411 15461669097214091787855617)
  ·
    refine ⟨11596251822910568840891713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15461669097214091787855617 11596251822910568840891713)
    ·
      refine ⟨8697188867182926630668785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11596251822910568840891713 8697188867182926630668785)
      ·
        refine ⟨6522891650387194973001589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8697188867182926630668785 6522891650387194973001589)
        ·
          refine ⟨611521092223799528718899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6522891650387194973001589 611521092223799528718899)
          ·
            refine ⟨917281638335699293078349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611521092223799528718899 917281638335699293078349)
            ·
              refine ⟨343980614375887234904381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 917281638335699293078349 343980614375887234904381)
              ·
                refine ⟨128992730390957713089143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343980614375887234904381 128992730390957713089143)
                ·
                  rfl

theorem cell19_423921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 3].length) (baseStart_423921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423921 prefixEnd_423921 := by exact prefixLift 423921
  have htrace : WordTrace (prefixWord ++ tailWord_423921) baseStart_423921 baseEnd_423921 := by
    simpa [prefixWord, tailWord_423921, baseEnd_423921] using wordTrace_append hprefix tailTrace_423921
  have hstable : (prefixWord ++ tailWord_423921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423921).length < 2 ^ (prefixWord ++ tailWord_423921).sum := by decide
  have hdescent : baseEnd_423921 < baseStart_423921 := by decide
  rcases family_descends (prefixWord ++ tailWord_423921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423940 : List Nat := [2, 3, 2, 4, 1, 1, 6]
def baseStart_423940 : Nat := 118140960795 + 423940 * 2 ^ 59
def prefixEnd_423940 : Nat := 4983230072969 + 3 ^ 40 * 423940 * 2
def baseEnd_423940 : Nat := 42999503934257099555623

theorem tailTrace_423940 : CollatzResearch.WordTrace tailWord_423940 prefixEnd_423940 42999503934257099555623 := by
  unfold tailWord_423940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7731181042072629016398637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10308241389430172021864849 7731181042072629016398637)
  ·
    refine ⟨2899192890777235881149489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7731181042072629016398637 2899192890777235881149489)
    ·
      refine ⟨2174394668082926910862117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2899192890777235881149489 2174394668082926910862117)
      ·
        refine ⟨407699000265548795786647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2174394668082926910862117 407699000265548795786647)
        ·
          refine ⟨611548500398323193679971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407699000265548795786647 611548500398323193679971)
          ·
            refine ⟨917322750597484790519957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611548500398323193679971 917322750597484790519957)
            ·
              refine ⟨42999503934257099555623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 917322750597484790519957 42999503934257099555623)
              ·
                rfl

theorem cell19_423940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 6].length) (baseStart_423940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423940 prefixEnd_423940 := by exact prefixLift 423940
  have htrace : WordTrace (prefixWord ++ tailWord_423940) baseStart_423940 baseEnd_423940 := by
    simpa [prefixWord, tailWord_423940, baseEnd_423940] using wordTrace_append hprefix tailTrace_423940
  have hstable : (prefixWord ++ tailWord_423940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423940).length < 2 ^ (prefixWord ++ tailWord_423940).sum := by decide
  have hdescent : baseEnd_423940 < baseStart_423940 := by decide
  rcases family_descends (prefixWord ++ tailWord_423940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423944 : List Nat := [2, 1, 3, 2, 1, 2, 8]
def baseStart_423944 : Nat := 118140960795 + 423944 * 2 ^ 59
def prefixEnd_423944 : Nat := 4983230072969 + 3 ^ 40 * 423944 * 2
def baseEnd_423944 : Nat := 42999909647366824859323

theorem tailTrace_423944 : CollatzResearch.WordTrace tailWord_423944 prefixEnd_423944 42999909647366824859323 := by
  unfold tailWord_423944
  simp only [CollatzResearch.WordTrace]
  refine ⟨7731253988065383357971443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10308338650753844477295257 7731253988065383357971443)
  ·
    refine ⟨11596880982098075036957165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7731253988065383357971443 11596880982098075036957165)
    ·
      refine ⟨4348830368286778138858937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11596880982098075036957165 4348830368286778138858937)
      ·
        refine ⟨3261622776215083604144203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4348830368286778138858937 3261622776215083604144203)
        ·
          refine ⟨4892434164322625406216305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261622776215083604144203 4892434164322625406216305)
          ·
            refine ⟨3669325623241969054662229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4892434164322625406216305 3669325623241969054662229)
            ·
              refine ⟨42999909647366824859323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3669325623241969054662229 42999909647366824859323)
              ·
                rfl

theorem cell19_423944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_423944 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423944 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423944 prefixEnd_423944 := by exact prefixLift 423944
  have htrace : WordTrace (prefixWord ++ tailWord_423944) baseStart_423944 baseEnd_423944 := by
    simpa [prefixWord, tailWord_423944, baseEnd_423944] using wordTrace_append hprefix tailTrace_423944
  have hstable : (prefixWord ++ tailWord_423944).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423944).length < 2 ^ (prefixWord ++ tailWord_423944).sum := by decide
  have hdescent : baseEnd_423944 < baseStart_423944 := by decide
  rcases family_descends (prefixWord ++ tailWord_423944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423978 : List Nat := [3, 1, 4, 1, 2, 1, 4, 3]
def baseStart_423978 : Nat := 118140960795 + 423978 * 2 ^ 59
def prefixEnd_423978 : Nat := 4983230072969 + 3 ^ 40 * 423978 * 2
def baseEnd_423978 : Nat := 129010074626398469822321

theorem tailTrace_423978 : CollatzResearch.WordTrace tailWord_423978 prefixEnd_423978 129010074626398469822321 := by
  unfold tailWord_423978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3865937014501897630670147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10309165372005060348453725 3865937014501897630670147)
  ·
    refine ⟨5798905521752846446005221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3865937014501897630670147 5798905521752846446005221)
    ·
      refine ⟨1087294785328658708625979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5798905521752846446005221 1087294785328658708625979)
      ·
        refine ⟨1630942177992988062938969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087294785328658708625979 1630942177992988062938969)
        ·
          refine ⟨1223206633494741047204227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1630942177992988062938969 1223206633494741047204227)
          ·
            refine ⟨1834809950242111570806341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223206633494741047204227 1834809950242111570806341)
            ·
              refine ⟨344026865670395919526189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1834809950242111570806341 344026865670395919526189)
              ·
                refine ⟨129010074626398469822321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344026865670395919526189 129010074626398469822321)
                ·
                  rfl

theorem cell19_423978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_423978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_423978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_423978 prefixEnd_423978 := by exact prefixLift 423978
  have htrace : WordTrace (prefixWord ++ tailWord_423978) baseStart_423978 baseEnd_423978 := by
    simpa [prefixWord, tailWord_423978, baseEnd_423978] using wordTrace_append hprefix tailTrace_423978
  have hstable : (prefixWord ++ tailWord_423978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423978).length < 2 ^ (prefixWord ++ tailWord_423978).sum := by decide
  have hdescent : baseEnd_423978 < baseStart_423978 := by decide
  rcases family_descends (prefixWord ++ tailWord_423978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424039 : List Nat := [1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_424039 : Nat := 118140960795 + 424039 * 2 ^ 59
def prefixEnd_424039 : Nat := 4983230072969 + 3 ^ 40 * 424039 * 2
def baseEnd_424039 : Nat := 129028636001168402466599

theorem tailTrace_424039 : CollatzResearch.WordTrace tailWord_424039 prefixEnd_424039 129028636001168402466599 := by
  unfold tailWord_424039
  simp only [CollatzResearch.WordTrace]
  refine ⟨15465972910786597940651171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10310648607191065293767447 15465972910786597940651171)
  ·
    refine ⟨23198959366179896910976757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15465972910786597940651171 23198959366179896910976757)
    ·
      refine ⟨2174902440579365335404071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23198959366179896910976757 2174902440579365335404071)
      ·
        refine ⟨3262353660869048003106107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174902440579365335404071 3262353660869048003106107)
        ·
          refine ⟨4893530491303572004659161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262353660869048003106107 4893530491303572004659161)
          ·
            refine ⟨3670147868477679003494371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4893530491303572004659161 3670147868477679003494371)
            ·
              refine ⟨5505221802716518505241557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3670147868477679003494371 5505221802716518505241557)
              ·
                refine ⟨129028636001168402466599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5505221802716518505241557 129028636001168402466599)
                ·
                  rfl

theorem cell19_424039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_424039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424039 prefixEnd_424039 := by exact prefixLift 424039
  have htrace : WordTrace (prefixWord ++ tailWord_424039) baseStart_424039 baseEnd_424039 := by
    simpa [prefixWord, tailWord_424039, baseEnd_424039] using wordTrace_append hprefix tailTrace_424039
  have hstable : (prefixWord ++ tailWord_424039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424039).length < 2 ^ (prefixWord ++ tailWord_424039).sum := by decide
  have hdescent : baseEnd_424039 < baseStart_424039 := by decide
  rcases family_descends (prefixWord ++ tailWord_424039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424113 : List Nat := [1, 2, 2, 5, 2, 1, 6]
def baseStart_424113 : Nat := 118140960795 + 424113 * 2 ^ 59
def prefixEnd_424113 : Nat := 4983230072969 + 3 ^ 40 * 424113 * 2
def baseEnd_424113 : Nat := 43017051026252718940651

theorem tailTrace_424113 : CollatzResearch.WordTrace tailWord_424113 prefixEnd_424113 43017051026252718940651 := by
  unfold tailWord_424113
  simp only [CollatzResearch.WordTrace]
  refine ⟨15468671912518508578844993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10312447941679005719229995 15468671912518508578844993)
  ·
    refine ⟨11601503934388881434133745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15468671912518508578844993 11601503934388881434133745)
    ·
      refine ⟨8701127950791661075600309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11601503934388881434133745 8701127950791661075600309)
      ·
        refine ⟨815730745386718225837529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8701127950791661075600309 815730745386718225837529)
        ·
          refine ⟨611798059040038669378147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815730745386718225837529 611798059040038669378147)
          ·
            refine ⟨917697088560058004067221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611798059040038669378147 917697088560058004067221)
            ·
              refine ⟨43017051026252718940651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 917697088560058004067221 43017051026252718940651)
              ·
                rfl

theorem cell19_424113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_424113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424113 prefixEnd_424113 := by exact prefixLift 424113
  have htrace : WordTrace (prefixWord ++ tailWord_424113) baseStart_424113 baseEnd_424113 := by
    simpa [prefixWord, tailWord_424113, baseEnd_424113] using wordTrace_append hprefix tailTrace_424113
  have hstable : (prefixWord ++ tailWord_424113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424113).length < 2 ^ (prefixWord ++ tailWord_424113).sum := by decide
  have hdescent : baseEnd_424113 < baseStart_424113 := by decide
  rcases family_descends (prefixWord ++ tailWord_424113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424191 : List Nat := [1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_424191 : Nat := 118140960795 + 424191 * 2 ^ 59
def prefixEnd_424191 : Nat := 4983230072969 + 3 ^ 40 * 424191 * 2
def baseEnd_424191 : Nat := 129074887295677087088407

theorem tailTrace_424191 : CollatzResearch.WordTrace tailWord_424191 prefixEnd_424191 129074887295677087088407 := by
  unfold tailWord_424191
  simp only [CollatzResearch.WordTrace]
  refine ⟨15471516806235927900184427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10314344537490618600122951 15471516806235927900184427)
  ·
    refine ⟨23207275209353891850276641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15471516806235927900184427 23207275209353891850276641)
    ·
      refine ⟨17405456407015418887707481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23207275209353891850276641 17405456407015418887707481)
      ·
        refine ⟨13054092305261564165780611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17405456407015418887707481 13054092305261564165780611)
        ·
          refine ⟨19581138457892346248670917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13054092305261564165780611 19581138457892346248670917)
          ·
            refine ⟨3671463460854814921625797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19581138457892346248670917 3671463460854814921625797)
            ·
              refine ⟨688399398910277797804837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3671463460854814921625797 688399398910277797804837)
              ·
                refine ⟨129074887295677087088407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 688399398910277797804837 129074887295677087088407)
                ·
                  rfl

theorem cell19_424191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_424191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424191 prefixEnd_424191 := by exact prefixLift 424191
  have htrace : WordTrace (prefixWord ++ tailWord_424191) baseStart_424191 baseEnd_424191 := by
    simpa [prefixWord, tailWord_424191, baseEnd_424191] using wordTrace_append hprefix tailTrace_424191
  have hstable : (prefixWord ++ tailWord_424191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424191).length < 2 ^ (prefixWord ++ tailWord_424191).sum := by decide
  have hdescent : baseEnd_424191 < baseStart_424191 := by decide
  rcases family_descends (prefixWord ++ tailWord_424191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424229 : List Nat := [1, 3, 1, 2, 5, 7]
def baseStart_424229 : Nat := 118140960795 + 424229 * 2 ^ 59
def prefixEnd_424229 : Nat := 4983230072969 + 3 ^ 40 * 424229 * 2
def baseEnd_424229 : Nat := 14342938902144917582651

theorem tailTrace_424229 : CollatzResearch.WordTrace tailWord_424229 prefixEnd_424229 14342938902144917582651 := by
  unfold tailWord_424229
  simp only [CollatzResearch.WordTrace]
  refine ⟨15472902780098260390067741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10315268520065506926711827 15472902780098260390067741)
  ·
    refine ⟨5802338542536847646275403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15472902780098260390067741 5802338542536847646275403)
    ·
      refine ⟨8703507813805271469413105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5802338542536847646275403 8703507813805271469413105)
      ·
        refine ⟨6527630860353953602059829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8703507813805271469413105 6527630860353953602059829)
        ·
          refine ⟨611965393158183150193109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6527630860353953602059829 611965393158183150193109)
          ·
            refine ⟨14342938902144917582651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 611965393158183150193109 14342938902144917582651)
            ·
              rfl

theorem cell19_424229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 7].length) (baseStart_424229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424229 prefixEnd_424229 := by exact prefixLift 424229
  have htrace : WordTrace (prefixWord ++ tailWord_424229) baseStart_424229 baseEnd_424229 := by
    simpa [prefixWord, tailWord_424229, baseEnd_424229] using wordTrace_append hprefix tailTrace_424229
  have hstable : (prefixWord ++ tailWord_424229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424229).length < 2 ^ (prefixWord ++ tailWord_424229).sum := by decide
  have hdescent : baseEnd_424229 < baseStart_424229 := by decide
  rcases family_descends (prefixWord ++ tailWord_424229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424244 : List Nat := [2, 5, 1, 1, 1, 4, 1, 4]
def baseStart_424244 : Nat := 118140960795 + 424244 * 2 ^ 59
def prefixEnd_424244 : Nat := 4983230072969 + 3 ^ 40 * 424244 * 2
def baseEnd_424244 : Nat := 129091014391788667910485

theorem tailTrace_424244 : CollatzResearch.WordTrace tailWord_424244 prefixEnd_424244 129091014391788667910485 := by
  unfold tailWord_424244
  simp only [CollatzResearch.WordTrace]
  refine ⟨7736724937521958975931893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10315633250029278634575857 7736724937521958975931893)
  ·
    refine ⟨725317962892683653993615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7736724937521958975931893 725317962892683653993615)
    ·
      refine ⟨1087976944339025480990423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 725317962892683653993615 1087976944339025480990423)
      ·
        refine ⟨1631965416508538221485635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087976944339025480990423 1631965416508538221485635)
        ·
          refine ⟨2447948124762807332228453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631965416508538221485635 2447948124762807332228453)
          ·
            refine ⟨458990273393026374792835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2447948124762807332228453 458990273393026374792835)
            ·
              refine ⟨688485410089539562189253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458990273393026374792835 688485410089539562189253)
              ·
                refine ⟨129091014391788667910485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 688485410089539562189253 129091014391788667910485)
                ·
                  rfl

theorem cell19_424244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_424244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424244 prefixEnd_424244 := by exact prefixLift 424244
  have htrace : WordTrace (prefixWord ++ tailWord_424244) baseStart_424244 baseEnd_424244 := by
    simpa [prefixWord, tailWord_424244, baseEnd_424244] using wordTrace_append hprefix tailTrace_424244
  have hstable : (prefixWord ++ tailWord_424244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424244).length < 2 ^ (prefixWord ++ tailWord_424244).sum := by decide
  have hdescent : baseEnd_424244 < baseStart_424244 := by decide
  rcases family_descends (prefixWord ++ tailWord_424244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424248 : List Nat := [2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_424248 : Nat := 118140960795 + 424248 * 2 ^ 59
def prefixEnd_424248 : Nat := 4983230072969 + 3 ^ 40 * 424248 * 2
def baseEnd_424248 : Nat := 129092231531117843821585

theorem tailTrace_424248 : CollatzResearch.WordTrace tailWord_424248 prefixEnd_424248 129092231531117843821585 := by
  unfold tailWord_424248
  simp only [CollatzResearch.WordTrace]
  refine ⟨7736797883514713317504699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10315730511352951090006265 7736797883514713317504699)
  ·
    refine ⟨11605196825272069976257049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7736797883514713317504699 11605196825272069976257049)
    ·
      refine ⟨8703897618954052482192787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11605196825272069976257049 8703897618954052482192787)
      ·
        refine ⟨13055846428431078723289181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8703897618954052482192787 13055846428431078723289181)
        ·
          refine ⟨4895942410661654521233443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13055846428431078723289181 4895942410661654521233443)
          ·
            refine ⟨7343913615992481781850165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895942410661654521233443 7343913615992481781850165)
            ·
              refine ⟨688491901499295167048453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7343913615992481781850165 688491901499295167048453)
              ·
                refine ⟨129092231531117843821585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 688491901499295167048453 129092231531117843821585)
                ·
                  rfl

theorem cell19_424248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_424248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424248 prefixEnd_424248 := by exact prefixLift 424248
  have htrace : WordTrace (prefixWord ++ tailWord_424248) baseStart_424248 baseEnd_424248 := by
    simpa [prefixWord, tailWord_424248, baseEnd_424248] using wordTrace_append hprefix tailTrace_424248
  have hstable : (prefixWord ++ tailWord_424248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424248).length < 2 ^ (prefixWord ++ tailWord_424248).sum := by decide
  have hdescent : baseEnd_424248 < baseStart_424248 := by decide
  rcases family_descends (prefixWord ++ tailWord_424248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424324 : List Nat := [2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_424324 : Nat := 118140960795 + 424324 * 2 ^ 59
def prefixEnd_424324 : Nat := 4983230072969 + 3 ^ 40 * 424324 * 2
def baseEnd_424324 : Nat := 129115357178372186132489

theorem tailTrace_424324 : CollatzResearch.WordTrace tailWord_424324 prefixEnd_424324 129115357178372186132489 := by
  unfold tailWord_424324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7738183857377045807388013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10317578476502727743184017 7738183857377045807388013)
  ·
    refine ⟨2901818946516392177770505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7738183857377045807388013 2901818946516392177770505)
    ·
      refine ⟨2176364209887294133327879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2901818946516392177770505 2176364209887294133327879)
      ·
        refine ⟨3264546314830941199991819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176364209887294133327879 3264546314830941199991819)
        ·
          refine ⟨4896819472246411799987729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3264546314830941199991819 4896819472246411799987729)
          ·
            refine ⟨3672614604184808849990797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4896819472246411799987729 3672614604184808849990797)
            ·
              refine ⟨1377230476569303318746549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3672614604184808849990797 1377230476569303318746549)
              ·
                refine ⟨129115357178372186132489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1377230476569303318746549 129115357178372186132489)
                ·
                  rfl

theorem cell19_424324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_424324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424324 prefixEnd_424324 := by exact prefixLift 424324
  have htrace : WordTrace (prefixWord ++ tailWord_424324) baseStart_424324 baseEnd_424324 := by
    simpa [prefixWord, tailWord_424324, baseEnd_424324] using wordTrace_append hprefix tailTrace_424324
  have hstable : (prefixWord ++ tailWord_424324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424324).length < 2 ^ (prefixWord ++ tailWord_424324).sum := by decide
  have hdescent : baseEnd_424324 < baseStart_424324 := by decide
  rcases family_descends (prefixWord ++ tailWord_424324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424360 : List Nat := [2, 1, 6, 1, 1, 1, 1, 6]
def baseStart_424360 : Nat := 118140960795 + 424360 * 2 ^ 59
def prefixEnd_424360 : Nat := 4983230072969 + 3 ^ 40 * 424360 * 2
def baseEnd_424360 : Nat := 129126311432334769332391

theorem tailTrace_424360 : CollatzResearch.WordTrace tailWord_424360 prefixEnd_424360 129126311432334769332391 := by
  unfold tailWord_424360
  simp only [CollatzResearch.WordTrace]
  refine ⟨7738840371311834881543267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10318453828415779842057689 7738840371311834881543267)
  ·
    refine ⟨11608260556967752322314901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7738840371311834881543267 11608260556967752322314901)
    ·
      refine ⟨544137213607863390108511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11608260556967752322314901 544137213607863390108511)
      ·
        refine ⟨816205820411795085162767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544137213607863390108511 816205820411795085162767)
        ·
          refine ⟨1224308730617692627744151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816205820411795085162767 1224308730617692627744151)
          ·
            refine ⟨1836463095926538941616227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224308730617692627744151 1836463095926538941616227)
            ·
              refine ⟨2754694643889808412424341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836463095926538941616227 2754694643889808412424341)
              ·
                refine ⟨129126311432334769332391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2754694643889808412424341 129126311432334769332391)
                ·
                  rfl

theorem cell19_424360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_424360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424360 prefixEnd_424360 := by exact prefixLift 424360
  have htrace : WordTrace (prefixWord ++ tailWord_424360) baseStart_424360 baseEnd_424360 := by
    simpa [prefixWord, tailWord_424360, baseEnd_424360] using wordTrace_append hprefix tailTrace_424360
  have hstable : (prefixWord ++ tailWord_424360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424360).length < 2 ^ (prefixWord ++ tailWord_424360).sum := by decide
  have hdescent : baseEnd_424360 < baseStart_424360 := by decide
  rcases family_descends (prefixWord ++ tailWord_424360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424381 : List Nat := [1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_424381 : Nat := 118140960795 + 424381 * 2 ^ 59
def prefixEnd_424381 : Nat := 4983230072969 + 3 ^ 40 * 424381 * 2
def baseEnd_424381 : Nat := 129132701413812942865667

theorem tailTrace_424381 : CollatzResearch.WordTrace tailWord_424381 prefixEnd_424381 129132701413812942865667 := by
  unfold tailWord_424381
  simp only [CollatzResearch.WordTrace]
  refine ⟨15478446675547590349600997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10318964450365060233067331 15478446675547590349600997)
  ·
    refine ⟨2902208751665173190550187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15478446675547590349600997 2902208751665173190550187)
    ·
      refine ⟨4353313127497759785825281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902208751665173190550187 4353313127497759785825281)
      ·
        refine ⟨3264984845623319839368961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4353313127497759785825281 3264984845623319839368961)
        ·
          refine ⟨2448738634217489879526721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3264984845623319839368961 2448738634217489879526721)
          ·
            refine ⟨1836553975663117409645041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2448738634217489879526721 1836553975663117409645041)
            ·
              refine ⟨1377415481747338057233781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836553975663117409645041 1377415481747338057233781)
              ·
                refine ⟨129132701413812942865667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1377415481747338057233781 129132701413812942865667)
                ·
                  rfl

theorem cell19_424381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_424381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424381 prefixEnd_424381 := by exact prefixLift 424381
  have htrace : WordTrace (prefixWord ++ tailWord_424381) baseStart_424381 baseEnd_424381 := by
    simpa [prefixWord, tailWord_424381, baseEnd_424381] using wordTrace_append hprefix tailTrace_424381
  have hstable : (prefixWord ++ tailWord_424381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424381).length < 2 ^ (prefixWord ++ tailWord_424381).sum := by decide
  have hdescent : baseEnd_424381 < baseStart_424381 := by decide
  rcases family_descends (prefixWord ++ tailWord_424381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424434 : List Nat := [3, 2, 1, 4, 2, 1, 3, 3]
def baseStart_424434 : Nat := 118140960795 + 424434 * 2 ^ 59
def prefixEnd_424434 : Nat := 4983230072969 + 3 ^ 40 * 424434 * 2
def baseEnd_424434 : Nat := 129148828509924523687745

theorem tailTrace_424434 : CollatzResearch.WordTrace tailWord_424434 prefixEnd_424434 129148828509924523687745 := by
  unfold tailWord_424434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870094936088895100320089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10320253162903720267520237 3870094936088895100320089)
  ·
    refine ⟨2902571202066671325240067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3870094936088895100320089 2902571202066671325240067)
    ·
      refine ⟨4353856803100006987860101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902571202066671325240067 4353856803100006987860101)
      ·
        refine ⟨816348150581251310223769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4353856803100006987860101 816348150581251310223769)
        ·
          refine ⟨612261112935938482667827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 816348150581251310223769 612261112935938482667827)
          ·
            refine ⟨918391669403907724001741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612261112935938482667827 918391669403907724001741)
            ·
              refine ⟨344396876026465396500653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 918391669403907724001741 344396876026465396500653)
              ·
                refine ⟨129148828509924523687745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344396876026465396500653 129148828509924523687745)
                ·
                  rfl

theorem cell19_424434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_424434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424434 prefixEnd_424434 := by exact prefixLift 424434
  have htrace : WordTrace (prefixWord ++ tailWord_424434) baseStart_424434 baseEnd_424434 := by
    simpa [prefixWord, tailWord_424434, baseEnd_424434] using wordTrace_append hprefix tailTrace_424434
  have hstable : (prefixWord ++ tailWord_424434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424434).length < 2 ^ (prefixWord ++ tailWord_424434).sum := by decide
  have hdescent : baseEnd_424434 < baseStart_424434 := by decide
  rcases family_descends (prefixWord ++ tailWord_424434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424487 : List Nat := [1, 1, 7, 2, 2, 1, 2, 3]
def baseStart_424487 : Nat := 118140960795 + 424487 * 2 ^ 59
def prefixEnd_424487 : Nat := 4983230072969 + 3 ^ 40 * 424487 * 2
def baseEnd_424487 : Nat := 129164955606036104509823

theorem tailTrace_424487 : CollatzResearch.WordTrace tailWord_424487 prefixEnd_424487 129164955606036104509823 := by
  unfold tailWord_424487
  simp only [CollatzResearch.WordTrace]
  refine ⟨15482312813163570452959715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10321541875442380301973143 15482312813163570452959715)
  ·
    refine ⟨23223469219745355679439573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15482312813163570452959715 23223469219745355679439573)
    ·
      refine ⟨544300059837781773736865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23223469219745355679439573 544300059837781773736865)
      ·
        refine ⟨408225044878336330302649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544300059837781773736865 408225044878336330302649)
        ·
          refine ⟨306168783658752247726987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408225044878336330302649 306168783658752247726987)
          ·
            refine ⟨459253175488128371590481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306168783658752247726987 459253175488128371590481)
            ·
              refine ⟨344439881616096278692861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459253175488128371590481 344439881616096278692861)
              ·
                refine ⟨129164955606036104509823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344439881616096278692861 129164955606036104509823)
                ·
                  rfl

theorem cell19_424487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 3].length) (baseStart_424487 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424487 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424487 prefixEnd_424487 := by exact prefixLift 424487
  have htrace : WordTrace (prefixWord ++ tailWord_424487) baseStart_424487 baseEnd_424487 := by
    simpa [prefixWord, tailWord_424487, baseEnd_424487] using wordTrace_append hprefix tailTrace_424487
  have hstable : (prefixWord ++ tailWord_424487).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424487).length < 2 ^ (prefixWord ++ tailWord_424487).sum := by decide
  have hdescent : baseEnd_424487 < baseStart_424487 := by decide
  rcases family_descends (prefixWord ++ tailWord_424487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424510 : List Nat := [4, 2, 1, 4, 1, 2, 5]
def baseStart_424510 : Nat := 118140960795 + 424510 * 2 ^ 59
def prefixEnd_424510 : Nat := 4983230072969 + 3 ^ 40 * 424510 * 2
def baseEnd_424510 : Nat := 43057318052392955332883

theorem tailTrace_424510 : CollatzResearch.WordTrace tailWord_424510 prefixEnd_424510 43057318052392955332883 := by
  unfold tailWord_424510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935393961510030672630873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10322101128053496920697989 1935393961510030672630873)
  ·
    refine ⟨1451545471132523004473155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1935393961510030672630873 1451545471132523004473155)
    ·
      refine ⟨2177318206698784506709733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451545471132523004473155 2177318206698784506709733)
      ·
        refine ⟨408247163756022095008075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2177318206698784506709733 408247163756022095008075)
        ·
          refine ⟨612370745634033142512113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408247163756022095008075 612370745634033142512113)
          ·
            refine ⟨459278059225524856884085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612370745634033142512113 459278059225524856884085)
            ·
              refine ⟨43057318052392955332883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 459278059225524856884085 43057318052392955332883)
              ·
                rfl

theorem cell19_424510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 5].length) (baseStart_424510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424510 prefixEnd_424510 := by exact prefixLift 424510
  have htrace : WordTrace (prefixWord ++ tailWord_424510) baseStart_424510 baseEnd_424510 := by
    simpa [prefixWord, tailWord_424510, baseEnd_424510] using wordTrace_append hprefix tailTrace_424510
  have hstable : (prefixWord ++ tailWord_424510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424510).length < 2 ^ (prefixWord ++ tailWord_424510).sum := by decide
  have hdescent : baseEnd_424510 < baseStart_424510 := by decide
  rcases family_descends (prefixWord ++ tailWord_424510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424573 : List Nat := [1, 4, 1, 1, 12]
def baseStart_424573 : Nat := 118140960795 + 424573 * 2 ^ 59
def prefixEnd_424573 : Nat := 4983230072969 + 3 ^ 40 * 424573 * 2
def baseEnd_424573 : Nat := 4784856448207903207351

theorem tailTrace_424573 : CollatzResearch.WordTrace tailWord_424573 prefixEnd_424573 4784856448207903207351 := by
  unfold tailWord_424573
  simp only [CollatzResearch.WordTrace]
  refine ⟨15485449490852007140590373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10323632993901338093726915 15485449490852007140590373)
  ·
    refine ⟨2903521779534751338860695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15485449490852007140590373 2903521779534751338860695)
    ·
      refine ⟨4355282669302127008291043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903521779534751338860695 4355282669302127008291043)
      ·
        refine ⟨6532924003953190512436565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4355282669302127008291043 6532924003953190512436565)
        ·
          refine ⟨4784856448207903207351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6532924003953190512436565 4784856448207903207351)
          ·
            rfl

theorem cell19_424573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 12].length) (baseStart_424573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424573 prefixEnd_424573 := by exact prefixLift 424573
  have htrace : WordTrace (prefixWord ++ tailWord_424573) baseStart_424573 baseEnd_424573 := by
    simpa [prefixWord, tailWord_424573, baseEnd_424573] using wordTrace_append hprefix tailTrace_424573
  have hstable : (prefixWord ++ tailWord_424573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424573).length < 2 ^ (prefixWord ++ tailWord_424573).sum := by decide
  have hdescent : baseEnd_424573 < baseStart_424573 := by decide
  rcases family_descends (prefixWord ++ tailWord_424573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424586 : List Nat := [3, 1, 2, 3, 4, 1, 1, 4]
def baseStart_424586 : Nat := 118140960795 + 424586 * 2 ^ 59
def prefixEnd_424586 : Nat := 4983230072969 + 3 ^ 40 * 424586 * 2
def baseEnd_424586 : Nat := 129195079804433208309553

theorem tailTrace_424586 : CollatzResearch.WordTrace tailWord_424586 prefixEnd_424586 129195079804433208309553 := by
  unfold tailWord_424586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871480909951227590203403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10323949093203273573875741 3871480909951227590203403)
  ·
    refine ⟨5807221364926841385305105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3871480909951227590203403 5807221364926841385305105)
    ·
      refine ⟨4355416023695131038978829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5807221364926841385305105 4355416023695131038978829)
      ·
        refine ⟨1633281008885674139617061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4355416023695131038978829 1633281008885674139617061)
        ·
          refine ⟨306240189166063901178199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1633281008885674139617061 306240189166063901178199)
          ·
            refine ⟨459360283749095851767299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306240189166063901178199 459360283749095851767299)
            ·
              refine ⟨689040425623643777650949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459360283749095851767299 689040425623643777650949)
              ·
                refine ⟨129195079804433208309553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 689040425623643777650949 129195079804433208309553)
                ·
                  rfl

theorem cell19_424586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_424586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424586 prefixEnd_424586 := by exact prefixLift 424586
  have htrace : WordTrace (prefixWord ++ tailWord_424586) baseStart_424586 baseEnd_424586 := by
    simpa [prefixWord, tailWord_424586, baseEnd_424586] using wordTrace_append hprefix tailTrace_424586
  have hstable : (prefixWord ++ tailWord_424586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424586).length < 2 ^ (prefixWord ++ tailWord_424586).sum := by decide
  have hdescent : baseEnd_424586 < baseStart_424586 := by decide
  rcases family_descends (prefixWord ++ tailWord_424586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424660 : List Nat := [2, 4, 1, 3, 3, 1, 2, 3]
def baseStart_424660 : Nat := 118140960795 + 424660 * 2 ^ 59
def prefixEnd_424660 : Nat := 4983230072969 + 3 ^ 40 * 424660 * 2
def baseEnd_424660 : Nat := 129217596882022962664907

theorem tailTrace_424660 : CollatzResearch.WordTrace tailWord_424660 prefixEnd_424660 129217596882022962664907 := by
  unfold tailWord_424660
  simp only [CollatzResearch.WordTrace]
  refine ⟨7744311320768410499503717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10325748427691213999338289 7744311320768410499503717)
  ·
    refine ⟨1452058372644076968656947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7744311320768410499503717 1452058372644076968656947)
    ·
      refine ⟨2178087558966115452985421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452058372644076968656947 2178087558966115452985421)
      ·
        refine ⟨816782834612293294869533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2178087558966115452985421 816782834612293294869533)
        ·
          refine ⟨306293562979609985576075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 816782834612293294869533 306293562979609985576075)
          ·
            refine ⟨459440344469414978364113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306293562979609985576075 459440344469414978364113)
            ·
              refine ⟨344580258352061233773085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459440344469414978364113 344580258352061233773085)
              ·
                refine ⟨129217596882022962664907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344580258352061233773085 129217596882022962664907)
                ·
                  rfl

theorem cell19_424660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_424660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424660 prefixEnd_424660 := by exact prefixLift 424660
  have htrace : WordTrace (prefixWord ++ tailWord_424660) baseStart_424660 baseEnd_424660 := by
    simpa [prefixWord, tailWord_424660, baseEnd_424660] using wordTrace_append hprefix tailTrace_424660
  have hstable : (prefixWord ++ tailWord_424660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424660).length < 2 ^ (prefixWord ++ tailWord_424660).sum := by decide
  have hdescent : baseEnd_424660 < baseStart_424660 := by decide
  rcases family_descends (prefixWord ++ tailWord_424660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424664 : List Nat := [2, 1, 2, 2, 3, 4, 2, 3]
def baseStart_424664 : Nat := 118140960795 + 424664 * 2 ^ 59
def prefixEnd_424664 : Nat := 4983230072969 + 3 ^ 40 * 424664 * 2
def baseEnd_424664 : Nat := 129218814021352138576007

theorem tailTrace_424664 : CollatzResearch.WordTrace tailWord_424664 prefixEnd_424664 129218814021352138576007 := by
  unfold tailWord_424664
  simp only [CollatzResearch.WordTrace]
  refine ⟨7744384266761164841076523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10325845689014886454768697 7744384266761164841076523)
  ·
    refine ⟨11616576400141747261614785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7744384266761164841076523 11616576400141747261614785)
    ·
      refine ⟨8712432300106310446211089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11616576400141747261614785 8712432300106310446211089)
      ·
        refine ⟨6534324225079732834658317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8712432300106310446211089 6534324225079732834658317)
        ·
          refine ⟨2450371584404899812996869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6534324225079732834658317 2450371584404899812996869)
          ·
            refine ⟨459444672075918714936913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2450371584404899812996869 459444672075918714936913)
            ·
              refine ⟨344583504056939036202685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459444672075918714936913 344583504056939036202685)
              ·
                refine ⟨129218814021352138576007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344583504056939036202685 129218814021352138576007)
                ·
                  rfl

theorem cell19_424664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_424664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424664 prefixEnd_424664 := by exact prefixLift 424664
  have htrace : WordTrace (prefixWord ++ tailWord_424664) baseStart_424664 baseEnd_424664 := by
    simpa [prefixWord, tailWord_424664, baseEnd_424664] using wordTrace_append hprefix tailTrace_424664
  have hstable : (prefixWord ++ tailWord_424664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424664).length < 2 ^ (prefixWord ++ tailWord_424664).sum := by decide
  have hdescent : baseEnd_424664 < baseStart_424664 := by decide
  rcases family_descends (prefixWord ++ tailWord_424664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424687 : List Nat := [1, 1, 2, 1, 5, 2, 7]
def baseStart_424687 : Nat := 118140960795 + 424687 * 2 ^ 59
def prefixEnd_424687 : Nat := 4983230072969 + 3 ^ 40 * 424687 * 2
def baseEnd_424687 : Nat := 43075270857498300021611

theorem tailTrace_424687 : CollatzResearch.WordTrace tailWord_424687 prefixEnd_424687 43075270857498300021611 := by
  unfold tailWord_424687
  simp only [CollatzResearch.WordTrace]
  refine ⟨15489607412439004610240315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10326404941626003073493543 15489607412439004610240315)
  ·
    refine ⟨23234411118658506915360473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15489607412439004610240315 23234411118658506915360473)
    ·
      refine ⟨17425808338993880186520355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23234411118658506915360473 17425808338993880186520355)
      ·
        refine ⟨26138712508490820279780533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17425808338993880186520355 26138712508490820279780533)
        ·
          refine ⟨2450504297671014401229425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26138712508490820279780533 2450504297671014401229425)
          ·
            refine ⟨1837878223253260800922069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2450504297671014401229425 1837878223253260800922069)
            ·
              refine ⟨43075270857498300021611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1837878223253260800922069 43075270857498300021611)
              ·
                rfl

theorem cell19_424687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_424687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424687 prefixEnd_424687 := by exact prefixLift 424687
  have htrace : WordTrace (prefixWord ++ tailWord_424687) baseStart_424687 baseEnd_424687 := by
    simpa [prefixWord, tailWord_424687, baseEnd_424687] using wordTrace_append hprefix tailTrace_424687
  have hstable : (prefixWord ++ tailWord_424687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424687).length < 2 ^ (prefixWord ++ tailWord_424687).sum := by decide
  have hdescent : baseEnd_424687 < baseStart_424687 := by decide
  rcases family_descends (prefixWord ++ tailWord_424687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424702 : List Nat := [4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_424702 : Nat := 118140960795 + 424702 * 2 ^ 59
def prefixEnd_424702 : Nat := 4983230072969 + 3 ^ 40 * 424702 * 2
def baseEnd_424702 : Nat := 129230376844979309731459

theorem tailTrace_424702 : CollatzResearch.WordTrace tailWord_424702 prefixEnd_424702 129230376844979309731459 := by
  unfold tailWord_424702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936269313423082771504545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10326769671589774781357573 1936269313423082771504545)
  ·
    refine ⟨1452201985067312078628409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1936269313423082771504545 1452201985067312078628409)
    ·
      refine ⟨1089151488800484058971307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1452201985067312078628409 1089151488800484058971307)
      ·
        refine ⟨1633727233200726088456961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089151488800484058971307 1633727233200726088456961)
        ·
          refine ⟨1225295424900544566342721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1633727233200726088456961 1225295424900544566342721)
          ·
            refine ⟨918971568675408424757041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225295424900544566342721 918971568675408424757041)
            ·
              refine ⟨689228676506556318567781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918971568675408424757041 689228676506556318567781)
              ·
                refine ⟨129230376844979309731459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 689228676506556318567781 129230376844979309731459)
                ·
                  rfl

theorem cell19_424702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_424702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424702 prefixEnd_424702 := by exact prefixLift 424702
  have htrace : WordTrace (prefixWord ++ tailWord_424702) baseStart_424702 baseEnd_424702 := by
    simpa [prefixWord, tailWord_424702, baseEnd_424702] using wordTrace_append hprefix tailTrace_424702
  have hstable : (prefixWord ++ tailWord_424702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424702).length < 2 ^ (prefixWord ++ tailWord_424702).sum := by decide
  have hdescent : baseEnd_424702 < baseStart_424702 := by decide
  rcases family_descends (prefixWord ++ tailWord_424702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424725 : List Nat := [1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_424725 : Nat := 118140960795 + 424725 * 2 ^ 59
def prefixEnd_424725 : Nat := 4983230072969 + 3 ^ 40 * 424725 * 2
def baseEnd_424725 : Nat := 129237375396122071220285

theorem tailTrace_424725 : CollatzResearch.WordTrace tailWord_424725 prefixEnd_424725 129237375396122071220285 := by
  unfold tailWord_424725
  simp only [CollatzResearch.WordTrace]
  refine ⟨15490993386301337100123629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10327328924200891400082419 15490993386301337100123629)
  ·
    refine ⟨5809122519863001412546361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15490993386301337100123629 5809122519863001412546361)
    ·
      refine ⟨4356841889897251059409771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5809122519863001412546361 4356841889897251059409771)
      ·
        refine ⟨6535262834845876589114657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356841889897251059409771 6535262834845876589114657)
        ·
          refine ⟨4901447126134407441835993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6535262834845876589114657 4901447126134407441835993)
          ·
            refine ⟨3676085344600805581376995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4901447126134407441835993 3676085344600805581376995)
            ·
              refine ⟨5514128016901208372065493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3676085344600805581376995 5514128016901208372065493)
              ·
                refine ⟨129237375396122071220285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5514128016901208372065493 129237375396122071220285)
                ·
                  rfl

theorem cell19_424725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_424725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424725 prefixEnd_424725 := by exact prefixLift 424725
  have htrace : WordTrace (prefixWord ++ tailWord_424725) baseStart_424725 baseEnd_424725 := by
    simpa [prefixWord, tailWord_424725, baseEnd_424725] using wordTrace_append hprefix tailTrace_424725
  have hstable : (prefixWord ++ tailWord_424725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424725).length < 2 ^ (prefixWord ++ tailWord_424725).sum := by decide
  have hdescent : baseEnd_424725 < baseStart_424725 := by decide
  rcases family_descends (prefixWord ++ tailWord_424725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424774 : List Nat := [6, 1, 1, 2, 2, 1, 3, 3]
def baseStart_424774 : Nat := 118140960795 + 424774 * 2 ^ 59
def prefixEnd_424774 : Nat := 4983230072969 + 3 ^ 40 * 424774 * 2
def baseEnd_424774 : Nat := 129252285352904476131263

theorem tailTrace_424774 : CollatzResearch.WordTrace tailWord_424774 prefixEnd_424774 129252285352904476131263 := by
  unfold tailWord_424774
  simp only [CollatzResearch.WordTrace]
  refine ⟨484149392597619327145543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10328520375415878979104917 484149392597619327145543)
  ·
    refine ⟨726224088896428990718315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 484149392597619327145543 726224088896428990718315)
    ·
      refine ⟨1089336133344643486077473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726224088896428990718315 1089336133344643486077473)
      ·
        refine ⟨817002100008482614558105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1089336133344643486077473 817002100008482614558105)
        ·
          refine ⟨612751575006361960918579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817002100008482614558105 612751575006361960918579)
          ·
            refine ⟨919127362509542941377869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612751575006361960918579 919127362509542941377869)
            ·
              refine ⟨344672760941078603016701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 919127362509542941377869 344672760941078603016701)
              ·
                refine ⟨129252285352904476131263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344672760941078603016701 129252285352904476131263)
                ·
                  rfl

theorem cell19_424774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_424774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424774 prefixEnd_424774 := by exact prefixLift 424774
  have htrace : WordTrace (prefixWord ++ tailWord_424774) baseStart_424774 baseEnd_424774 := by
    simpa [prefixWord, tailWord_424774, baseEnd_424774] using wordTrace_append hprefix tailTrace_424774
  have hstable : (prefixWord ++ tailWord_424774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424774).length < 2 ^ (prefixWord ++ tailWord_424774).sum := by decide
  have hdescent : baseEnd_424774 < baseStart_424774 := by decide
  rcases family_descends (prefixWord ++ tailWord_424774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424782 : List Nat := [4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_424782 : Nat := 118140960795 + 424782 * 2 ^ 59
def prefixEnd_424782 : Nat := 4983230072969 + 3 ^ 40 * 424782 * 2
def baseEnd_424782 : Nat := 129254719631562827953463

theorem tailTrace_424782 : CollatzResearch.WordTrace tailWord_424782 prefixEnd_424782 129254719631562827953463 := by
  unfold tailWord_424782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936634043386854479368575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10328714898063223889965733 1936634043386854479368575)
  ·
    refine ⟨2904951065080281719052863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1936634043386854479368575 2904951065080281719052863)
    ·
      refine ⟨4357426597620422578579295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2904951065080281719052863 4357426597620422578579295)
      ·
        refine ⟨6536139896430633867868943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4357426597620422578579295 6536139896430633867868943)
        ·
          refine ⟨9804209844645950801803415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6536139896430633867868943 9804209844645950801803415)
          ·
            refine ⟨14706314766968926202705123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9804209844645950801803415 14706314766968926202705123)
            ·
              refine ⟨22059472150453389304057685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14706314766968926202705123 22059472150453389304057685)
              ·
                refine ⟨129254719631562827953463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22059472150453389304057685 129254719631562827953463)
                ·
                  rfl

theorem cell19_424782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_424782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424782 prefixEnd_424782 := by exact prefixLift 424782
  have htrace : WordTrace (prefixWord ++ tailWord_424782) baseStart_424782 baseEnd_424782 := by
    simpa [prefixWord, tailWord_424782, baseEnd_424782] using wordTrace_append hprefix tailTrace_424782
  have hstable : (prefixWord ++ tailWord_424782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424782).length < 2 ^ (prefixWord ++ tailWord_424782).sum := by decide
  have hdescent : baseEnd_424782 < baseStart_424782 := by decide
  rcases family_descends (prefixWord ++ tailWord_424782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424837 : List Nat := [1, 3, 1, 1, 3, 3, 4, 3]
def baseStart_424837 : Nat := 118140960795 + 424837 * 2 ^ 59
def prefixEnd_424837 : Nat := 4983230072969 + 3 ^ 40 * 424837 * 2
def baseEnd_424837 : Nat := 129271455297338996731091

theorem tailTrace_424837 : CollatzResearch.WordTrace tailWord_424837 prefixEnd_424837 129271455297338996731091 := by
  unfold tailWord_424837
  simp only [CollatzResearch.WordTrace]
  refine ⟨15495078361895580228200765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10330052241263720152133843 15495078361895580228200765)
  ·
    refine ⟨5810654385710842585575287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15495078361895580228200765 5810654385710842585575287)
    ·
      refine ⟨8715981578566263878362931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5810654385710842585575287 8715981578566263878362931)
      ·
        refine ⟨13073972367849395817544397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8715981578566263878362931 13073972367849395817544397)
        ·
          refine ⟨4902739637943523431579149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13073972367849395817544397 4902739637943523431579149)
          ·
            refine ⟨1838527364228821286842181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4902739637943523431579149 1838527364228821286842181)
            ·
              refine ⟨344723880792903991282909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1838527364228821286842181 344723880792903991282909)
              ·
                refine ⟨129271455297338996731091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344723880792903991282909 129271455297338996731091)
                ·
                  rfl

theorem cell19_424837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 3].length) (baseStart_424837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424837 prefixEnd_424837 := by exact prefixLift 424837
  have htrace : WordTrace (prefixWord ++ tailWord_424837) baseStart_424837 baseEnd_424837 := by
    simpa [prefixWord, tailWord_424837, baseEnd_424837] using wordTrace_append hprefix tailTrace_424837
  have hstable : (prefixWord ++ tailWord_424837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424837).length < 2 ^ (prefixWord ++ tailWord_424837).sum := by decide
  have hdescent : baseEnd_424837 < baseStart_424837 := by decide
  rcases family_descends (prefixWord ++ tailWord_424837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424896 : List Nat := [2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_424896 : Nat := 118140960795 + 424896 * 2 ^ 59
def prefixEnd_424896 : Nat := 4983230072969 + 3 ^ 40 * 424896 * 2
def baseEnd_424896 : Nat := 129289408102444341419819

theorem tailTrace_424896 : CollatzResearch.WordTrace tailWord_424896 prefixEnd_424896 129289408102444341419819 := by
  unfold tailWord_424896
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748615134340916652299271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10331486845787888869732361 7748615134340916652299271)
  ·
    refine ⟨11622922701511374978448907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7748615134340916652299271 11622922701511374978448907)
    ·
      refine ⟨17434384052267062467673361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11622922701511374978448907 17434384052267062467673361)
      ·
        refine ⟨13075788039200296850755021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17434384052267062467673361 13075788039200296850755021)
        ·
          refine ⟨4903420514700111319033133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13075788039200296850755021 4903420514700111319033133)
          ·
            refine ⟨1838782693012541744637425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4903420514700111319033133 1838782693012541744637425)
            ·
              refine ⟨1379087019759406308478069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838782693012541744637425 1379087019759406308478069)
              ·
                refine ⟨129289408102444341419819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1379087019759406308478069 129289408102444341419819)
                ·
                  rfl

theorem cell19_424896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_424896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424896 prefixEnd_424896 := by exact prefixLift 424896
  have htrace : WordTrace (prefixWord ++ tailWord_424896) baseStart_424896 baseEnd_424896 := by
    simpa [prefixWord, tailWord_424896, baseEnd_424896] using wordTrace_append hprefix tailTrace_424896
  have hstable : (prefixWord ++ tailWord_424896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424896).length < 2 ^ (prefixWord ++ tailWord_424896).sum := by decide
  have hdescent : baseEnd_424896 < baseStart_424896 := by decide
  rcases family_descends (prefixWord ++ tailWord_424896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424909 : List Nat := [1, 6, 3, 1, 1, 7]
def baseStart_424909 : Nat := 118140960795 + 424909 * 2 ^ 59
def prefixEnd_424909 : Nat := 4983230072969 + 3 ^ 40 * 424909 * 2
def baseEnd_424909 : Nat := 14365929311696018125655

theorem tailTrace_424909 : CollatzResearch.WordTrace tailWord_424909 prefixEnd_424909 14365929311696018125655 := by
  unfold tailWord_424909
  simp only [CollatzResearch.WordTrace]
  refine ⟨15497704417634736524821781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10331802945089824349881187 15497704417634736524821781)
  ·
    refine ⟨726454894576628274601021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15497704417634736524821781 726454894576628274601021)
    ·
      refine ⟨272420585466235602975383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 726454894576628274601021 272420585466235602975383)
      ·
        refine ⟨408630878199353404463075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272420585466235602975383 408630878199353404463075)
        ·
          refine ⟨612946317299030106694613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408630878199353404463075 612946317299030106694613)
          ·
            refine ⟨14365929311696018125655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 612946317299030106694613 14365929311696018125655)
            ·
              rfl

theorem cell19_424909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 7].length) (baseStart_424909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424909 prefixEnd_424909 := by exact prefixLift 424909
  have htrace : WordTrace (prefixWord ++ tailWord_424909) baseStart_424909 baseEnd_424909 := by
    simpa [prefixWord, tailWord_424909, baseEnd_424909] using wordTrace_append hprefix tailTrace_424909
  have hstable : (prefixWord ++ tailWord_424909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424909).length < 2 ^ (prefixWord ++ tailWord_424909).sum := by decide
  have hdescent : baseEnd_424909 < baseStart_424909 := by decide
  rcases family_descends (prefixWord ++ tailWord_424909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424930 : List Nat := [3, 3, 3, 1, 1, 1, 3, 4]
def baseStart_424930 : Nat := 118140960795 + 424930 * 2 ^ 59
def prefixEnd_424930 : Nat := 4983230072969 + 3 ^ 40 * 424930 * 2
def baseEnd_424930 : Nat := 129299753786742336664171

theorem tailTrace_424930 : CollatzResearch.WordTrace tailWord_424930 prefixEnd_424930 129299753786742336664171 := by
  unfold tailWord_424930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874617587639664277834061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10332313567039104740890829 3874617587639664277834061)
  ·
    refine ⟨1452981595364874104187773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3874617587639664277834061 1452981595364874104187773)
    ·
      refine ⟨544868098261827789070415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1452981595364874104187773 544868098261827789070415)
      ·
        refine ⟨817302147392741683605623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544868098261827789070415 817302147392741683605623)
        ·
          refine ⟨1225953221089112525408435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817302147392741683605623 1225953221089112525408435)
          ·
            refine ⟨1838929831633668788112653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225953221089112525408435 1838929831633668788112653)
            ·
              refine ⟨689598686862625795542245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1838929831633668788112653 689598686862625795542245)
              ·
                refine ⟨129299753786742336664171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 689598686862625795542245 129299753786742336664171)
                ·
                  rfl

theorem cell19_424930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_424930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424930 prefixEnd_424930 := by exact prefixLift 424930
  have htrace : WordTrace (prefixWord ++ tailWord_424930) baseStart_424930 baseEnd_424930 := by
    simpa [prefixWord, tailWord_424930, baseEnd_424930] using wordTrace_append hprefix tailTrace_424930
  have hstable : (prefixWord ++ tailWord_424930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424930).length < 2 ^ (prefixWord ++ tailWord_424930).sum := by decide
  have hdescent : baseEnd_424930 < baseStart_424930 := by decide
  rcases family_descends (prefixWord ++ tailWord_424930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424972 : List Nat := [2, 2, 1, 2, 3, 3, 6]
def baseStart_424972 : Nat := 118140960795 + 424972 * 2 ^ 59
def prefixEnd_424972 : Nat := 4983230072969 + 3 ^ 40 * 424972 * 2
def baseEnd_424972 : Nat := 43104177916566227910241

theorem tailTrace_424972 : CollatzResearch.WordTrace tailWord_424972 prefixEnd_424972 43104177916566227910241 := by
  unfold tailWord_424972
  simp only [CollatzResearch.WordTrace]
  refine ⟨7750001108203249142182585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10333334810937665522910113 7750001108203249142182585)
  ·
    refine ⟨5812500831152436856636939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7750001108203249142182585 5812500831152436856636939)
    ·
      refine ⟨8718751246728655284955409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5812500831152436856636939 8718751246728655284955409)
      ·
        refine ⟨6539063435046491463716557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8718751246728655284955409 6539063435046491463716557)
        ·
          refine ⟨2452148788142434298893709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6539063435046491463716557 2452148788142434298893709)
          ·
            refine ⟨919555795553412862085141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2452148788142434298893709 919555795553412862085141)
            ·
              refine ⟨43104177916566227910241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 919555795553412862085141 43104177916566227910241)
              ·
                rfl

theorem cell19_424972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_424972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_424972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_424972 prefixEnd_424972 := by exact prefixLift 424972
  have htrace : WordTrace (prefixWord ++ tailWord_424972) baseStart_424972 baseEnd_424972 := by
    simpa [prefixWord, tailWord_424972, baseEnd_424972] using wordTrace_append hprefix tailTrace_424972
  have hstable : (prefixWord ++ tailWord_424972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424972).length < 2 ^ (prefixWord ++ tailWord_424972).sum := by decide
  have hdescent : baseEnd_424972 < baseStart_424972 := by decide
  rcases family_descends (prefixWord ++ tailWord_424972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425010 : List Nat := [3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_425010 : Nat := 118140960795 + 425010 * 2 ^ 59
def prefixEnd_425010 : Nat := 4983230072969 + 3 ^ 40 * 425010 * 2
def baseEnd_425010 : Nat := 129324096573325854886175

theorem tailTrace_425010 : CollatzResearch.WordTrace tailWord_425010 prefixEnd_425010 129324096573325854886175 := by
  unfold tailWord_425010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3875347047567207693562121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10334258793512553849498989 3875347047567207693562121)
  ·
    refine ⟨2906510285675405770171591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3875347047567207693562121 2906510285675405770171591)
    ·
      refine ⟨4359765428513108655257387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2906510285675405770171591 4359765428513108655257387)
      ·
        refine ⟨6539648142769662982886081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359765428513108655257387 6539648142769662982886081)
        ·
          refine ⟨4904736107077247237164561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6539648142769662982886081 4904736107077247237164561)
          ·
            refine ⟨3678552080307935427873421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4904736107077247237164561 3678552080307935427873421)
            ·
              refine ⟨1379457030115475785452533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3678552080307935427873421 1379457030115475785452533)
              ·
                refine ⟨129324096573325854886175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1379457030115475785452533 129324096573325854886175)
                ·
                  rfl

theorem cell19_425010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_425010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425010 prefixEnd_425010 := by exact prefixLift 425010
  have htrace : WordTrace (prefixWord ++ tailWord_425010) baseStart_425010 baseEnd_425010 := by
    simpa [prefixWord, tailWord_425010, baseEnd_425010] using wordTrace_append hprefix tailTrace_425010
  have hstable : (prefixWord ++ tailWord_425010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425010).length < 2 ^ (prefixWord ++ tailWord_425010).sum := by decide
  have hdescent : baseEnd_425010 < baseStart_425010 := by decide
  rcases family_descends (prefixWord ++ tailWord_425010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425025 : List Nat := [1, 2, 5, 1, 4, 1, 5]
def baseStart_425025 : Nat := 118140960795 + 425025 * 2 ^ 59
def prefixEnd_425025 : Nat := 4983230072969 + 3 ^ 40 * 425025 * 2
def baseEnd_425025 : Nat := 43109553615270088184267

theorem tailTrace_425025 : CollatzResearch.WordTrace tailWord_425025 prefixEnd_425025 43109553615270088184267 := by
  unfold tailWord_425025
  simp only [CollatzResearch.WordTrace]
  refine ⟨15501935285214488336044529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10334623523476325557363019 15501935285214488336044529)
  ·
    refine ⟨11626451463910866252033397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15501935285214488336044529 11626451463910866252033397)
    ·
      refine ⟨1089979824741643711128131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11626451463910866252033397 1089979824741643711128131)
      ·
        refine ⟨1634969737112465566692197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089979824741643711128131 1634969737112465566692197)
        ·
          refine ⟨306556825708587293754787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1634969737112465566692197 306556825708587293754787)
          ·
            refine ⟨459835238562880940632181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306556825708587293754787 459835238562880940632181)
            ·
              refine ⟨43109553615270088184267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 459835238562880940632181 43109553615270088184267)
              ·
                rfl

theorem cell19_425025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 5].length) (baseStart_425025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425025 prefixEnd_425025 := by exact prefixLift 425025
  have htrace : WordTrace (prefixWord ++ tailWord_425025) baseStart_425025 baseEnd_425025 := by
    simpa [prefixWord, tailWord_425025, baseEnd_425025] using wordTrace_append hprefix tailTrace_425025
  have hstable : (prefixWord ++ tailWord_425025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425025).length < 2 ^ (prefixWord ++ tailWord_425025).sum := by decide
  have hdescent : baseEnd_425025 < baseStart_425025 := by decide
  rcases family_descends (prefixWord ++ tailWord_425025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425048 : List Nat := [2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_425048 : Nat := 118140960795 + 425048 * 2 ^ 59
def prefixEnd_425048 : Nat := 4983230072969 + 3 ^ 40 * 425048 * 2
def baseEnd_425048 : Nat := 129335659396953026041627

theorem tailTrace_425048 : CollatzResearch.WordTrace tailWord_425048 prefixEnd_425048 129335659396953026041627 := by
  unfold tailWord_425048
  simp only [CollatzResearch.WordTrace]
  refine ⟨7751387082065581632065899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10335182776087442176087865 7751387082065581632065899)
  ·
    refine ⟨11627080623098372448098849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7751387082065581632065899 11627080623098372448098849)
    ·
      refine ⟨8720310467323779336074137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11627080623098372448098849 8720310467323779336074137)
      ·
        refine ⟨6540232850492834502055603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8720310467323779336074137 6540232850492834502055603)
        ·
          refine ⟨9810349275739251753083405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6540232850492834502055603 9810349275739251753083405)
          ·
            refine ⟨3678880978402219407406277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9810349275739251753083405 3678880978402219407406277)
            ·
              refine ⟨689790183450416138888677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3678880978402219407406277 689790183450416138888677)
              ·
                refine ⟨129335659396953026041627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 689790183450416138888677 129335659396953026041627)
                ·
                  rfl

theorem cell19_425048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_425048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425048 prefixEnd_425048 := by exact prefixLift 425048
  have htrace : WordTrace (prefixWord ++ tailWord_425048) baseStart_425048 baseEnd_425048 := by
    simpa [prefixWord, tailWord_425048, baseEnd_425048] using wordTrace_append hprefix tailTrace_425048
  have hstable : (prefixWord ++ tailWord_425048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425048).length < 2 ^ (prefixWord ++ tailWord_425048).sum := by decide
  have hdescent : baseEnd_425048 < baseStart_425048 := by decide
  rcases family_descends (prefixWord ++ tailWord_425048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425219 : List Nat := [1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_425219 : Nat := 118140960795 + 425219 * 2 ^ 59
def prefixEnd_425219 : Nat := 4983230072969 + 3 ^ 40 * 425219 * 2
def baseEnd_425219 : Nat := 129387692103275296241161

theorem tailTrace_425219 : CollatzResearch.WordTrace tailWord_425219 prefixEnd_425219 129387692103275296241161 := by
  unfold tailWord_425219
  simp only [CollatzResearch.WordTrace]
  refine ⟨15509011046511659468606711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10339340697674439645737807 15509011046511659468606711)
  ·
    refine ⟨23263516569767489202910067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15509011046511659468606711 23263516569767489202910067)
    ·
      refine ⟨34895274854651233804365101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23263516569767489202910067 34895274854651233804365101)
      ·
        refine ⟨13085728070494212676636913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34895274854651233804365101 13085728070494212676636913)
        ·
          refine ⟨9814296052870659507477685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13085728070494212676636913 9814296052870659507477685)
          ·
            refine ⟨920090254956624328826033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9814296052870659507477685 920090254956624328826033)
            ·
              refine ⟨690067691217468246619525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 920090254956624328826033 690067691217468246619525)
              ·
                refine ⟨129387692103275296241161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690067691217468246619525 129387692103275296241161)
                ·
                  rfl

theorem cell19_425219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_425219 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425219 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425219 prefixEnd_425219 := by exact prefixLift 425219
  have htrace : WordTrace (prefixWord ++ tailWord_425219) baseStart_425219 baseEnd_425219 := by
    simpa [prefixWord, tailWord_425219, baseEnd_425219] using wordTrace_append hprefix tailTrace_425219
  have hstable : (prefixWord ++ tailWord_425219).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425219).length < 2 ^ (prefixWord ++ tailWord_425219).sum := by decide
  have hdescent : baseEnd_425219 < baseStart_425219 := by decide
  rcases family_descends (prefixWord ++ tailWord_425219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425270 : List Nat := [5, 1, 2, 3, 1, 2, 1, 4]
def baseStart_425270 : Nat := 118140960795 + 425270 * 2 ^ 59
def prefixEnd_425270 : Nat := 4983230072969 + 3 ^ 40 * 425270 * 2
def baseEnd_425270 : Nat := 129403210629722289107689

theorem tailTrace_425270 : CollatzResearch.WordTrace tailWord_425270 prefixEnd_425270 129403210629722289107689 := by
  unfold tailWord_425270
  simp only [CollatzResearch.WordTrace]
  refine ⟨969429448082930948669579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10340580779551263452475509 969429448082930948669579)
  ·
    refine ⟨1454144172124396423004369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 969429448082930948669579 1454144172124396423004369)
    ·
      refine ⟨1090608129093297317253277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1454144172124396423004369 1090608129093297317253277)
      ·
        refine ⟨408978048409986493969979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1090608129093297317253277 408978048409986493969979)
        ·
          refine ⟨613467072614979740954969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408978048409986493969979 613467072614979740954969)
          ·
            refine ⟨460100304461234805716227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613467072614979740954969 460100304461234805716227)
            ·
              refine ⟨690150456691852208574341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460100304461234805716227 690150456691852208574341)
              ·
                refine ⟨129403210629722289107689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690150456691852208574341 129403210629722289107689)
                ·
                  rfl

theorem cell19_425270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_425270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425270 prefixEnd_425270 := by exact prefixLift 425270
  have htrace : WordTrace (prefixWord ++ tailWord_425270) baseStart_425270 baseEnd_425270 := by
    simpa [prefixWord, tailWord_425270, baseEnd_425270] using wordTrace_append hprefix tailTrace_425270
  have hstable : (prefixWord ++ tailWord_425270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425270).length < 2 ^ (prefixWord ++ tailWord_425270).sum := by decide
  have hdescent : baseEnd_425270 < baseStart_425270 := by decide
  rcases family_descends (prefixWord ++ tailWord_425270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425276 : List Nat := [2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_425276 : Nat := 118140960795 + 425276 * 2 ^ 59
def prefixEnd_425276 : Nat := 4983230072969 + 3 ^ 40 * 425276 * 2
def baseEnd_425276 : Nat := 129405036338716052974339

theorem tailTrace_425276 : CollatzResearch.WordTrace tailWord_425276 prefixEnd_425276 129405036338716052974339 := by
  unfold tailWord_425276
  simp only [CollatzResearch.WordTrace]
  refine ⟨7755545003652579101715841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10340726671536772135621121 7755545003652579101715841)
  ·
    refine ⟨5816658752739434326286881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7755545003652579101715841 5816658752739434326286881)
    ·
      refine ⟨4362494064554575744715161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5816658752739434326286881 4362494064554575744715161)
      ·
        refine ⟨3271870548415931808536371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4362494064554575744715161 3271870548415931808536371)
        ·
          refine ⟨4907805822623897712804557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271870548415931808536371 4907805822623897712804557)
          ·
            refine ⟨1840427183483961642301709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4907805822623897712804557 1840427183483961642301709)
            ·
              refine ⟨690160193806485615863141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1840427183483961642301709 690160193806485615863141)
              ·
                refine ⟨129405036338716052974339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690160193806485615863141 129405036338716052974339)
                ·
                  rfl

theorem cell19_425276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_425276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425276 prefixEnd_425276 := by exact prefixLift 425276
  have htrace : WordTrace (prefixWord ++ tailWord_425276) baseStart_425276 baseEnd_425276 := by
    simpa [prefixWord, tailWord_425276, baseEnd_425276] using wordTrace_append hprefix tailTrace_425276
  have hstable : (prefixWord ++ tailWord_425276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425276).length < 2 ^ (prefixWord ++ tailWord_425276).sum := by decide
  have hdescent : baseEnd_425276 < baseStart_425276 := by decide
  rcases family_descends (prefixWord ++ tailWord_425276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425314 : List Nat := [3, 3, 2, 1, 1, 1, 8]
def baseStart_425314 : Nat := 118140960795 + 425314 * 2 ^ 59
def prefixEnd_425314 : Nat := 4983230072969 + 3 ^ 40 * 425314 * 2
def baseEnd_425314 : Nat := 43138866387447741376597

theorem tailTrace_425314 : CollatzResearch.WordTrace tailWord_425314 prefixEnd_425314 43138866387447741376597 := by
  unfold tailWord_425314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878118995291872673328749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10341650654111660462209997 3878118995291872673328749)
  ·
    refine ⟨1454294623234452252498281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3878118995291872673328749 1454294623234452252498281)
    ·
      refine ⟨1090720967425839189373711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1454294623234452252498281 1090720967425839189373711)
      ·
        refine ⟨1636081451138758784060567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090720967425839189373711 1636081451138758784060567)
        ·
          refine ⟨2454122176708138176090851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636081451138758784060567 2454122176708138176090851)
          ·
            refine ⟨3681183265062207264136277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454122176708138176090851 3681183265062207264136277)
            ·
              refine ⟨43138866387447741376597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3681183265062207264136277 43138866387447741376597)
              ·
                rfl

theorem cell19_425314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_425314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425314 prefixEnd_425314 := by exact prefixLift 425314
  have htrace : WordTrace (prefixWord ++ tailWord_425314) baseStart_425314 baseEnd_425314 := by
    simpa [prefixWord, tailWord_425314, baseEnd_425314] using wordTrace_append hprefix tailTrace_425314
  have hstable : (prefixWord ++ tailWord_425314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425314).length < 2 ^ (prefixWord ++ tailWord_425314).sum := by decide
  have hdescent : baseEnd_425314 < baseStart_425314 := by decide
  rcases family_descends (prefixWord ++ tailWord_425314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425335 : List Nat := [1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_425335 : Nat := 118140960795 + 425335 * 2 ^ 59
def prefixEnd_425335 : Nat := 4983230072969 + 3 ^ 40 * 425335 * 2
def baseEnd_425335 : Nat := 129422989143821397663067

theorem tailTrace_425335 : CollatzResearch.WordTrace tailWord_425335 prefixEnd_425335 129422989143821397663067 := by
  unfold tailWord_425335
  simp only [CollatzResearch.WordTrace]
  refine ⟨15513241914091411279829459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10342161276060940853219639 15513241914091411279829459)
  ·
    refine ⟨23269862871137116919744189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15513241914091411279829459 23269862871137116919744189)
    ·
      refine ⟨8726198576676418844904071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23269862871137116919744189 8726198576676418844904071)
      ·
        refine ⟨13089297865014628267356107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8726198576676418844904071 13089297865014628267356107)
        ·
          refine ⟨19633946797521942401034161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13089297865014628267356107 19633946797521942401034161)
          ·
            refine ⟨14725460098141456800775621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19633946797521942401034161 14725460098141456800775621)
            ·
              refine ⟨2761023768401523150145429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14725460098141456800775621 2761023768401523150145429)
              ·
                refine ⟨129422989143821397663067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2761023768401523150145429 129422989143821397663067)
                ·
                  rfl

theorem cell19_425335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_425335 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425335 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425335 prefixEnd_425335 := by exact prefixLift 425335
  have htrace : WordTrace (prefixWord ++ tailWord_425335) baseStart_425335 baseEnd_425335 := by
    simpa [prefixWord, tailWord_425335, baseEnd_425335] using wordTrace_append hprefix tailTrace_425335
  have hstable : (prefixWord ++ tailWord_425335).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425335).length < 2 ^ (prefixWord ++ tailWord_425335).sum := by decide
  have hdescent : baseEnd_425335 < baseStart_425335 := by decide
  rcases family_descends (prefixWord ++ tailWord_425335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425346 : List Nat := [3, 4, 2, 1, 1, 3, 2, 3]
def baseStart_425346 : Nat := 118140960795 + 425346 * 2 ^ 59
def prefixEnd_425346 : Nat := 4983230072969 + 3 ^ 40 * 425346 * 2
def baseEnd_425346 : Nat := 129426336276976631418593

theorem tailTrace_425346 : CollatzResearch.WordTrace tailWord_425346 prefixEnd_425346 129426336276976631418593 := by
  unfold tailWord_425346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878410779262890039619973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10342428744701040105653261 3878410779262890039619973)
  ·
    refine ⟨727202021111791882428745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3878410779262890039619973 727202021111791882428745)
    ·
      refine ⟨545401515833843911821559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 727202021111791882428745 545401515833843911821559)
      ·
        refine ⟨818102273750765867732339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545401515833843911821559 818102273750765867732339)
        ·
          refine ⟨1227153410626148801598509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818102273750765867732339 1227153410626148801598509)
          ·
            refine ⟨460182528984805800599441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1227153410626148801598509 460182528984805800599441)
            ·
              refine ⟨345136896738604350449581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460182528984805800599441 345136896738604350449581)
              ·
                refine ⟨129426336276976631418593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345136896738604350449581 129426336276976631418593)
                ·
                  rfl

theorem cell19_425346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_425346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425346 prefixEnd_425346 := by exact prefixLift 425346
  have htrace : WordTrace (prefixWord ++ tailWord_425346) baseStart_425346 baseEnd_425346 := by
    simpa [prefixWord, tailWord_425346, baseEnd_425346] using wordTrace_append hprefix tailTrace_425346
  have hstable : (prefixWord ++ tailWord_425346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425346).length < 2 ^ (prefixWord ++ tailWord_425346).sum := by decide
  have hdescent : baseEnd_425346 < baseStart_425346 := by decide
  rcases family_descends (prefixWord ++ tailWord_425346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425352 : List Nat := [2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_425352 : Nat := 118140960795 + 425352 * 2 ^ 59
def prefixEnd_425352 : Nat := 4983230072969 + 3 ^ 40 * 425352 * 2
def baseEnd_425352 : Nat := 129428161985970395285243

theorem tailTrace_425352 : CollatzResearch.WordTrace tailWord_425352 prefixEnd_425352 129428161985970395285243 := by
  unfold tailWord_425352
  simp only [CollatzResearch.WordTrace]
  refine ⟨7756930977514911591599155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10342574636686548788798873 7756930977514911591599155)
  ·
    refine ⟨11635396466272367387398733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7756930977514911591599155 11635396466272367387398733)
    ·
      refine ⟨4363273674852137770274525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11635396466272367387398733 4363273674852137770274525)
      ·
        refine ⟨1636227628069551663852947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4363273674852137770274525 1636227628069551663852947)
        ·
          refine ⟨2454341442104327495779421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636227628069551663852947 2454341442104327495779421)
          ·
            refine ⟨920378040789122810917283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2454341442104327495779421 920378040789122810917283)
            ·
              refine ⟨1380567061183684216375925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920378040789122810917283 1380567061183684216375925)
              ·
                refine ⟨129428161985970395285243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1380567061183684216375925 129428161985970395285243)
                ·
                  rfl

theorem cell19_425352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_425352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425352 prefixEnd_425352 := by exact prefixLift 425352
  have htrace : WordTrace (prefixWord ++ tailWord_425352) baseStart_425352 baseEnd_425352 := by
    simpa [prefixWord, tailWord_425352, baseEnd_425352] using wordTrace_append hprefix tailTrace_425352
  have hstable : (prefixWord ++ tailWord_425352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425352).length < 2 ^ (prefixWord ++ tailWord_425352).sum := by decide
  have hdescent : baseEnd_425352 < baseStart_425352 := by decide
  rcases family_descends (prefixWord ++ tailWord_425352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425411 : List Nat := [1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_425411 : Nat := 118140960795 + 425411 * 2 ^ 59
def prefixEnd_425411 : Nat := 4983230072969 + 3 ^ 40 * 425411 * 2
def baseEnd_425411 : Nat := 129446114791075739973971

theorem tailTrace_425411 : CollatzResearch.WordTrace tailWord_425411 prefixEnd_425411 129446114791075739973971 := by
  unfold tailWord_425411
  simp only [CollatzResearch.WordTrace]
  refine ⟨15516013861816076259596087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10344009241210717506397391 15516013861816076259596087)
  ·
    refine ⟨23274020792724114389394131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15516013861816076259596087 23274020792724114389394131)
    ·
      refine ⟨34911031189086171584091197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23274020792724114389394131 34911031189086171584091197)
      ·
        refine ⟨13091636695907314344034199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34911031189086171584091197 13091636695907314344034199)
        ·
          refine ⟨19637455043860971516051299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13091636695907314344034199 19637455043860971516051299)
          ·
            refine ⟨29456182565791457274076949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19637455043860971516051299 29456182565791457274076949)
            ·
              refine ⟨1380758557771474559722357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29456182565791457274076949 1380758557771474559722357)
              ·
                refine ⟨129446114791075739973971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1380758557771474559722357 129446114791075739973971)
                ·
                  rfl

theorem cell19_425411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_425411 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425411 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425411 prefixEnd_425411 := by exact prefixLift 425411
  have htrace : WordTrace (prefixWord ++ tailWord_425411) baseStart_425411 baseEnd_425411 := by
    simpa [prefixWord, tailWord_425411, baseEnd_425411] using wordTrace_append hprefix tailTrace_425411
  have hstable : (prefixWord ++ tailWord_425411).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425411).length < 2 ^ (prefixWord ++ tailWord_425411).sum := by decide
  have hdescent : baseEnd_425411 < baseStart_425411 := by decide
  rcases family_descends (prefixWord ++ tailWord_425411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425428 : List Nat := [2, 4, 1, 2, 3, 7]
def baseStart_425428 : Nat := 118140960795 + 425428 * 2 ^ 59
def prefixEnd_425428 : Nat := 4983230072969 + 3 ^ 40 * 425428 * 2
def baseEnd_425428 : Nat := 14383476403691637510683

theorem tailTrace_425428 : CollatzResearch.WordTrace tailWord_425428 prefixEnd_425428 14383476403691637510683 := by
  unfold tailWord_425428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758316951377244081482469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10344422601836325441976625 7758316951377244081482469)
  ·
    refine ⟨1454684428383233265277963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7758316951377244081482469 1454684428383233265277963)
    ·
      refine ⟨2182026642574849897916945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454684428383233265277963 2182026642574849897916945)
      ·
        refine ⟨1636519981931137423437709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2182026642574849897916945 1636519981931137423437709)
        ·
          refine ⟨613694993224176533789141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1636519981931137423437709 613694993224176533789141)
          ·
            refine ⟨14383476403691637510683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 613694993224176533789141 14383476403691637510683)
            ·
              rfl

theorem cell19_425428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 7].length) (baseStart_425428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425428 prefixEnd_425428 := by exact prefixLift 425428
  have htrace : WordTrace (prefixWord ++ tailWord_425428) baseStart_425428 baseEnd_425428 := by
    simpa [prefixWord, tailWord_425428, baseEnd_425428] using wordTrace_append hprefix tailTrace_425428
  have hstable : (prefixWord ++ tailWord_425428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425428).length < 2 ^ (prefixWord ++ tailWord_425428).sum := by decide
  have hdescent : baseEnd_425428 < baseStart_425428 := by decide
  rcases family_descends (prefixWord ++ tailWord_425428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425445 : List Nat := [1, 3, 1, 5, 1, 3, 1, 4]
def baseStart_425445 : Nat := 118140960795 + 425445 * 2 ^ 59
def prefixEnd_425445 : Nat := 4983230072969 + 3 ^ 40 * 425445 * 2
def baseEnd_425445 : Nat := 129456460475373735218323

theorem tailTrace_425445 : CollatzResearch.WordTrace tailWord_425445 prefixEnd_425445 129456460475373735218323 := by
  unfold tailWord_425445
  simp only [CollatzResearch.WordTrace]
  refine ⟨15517253943692900066333789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10344835962461933377555859 15517253943692900066333789)
  ·
    refine ⟨5818970228884837524875171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15517253943692900066333789 5818970228884837524875171)
    ·
      refine ⟨8728455343327256287312757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5818970228884837524875171 8728455343327256287312757)
      ·
        refine ⟨818292688436930276935571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8728455343327256287312757 818292688436930276935571)
        ·
          refine ⟨1227439032655395415403357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818292688436930276935571 1227439032655395415403357)
          ·
            refine ⟨460289637245773280776259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1227439032655395415403357 460289637245773280776259)
            ·
              refine ⟨690434455868659921164389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460289637245773280776259 690434455868659921164389)
              ·
                refine ⟨129456460475373735218323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690434455868659921164389 129456460475373735218323)
                ·
                  rfl

theorem cell19_425445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_425445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425445 prefixEnd_425445 := by exact prefixLift 425445
  have htrace : WordTrace (prefixWord ++ tailWord_425445) baseStart_425445 baseEnd_425445 := by
    simpa [prefixWord, tailWord_425445, baseEnd_425445] using wordTrace_append hprefix tailTrace_425445
  have hstable : (prefixWord ++ tailWord_425445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425445).length < 2 ^ (prefixWord ++ tailWord_425445).sum := by decide
  have hdescent : baseEnd_425445 < baseStart_425445 := by decide
  rcases family_descends (prefixWord ++ tailWord_425445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425447 : List Nat := [1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_425447 : Nat := 118140960795 + 425447 * 2 ^ 59
def prefixEnd_425447 : Nat := 4983230072969 + 3 ^ 40 * 425447 * 2
def baseEnd_425447 : Nat := 129457069045038323173873

theorem tailTrace_425447 : CollatzResearch.WordTrace tailWord_425447 prefixEnd_425447 129457069045038323173873 := by
  unfold tailWord_425447
  simp only [CollatzResearch.WordTrace]
  refine ⟨15517326889685654407906595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10344884593123769605271063 15517326889685654407906595)
  ·
    refine ⟨23275990334528481611859893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15517326889685654407906595 23275990334528481611859893)
    ·
      refine ⟨2182124093862045151111865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23275990334528481611859893 2182124093862045151111865)
      ·
        refine ⟨1636593070396533863333899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2182124093862045151111865 1636593070396533863333899)
        ·
          refine ⟨2454889605594800795000849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636593070396533863333899 2454889605594800795000849)
          ·
            refine ⟨1841167204196100596250637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2454889605594800795000849 1841167204196100596250637)
            ·
              refine ⟨690437701573537723593989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1841167204196100596250637 690437701573537723593989)
              ·
                refine ⟨129457069045038323173873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690437701573537723593989 129457069045038323173873)
                ·
                  rfl

theorem cell19_425447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_425447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425447 prefixEnd_425447 := by exact prefixLift 425447
  have htrace : WordTrace (prefixWord ++ tailWord_425447) baseStart_425447 baseEnd_425447 := by
    simpa [prefixWord, tailWord_425447, baseEnd_425447] using wordTrace_append hprefix tailTrace_425447
  have hstable : (prefixWord ++ tailWord_425447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425447).length < 2 ^ (prefixWord ++ tailWord_425447).sum := by decide
  have hdescent : baseEnd_425447 < baseStart_425447 := by decide
  rcases family_descends (prefixWord ++ tailWord_425447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425466 : List Nat := [3, 1, 1, 1, 1, 2, 7, 3]
def baseStart_425466 : Nat := 118140960795 + 425466 * 2 ^ 59
def prefixEnd_425466 : Nat := 4983230072969 + 3 ^ 40 * 425466 * 2
def baseEnd_425466 : Nat := 129462850456851908751599

theorem tailTrace_425466 : CollatzResearch.WordTrace tailWord_425466 prefixEnd_425466 129462850456851908751599 := by
  unfold tailWord_425466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3879504969154205163212063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10345346584411213768565501 3879504969154205163212063)
  ·
    refine ⟨5819257453731307744818095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3879504969154205163212063 5819257453731307744818095)
    ·
      refine ⟨8728886180596961617227143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5819257453731307744818095 8728886180596961617227143)
      ·
        refine ⟨13093329270895442425840715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8728886180596961617227143 13093329270895442425840715)
        ·
          refine ⟨19639993906343163638761073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13093329270895442425840715 19639993906343163638761073)
          ·
            refine ⟨14729995429757372729070805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19639993906343163638761073 14729995429757372729070805)
            ·
              refine ⟨345234267884938423337597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14729995429757372729070805 345234267884938423337597)
              ·
                refine ⟨129462850456851908751599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345234267884938423337597 129462850456851908751599)
                ·
                  rfl

theorem cell19_425466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_425466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425466 prefixEnd_425466 := by exact prefixLift 425466
  have htrace : WordTrace (prefixWord ++ tailWord_425466) baseStart_425466 baseEnd_425466 := by
    simpa [prefixWord, tailWord_425466, baseEnd_425466] using wordTrace_append hprefix tailTrace_425466
  have hstable : (prefixWord ++ tailWord_425466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425466).length < 2 ^ (prefixWord ++ tailWord_425466).sum := by decide
  have hdescent : baseEnd_425466 < baseStart_425466 := by decide
  rcases family_descends (prefixWord ++ tailWord_425466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425468 : List Nat := [2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_425468 : Nat := 118140960795 + 425468 * 2 ^ 59
def prefixEnd_425468 : Nat := 4983230072969 + 3 ^ 40 * 425468 * 2
def baseEnd_425468 : Nat := 129463459026516496707149

theorem tailTrace_425468 : CollatzResearch.WordTrace tailWord_425468 prefixEnd_425468 129463459026516496707149 := by
  unfold tailWord_425468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7759046411304787497210529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10345395215073049996280705 7759046411304787497210529)
  ·
    refine ⟨5819284808478590622907897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7759046411304787497210529 5819284808478590622907897)
    ·
      refine ⟨4364463606358942967180923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5819284808478590622907897 4364463606358942967180923)
      ·
        refine ⟨6546695409538414450771385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4364463606358942967180923 6546695409538414450771385)
        ·
          refine ⟨4910021557153810838078539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6546695409538414450771385 4910021557153810838078539)
          ·
            refine ⟨7365032335730716257117809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4910021557153810838078539 7365032335730716257117809)
            ·
              refine ⟨5523774251798037192838357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7365032335730716257117809 5523774251798037192838357)
              ·
                refine ⟨129463459026516496707149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5523774251798037192838357 129463459026516496707149)
                ·
                  rfl

theorem cell19_425468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_425468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425468 prefixEnd_425468 := by exact prefixLift 425468
  have htrace : WordTrace (prefixWord ++ tailWord_425468) baseStart_425468 baseEnd_425468 := by
    simpa [prefixWord, tailWord_425468, baseEnd_425468] using wordTrace_append hprefix tailTrace_425468
  have hstable : (prefixWord ++ tailWord_425468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425468).length < 2 ^ (prefixWord ++ tailWord_425468).sum := by decide
  have hdescent : baseEnd_425468 < baseStart_425468 := by decide
  rcases family_descends (prefixWord ++ tailWord_425468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425523 : List Nat := [1, 1, 1, 2, 4, 3, 4, 3]
def baseStart_425523 : Nat := 118140960795 + 425523 * 2 ^ 59
def prefixEnd_425523 : Nat := 4983230072969 + 3 ^ 40 * 425523 * 2
def baseEnd_425523 : Nat := 129480194692292665484777

theorem tailTrace_425523 : CollatzResearch.WordTrace tailWord_425523 prefixEnd_425523 129480194692292665484777 := by
  unfold tailWord_425523
  simp only [CollatzResearch.WordTrace]
  refine ⟨15520098837410319387673223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10346732558273546258448815 15520098837410319387673223)
  ·
    refine ⟨23280148256115479081509835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15520098837410319387673223 23280148256115479081509835)
    ·
      refine ⟨34920222384173218622264753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23280148256115479081509835 34920222384173218622264753)
      ·
        refine ⟨26190166788129913966698565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34920222384173218622264753 26190166788129913966698565)
        ·
          refine ⟨4910656272774358868755981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26190166788129913966698565 4910656272774358868755981)
          ·
            refine ⟨1841496102290384575783493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4910656272774358868755981 1841496102290384575783493)
            ·
              refine ⟨345280519179447107959405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1841496102290384575783493 345280519179447107959405)
              ·
                refine ⟨129480194692292665484777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345280519179447107959405 129480194692292665484777)
                ·
                  rfl

theorem cell19_425523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 3].length) (baseStart_425523 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425523 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425523 prefixEnd_425523 := by exact prefixLift 425523
  have htrace : WordTrace (prefixWord ++ tailWord_425523) baseStart_425523 baseEnd_425523 := by
    simpa [prefixWord, tailWord_425523, baseEnd_425523] using wordTrace_append hprefix tailTrace_425523
  have hstable : (prefixWord ++ tailWord_425523).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425523).length < 2 ^ (prefixWord ++ tailWord_425523).sum := by decide
  have hdescent : baseEnd_425523 < baseStart_425523 := by decide
  rcases family_descends (prefixWord ++ tailWord_425523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425601 : List Nat := [1, 2, 4, 2, 1, 9]
def baseStart_425601 : Nat := 118140960795 + 425601 * 2 ^ 59
def prefixEnd_425601 : Nat := 4983230072969 + 3 ^ 40 * 425601 * 2
def baseEnd_425601 : Nat := 14389325434356843972359

theorem tailTrace_425601 : CollatzResearch.WordTrace tailWord_425601 prefixEnd_425601 14389325434356843972359 := by
  unfold tailWord_425601
  simp only [CollatzResearch.WordTrace]
  refine ⟨15522943731127738709012657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10348629154085159139341771 15522943731127738709012657)
  ·
    refine ⟨11642207798345804031759493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15522943731127738709012657 11642207798345804031759493)
    ·
      refine ⟨2182913962189838255954905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11642207798345804031759493 2182913962189838255954905)
      ·
        refine ⟨1637185471642378691966179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2182913962189838255954905 1637185471642378691966179)
        ·
          refine ⟨2455778207463568037949269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637185471642378691966179 2455778207463568037949269)
          ·
            refine ⟨14389325434356843972359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2455778207463568037949269 14389325434356843972359)
            ·
              rfl

theorem cell19_425601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 9].length) (baseStart_425601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425601 prefixEnd_425601 := by exact prefixLift 425601
  have htrace : WordTrace (prefixWord ++ tailWord_425601) baseStart_425601 baseEnd_425601 := by
    simpa [prefixWord, tailWord_425601, baseEnd_425601] using wordTrace_append hprefix tailTrace_425601
  have hstable : (prefixWord ++ tailWord_425601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425601).length < 2 ^ (prefixWord ++ tailWord_425601).sum := by decide
  have hdescent : baseEnd_425601 < baseStart_425601 := by decide
  rcases family_descends (prefixWord ++ tailWord_425601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425654 : List Nat := [5, 1, 3, 1, 1, 2, 6]
def baseStart_425654 : Nat := 118140960795 + 425654 * 2 ^ 59
def prefixEnd_425654 : Nat := 4983230072969 + 3 ^ 40 * 425654 * 2
def baseEnd_425654 : Nat := 43173352001774392191103

theorem tailTrace_425654 : CollatzResearch.WordTrace tailWord_425654 prefixEnd_425654 43173352001774392191103 := by
  unfold tailWord_425654
  simp only [CollatzResearch.WordTrace]
  refine ⟨970304799995983047543251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10349917866623819173794677 970304799995983047543251)
  ·
    refine ⟨1455457199993974571314877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 970304799995983047543251 1455457199993974571314877)
    ·
      refine ⟨545796449997740464243079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1455457199993974571314877 545796449997740464243079)
      ·
        refine ⟨818694674996610696364619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545796449997740464243079 818694674996610696364619)
        ·
          refine ⟨1228042012494916044546929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818694674996610696364619 1228042012494916044546929)
          ·
            refine ⟨921031509371187033410197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1228042012494916044546929 921031509371187033410197)
            ·
              refine ⟨43173352001774392191103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 921031509371187033410197 43173352001774392191103)
              ·
                rfl

theorem cell19_425654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_425654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425654 prefixEnd_425654 := by exact prefixLift 425654
  have htrace : WordTrace (prefixWord ++ tailWord_425654) baseStart_425654 baseEnd_425654 := by
    simpa [prefixWord, tailWord_425654, baseEnd_425654] using wordTrace_append hprefix tailTrace_425654
  have hstable : (prefixWord ++ tailWord_425654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425654).length < 2 ^ (prefixWord ++ tailWord_425654).sum := by decide
  have hdescent : baseEnd_425654 < baseStart_425654 := by decide
  rcases family_descends (prefixWord ++ tailWord_425654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425658 : List Nat := [3, 1, 1, 1, 2, 5, 6]
def baseStart_425658 : Nat := 118140960795 + 425658 * 2 ^ 59
def prefixEnd_425658 : Nat := 4983230072969 + 3 ^ 40 * 425658 * 2
def baseEnd_425658 : Nat := 43173757714884117494803

theorem tailTrace_425658 : CollatzResearch.WordTrace tailWord_425658 prefixEnd_425658 43173757714884117494803 := by
  unfold tailWord_425658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3881255672980309360959407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10350015127947491629225085 3881255672980309360959407)
  ·
    refine ⟨5821883509470464041439111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3881255672980309360959407 5821883509470464041439111)
    ·
      refine ⟨8732825264205696062158667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5821883509470464041439111 8732825264205696062158667)
      ·
        refine ⟨13099237896308544093238001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8732825264205696062158667 13099237896308544093238001)
        ·
          refine ⟨9824428422231408069928501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13099237896308544093238001 9824428422231408069928501)
          ·
            refine ⟨921040164584194506555797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9824428422231408069928501 921040164584194506555797)
            ·
              refine ⟨43173757714884117494803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 921040164584194506555797 43173757714884117494803)
              ·
                rfl

theorem cell19_425658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_425658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425658 prefixEnd_425658 := by exact prefixLift 425658
  have htrace : WordTrace (prefixWord ++ tailWord_425658) baseStart_425658 baseEnd_425658 := by
    simpa [prefixWord, tailWord_425658, baseEnd_425658] using wordTrace_append hprefix tailTrace_425658
  have hstable : (prefixWord ++ tailWord_425658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425658).length < 2 ^ (prefixWord ++ tailWord_425658).sum := by decide
  have hdescent : baseEnd_425658 < baseStart_425658 := by decide
  rcases family_descends (prefixWord ++ tailWord_425658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425686 : List Nat := [5, 2, 1, 3, 2, 1, 2, 3]
def baseStart_425686 : Nat := 118140960795 + 425686 * 2 ^ 59
def prefixEnd_425686 : Nat := 4983230072969 + 3 ^ 40 * 425686 * 2
def baseEnd_425686 : Nat := 129529793119956583862111

theorem tailTrace_425686 : CollatzResearch.WordTrace tailWord_425686 prefixEnd_425686 129529793119956583862111 := by
  unfold tailWord_425686
  simp only [CollatzResearch.WordTrace]
  refine ⟨970377745988737389116057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10350695957213198817237941 970377745988737389116057)
  ·
    refine ⟨727783309491553041837043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 970377745988737389116057 727783309491553041837043)
    ·
      refine ⟨1091674964237329562755565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 727783309491553041837043 1091674964237329562755565)
      ·
        refine ⟨409378111588998586033337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1091674964237329562755565 409378111588998586033337)
        ·
          refine ⟨307033583691748939525003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409378111588998586033337 307033583691748939525003)
          ·
            refine ⟨460550375537623409287505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307033583691748939525003 460550375537623409287505)
            ·
              refine ⟨345412781653217556965629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460550375537623409287505 345412781653217556965629)
              ·
                refine ⟨129529793119956583862111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345412781653217556965629 129529793119956583862111)
                ·
                  rfl

theorem cell19_425686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_425686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425686 prefixEnd_425686 := by exact prefixLift 425686
  have htrace : WordTrace (prefixWord ++ tailWord_425686) baseStart_425686 baseEnd_425686 := by
    simpa [prefixWord, tailWord_425686, baseEnd_425686] using wordTrace_append hprefix tailTrace_425686
  have hstable : (prefixWord ++ tailWord_425686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425686).length < 2 ^ (prefixWord ++ tailWord_425686).sum := by decide
  have hdescent : baseEnd_425686 < baseStart_425686 := by decide
  rcases family_descends (prefixWord ++ tailWord_425686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425692 : List Nat := [2, 2, 5, 1, 2, 1, 1, 5]
def baseStart_425692 : Nat := 118140960795 + 425692 * 2 ^ 59
def prefixEnd_425692 : Nat := 4983230072969 + 3 ^ 40 * 425692 * 2
def baseEnd_425692 : Nat := 129531618828950347728761

theorem tailTrace_425692 : CollatzResearch.WordTrace tailWord_425692 prefixEnd_425692 129531618828950347728761 := by
  unfold tailWord_425692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7763131386899030625287665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10350841849198707500383553 7763131386899030625287665)
  ·
    refine ⟨5822348540174272968965749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7763131386899030625287665 5822348540174272968965749)
    ·
      refine ⟨545845175641338090840539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5822348540174272968965749 545845175641338090840539)
      ·
        refine ⟨818767763462007136260809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545845175641338090840539 818767763462007136260809)
        ·
          refine ⟨614075822596505352195607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818767763462007136260809 614075822596505352195607)
          ·
            refine ⟨921113733894758028293411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614075822596505352195607 921113733894758028293411)
            ·
              refine ⟨1381670600842137042440117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921113733894758028293411 1381670600842137042440117)
              ·
                refine ⟨129531618828950347728761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1381670600842137042440117 129531618828950347728761)
                ·
                  rfl

theorem cell19_425692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_425692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425692 prefixEnd_425692 := by exact prefixLift 425692
  have htrace : WordTrace (prefixWord ++ tailWord_425692) baseStart_425692 baseEnd_425692 := by
    simpa [prefixWord, tailWord_425692, baseEnd_425692] using wordTrace_append hprefix tailTrace_425692
  have hstable : (prefixWord ++ tailWord_425692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425692).length < 2 ^ (prefixWord ++ tailWord_425692).sum := by decide
  have hdescent : baseEnd_425692 < baseStart_425692 := by decide
  rcases family_descends (prefixWord ++ tailWord_425692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425732 : List Nat := [2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_425732 : Nat := 118140960795 + 425732 * 2 ^ 59
def prefixEnd_425732 : Nat := 4983230072969 + 3 ^ 40 * 425732 * 2
def baseEnd_425732 : Nat := 129543790222242106839763

theorem tailTrace_425732 : CollatzResearch.WordTrace tailWord_425732 prefixEnd_425732 129543790222242106839763 := by
  unfold tailWord_425732
  simp only [CollatzResearch.WordTrace]
  refine ⟨7763860846826574041015725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10351814462435432054687633 7763860846826574041015725)
  ·
    refine ⟨2911447817559965265380897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7763860846826574041015725 2911447817559965265380897)
    ·
      refine ⟨2183585863169973949035673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2911447817559965265380897 2183585863169973949035673)
      ·
        refine ⟨1637689397377480461776755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2183585863169973949035673 1637689397377480461776755)
        ·
          refine ⟨2456534096066220692665133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637689397377480461776755 2456534096066220692665133)
          ·
            refine ⟨921200286024832759749425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2456534096066220692665133 921200286024832759749425)
            ·
              refine ⟨690900214518624569812069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921200286024832759749425 690900214518624569812069)
              ·
                refine ⟨129543790222242106839763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690900214518624569812069 129543790222242106839763)
                ·
                  rfl

theorem cell19_425732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_425732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425732 prefixEnd_425732 := by exact prefixLift 425732
  have htrace : WordTrace (prefixWord ++ tailWord_425732) baseStart_425732 baseEnd_425732 := by
    simpa [prefixWord, tailWord_425732, baseEnd_425732] using wordTrace_append hprefix tailTrace_425732
  have hstable : (prefixWord ++ tailWord_425732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425732).length < 2 ^ (prefixWord ++ tailWord_425732).sum := by decide
  have hdescent : baseEnd_425732 < baseStart_425732 := by decide
  rcases family_descends (prefixWord ++ tailWord_425732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425785 : List Nat := [1, 2, 1, 7, 2, 1, 1, 4]
def baseStart_425785 : Nat := 118140960795 + 425785 * 2 ^ 59
def prefixEnd_425785 : Nat := 4983230072969 + 3 ^ 40 * 425785 * 2
def baseEnd_425785 : Nat := 129559917318353687661841

theorem tailTrace_425785 : CollatzResearch.WordTrace tailWord_425785 prefixEnd_425785 129559917318353687661841 := by
  unfold tailWord_425785
  simp only [CollatzResearch.WordTrace]
  refine ⟨15529654762461138133710809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10353103174974092089140539 15529654762461138133710809)
  ·
    refine ⟨11647241071845853600283107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15529654762461138133710809 11647241071845853600283107)
    ·
      refine ⟨17470861607768780400424661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11647241071845853600283107 17470861607768780400424661)
      ·
        refine ⟨409473318932080790634953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 17470861607768780400424661 409473318932080790634953)
        ·
          refine ⟨307104989199060592976215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409473318932080790634953 307104989199060592976215)
          ·
            refine ⟨460657483798590889464323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307104989199060592976215 460657483798590889464323)
            ·
              refine ⟨690986225697886334196485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460657483798590889464323 690986225697886334196485)
              ·
                refine ⟨129559917318353687661841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690986225697886334196485 129559917318353687661841)
                ·
                  rfl

theorem cell19_425785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 4].length) (baseStart_425785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425785 prefixEnd_425785 := by exact prefixLift 425785
  have htrace : WordTrace (prefixWord ++ tailWord_425785) baseStart_425785 baseEnd_425785 := by
    simpa [prefixWord, tailWord_425785, baseEnd_425785] using wordTrace_append hprefix tailTrace_425785
  have hstable : (prefixWord ++ tailWord_425785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425785).length < 2 ^ (prefixWord ++ tailWord_425785).sum := by decide
  have hdescent : baseEnd_425785 < baseStart_425785 := by decide
  rcases family_descends (prefixWord ++ tailWord_425785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425789 : List Nat := [1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_425789 : Nat := 118140960795 + 425789 * 2 ^ 59
def prefixEnd_425789 : Nat := 4983230072969 + 3 ^ 40 * 425789 * 2
def baseEnd_425789 : Nat := 129561134457682863572941

theorem tailTrace_425789 : CollatzResearch.WordTrace tailWord_425789 prefixEnd_425789 129561134457682863572941 := by
  unfold tailWord_425789
  simp only [CollatzResearch.WordTrace]
  refine ⟨15529800654446646816856421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10353200436297764544570947 15529800654446646816856421)
  ·
    refine ⟨2911837622708746278160579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15529800654446646816856421 2911837622708746278160579)
    ·
      refine ⟨4367756434063119417240869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2911837622708746278160579 4367756434063119417240869)
      ·
        refine ⟨818954331386834890732663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4367756434063119417240869 818954331386834890732663)
        ·
          refine ⟨1228431497080252336098995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818954331386834890732663 1228431497080252336098995)
          ·
            refine ⟨1842647245620378504148493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228431497080252336098995 1842647245620378504148493)
            ·
              refine ⟨690992717107641939055685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1842647245620378504148493 690992717107641939055685)
              ·
                refine ⟨129561134457682863572941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690992717107641939055685 129561134457682863572941)
                ·
                  rfl

theorem cell19_425789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_425789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425789 prefixEnd_425789 := by exact prefixLift 425789
  have htrace : WordTrace (prefixWord ++ tailWord_425789) baseStart_425789 baseEnd_425789 := by
    simpa [prefixWord, tailWord_425789, baseEnd_425789] using wordTrace_append hprefix tailTrace_425789
  have hstable : (prefixWord ++ tailWord_425789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425789).length < 2 ^ (prefixWord ++ tailWord_425789).sum := by decide
  have hdescent : baseEnd_425789 < baseStart_425789 := by decide
  rcases family_descends (prefixWord ++ tailWord_425789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425863 : List Nat := [1, 1, 4, 2, 4, 2, 2, 3]
def baseStart_425863 : Nat := 118140960795 + 425863 * 2 ^ 59
def prefixEnd_425863 : Nat := 4983230072969 + 3 ^ 40 * 425863 * 2
def baseEnd_425863 : Nat := 129583651535272617928295

theorem tailTrace_425863 : CollatzResearch.WordTrace tailWord_425863 prefixEnd_425863 129583651535272617928295 := by
  unfold tailWord_425863
  simp only [CollatzResearch.WordTrace]
  refine ⟨15532499656178557455050243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10354999770785704970033495 15532499656178557455050243)
  ·
    refine ⟨23298749484267836182575365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15532499656178557455050243 23298749484267836182575365)
    ·
      refine ⟨4368515528300219284232881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23298749484267836182575365 4368515528300219284232881)
      ·
        refine ⟨3276386646225164463174661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4368515528300219284232881 3276386646225164463174661)
        ·
          refine ⟨614322496167218336845249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3276386646225164463174661 614322496167218336845249)
          ·
            refine ⟨460741872125413752633937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614322496167218336845249 460741872125413752633937)
            ·
              refine ⟨345556404094060314475453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460741872125413752633937 345556404094060314475453)
              ·
                refine ⟨129583651535272617928295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345556404094060314475453 129583651535272617928295)
                ·
                  rfl

theorem cell19_425863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 3].length) (baseStart_425863 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425863 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425863 prefixEnd_425863 := by exact prefixLift 425863
  have htrace : WordTrace (prefixWord ++ tailWord_425863) baseStart_425863 baseEnd_425863 := by
    simpa [prefixWord, tailWord_425863, baseEnd_425863] using wordTrace_append hprefix tailTrace_425863
  have hstable : (prefixWord ++ tailWord_425863).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425863).length < 2 ^ (prefixWord ++ tailWord_425863).sum := by decide
  have hdescent : baseEnd_425863 < baseStart_425863 := by decide
  rcases family_descends (prefixWord ++ tailWord_425863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425878 : List Nat := [5, 3, 1, 1, 3, 1, 5]
def baseStart_425878 : Nat := 118140960795 + 425878 * 2 ^ 59
def prefixEnd_425878 : Nat := 4983230072969 + 3 ^ 40 * 425878 * 2
def baseEnd_425878 : Nat := 43196071935919009198307

theorem tailTrace_425878 : CollatzResearch.WordTrace tailWord_425878 prefixEnd_425878 43196071935919009198307 := by
  unfold tailWord_425878
  simp only [CollatzResearch.WordTrace]
  refine ⟨970815421945263438552893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10355364500749476677897525 970815421945263438552893)
  ·
    refine ⟨364055783229473789457335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 970815421945263438552893 364055783229473789457335)
    ·
      refine ⟨546083674844210684186003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364055783229473789457335 546083674844210684186003)
      ·
        refine ⟨819125512266316026279005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546083674844210684186003 819125512266316026279005)
        ·
          refine ⟨307172067099868509854627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 819125512266316026279005 307172067099868509854627)
          ·
            refine ⟨460758100649802764781941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307172067099868509854627 460758100649802764781941)
            ·
              refine ⟨43196071935919009198307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 460758100649802764781941 43196071935919009198307)
              ·
                rfl

theorem cell19_425878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 5].length) (baseStart_425878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425878 prefixEnd_425878 := by exact prefixLift 425878
  have htrace : WordTrace (prefixWord ++ tailWord_425878) baseStart_425878 baseEnd_425878 := by
    simpa [prefixWord, tailWord_425878, baseEnd_425878] using wordTrace_append hprefix tailTrace_425878
  have hstable : (prefixWord ++ tailWord_425878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425878).length < 2 ^ (prefixWord ++ tailWord_425878).sum := by decide
  have hdescent : baseEnd_425878 < baseStart_425878 := by decide
  rcases family_descends (prefixWord ++ tailWord_425878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425884 : List Nat := [2, 2, 3, 3, 1, 3, 5]
def baseStart_425884 : Nat := 118140960795 + 425884 * 2 ^ 59
def prefixEnd_425884 : Nat := 4983230072969 + 3 ^ 40 * 425884 * 2
def baseEnd_425884 : Nat := 43196680505583597153857

theorem tailTrace_425884 : CollatzResearch.WordTrace tailWord_425884 prefixEnd_425884 43196680505583597153857 := by
  unfold tailWord_425884
  simp only [CollatzResearch.WordTrace]
  refine ⟨7766632794551239020782353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10355510392734985361043137 7766632794551239020782353)
  ·
    refine ⟨5824974595913429265586765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7766632794551239020782353 5824974595913429265586765)
    ·
      refine ⟨2184365473467535974595037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5824974595913429265586765 2184365473467535974595037)
      ·
        refine ⟨819137052550325990473139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2184365473467535974595037 819137052550325990473139)
        ·
          refine ⟨1228705578825488985709709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819137052550325990473139 1228705578825488985709709)
          ·
            refine ⟨460764592059558369641141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1228705578825488985709709 460764592059558369641141)
            ·
              refine ⟨43196680505583597153857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 460764592059558369641141 43196680505583597153857)
              ·
                rfl

theorem cell19_425884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_425884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425884 prefixEnd_425884 := by exact prefixLift 425884
  have htrace : WordTrace (prefixWord ++ tailWord_425884) baseStart_425884 baseEnd_425884 := by
    simpa [prefixWord, tailWord_425884, baseEnd_425884] using wordTrace_append hprefix tailTrace_425884
  have hstable : (prefixWord ++ tailWord_425884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425884).length < 2 ^ (prefixWord ++ tailWord_425884).sum := by decide
  have hdescent : baseEnd_425884 < baseStart_425884 := by decide
  rcases family_descends (prefixWord ++ tailWord_425884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425905 : List Nat := [1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_425905 : Nat := 118140960795 + 425905 * 2 ^ 59
def prefixEnd_425905 : Nat := 4983230072969 + 3 ^ 40 * 425905 * 2
def baseEnd_425905 : Nat := 129596431498228964994847

theorem tailTrace_425905 : CollatzResearch.WordTrace tailWord_425905 prefixEnd_425905 129596431498228964994847 := by
  unfold tailWord_425905
  simp only [CollatzResearch.WordTrace]
  refine ⟨15534031522026398628079169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10356021014684265752052779 15534031522026398628079169)
  ·
    refine ⟨11650523641519798971059377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15534031522026398628079169 11650523641519798971059377)
    ·
      refine ⟨8737892731139849228294533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11650523641519798971059377 8737892731139849228294533)
      ·
        refine ⟨1638354887088721730305225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8737892731139849228294533 1638354887088721730305225)
        ·
          refine ⟨1228766165316541297728919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1638354887088721730305225 1228766165316541297728919)
          ·
            refine ⟨1843149247974811946593379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228766165316541297728919 1843149247974811946593379)
            ·
              refine ⟨2764723871962217919890069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843149247974811946593379 2764723871962217919890069)
              ·
                refine ⟨129596431498228964994847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2764723871962217919890069 129596431498228964994847)
                ·
                  rfl

theorem cell19_425905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_425905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425905 prefixEnd_425905 := by exact prefixLift 425905
  have htrace : WordTrace (prefixWord ++ tailWord_425905) baseStart_425905 baseEnd_425905 := by
    simpa [prefixWord, tailWord_425905, baseEnd_425905] using wordTrace_append hprefix tailTrace_425905
  have hstable : (prefixWord ++ tailWord_425905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425905).length < 2 ^ (prefixWord ++ tailWord_425905).sum := by decide
  have hdescent : baseEnd_425905 < baseStart_425905 := by decide
  rcases family_descends (prefixWord ++ tailWord_425905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425945 : List Nat := [1, 2, 1, 2, 13]
def baseStart_425945 : Nat := 118140960795 + 425945 * 2 ^ 59
def prefixEnd_425945 : Nat := 4983230072969 + 3 ^ 40 * 425945 * 2
def baseEnd_425945 : Nat := 4800318625611878670587

theorem tailTrace_425945 : CollatzResearch.WordTrace tailWord_425945 prefixEnd_425945 4800318625611878670587 := by
  unfold tailWord_425945
  simp only [CollatzResearch.WordTrace]
  refine ⟨15535490441881485459535289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10356993627920990306356859 15535490441881485459535289)
  ·
    refine ⟨11651617831411114094651467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15535490441881485459535289 11651617831411114094651467)
    ·
      refine ⟨17477426747116671141977201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11651617831411114094651467 17477426747116671141977201)
      ·
        refine ⟨13108070060337503356482901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17477426747116671141977201 13108070060337503356482901)
        ·
          refine ⟨4800318625611878670587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13108070060337503356482901 4800318625611878670587)
          ·
            rfl

theorem cell19_425945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 13].length) (baseStart_425945 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425945 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425945 prefixEnd_425945 := by exact prefixLift 425945
  have htrace : WordTrace (prefixWord ++ tailWord_425945) baseStart_425945 baseEnd_425945 := by
    simpa [prefixWord, tailWord_425945, baseEnd_425945] using wordTrace_append hprefix tailTrace_425945
  have hstable : (prefixWord ++ tailWord_425945).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425945).length < 2 ^ (prefixWord ++ tailWord_425945).sum := by decide
  have hdescent : baseEnd_425945 < baseStart_425945 := by decide
  rcases family_descends (prefixWord ++ tailWord_425945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425983 : List Nat := [1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_425983 : Nat := 118140960795 + 425983 * 2 ^ 59
def prefixEnd_425983 : Nat := 4983230072969 + 3 ^ 40 * 425983 * 2
def baseEnd_425983 : Nat := 129620165715147895261301

theorem tailTrace_425983 : CollatzResearch.WordTrace tailWord_425983 prefixEnd_425983 129620165715147895261301 := by
  unfold tailWord_425983
  simp only [CollatzResearch.WordTrace]
  refine ⟨15536876415743817949418603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10357917610495878632945735 15536876415743817949418603)
  ·
    refine ⟨23305314623615726924127905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15536876415743817949418603 23305314623615726924127905)
    ·
      refine ⟨17478985967711795193095929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23305314623615726924127905 17478985967711795193095929)
      ·
        refine ⟨13109239475783846394821947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17478985967711795193095929 13109239475783846394821947)
        ·
          refine ⟨19663859213675769592232921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13109239475783846394821947 19663859213675769592232921)
          ·
            refine ⟨14747894410256827194174691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19663859213675769592232921 14747894410256827194174691)
            ·
              refine ⟨22121841615385240791262037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14747894410256827194174691 22121841615385240791262037)
              ·
                refine ⟨129620165715147895261301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22121841615385240791262037 129620165715147895261301)
                ·
                  rfl

theorem cell19_425983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_425983 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_425983 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_425983 prefixEnd_425983 := by exact prefixLift 425983
  have htrace : WordTrace (prefixWord ++ tailWord_425983) baseStart_425983 baseEnd_425983 := by
    simpa [prefixWord, tailWord_425983, baseEnd_425983] using wordTrace_append hprefix tailTrace_425983
  have hstable : (prefixWord ++ tailWord_425983).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425983).length < 2 ^ (prefixWord ++ tailWord_425983).sum := by decide
  have hdescent : baseEnd_425983 < baseStart_425983 := by decide
  rcases family_descends (prefixWord ++ tailWord_425983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426076 : List Nat := [2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_426076 : Nat := 118140960795 + 426076 * 2 ^ 59
def prefixEnd_426076 : Nat := 4983230072969 + 3 ^ 40 * 426076 * 2
def baseEnd_426076 : Nat := 129648464204551235194381

theorem tailTrace_426076 : CollatzResearch.WordTrace tailWord_426076 prefixEnd_426076 129648464204551235194381 := by
  unfold tailWord_426076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7770134202203447416277041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10360178936271263221702721 7770134202203447416277041)
  ·
    refine ⟨5827600651652585562207781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7770134202203447416277041 5827600651652585562207781)
    ·
      refine ⟨1092675122184859792913959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5827600651652585562207781 1092675122184859792913959)
      ·
        refine ⟨1639012683277289689370939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092675122184859792913959 1639012683277289689370939)
        ·
          refine ⟨2458519024915934534056409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639012683277289689370939 2458519024915934534056409)
          ·
            refine ⟨1843889268686950900542307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2458519024915934534056409 1843889268686950900542307)
            ·
              refine ⟨2765833903030426350813461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843889268686950900542307 2765833903030426350813461)
              ·
                refine ⟨129648464204551235194381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2765833903030426350813461 129648464204551235194381)
                ·
                  rfl

theorem cell19_426076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_426076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426076 prefixEnd_426076 := by exact prefixLift 426076
  have htrace : WordTrace (prefixWord ++ tailWord_426076) baseStart_426076 baseEnd_426076 := by
    simpa [prefixWord, tailWord_426076, baseEnd_426076] using wordTrace_append hprefix tailTrace_426076
  have hstable : (prefixWord ++ tailWord_426076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426076).length < 2 ^ (prefixWord ++ tailWord_426076).sum := by decide
  have hdescent : baseEnd_426076 < baseStart_426076 := by decide
  rcases family_descends (prefixWord ++ tailWord_426076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426097 : List Nat := [1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_426097 : Nat := 118140960795 + 426097 * 2 ^ 59
def prefixEnd_426097 : Nat := 4983230072969 + 3 ^ 40 * 426097 * 2
def baseEnd_426097 : Nat := 129654854186029408727657

theorem tailTrace_426097 : CollatzResearch.WordTrace tailWord_426097 prefixEnd_426097 129654854186029408727657 := by
  unfold tailWord_426097
  simp only [CollatzResearch.WordTrace]
  refine ⟨15541034337330815419068545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10360689558220543612712363 15541034337330815419068545)
  ·
    refine ⟨11655775752998111564301409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15541034337330815419068545 11655775752998111564301409)
    ·
      refine ⟨8741831814748583673226057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11655775752998111564301409 8741831814748583673226057)
      ·
        refine ⟨6556373861061437754919543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8741831814748583673226057 6556373861061437754919543)
        ·
          refine ⟨9834560791592156632379315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6556373861061437754919543 9834560791592156632379315)
          ·
            refine ⟨14751841187388234948568973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9834560791592156632379315 14751841187388234948568973)
            ·
              refine ⟨5531940445270588105713365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14751841187388234948568973 5531940445270588105713365)
              ·
                refine ⟨129654854186029408727657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5531940445270588105713365 129654854186029408727657)
                ·
                  rfl

theorem cell19_426097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_426097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426097 prefixEnd_426097 := by exact prefixLift 426097
  have htrace : WordTrace (prefixWord ++ tailWord_426097) baseStart_426097 baseEnd_426097 := by
    simpa [prefixWord, tailWord_426097, baseEnd_426097] using wordTrace_append hprefix tailTrace_426097
  have hstable : (prefixWord ++ tailWord_426097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426097).length < 2 ^ (prefixWord ++ tailWord_426097).sum := by decide
  have hdescent : baseEnd_426097 < baseStart_426097 := by decide
  rcases family_descends (prefixWord ++ tailWord_426097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426205 : List Nat := [1, 4, 3, 2, 1, 3, 2, 3]
def baseStart_426205 : Nat := 118140960795 + 426205 * 2 ^ 59
def prefixEnd_426205 : Nat := 4983230072969 + 3 ^ 40 * 426205 * 2
def baseEnd_426205 : Nat := 129687716947917158327363

theorem tailTrace_426205 : CollatzResearch.WordTrace tailWord_426205 prefixEnd_426205 129687716947917158327363 := by
  unfold tailWord_426205
  simp only [CollatzResearch.WordTrace]
  refine ⟨15544973420939549864000069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10363315613959699909333379 15544973420939549864000069)
  ·
    refine ⟨2914682516426165599500013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15544973420939549864000069 2914682516426165599500013)
    ·
      refine ⟨1093005943659812099812505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2914682516426165599500013 1093005943659812099812505)
      ·
        refine ⟨819754457744859074859379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1093005943659812099812505 819754457744859074859379)
        ·
          refine ⟨1229631686617288612289069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819754457744859074859379 1229631686617288612289069)
          ·
            refine ⟨461111882481483229608401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1229631686617288612289069 461111882481483229608401)
            ·
              refine ⟨345833911861112422206301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461111882481483229608401 345833911861112422206301)
              ·
                refine ⟨129687716947917158327363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345833911861112422206301 129687716947917158327363)
                ·
                  rfl

theorem cell19_426205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 3].length) (baseStart_426205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426205 prefixEnd_426205 := by exact prefixLift 426205
  have htrace : WordTrace (prefixWord ++ tailWord_426205) baseStart_426205 baseEnd_426205 := by
    simpa [prefixWord, tailWord_426205, baseEnd_426205] using wordTrace_append hprefix tailTrace_426205
  have hstable : (prefixWord ++ tailWord_426205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426205).length < 2 ^ (prefixWord ++ tailWord_426205).sum := by decide
  have hdescent : baseEnd_426205 < baseStart_426205 := by decide
  rcases family_descends (prefixWord ++ tailWord_426205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426249 : List Nat := [1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_426249 : Nat := 118140960795 + 426249 * 2 ^ 59
def prefixEnd_426249 : Nat := 4983230072969 + 3 ^ 40 * 426249 * 2
def baseEnd_426249 : Nat := 129701105480538093349465

theorem tailTrace_426249 : CollatzResearch.WordTrace tailWord_426249 prefixEnd_426249 129701105480538093349465 := by
  unfold tailWord_426249
  simp only [CollatzResearch.WordTrace]
  refine ⟨15546578232780145378601801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10364385488520096919067867 15546578232780145378601801)
  ·
    refine ⟨11659933674585109033951351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15546578232780145378601801 11659933674585109033951351)
    ·
      refine ⟨17489900511877663550927027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11659933674585109033951351 17489900511877663550927027)
      ·
        refine ⟨26234850767816495326390541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17489900511877663550927027 26234850767816495326390541)
        ·
          refine ⟨9838069037931185747396453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26234850767816495326390541 9838069037931185747396453)
          ·
            refine ⟨1844637944612097327636835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9838069037931185747396453 1844637944612097327636835)
            ·
              refine ⟨2766956916918145991455253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844637944612097327636835 2766956916918145991455253)
              ·
                refine ⟨129701105480538093349465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2766956916918145991455253 129701105480538093349465)
                ·
                  rfl

theorem cell19_426249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_426249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426249 prefixEnd_426249 := by exact prefixLift 426249
  have htrace : WordTrace (prefixWord ++ tailWord_426249) baseStart_426249 baseEnd_426249 := by
    simpa [prefixWord, tailWord_426249, baseEnd_426249] using wordTrace_append hprefix tailTrace_426249
  have hstable : (prefixWord ++ tailWord_426249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426249).length < 2 ^ (prefixWord ++ tailWord_426249).sum := by decide
  have hdescent : baseEnd_426249 < baseStart_426249 := by decide
  rcases family_descends (prefixWord ++ tailWord_426249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426285 : List Nat := [1, 5, 3, 1, 9]
def baseStart_426285 : Nat := 118140960795 + 426285 * 2 ^ 59
def prefixEnd_426285 : Nat := 4983230072969 + 3 ^ 40 * 426285 * 2
def baseEnd_426285 : Nat := 4804150360537062094421

theorem tailTrace_426285 : CollatzResearch.WordTrace tailWord_426285 prefixEnd_426285 4804150360537062094421 := by
  unfold tailWord_426285
  simp only [CollatzResearch.WordTrace]
  refine ⟨15547891260649723526912309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10365260840433149017941539 15547891260649723526912309)
  ·
    refine ⟨1457614805685911580648029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15547891260649723526912309 1457614805685911580648029)
    ·
      refine ⟨546605552132216842743011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1457614805685911580648029 546605552132216842743011)
      ·
        refine ⟨819908328198325264114517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546605552132216842743011 819908328198325264114517)
        ·
          refine ⟨4804150360537062094421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 819908328198325264114517 4804150360537062094421)
          ·
            rfl

theorem cell19_426285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 9].length) (baseStart_426285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426285 prefixEnd_426285 := by exact prefixLift 426285
  have htrace : WordTrace (prefixWord ++ tailWord_426285) baseStart_426285 baseEnd_426285 := by
    simpa [prefixWord, tailWord_426285, baseEnd_426285] using wordTrace_append hprefix tailTrace_426285
  have hstable : (prefixWord ++ tailWord_426285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426285).length < 2 ^ (prefixWord ++ tailWord_426285).sum := by decide
  have hdescent : baseEnd_426285 < baseStart_426285 := by decide
  rcases family_descends (prefixWord ++ tailWord_426285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426302 : List Nat := [4, 2, 1, 2, 1, 4, 1, 4]
def baseStart_426302 : Nat := 118140960795 + 426302 * 2 ^ 59
def prefixEnd_426302 : Nat := 4983230072969 + 3 ^ 40 * 426302 * 2
def baseEnd_426302 : Nat := 129717232576649674171543

theorem tailTrace_426302 : CollatzResearch.WordTrace tailWord_426302 prefixEnd_426302 129717232576649674171543 := by
  unfold tailWord_426302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943563912698516928785145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10365674201058756953520773 1943563912698516928785145)
  ·
    refine ⟨1457672934523887696588859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1943563912698516928785145 1457672934523887696588859)
    ·
      refine ⟨2186509401785831544883289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1457672934523887696588859 2186509401785831544883289)
      ·
        refine ⟨1639882051339373658662467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2186509401785831544883289 1639882051339373658662467)
        ·
          refine ⟨2459823077009060487993701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639882051339373658662467 2459823077009060487993701)
          ·
            refine ⟨461216826939198841498819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2459823077009060487993701 461216826939198841498819)
            ·
              refine ⟨691825240408798262248229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461216826939198841498819 691825240408798262248229)
              ·
                refine ⟨129717232576649674171543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 691825240408798262248229 129717232576649674171543)
                ·
                  rfl

theorem cell19_426302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_426302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426302 prefixEnd_426302 := by exact prefixLift 426302
  have htrace : WordTrace (prefixWord ++ tailWord_426302) baseStart_426302 baseEnd_426302 := by
    simpa [prefixWord, tailWord_426302, baseEnd_426302] using wordTrace_append hprefix tailTrace_426302
  have hstable : (prefixWord ++ tailWord_426302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426302).length < 2 ^ (prefixWord ++ tailWord_426302).sum := by decide
  have hdescent : baseEnd_426302 < baseStart_426302 := by decide
  rcases family_descends (prefixWord ++ tailWord_426302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426378 : List Nat := [3, 1, 2, 5, 1, 1, 1, 5]
def baseStart_426378 : Nat := 118140960795 + 426378 * 2 ^ 59
def prefixEnd_426378 : Nat := 4983230072969 + 3 ^ 40 * 426378 * 2
def baseEnd_426378 : Nat := 129740358223904016482447

theorem tailTrace_426378 : CollatzResearch.WordTrace tailWord_426378 prefixEnd_426378 129740358223904016482447 := by
  unfold tailWord_426378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887820812328200102511947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10367522166208533606698525 3887820812328200102511947)
  ·
    refine ⟨5831731218492300153767921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3887820812328200102511947 5831731218492300153767921)
    ·
      refine ⟨4373798413869225115325941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5831731218492300153767921 4373798413869225115325941)
      ·
        refine ⟨410043601300239854561807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4373798413869225115325941 410043601300239854561807)
        ·
          refine ⟨615065401950359781842711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410043601300239854561807 615065401950359781842711)
          ·
            refine ⟨922598102925539672764067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615065401950359781842711 922598102925539672764067)
            ·
              refine ⟨1383897154388309509146101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922598102925539672764067 1383897154388309509146101)
              ·
                refine ⟨129740358223904016482447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1383897154388309509146101 129740358223904016482447)
                ·
                  rfl

theorem cell19_426378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_426378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426378 prefixEnd_426378 := by exact prefixLift 426378
  have htrace : WordTrace (prefixWord ++ tailWord_426378) baseStart_426378 baseEnd_426378 := by
    simpa [prefixWord, tailWord_426378, baseEnd_426378] using wordTrace_append hprefix tailTrace_426378
  have hstable : (prefixWord ++ tailWord_426378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426378).length < 2 ^ (prefixWord ++ tailWord_426378).sum := by decide
  have hdescent : baseEnd_426378 < baseStart_426378 := by decide
  rcases family_descends (prefixWord ++ tailWord_426378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426380 : List Nat := [2, 2, 1, 2, 1, 4, 4, 3]
def baseStart_426380 : Nat := 118140960795 + 426380 * 2 ^ 59
def prefixEnd_426380 : Nat := 4983230072969 + 3 ^ 40 * 426380 * 2
def baseEnd_426380 : Nat := 129740966793568604437997

theorem tailTrace_426380 : CollatzResearch.WordTrace tailWord_426380 prefixEnd_426380 129740966793568604437997 := by
  unfold tailWord_426380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7775678097652777375810297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10367570796870369834413729 7775678097652777375810297)
  ·
    refine ⟨5831758573239583031857723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7775678097652777375810297 5831758573239583031857723)
    ·
      refine ⟨8747637859859374547786585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5831758573239583031857723 8747637859859374547786585)
      ·
        refine ⟨6560728394894530910839939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8747637859859374547786585 6560728394894530910839939)
        ·
          refine ⟨9841092592341796366259909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6560728394894530910839939 9841092592341796366259909)
          ·
            refine ⟨1845204861064086818673733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9841092592341796366259909 1845204861064086818673733)
            ·
              refine ⟨345975911449516278501325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1845204861064086818673733 345975911449516278501325)
              ·
                refine ⟨129740966793568604437997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345975911449516278501325 129740966793568604437997)
                ·
                  rfl

theorem cell19_426380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_426380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426380 prefixEnd_426380 := by exact prefixLift 426380
  have htrace : WordTrace (prefixWord ++ tailWord_426380) baseStart_426380 baseEnd_426380 := by
    simpa [prefixWord, tailWord_426380, baseEnd_426380] using wordTrace_append hprefix tailTrace_426380
  have hstable : (prefixWord ++ tailWord_426380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426380).length < 2 ^ (prefixWord ++ tailWord_426380).sum := by decide
  have hdescent : baseEnd_426380 < baseStart_426380 := by decide
  rcases family_descends (prefixWord ++ tailWord_426380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426397 : List Nat := [1, 4, 2, 1, 5, 1, 5]
def baseStart_426397 : Nat := 118140960795 + 426397 * 2 ^ 59
def prefixEnd_426397 : Nat := 4983230072969 + 3 ^ 40 * 426397 * 2
def baseEnd_426397 : Nat := 43248713211905867353391

theorem tailTrace_426397 : CollatzResearch.WordTrace tailWord_426397 prefixEnd_426397 43248713211905867353391 := by
  unfold tailWord_426397
  simp only [CollatzResearch.WordTrace]
  refine ⟨15551976236243966654989445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10367984157495977769992963 15551976236243966654989445)
  ·
    refine ⟨2915995544295743747810521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15551976236243966654989445 2915995544295743747810521)
    ·
      refine ⟨2186996658221807810857891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2915995544295743747810521 2186996658221807810857891)
      ·
        refine ⟨3280494987332711716286837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186996658221807810857891 3280494987332711716286837)
        ·
          refine ⟨307546405062441723401891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3280494987332711716286837 307546405062441723401891)
          ·
            refine ⟨461319607593662585102837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307546405062441723401891 461319607593662585102837)
            ·
              refine ⟨43248713211905867353391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 461319607593662585102837 43248713211905867353391)
              ·
                rfl

theorem cell19_426397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 5].length) (baseStart_426397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426397 prefixEnd_426397 := by exact prefixLift 426397
  have htrace : WordTrace (prefixWord ++ tailWord_426397) baseStart_426397 baseEnd_426397 := by
    simpa [prefixWord, tailWord_426397, baseEnd_426397] using wordTrace_append hprefix tailTrace_426397
  have hstable : (prefixWord ++ tailWord_426397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426397).length < 2 ^ (prefixWord ++ tailWord_426397).sum := by decide
  have hdescent : baseEnd_426397 < baseStart_426397 := by decide
  rcases family_descends (prefixWord ++ tailWord_426397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426439 : List Nat := [1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_426439 : Nat := 118140960795 + 426439 * 2 ^ 59
def prefixEnd_426439 : Nat := 4983230072969 + 3 ^ 40 * 426439 * 2
def baseEnd_426439 : Nat := 129758919598673949126725

theorem tailTrace_426439 : CollatzResearch.WordTrace tailWord_426439 prefixEnd_426439 129758919598673949126725 := by
  unfold tailWord_426439
  simp only [CollatzResearch.WordTrace]
  refine ⟨15553508102091807828018371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10369005401394538552012247 15553508102091807828018371)
  ·
    refine ⟨23330262153137711742027557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15553508102091807828018371 23330262153137711742027557)
    ·
      refine ⟨4374424153713320951630167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23330262153137711742027557 4374424153713320951630167)
      ·
        refine ⟨6561636230569981427445251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4374424153713320951630167 6561636230569981427445251)
        ·
          refine ⟨9842454345854972141167877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6561636230569981427445251 9842454345854972141167877)
          ·
            refine ⟨1845460189847807276468977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9842454345854972141167877 1845460189847807276468977)
            ·
              refine ⟨1384095142385855457351733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1845460189847807276468977 1384095142385855457351733)
              ·
                refine ⟨129758919598673949126725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1384095142385855457351733 129758919598673949126725)
                ·
                  rfl

theorem cell19_426439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_426439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426439 prefixEnd_426439 := by exact prefixLift 426439
  have htrace : WordTrace (prefixWord ++ tailWord_426439) baseStart_426439 baseEnd_426439 := by
    simpa [prefixWord, tailWord_426439, baseEnd_426439] using wordTrace_append hprefix tailTrace_426439
  have hstable : (prefixWord ++ tailWord_426439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426439).length < 2 ^ (prefixWord ++ tailWord_426439).sum := by decide
  have hdescent : baseEnd_426439 < baseStart_426439 := by decide
  rcases family_descends (prefixWord ++ tailWord_426439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426553 : List Nat := [1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_426553 : Nat := 118140960795 + 426553 * 2 ^ 59
def prefixEnd_426553 : Nat := 4983230072969 + 3 ^ 40 * 426553 * 2
def baseEnd_426553 : Nat := 129793608069555462593081

theorem tailTrace_426553 : CollatzResearch.WordTrace tailWord_426553 prefixEnd_426553 129793608069555462593081 := by
  unfold tailWord_426553
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557666023678805297668313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10371777349119203531778875 15557666023678805297668313)
  ·
    refine ⟨11668249517759103973251235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15557666023678805297668313 11668249517759103973251235)
    ·
      refine ⟨17502374276638655959876853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11668249517759103973251235 17502374276638655959876853)
      ·
        refine ⟨1640847588434873996238455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17502374276638655959876853 1640847588434873996238455)
        ·
          refine ⟨2461271382652310994357683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1640847588434873996238455 2461271382652310994357683)
          ·
            refine ⟨3691907073978466491536525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461271382652310994357683 3691907073978466491536525)
            ·
              refine ⟨1384465152741924934326197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3691907073978466491536525 1384465152741924934326197)
              ·
                refine ⟨129793608069555462593081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1384465152741924934326197 129793608069555462593081)
                ·
                  rfl

theorem cell19_426553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_426553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426553 prefixEnd_426553 := by exact prefixLift 426553
  have htrace : WordTrace (prefixWord ++ tailWord_426553) baseStart_426553 baseEnd_426553 := by
    simpa [prefixWord, tailWord_426553, baseEnd_426553] using wordTrace_append hprefix tailTrace_426553
  have hstable : (prefixWord ++ tailWord_426553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426553).length < 2 ^ (prefixWord ++ tailWord_426553).sum := by decide
  have hdescent : baseEnd_426553 < baseStart_426553 := by decide
  rcases family_descends (prefixWord ++ tailWord_426553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426564 : List Nat := [2, 3, 5, 1, 2, 1, 5]
def baseStart_426564 : Nat := 118140960795 + 426564 * 2 ^ 59
def prefixEnd_426564 : Nat := 4983230072969 + 3 ^ 40 * 426564 * 2
def baseEnd_426564 : Nat := 43265651734236898782869

theorem tailTrace_426564 : CollatzResearch.WordTrace tailWord_426564 prefixEnd_426564 43265651734236898782869 := by
  unfold tailWord_426564
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779033613319477088159373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10372044817759302784212497 7779033613319477088159373)
  ·
    refine ⟨2917137604994803908059765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7779033613319477088159373 2917137604994803908059765)
    ·
      refine ⟨273481650468262866380603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2917137604994803908059765 273481650468262866380603)
      ·
        refine ⟨410222475702394299570905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273481650468262866380603 410222475702394299570905)
        ·
          refine ⟨307666856776795724678179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410222475702394299570905 307666856776795724678179)
          ·
            refine ⟨461500285165193587017269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307666856776795724678179 461500285165193587017269)
            ·
              refine ⟨43265651734236898782869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 461500285165193587017269 43265651734236898782869)
              ·
                rfl

theorem cell19_426564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 5].length) (baseStart_426564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426564 prefixEnd_426564 := by exact prefixLift 426564
  have htrace : WordTrace (prefixWord ++ tailWord_426564) baseStart_426564 baseEnd_426564 := by
    simpa [prefixWord, tailWord_426564, baseEnd_426564] using wordTrace_append hprefix tailTrace_426564
  have hstable : (prefixWord ++ tailWord_426564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426564).length < 2 ^ (prefixWord ++ tailWord_426564).sum := by decide
  have hdescent : baseEnd_426564 < baseStart_426564 := by decide
  rcases family_descends (prefixWord ++ tailWord_426564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426644 : List Nat := [2, 4, 2, 2, 1, 3, 1, 4]
def baseStart_426644 : Nat := 118140960795 + 426644 * 2 ^ 59
def prefixEnd_426644 : Nat := 4983230072969 + 3 ^ 40 * 426644 * 2
def baseEnd_426644 : Nat := 129821297989294214570611

theorem tailTrace_426644 : CollatzResearch.WordTrace tailWord_426644 prefixEnd_426644 129821297989294214570611 := by
  unfold tailWord_426644
  simp only [CollatzResearch.WordTrace]
  refine ⟨7780492533174563919615493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10373990044232751892820657 7780492533174563919615493)
  ·
    refine ⟨1458842349970230734927905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7780492533174563919615493 1458842349970230734927905)
    ·
      refine ⟨1094131762477673051195929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1458842349970230734927905 1094131762477673051195929)
      ·
        refine ⟨820598821858254788396947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1094131762477673051195929 820598821858254788396947)
        ·
          refine ⟨1230898232787382182595421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820598821858254788396947 1230898232787382182595421)
          ·
            refine ⟨461586837295268318473283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1230898232787382182595421 461586837295268318473283)
            ·
              refine ⟨692380255942902477709925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461586837295268318473283 692380255942902477709925)
              ·
                refine ⟨129821297989294214570611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692380255942902477709925 129821297989294214570611)
                ·
                  rfl

theorem cell19_426644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_426644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426644 prefixEnd_426644 := by exact prefixLift 426644
  have htrace : WordTrace (prefixWord ++ tailWord_426644) baseStart_426644 baseEnd_426644 := by
    simpa [prefixWord, tailWord_426644, baseEnd_426644] using wordTrace_append hprefix tailTrace_426644
  have hstable : (prefixWord ++ tailWord_426644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426644).length < 2 ^ (prefixWord ++ tailWord_426644).sum := by decide
  have hdescent : baseEnd_426644 < baseStart_426644 := by decide
  rcases family_descends (prefixWord ++ tailWord_426644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426686 : List Nat := [4, 2, 1, 1, 2, 1, 8]
def baseStart_426686 : Nat := 118140960795 + 426686 * 2 ^ 59
def prefixEnd_426686 : Nat := 4983230072969 + 3 ^ 40 * 426686 * 2
def baseEnd_426686 : Nat := 43278025984083520545721

theorem tailTrace_426686 : CollatzResearch.WordTrace tailWord_426686 prefixEnd_426686 43278025984083520545721 := by
  unfold tailWord_426686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945314616524621126532489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10375011288131312674839941 1945314616524621126532489)
  ·
    refine ⟨1458985962393465844899367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1945314616524621126532489 1458985962393465844899367)
    ·
      refine ⟨2188478943590198767349051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1458985962393465844899367 2188478943590198767349051)
      ·
        refine ⟨3282718415385298151023577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188478943590198767349051 3282718415385298151023577)
        ·
          refine ⟨2462038811538973613267683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3282718415385298151023577 2462038811538973613267683)
          ·
            refine ⟨3693058217308460419901525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462038811538973613267683 3693058217308460419901525)
            ·
              refine ⟨43278025984083520545721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3693058217308460419901525 43278025984083520545721)
              ·
                rfl

theorem cell19_426686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_426686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426686 prefixEnd_426686 := by exact prefixLift 426686
  have htrace : WordTrace (prefixWord ++ tailWord_426686) baseStart_426686 baseEnd_426686 := by
    simpa [prefixWord, tailWord_426686, baseEnd_426686] using wordTrace_append hprefix tailTrace_426686
  have hstable : (prefixWord ++ tailWord_426686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426686).length < 2 ^ (prefixWord ++ tailWord_426686).sum := by decide
  have hdescent : baseEnd_426686 < baseStart_426686 := by decide
  rcases family_descends (prefixWord ++ tailWord_426686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426724 : List Nat := [2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_426724 : Nat := 118140960795 + 426724 * 2 ^ 59
def prefixEnd_426724 : Nat := 4983230072969 + 3 ^ 40 * 426724 * 2
def baseEnd_426724 : Nat := 129845640775877732792615

theorem tailTrace_426724 : CollatzResearch.WordTrace tailWord_426724 prefixEnd_426724 129845640775877732792615 := by
  unfold tailWord_426724
  simp only [CollatzResearch.WordTrace]
  refine ⟨7781951453029650751071613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10375935270706201001428817 7781951453029650751071613)
  ·
    refine ⟨2918231794886119031651855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7781951453029650751071613 2918231794886119031651855)
    ·
      refine ⟨4377347692329178547477783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918231794886119031651855 4377347692329178547477783)
      ·
        refine ⟨6566021538493767821216675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377347692329178547477783 6566021538493767821216675)
        ·
          refine ⟨9849032307740651731825013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6566021538493767821216675 9849032307740651731825013)
          ·
            refine ⟨923346778850686099858595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9849032307740651731825013 923346778850686099858595)
            ·
              refine ⟨1385020168276029149787893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923346778850686099858595 1385020168276029149787893)
              ·
                refine ⟨129845640775877732792615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1385020168276029149787893 129845640775877732792615)
                ·
                  rfl

theorem cell19_426724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_426724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426724 prefixEnd_426724 := by exact prefixLift 426724
  have htrace : WordTrace (prefixWord ++ tailWord_426724) baseStart_426724 baseEnd_426724 := by
    simpa [prefixWord, tailWord_426724, baseEnd_426724] using wordTrace_append hprefix tailTrace_426724
  have hstable : (prefixWord ++ tailWord_426724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426724).length < 2 ^ (prefixWord ++ tailWord_426724).sum := by decide
  have hdescent : baseEnd_426724 < baseStart_426724 := by decide
  rcases family_descends (prefixWord ++ tailWord_426724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426762 : List Nat := [3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_426762 : Nat := 118140960795 + 426762 * 2 ^ 59
def prefixEnd_426762 : Nat := 4983230072969 + 3 ^ 40 * 426762 * 2
def baseEnd_426762 : Nat := 129857203599504903948067

theorem tailTrace_426762 : CollatzResearch.WordTrace tailWord_426762 prefixEnd_426762 129857203599504903948067 := by
  unfold tailWord_426762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3891322219980408498006635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10376859253281089328017693 3891322219980408498006635)
  ·
    refine ⟨5836983329970612747009953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3891322219980408498006635 5836983329970612747009953)
    ·
      refine ⟨4377737497477959560257465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5836983329970612747009953 4377737497477959560257465)
      ·
        refine ⟨3283303123108469670193099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4377737497477959560257465 3283303123108469670193099)
        ·
          refine ⟨4924954684662704505289649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283303123108469670193099 4924954684662704505289649)
          ·
            refine ⟨3693716013497028378967237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4924954684662704505289649 3693716013497028378967237)
            ·
              refine ⟨692571752530692821056357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3693716013497028378967237 692571752530692821056357)
              ·
                refine ⟨129857203599504903948067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692571752530692821056357 129857203599504903948067)
                ·
                  rfl

theorem cell19_426762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_426762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426762 prefixEnd_426762 := by exact prefixLift 426762
  have htrace : WordTrace (prefixWord ++ tailWord_426762) baseStart_426762 baseEnd_426762 := by
    simpa [prefixWord, tailWord_426762, baseEnd_426762] using wordTrace_append hprefix tailTrace_426762
  have hstable : (prefixWord ++ tailWord_426762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426762).length < 2 ^ (prefixWord ++ tailWord_426762).sum := by decide
  have hdescent : baseEnd_426762 < baseStart_426762 := by decide
  rcases family_descends (prefixWord ++ tailWord_426762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426821 : List Nat := [1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_426821 : Nat := 118140960795 + 426821 * 2 ^ 59
def prefixEnd_426821 : Nat := 4983230072969 + 3 ^ 40 * 426821 * 2
def baseEnd_426821 : Nat := 129875156404610248636795

theorem tailTrace_426821 : CollatzResearch.WordTrace tailWord_426821 prefixEnd_426821 129875156404610248636795 := by
  unfold tailWord_426821
  simp only [CollatzResearch.WordTrace]
  refine ⟨15567440786707887068424317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10378293857805258045616211 15567440786707887068424317)
  ·
    refine ⟨5837790295015457650659119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15567440786707887068424317 5837790295015457650659119)
    ·
      refine ⟨8756685442523186475988679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5837790295015457650659119 8756685442523186475988679)
      ·
        refine ⟨13135028163784779713983019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8756685442523186475988679 13135028163784779713983019)
        ·
          refine ⟨19702542245677169570974529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13135028163784779713983019 19702542245677169570974529)
          ·
            refine ⟨14776906684257877178230897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19702542245677169570974529 14776906684257877178230897)
            ·
              refine ⟨11082680013193407883673173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14776906684257877178230897 11082680013193407883673173)
              ·
                refine ⟨129875156404610248636795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11082680013193407883673173 129875156404610248636795)
                ·
                  rfl

theorem cell19_426821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_426821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426821 prefixEnd_426821 := by exact prefixLift 426821
  have htrace : WordTrace (prefixWord ++ tailWord_426821) baseStart_426821 baseEnd_426821 := by
    simpa [prefixWord, tailWord_426821, baseEnd_426821] using wordTrace_append hprefix tailTrace_426821
  have hstable : (prefixWord ++ tailWord_426821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426821).length < 2 ^ (prefixWord ++ tailWord_426821).sum := by decide
  have hdescent : baseEnd_426821 < baseStart_426821 := by decide
  rcases family_descends (prefixWord ++ tailWord_426821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426840 : List Nat := [2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_426840 : Nat := 118140960795 + 426840 * 2 ^ 59
def prefixEnd_426840 : Nat := 4983230072969 + 3 ^ 40 * 426840 * 2
def baseEnd_426840 : Nat := 129880937816423834214521

theorem tailTrace_426840 : CollatzResearch.WordTrace tailWord_426840 prefixEnd_426840 129880937816423834214521 := by
  unfold tailWord_426840
  simp only [CollatzResearch.WordTrace]
  refine ⟨7784066886819526656682987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10378755849092702208910649 7784066886819526656682987)
  ·
    refine ⟨11676100330229289985024481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7784066886819526656682987 11676100330229289985024481)
    ·
      refine ⟨8757075247671967488768361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11676100330229289985024481 8757075247671967488768361)
      ·
        refine ⟨6567806435753975616576271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8757075247671967488768361 6567806435753975616576271)
        ·
          refine ⟨9851709653630963424864407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6567806435753975616576271 9851709653630963424864407)
          ·
            refine ⟨14777564480446445137296611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9851709653630963424864407 14777564480446445137296611)
            ·
              refine ⟨22166346720669667705944917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14777564480446445137296611 22166346720669667705944917)
              ·
                refine ⟨129880937816423834214521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22166346720669667705944917 129880937816423834214521)
                ·
                  rfl

theorem cell19_426840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_426840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426840 prefixEnd_426840 := by exact prefixLift 426840
  have htrace : WordTrace (prefixWord ++ tailWord_426840) baseStart_426840 baseEnd_426840 := by
    simpa [prefixWord, tailWord_426840, baseEnd_426840] using wordTrace_append hprefix tailTrace_426840
  have hstable : (prefixWord ++ tailWord_426840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426840).length < 2 ^ (prefixWord ++ tailWord_426840).sum := by decide
  have hdescent : baseEnd_426840 < baseStart_426840 := by decide
  rcases family_descends (prefixWord ++ tailWord_426840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426914 : List Nat := [3, 3, 1, 2, 2, 1, 7]
def baseStart_426914 : Nat := 118140960795 + 426914 * 2 ^ 59
def prefixEnd_426914 : Nat := 4983230072969 + 3 ^ 40 * 426914 * 2
def baseEnd_426914 : Nat := 43301151631337862856625

theorem tailTrace_426914 : CollatzResearch.WordTrace tailWord_426914 prefixEnd_426914 43301151631337862856625 := by
  unfold tailWord_426914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892708193842740987889949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10380555183580642634373197 3892708193842740987889949)
  ·
    refine ⟨1459765572691027870458731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3892708193842740987889949 1459765572691027870458731)
    ·
      refine ⟨2189648359036541805688097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459765572691027870458731 2189648359036541805688097)
      ·
        refine ⟨1642236269277406354266073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2189648359036541805688097 1642236269277406354266073)
        ·
          refine ⟨1231677201958054765699555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642236269277406354266073 1231677201958054765699555)
          ·
            refine ⟨1847515802937082148549333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231677201958054765699555 1847515802937082148549333)
            ·
              refine ⟨43301151631337862856625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1847515802937082148549333 43301151631337862856625)
              ·
                rfl

theorem cell19_426914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_426914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426914 prefixEnd_426914 := by exact prefixLift 426914
  have htrace : WordTrace (prefixWord ++ tailWord_426914) baseStart_426914 baseEnd_426914 := by
    simpa [prefixWord, tailWord_426914, baseEnd_426914] using wordTrace_append hprefix tailTrace_426914
  have hstable : (prefixWord ++ tailWord_426914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426914).length < 2 ^ (prefixWord ++ tailWord_426914).sum := by decide
  have hdescent : baseEnd_426914 < baseStart_426914 := by decide
  rcases family_descends (prefixWord ++ tailWord_426914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426933 : List Nat := [1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_426933 : Nat := 118140960795 + 426933 * 2 ^ 59
def prefixEnd_426933 : Nat := 4983230072969 + 3 ^ 40 * 426933 * 2
def baseEnd_426933 : Nat := 129909236305827174147601

theorem tailTrace_426933 : CollatzResearch.WordTrace tailWord_426933 prefixEnd_426933 129909236305827174147601 := by
  unfold tailWord_426933
  simp only [CollatzResearch.WordTrace]
  refine ⟨15571525762302130196501453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10381017174868086797667635 15571525762302130196501453)
  ·
    refine ⟨5839322160863298823688045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15571525762302130196501453 5839322160863298823688045)
    ·
      refine ⟨2189745810323737058883017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5839322160863298823688045 2189745810323737058883017)
      ·
        refine ⟨1642309357742802794162263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2189745810323737058883017 1642309357742802794162263)
        ·
          refine ⟨2463464036614204191243395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642309357742802794162263 2463464036614204191243395)
          ·
            refine ⟨3695196054921306286865093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463464036614204191243395 3695196054921306286865093)
            ·
              refine ⟨692849260297744928787205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3695196054921306286865093 692849260297744928787205)
              ·
                refine ⟨129909236305827174147601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692849260297744928787205 129909236305827174147601)
                ·
                  rfl

theorem cell19_426933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_426933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426933 prefixEnd_426933 := by exact prefixLift 426933
  have htrace : WordTrace (prefixWord ++ tailWord_426933) baseStart_426933 baseEnd_426933 := by
    simpa [prefixWord, tailWord_426933, baseEnd_426933] using wordTrace_append hprefix tailTrace_426933
  have hstable : (prefixWord ++ tailWord_426933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426933).length < 2 ^ (prefixWord ++ tailWord_426933).sum := by decide
  have hdescent : baseEnd_426933 < baseStart_426933 := by decide
  rcases family_descends (prefixWord ++ tailWord_426933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426935 : List Nat := [1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_426935 : Nat := 118140960795 + 426935 * 2 ^ 59
def prefixEnd_426935 : Nat := 4983230072969 + 3 ^ 40 * 426935 * 2
def baseEnd_426935 : Nat := 129909844875491762103151

theorem tailTrace_426935 : CollatzResearch.WordTrace tailWord_426935 prefixEnd_426935 129909844875491762103151 := by
  unfold tailWord_426935
  simp only [CollatzResearch.WordTrace]
  refine ⟨15571598708294884538074259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10381065805529923025382839 15571598708294884538074259)
  ·
    refine ⟨23357398062442326807111389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15571598708294884538074259 23357398062442326807111389)
    ·
      refine ⟨8759024273415872552666771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23357398062442326807111389 8759024273415872552666771)
      ·
        refine ⟨13138536410123808829000157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8759024273415872552666771 13138536410123808829000157)
        ·
          refine ⟨4926951153796428310875059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13138536410123808829000157 4926951153796428310875059)
          ·
            refine ⟨7390426730694642466312589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926951153796428310875059 7390426730694642466312589)
            ·
              refine ⟨2771410024010490924867221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7390426730694642466312589 2771410024010490924867221)
              ·
                refine ⟨129909844875491762103151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2771410024010490924867221 129909844875491762103151)
                ·
                  rfl

theorem cell19_426935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_426935 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_426935 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_426935 prefixEnd_426935 := by exact prefixLift 426935
  have htrace : WordTrace (prefixWord ++ tailWord_426935) baseStart_426935 baseEnd_426935 := by
    simpa [prefixWord, tailWord_426935, baseEnd_426935] using wordTrace_append hprefix tailTrace_426935
  have hstable : (prefixWord ++ tailWord_426935).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426935).length < 2 ^ (prefixWord ++ tailWord_426935).sum := by decide
  have hdescent : baseEnd_426935 < baseStart_426935 := by decide
  rcases family_descends (prefixWord ++ tailWord_426935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427062 : List Nat := [5, 1, 2, 1, 1, 4, 2, 3]
def baseStart_427062 : Nat := 118140960795 + 427062 * 2 ^ 59
def prefixEnd_427062 : Nat := 4983230072969 + 3 ^ 40 * 427062 * 2
def baseEnd_427062 : Nat := 129948489049193097280583

theorem tailTrace_427062 : CollatzResearch.WordTrace tailWord_427062 prefixEnd_427062 129948489049193097280583 := by
  unfold tailWord_427062
  simp only [CollatzResearch.WordTrace]
  refine ⟨973514423677174076746715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10384153852556523485298293 973514423677174076746715)
  ·
    refine ⟨1460271635515761115120073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 973514423677174076746715 1460271635515761115120073)
    ·
      refine ⟨1095203726636820836340055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1460271635515761115120073 1095203726636820836340055)
      ·
        refine ⟨1642805589955231254510083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095203726636820836340055 1642805589955231254510083)
        ·
          refine ⟨2464208384932846881765125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642805589955231254510083 2464208384932846881765125)
          ·
            refine ⟨462039072174908790330961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2464208384932846881765125 462039072174908790330961)
            ·
              refine ⟨346529304131181592748221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462039072174908790330961 346529304131181592748221)
              ·
                refine ⟨129948489049193097280583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346529304131181592748221 129948489049193097280583)
                ·
                  rfl

theorem cell19_427062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_427062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427062 prefixEnd_427062 := by exact prefixLift 427062
  have htrace : WordTrace (prefixWord ++ tailWord_427062) baseStart_427062 baseEnd_427062 := by
    simpa [prefixWord, tailWord_427062, baseEnd_427062] using wordTrace_append hprefix tailTrace_427062
  have hstable : (prefixWord ++ tailWord_427062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427062).length < 2 ^ (prefixWord ++ tailWord_427062).sum := by decide
  have hdescent : baseEnd_427062 < baseStart_427062 := by decide
  rcases family_descends (prefixWord ++ tailWord_427062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427064 : List Nat := [2, 1, 2, 1, 5, 3, 2, 3]
def baseStart_427064 : Nat := 118140960795 + 427064 * 2 ^ 59
def prefixEnd_427064 : Nat := 4983230072969 + 3 ^ 40 * 427064 * 2
def baseEnd_427064 : Nat := 129949097618857685236133

theorem tailTrace_427064 : CollatzResearch.WordTrace tailWord_427064 prefixEnd_427064 129949097618857685236133 := by
  unfold tailWord_427064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7788151862413769784760123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10384202483218359713013497 7788151862413769784760123)
  ·
    refine ⟨11682227793620654677140185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7788151862413769784760123 11682227793620654677140185)
    ·
      refine ⟨8761670845215491007855139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11682227793620654677140185 8761670845215491007855139)
      ·
        refine ⟨13142506267823236511782709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8761670845215491007855139 13142506267823236511782709)
        ·
          refine ⟨1232109962608428422979629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13142506267823236511782709 1232109962608428422979629)
          ·
            refine ⟨462041235978160658617361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1232109962608428422979629 462041235978160658617361)
            ·
              refine ⟨346530926983620493963021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462041235978160658617361 346530926983620493963021)
              ·
                refine ⟨129949097618857685236133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346530926983620493963021 129949097618857685236133)
                ·
                  rfl

theorem cell19_427064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_427064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427064 prefixEnd_427064 := by exact prefixLift 427064
  have htrace : WordTrace (prefixWord ++ tailWord_427064) baseStart_427064 baseEnd_427064 := by
    simpa [prefixWord, tailWord_427064, baseEnd_427064] using wordTrace_append hprefix tailTrace_427064
  have hstable : (prefixWord ++ tailWord_427064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427064).length < 2 ^ (prefixWord ++ tailWord_427064).sum := by decide
  have hdescent : baseEnd_427064 < baseStart_427064 := by decide
  rcases family_descends (prefixWord ++ tailWord_427064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427066 : List Nat := [3, 1, 1, 1, 3, 1, 6, 3]
def baseStart_427066 : Nat := 118140960795 + 427066 * 2 ^ 59
def prefixEnd_427066 : Nat := 4983230072969 + 3 ^ 40 * 427066 * 2
def baseEnd_427066 : Nat := 129949706188522273191683

theorem tailTrace_427066 : CollatzResearch.WordTrace tailWord_427066 prefixEnd_427066 129949706188522273191683 := by
  unfold tailWord_427066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894094167705073477773263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10384251113880195940728701 3894094167705073477773263)
  ·
    refine ⟨5841141251557610216659895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3894094167705073477773263 5841141251557610216659895)
    ·
      refine ⟨8761711877336415324989843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5841141251557610216659895 8761711877336415324989843)
      ·
        refine ⟨13142567816004622987484765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8761711877336415324989843 13142567816004622987484765)
        ·
          refine ⟨4928462931001733620306787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13142567816004622987484765 4928462931001733620306787)
          ·
            refine ⟨7392694396502600430460181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928462931001733620306787 7392694396502600430460181)
            ·
              refine ⟨346532549836059395177821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7392694396502600430460181 346532549836059395177821)
              ·
                refine ⟨129949706188522273191683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346532549836059395177821 129949706188522273191683)
                ·
                  rfl

theorem cell19_427066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_427066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427066 prefixEnd_427066 := by exact prefixLift 427066
  have htrace : WordTrace (prefixWord ++ tailWord_427066) baseStart_427066 baseEnd_427066 := by
    simpa [prefixWord, tailWord_427066, baseEnd_427066] using wordTrace_append hprefix tailTrace_427066
  have hstable : (prefixWord ++ tailWord_427066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427066).length < 2 ^ (prefixWord ++ tailWord_427066).sum := by decide
  have hdescent : baseEnd_427066 < baseStart_427066 := by decide
  rcases family_descends (prefixWord ++ tailWord_427066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427085 : List Nat := [1, 6, 1, 1, 1, 2, 7]
def baseStart_427085 : Nat := 118140960795 + 427085 * 2 ^ 59
def prefixEnd_427085 : Nat := 4983230072969 + 3 ^ 40 * 427085 * 2
def baseEnd_427085 : Nat := 43318495866778619589803

theorem tailTrace_427085 : CollatzResearch.WordTrace tailWord_427085 prefixEnd_427085 43318495866778619589803 := by
  unfold tailWord_427085
  simp only [CollatzResearch.WordTrace]
  refine ⟨15577069657751460156034709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10384713105167640104023139 15577069657751460156034709)
  ·
    refine ⟨730175140207099694814127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15577069657751460156034709 730175140207099694814127)
    ·
      refine ⟨1095262710310649542221191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730175140207099694814127 1095262710310649542221191)
      ·
        refine ⟨1642894065465974313331787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095262710310649542221191 1642894065465974313331787)
        ·
          refine ⟨2464341098198961469997681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642894065465974313331787 2464341098198961469997681)
          ·
            refine ⟨1848255823649221102498261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2464341098198961469997681 1848255823649221102498261)
            ·
              refine ⟨43318495866778619589803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1848255823649221102498261 43318495866778619589803)
              ·
                rfl

theorem cell19_427085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_427085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427085 prefixEnd_427085 := by exact prefixLift 427085
  have htrace : WordTrace (prefixWord ++ tailWord_427085) baseStart_427085 baseEnd_427085 := by
    simpa [prefixWord, tailWord_427085, baseEnd_427085] using wordTrace_append hprefix tailTrace_427085
  have hstable : (prefixWord ++ tailWord_427085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427085).length < 2 ^ (prefixWord ++ tailWord_427085).sum := by decide
  have hdescent : baseEnd_427085 < baseStart_427085 := by decide
  rcases family_descends (prefixWord ++ tailWord_427085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427144 : List Nat := [2, 1, 3, 4, 9]
def baseStart_427144 : Nat := 118140960795 + 427144 * 2 ^ 59
def prefixEnd_427144 : Nat := 4983230072969 + 3 ^ 40 * 427144 * 2
def baseEnd_427144 : Nat := 4813831126127451979931

theorem tailTrace_427144 : CollatzResearch.WordTrace tailWord_427144 prefixEnd_427144 4813831126127451979931 := by
  unfold tailWord_427144
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789610782268856616216243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10386147709691808821621657 7789610782268856616216243)
  ·
    refine ⟨11684416173403284924324365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7789610782268856616216243 11684416173403284924324365)
    ·
      refine ⟨4381656065026231846621637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11684416173403284924324365 4381656065026231846621637)
      ·
        refine ⟨821560512192418471241557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4381656065026231846621637 821560512192418471241557)
        ·
          refine ⟨4813831126127451979931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 821560512192418471241557 4813831126127451979931)
          ·
            rfl

theorem cell19_427144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 9].length) (baseStart_427144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427144 prefixEnd_427144 := by exact prefixLift 427144
  have htrace : WordTrace (prefixWord ++ tailWord_427144) baseStart_427144 baseEnd_427144 := by
    simpa [prefixWord, tailWord_427144, baseEnd_427144] using wordTrace_append hprefix tailTrace_427144
  have hstable : (prefixWord ++ tailWord_427144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427144).length < 2 ^ (prefixWord ++ tailWord_427144).sum := by decide
  have hdescent : baseEnd_427144 < baseStart_427144 := by decide
  rcases family_descends (prefixWord ++ tailWord_427144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427237 : List Nat := [1, 3, 1, 4, 3, 1, 1, 5]
def baseStart_427237 : Nat := 118140960795 + 427237 * 2 ^ 59
def prefixEnd_427237 : Nat := 4983230072969 + 3 ^ 40 * 427237 * 2
def baseEnd_427237 : Nat := 130001738894844543391217

theorem tailTrace_427237 : CollatzResearch.WordTrace tailWord_427237 prefixEnd_427237 130001738894844543391217 := by
  unfold tailWord_427237
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582613553200790115567965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10388409035467193410378643 15582613553200790115567965)
  ·
    refine ⟨5843480082450296293337987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15582613553200790115567965 5843480082450296293337987)
    ·
      refine ⟨8765220123675444440006981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5843480082450296293337987 8765220123675444440006981)
      ·
        refine ⟨1643478773189145832501309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8765220123675444440006981 1643478773189145832501309)
        ·
          refine ⟨616304539945929687187991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1643478773189145832501309 616304539945929687187991)
          ·
            refine ⟨924456809918894530781987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616304539945929687187991 924456809918894530781987)
            ·
              refine ⟨1386685214878341796172981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924456809918894530781987 1386685214878341796172981)
              ·
                refine ⟨130001738894844543391217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1386685214878341796172981 130001738894844543391217)
                ·
                  rfl

theorem cell19_427237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_427237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427237 prefixEnd_427237 := by exact prefixLift 427237
  have htrace : WordTrace (prefixWord ++ tailWord_427237) baseStart_427237 baseEnd_427237 := by
    simpa [prefixWord, tailWord_427237, baseEnd_427237] using wordTrace_append hprefix tailTrace_427237
  have hstable : (prefixWord ++ tailWord_427237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427237).length < 2 ^ (prefixWord ++ tailWord_427237).sum := by decide
  have hdescent : baseEnd_427237 < baseStart_427237 := by decide
  rcases family_descends (prefixWord ++ tailWord_427237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427351 : List Nat := [1, 1, 3, 2, 3, 3, 3, 3]
def baseStart_427351 : Nat := 118140960795 + 427351 * 2 ^ 59
def prefixEnd_427351 : Nat := 4983230072969 + 3 ^ 40 * 427351 * 2
def baseEnd_427351 : Nat := 130036427365726056857573

theorem tailTrace_427351 : CollatzResearch.WordTrace tailWord_427351 prefixEnd_427351 130036427365726056857573 := by
  unfold tailWord_427351
  simp only [CollatzResearch.WordTrace]
  refine ⟨15586771474787787585217907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10391180983191858390145271 15586771474787787585217907)
  ·
    refine ⟨23380157212181681377826861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15586771474787787585217907 23380157212181681377826861)
    ·
      refine ⟨8767558954568130516685073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23380157212181681377826861 8767558954568130516685073)
      ·
        refine ⟨6575669215926097887513805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8767558954568130516685073 6575669215926097887513805)
        ·
          refine ⟨2465875955972286707817677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6575669215926097887513805 2465875955972286707817677)
          ·
            refine ⟨924703483489607515431629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2465875955972286707817677 924703483489607515431629)
            ·
              refine ⟨346763806308602818286861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 924703483489607515431629 346763806308602818286861)
              ·
                refine ⟨130036427365726056857573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346763806308602818286861 130036427365726056857573)
                ·
                  rfl

theorem cell19_427351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 3].length) (baseStart_427351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427351 prefixEnd_427351 := by exact prefixLift 427351
  have htrace : WordTrace (prefixWord ++ tailWord_427351) baseStart_427351 baseEnd_427351 := by
    simpa [prefixWord, tailWord_427351, baseEnd_427351] using wordTrace_append hprefix tailTrace_427351
  have hstable : (prefixWord ++ tailWord_427351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427351).length < 2 ^ (prefixWord ++ tailWord_427351).sum := by decide
  have hdescent : baseEnd_427351 < baseStart_427351 := by decide
  rcases family_descends (prefixWord ++ tailWord_427351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427370 : List Nat := [3, 1, 3, 3, 2, 1, 6]
def baseStart_427370 : Nat := 118140960795 + 427370 * 2 ^ 59
def prefixEnd_427370 : Nat := 4983230072969 + 3 ^ 40 * 427370 * 2
def baseEnd_427370 : Nat := 43347402925846547478433

theorem tailTrace_427370 : CollatzResearch.WordTrace tailWord_427370 prefixEnd_427370 43347402925846547478433 := by
  unfold tailWord_427370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3896866115429738457539891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10391642974479302553439709 3896866115429738457539891)
  ·
    refine ⟨5845299173144607686309837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3896866115429738457539891 5845299173144607686309837)
    ·
      refine ⟨2191987189929227882366189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5845299173144607686309837 2191987189929227882366189)
      ·
        refine ⟨821995196223460455887321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2191987189929227882366189 821995196223460455887321)
        ·
          refine ⟨616496397167595341915491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821995196223460455887321 616496397167595341915491)
          ·
            refine ⟨924744595751393012873237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616496397167595341915491 924744595751393012873237)
            ·
              refine ⟨43347402925846547478433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 924744595751393012873237 43347402925846547478433)
              ·
                rfl

theorem cell19_427370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_427370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427370 prefixEnd_427370 := by exact prefixLift 427370
  have htrace : WordTrace (prefixWord ++ tailWord_427370) baseStart_427370 baseEnd_427370 := by
    simpa [prefixWord, tailWord_427370, baseEnd_427370] using wordTrace_append hprefix tailTrace_427370
  have hstable : (prefixWord ++ tailWord_427370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427370).length < 2 ^ (prefixWord ++ tailWord_427370).sum := by decide
  have hdescent : baseEnd_427370 < baseStart_427370 := by decide
  rcases family_descends (prefixWord ++ tailWord_427370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427372 : List Nat := [2, 2, 1, 1, 5, 2, 6]
def baseStart_427372 : Nat := 118140960795 + 427372 * 2 ^ 59
def prefixEnd_427372 : Nat := 4983230072969 + 3 ^ 40 * 427372 * 2
def baseEnd_427372 : Nat := 43347605782401410130283

theorem tailTrace_427372 : CollatzResearch.WordTrace tailWord_427372 prefixEnd_427372 43347605782401410130283 := by
  unfold tailWord_427372
  simp only [CollatzResearch.WordTrace]
  refine ⟨7793768703855854085866185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10391691605141138781154913 7793768703855854085866185)
  ·
    refine ⟨5845326527891890564399639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7793768703855854085866185 5845326527891890564399639)
    ·
      refine ⟨8767989791837835846599459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5845326527891890564399639 8767989791837835846599459)
      ·
        refine ⟨13151984687756753769899189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8767989791837835846599459 13151984687756753769899189)
        ·
          refine ⟨1232998564477195665928049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13151984687756753769899189 1232998564477195665928049)
          ·
            refine ⟨924748923357896749446037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1232998564477195665928049 924748923357896749446037)
            ·
              refine ⟨43347605782401410130283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 924748923357896749446037 43347605782401410130283)
              ·
                rfl

theorem cell19_427372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_427372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427372 prefixEnd_427372 := by exact prefixLift 427372
  have htrace : WordTrace (prefixWord ++ tailWord_427372) baseStart_427372 baseEnd_427372 := by
    simpa [prefixWord, tailWord_427372, baseEnd_427372] using wordTrace_append hprefix tailTrace_427372
  have hstable : (prefixWord ++ tailWord_427372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427372).length < 2 ^ (prefixWord ++ tailWord_427372).sum := by decide
  have hdescent : baseEnd_427372 < baseStart_427372 := by decide
  rcases family_descends (prefixWord ++ tailWord_427372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427501 : List Nat := [1, 5, 1, 3, 2, 2, 1, 4]
def baseStart_427501 : Nat := 118140960795 + 427501 * 2 ^ 59
def prefixEnd_427501 : Nat := 4983230072969 + 3 ^ 40 * 427501 * 2
def baseEnd_427501 : Nat := 130082070090570153523831

theorem tailTrace_427501 : CollatzResearch.WordTrace tailWord_427501 prefixEnd_427501 130082070090570153523831 := by
  unfold tailWord_427501
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592242424244363203178357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10394828282829575468785571 15592242424244363203178357)
  ·
    refine ⟨1461772727272909050297971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15592242424244363203178357 1461772727272909050297971)
    ·
      refine ⟨2192659090909363575446957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1461772727272909050297971 2192659090909363575446957)
      ·
        refine ⟨822247159091011340792609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2192659090909363575446957 822247159091011340792609)
        ·
          refine ⟨616685369318258505594457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822247159091011340792609 616685369318258505594457)
          ·
            refine ⟨462514026988693879195843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616685369318258505594457 462514026988693879195843)
            ·
              refine ⟨693771040483040818793765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462514026988693879195843 693771040483040818793765)
              ·
                refine ⟨130082070090570153523831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 693771040483040818793765 130082070090570153523831)
                ·
                  rfl

theorem cell19_427501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_427501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427501 prefixEnd_427501 := by exact prefixLift 427501
  have htrace : WordTrace (prefixWord ++ tailWord_427501) baseStart_427501 baseEnd_427501 := by
    simpa [prefixWord, tailWord_427501, baseEnd_427501] using wordTrace_append hprefix tailTrace_427501
  have hstable : (prefixWord ++ tailWord_427501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427501).length < 2 ^ (prefixWord ++ tailWord_427501).sum := by decide
  have hdescent : baseEnd_427501 < baseStart_427501 := by decide
  rcases family_descends (prefixWord ++ tailWord_427501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427505 : List Nat := [1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_427505 : Nat := 118140960795 + 427505 * 2 ^ 59
def prefixEnd_427505 : Nat := 4983230072969 + 3 ^ 40 * 427505 * 2
def baseEnd_427505 : Nat := 130083287229899329434931

theorem tailTrace_427505 : CollatzResearch.WordTrace tailWord_427505 prefixEnd_427505 130083287229899329434931 := by
  unfold tailWord_427505
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592388316229871886323969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10394925544153247924215979 15592388316229871886323969)
  ·
    refine ⟨11694291237172403914742977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15592388316229871886323969 11694291237172403914742977)
    ·
      refine ⟨8770718427879302936057233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11694291237172403914742977 8770718427879302936057233)
      ·
        refine ⟨6578038820909477202042925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8770718427879302936057233 6578038820909477202042925)
        ·
          refine ⟨2466764557841053950766097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6578038820909477202042925 2466764557841053950766097)
          ·
            refine ⟨1850073418380790463074573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2466764557841053950766097 1850073418380790463074573)
            ·
              refine ⟨693777531892796423652965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1850073418380790463074573 693777531892796423652965)
              ·
                refine ⟨130083287229899329434931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 693777531892796423652965 130083287229899329434931)
                ·
                  rfl

theorem cell19_427505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_427505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427505 prefixEnd_427505 := by exact prefixLift 427505
  have htrace : WordTrace (prefixWord ++ tailWord_427505) baseStart_427505 baseEnd_427505 := by
    simpa [prefixWord, tailWord_427505, baseEnd_427505] using wordTrace_append hprefix tailTrace_427505
  have hstable : (prefixWord ++ tailWord_427505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427505).length < 2 ^ (prefixWord ++ tailWord_427505).sum := by decide
  have hdescent : baseEnd_427505 < baseStart_427505 := by decide
  rcases family_descends (prefixWord ++ tailWord_427505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427507 : List Nat := [1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_427507 : Nat := 118140960795 + 427507 * 2 ^ 59
def prefixEnd_427507 : Nat := 4983230072969 + 3 ^ 40 * 427507 * 2
def baseEnd_427507 : Nat := 130083895799563917390481

theorem tailTrace_427507 : CollatzResearch.WordTrace tailWord_427507 prefixEnd_427507 130083895799563917390481 := by
  unfold tailWord_427507
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592461262222626227896775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10394974174815084151931183 15592461262222626227896775)
  ·
    refine ⟨23388691893333939341845163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15592461262222626227896775 23388691893333939341845163)
    ·
      refine ⟨35083037840000909012767745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23388691893333939341845163 35083037840000909012767745)
      ·
        refine ⟨26312278380000681759575809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35083037840000909012767745 26312278380000681759575809)
        ·
          refine ⟨19734208785000511319681857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26312278380000681759575809 19734208785000511319681857)
          ·
            refine ⟨14800656588750383489761393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19734208785000511319681857 14800656588750383489761393)
            ·
              refine ⟨11100492441562787617321045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14800656588750383489761393 11100492441562787617321045)
              ·
                refine ⟨130083895799563917390481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11100492441562787617321045 130083895799563917390481)
                ·
                  rfl

theorem cell19_427507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_427507 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427507 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427507 prefixEnd_427507 := by exact prefixLift 427507
  have htrace : WordTrace (prefixWord ++ tailWord_427507) baseStart_427507 baseEnd_427507 := by
    simpa [prefixWord, tailWord_427507, baseEnd_427507] using wordTrace_append hprefix tailTrace_427507
  have hstable : (prefixWord ++ tailWord_427507).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427507).length < 2 ^ (prefixWord ++ tailWord_427507).sum := by decide
  have hdescent : baseEnd_427507 < baseStart_427507 := by decide
  rcases family_descends (prefixWord ++ tailWord_427507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427518 : List Nat := [4, 2, 2, 3, 1, 1, 3, 3]
def baseStart_427518 : Nat := 118140960795 + 427518 * 2 ^ 59
def prefixEnd_427518 : Nat := 4983230072969 + 3 ^ 40 * 427518 * 2
def baseEnd_427518 : Nat := 130087242932719151146007

theorem tailTrace_427518 : CollatzResearch.WordTrace tailWord_427518 prefixEnd_427518 130087242932719151146007 := by
  unfold tailWord_427518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949107808147846888318401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10395241643455183404364805 1949107808147846888318401)
  ·
    refine ⟨1461830856110885166238801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1949107808147846888318401 1461830856110885166238801)
    ·
      refine ⟨1096373142083163874679101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1461830856110885166238801 1096373142083163874679101)
      ·
        refine ⟨411139928281186453004663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1096373142083163874679101 411139928281186453004663)
        ·
          refine ⟨616709892421779679506995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411139928281186453004663 616709892421779679506995)
          ·
            refine ⟨925064838632669519260493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616709892421779679506995 925064838632669519260493)
            ·
              refine ⟨346899314487251069722685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925064838632669519260493 346899314487251069722685)
              ·
                refine ⟨130087242932719151146007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346899314487251069722685 130087242932719151146007)
                ·
                  rfl

theorem cell19_427518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_427518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427518 prefixEnd_427518 := by exact prefixLift 427518
  have htrace : WordTrace (prefixWord ++ tailWord_427518) baseStart_427518 baseEnd_427518 := by
    simpa [prefixWord, tailWord_427518, baseEnd_427518] using wordTrace_append hprefix tailTrace_427518
  have hstable : (prefixWord ++ tailWord_427518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427518).length < 2 ^ (prefixWord ++ tailWord_427518).sum := by decide
  have hdescent : baseEnd_427518 < baseStart_427518 := by decide
  rcases family_descends (prefixWord ++ tailWord_427518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427562 : List Nat := [3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_427562 : Nat := 118140960795 + 427562 * 2 ^ 59
def prefixEnd_427562 : Nat := 4983230072969 + 3 ^ 40 * 427562 * 2
def baseEnd_427562 : Nat := 130100631465340086168109

theorem tailTrace_427562 : CollatzResearch.WordTrace tailWord_427562 prefixEnd_427562 130100631465340086168109 := by
  unfold tailWord_427562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3898616819255842655287235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10396311518015580414099293 3898616819255842655287235)
  ·
    refine ⟨5847925228883763982930853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3898616819255842655287235 5847925228883763982930853)
    ·
      refine ⟨1096485980415705746799535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5847925228883763982930853 1096485980415705746799535)
      ·
        refine ⟨1644728970623558620199303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096485980415705746799535 1644728970623558620199303)
        ·
          refine ⟨2467093455935337930298955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644728970623558620199303 2467093455935337930298955)
          ·
            refine ⟨3700640183903006895448433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467093455935337930298955 3700640183903006895448433)
            ·
              refine ⟨2775480137927255171586325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3700640183903006895448433 2775480137927255171586325)
              ·
                refine ⟨130100631465340086168109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2775480137927255171586325 130100631465340086168109)
                ·
                  rfl

theorem cell19_427562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_427562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427562 prefixEnd_427562 := by exact prefixLift 427562
  have htrace : WordTrace (prefixWord ++ tailWord_427562) baseStart_427562 baseEnd_427562 := by
    simpa [prefixWord, tailWord_427562, baseEnd_427562] using wordTrace_append hprefix tailTrace_427562
  have hstable : (prefixWord ++ tailWord_427562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427562).length < 2 ^ (prefixWord ++ tailWord_427562).sum := by decide
  have hdescent : baseEnd_427562 < baseStart_427562 := by decide
  rcases family_descends (prefixWord ++ tailWord_427562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427619 : List Nat := [1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_427619 : Nat := 118140960795 + 427619 * 2 ^ 59
def prefixEnd_427619 : Nat := 4983230072969 + 3 ^ 40 * 427619 * 2
def baseEnd_427619 : Nat := 130117975700780842901287

theorem tailTrace_427619 : CollatzResearch.WordTrace tailWord_427619 prefixEnd_427619 130117975700780842901287 := by
  unfold tailWord_427619
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596546237816869355973911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10397697491877912903982607 15596546237816869355973911)
  ·
    refine ⟨23394819356725304033960867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15596546237816869355973911 23394819356725304033960867)
    ·
      refine ⟨35092229035087956050941301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23394819356725304033960867 35092229035087956050941301)
      ·
        refine ⟨3289896472039495879775747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35092229035087956050941301 3289896472039495879775747)
        ·
          refine ⟨4934844708059243819663621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3289896472039495879775747 4934844708059243819663621)
          ·
            refine ⟨925283382761108216186929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4934844708059243819663621 925283382761108216186929)
            ·
              refine ⟨693962537070831162140197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925283382761108216186929 693962537070831162140197)
              ·
                refine ⟨130117975700780842901287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 693962537070831162140197 130117975700780842901287)
                ·
                  rfl

theorem cell19_427619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_427619 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427619 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427619 prefixEnd_427619 := by exact prefixLift 427619
  have htrace : WordTrace (prefixWord ++ tailWord_427619) baseStart_427619 baseEnd_427619 := by
    simpa [prefixWord, tailWord_427619, baseEnd_427619] using wordTrace_append hprefix tailTrace_427619
  have hstable : (prefixWord ++ tailWord_427619).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427619).length < 2 ^ (prefixWord ++ tailWord_427619).sum := by decide
  have hdescent : baseEnd_427619 < baseStart_427619 := by decide
  rcases family_descends (prefixWord ++ tailWord_427619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427693 : List Nat := [1, 5, 2, 1, 1, 1, 5, 3]
def baseStart_427693 : Nat := 118140960795 + 427693 * 2 ^ 59
def prefixEnd_427693 : Nat := 4983230072969 + 3 ^ 40 * 427693 * 2
def baseEnd_427693 : Nat := 130140492778370597256641

theorem tailTrace_427693 : CollatzResearch.WordTrace tailWord_427693 prefixEnd_427693 130140492778370597256641 := by
  unfold tailWord_427693
  simp only [CollatzResearch.WordTrace]
  refine ⟨15599245239548779994167733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10399496826365853329445155 15599245239548779994167733)
  ·
    refine ⟨1462429241207698124453225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15599245239548779994167733 1462429241207698124453225)
    ·
      refine ⟨1096821930905773593339919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1462429241207698124453225 1096821930905773593339919)
      ·
        refine ⟨1645232896358660390009879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096821930905773593339919 1645232896358660390009879)
        ·
          refine ⟨2467849344537990585014819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1645232896358660390009879 2467849344537990585014819)
          ·
            refine ⟨3701774016806985877522229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467849344537990585014819 3701774016806985877522229)
            ·
              refine ⟨347041314075654926017709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3701774016806985877522229 347041314075654926017709)
              ·
                refine ⟨130140492778370597256641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347041314075654926017709 130140492778370597256641)
                ·
                  rfl

theorem cell19_427693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 3].length) (baseStart_427693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427693 prefixEnd_427693 := by exact prefixLift 427693
  have htrace : WordTrace (prefixWord ++ tailWord_427693) baseStart_427693 baseEnd_427693 := by
    simpa [prefixWord, tailWord_427693, baseEnd_427693] using wordTrace_append hprefix tailTrace_427693
  have hstable : (prefixWord ++ tailWord_427693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427693).length < 2 ^ (prefixWord ++ tailWord_427693).sum := by decide
  have hdescent : baseEnd_427693 < baseStart_427693 := by decide
  rcases family_descends (prefixWord ++ tailWord_427693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427695 : List Nat := [1, 1, 2, 1, 2, 4, 5, 3]
def baseStart_427695 : Nat := 118140960795 + 427695 * 2 ^ 59
def prefixEnd_427695 : Nat := 4983230072969 + 3 ^ 40 * 427695 * 2
def baseEnd_427695 : Nat := 130141101348035185212191

theorem tailTrace_427695 : CollatzResearch.WordTrace tailWord_427695 prefixEnd_427695 130141101348035185212191 := by
  unfold tailWord_427695
  simp only [CollatzResearch.WordTrace]
  refine ⟨15599318185541534335740539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10399545457027689557160359 15599318185541534335740539)
  ·
    refine ⟨23398977278312301503610809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15599318185541534335740539 23398977278312301503610809)
    ·
      refine ⟨17549232958734226127708107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23398977278312301503610809 17549232958734226127708107)
      ·
        refine ⟨26323849438101339191562161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17549232958734226127708107 26323849438101339191562161)
        ·
          refine ⟨19742887078576004393671621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26323849438101339191562161 19742887078576004393671621)
          ·
            refine ⟨3701791327233000823813429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19742887078576004393671621 3701791327233000823813429)
            ·
              refine ⟨347042936928093827232509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3701791327233000823813429 347042936928093827232509)
              ·
                refine ⟨130141101348035185212191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347042936928093827232509 130141101348035185212191)
                ·
                  rfl

theorem cell19_427695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 3].length) (baseStart_427695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427695 prefixEnd_427695 := by exact prefixLift 427695
  have htrace : WordTrace (prefixWord ++ tailWord_427695) baseStart_427695 baseEnd_427695 := by
    simpa [prefixWord, tailWord_427695, baseEnd_427695] using wordTrace_append hprefix tailTrace_427695
  have hstable : (prefixWord ++ tailWord_427695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427695).length < 2 ^ (prefixWord ++ tailWord_427695).sum := by decide
  have hdescent : baseEnd_427695 < baseStart_427695 := by decide
  rcases family_descends (prefixWord ++ tailWord_427695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427735 : List Nat := [1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_427735 : Nat := 118140960795 + 427735 * 2 ^ 59
def prefixEnd_427735 : Nat := 4983230072969 + 3 ^ 40 * 427735 * 2
def baseEnd_427735 : Nat := 130153272741326944323193

theorem tailTrace_427735 : CollatzResearch.WordTrace tailWord_427735 prefixEnd_427735 130153272741326944323193 := by
  unfold tailWord_427735
  simp only [CollatzResearch.WordTrace]
  refine ⟨15600777105396621167196659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10400518070264414111464439 15600777105396621167196659)
  ·
    refine ⟨23401165658094931750794989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15600777105396621167196659 23401165658094931750794989)
    ·
      refine ⟨8775437121785599406548121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23401165658094931750794989 8775437121785599406548121)
      ·
        refine ⟨6581577841339199554911091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8775437121785599406548121 6581577841339199554911091)
        ·
          refine ⟨9872366762008799332366637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6581577841339199554911091 9872366762008799332366637)
          ·
            refine ⟨3702137535753299749637489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9872366762008799332366637 3702137535753299749637489)
            ·
              refine ⟨2776603151814974812228117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3702137535753299749637489 2776603151814974812228117)
              ·
                refine ⟨130153272741326944323193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2776603151814974812228117 130153272741326944323193)
                ·
                  rfl

theorem cell19_427735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_427735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427735 prefixEnd_427735 := by exact prefixLift 427735
  have htrace : WordTrace (prefixWord ++ tailWord_427735) baseStart_427735 baseEnd_427735 := by
    simpa [prefixWord, tailWord_427735, baseEnd_427735] using wordTrace_append hprefix tailTrace_427735
  have hstable : (prefixWord ++ tailWord_427735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427735).length < 2 ^ (prefixWord ++ tailWord_427735).sum := by decide
  have hdescent : baseEnd_427735 < baseStart_427735 := by decide
  rcases family_descends (prefixWord ++ tailWord_427735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427752 : List Nat := [2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_427752 : Nat := 118140960795 + 427752 * 2 ^ 59
def prefixEnd_427752 : Nat := 4983230072969 + 3 ^ 40 * 427752 * 2
def baseEnd_427752 : Nat := 130158445583475941945369

theorem tailTrace_427752 : CollatzResearch.WordTrace tailWord_427752 prefixEnd_427752 130158445583475941945369 := by
  unfold tailWord_427752
  simp only [CollatzResearch.WordTrace]
  refine ⟨7800698573167516535282755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10400931430890022047043673 7800698573167516535282755)
  ·
    refine ⟨11701047859751274802924133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7800698573167516535282755 11701047859751274802924133)
    ·
      refine ⟨2193946473703364025548275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11701047859751274802924133 2193946473703364025548275)
      ·
        refine ⟨3290919710555046038322413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193946473703364025548275 3290919710555046038322413)
        ·
          refine ⟨1234094891458142264370905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3290919710555046038322413 1234094891458142264370905)
          ·
            refine ⟨925571168593606698278179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1234094891458142264370905 925571168593606698278179)
            ·
              refine ⟨1388356752890410047417269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925571168593606698278179 1388356752890410047417269)
              ·
                refine ⟨130158445583475941945369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1388356752890410047417269 130158445583475941945369)
                ·
                  rfl

theorem cell19_427752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_427752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427752 prefixEnd_427752 := by exact prefixLift 427752
  have htrace : WordTrace (prefixWord ++ tailWord_427752) baseStart_427752 baseEnd_427752 := by
    simpa [prefixWord, tailWord_427752, baseEnd_427752] using wordTrace_append hprefix tailTrace_427752
  have hstable : (prefixWord ++ tailWord_427752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427752).length < 2 ^ (prefixWord ++ tailWord_427752).sum := by decide
  have hdescent : baseEnd_427752 < baseStart_427752 := by decide
  rcases family_descends (prefixWord ++ tailWord_427752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427811 : List Nat := [1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_427811 : Nat := 118140960795 + 427811 * 2 ^ 59
def prefixEnd_427811 : Nat := 4983230072969 + 3 ^ 40 * 427811 * 2
def baseEnd_427811 : Nat := 130176398388581286634097

theorem tailTrace_427811 : CollatzResearch.WordTrace tailWord_427811 prefixEnd_427811 130176398388581286634097 := by
  unfold tailWord_427811
  simp only [CollatzResearch.WordTrace]
  refine ⟨15603549053121286146963287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10402366035414190764642191 15603549053121286146963287)
  ·
    refine ⟨23405323579681929220444931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15603549053121286146963287 23405323579681929220444931)
    ·
      refine ⟨35107985369522893830667397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23405323579681929220444931 35107985369522893830667397)
      ·
        refine ⟨6582747256785542593250137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35107985369522893830667397 6582747256785542593250137)
        ·
          refine ⟨4937060442589156944937603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6582747256785542593250137 4937060442589156944937603)
          ·
            refine ⟨7405590663883735417406405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937060442589156944937603 7405590663883735417406405)
            ·
              refine ⟨1388548249478200390763701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7405590663883735417406405 1388548249478200390763701)
              ·
                refine ⟨130176398388581286634097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1388548249478200390763701 130176398388581286634097)
                ·
                  rfl

theorem cell19_427811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_427811 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427811 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427811 prefixEnd_427811 := by exact prefixLift 427811
  have htrace : WordTrace (prefixWord ++ tailWord_427811) baseStart_427811 baseEnd_427811 := by
    simpa [prefixWord, tailWord_427811, baseEnd_427811] using wordTrace_append hprefix tailTrace_427811
  have hstable : (prefixWord ++ tailWord_427811).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427811).length < 2 ^ (prefixWord ++ tailWord_427811).sum := by decide
  have hdescent : baseEnd_427811 < baseStart_427811 := by decide
  rcases family_descends (prefixWord ++ tailWord_427811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427828 : List Nat := [2, 5, 1, 1, 2, 8]
def baseStart_427828 : Nat := 118140960795 + 427828 * 2 ^ 59
def prefixEnd_427828 : Nat := 4983230072969 + 3 ^ 40 * 427828 * 2
def baseEnd_427828 : Nat := 14464619025636698250697

theorem tailTrace_427828 : CollatzResearch.WordTrace tailWord_427828 prefixEnd_427828 14464619025636698250697 := by
  unfold tailWord_427828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7802084547029849025166069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10402779396039798700221425 7802084547029849025166069)
  ·
    refine ⟨731445426284048346109319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7802084547029849025166069 731445426284048346109319)
    ·
      refine ⟨1097168139426072519163979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731445426284048346109319 1097168139426072519163979)
      ·
        refine ⟨1645752209139108778745969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1097168139426072519163979 1645752209139108778745969)
        ·
          refine ⟨1234314156854331584059477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1645752209139108778745969 1234314156854331584059477)
          ·
            refine ⟨14464619025636698250697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1234314156854331584059477 14464619025636698250697)
            ·
              rfl

theorem cell19_427828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 8].length) (baseStart_427828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427828 prefixEnd_427828 := by exact prefixLift 427828
  have htrace : WordTrace (prefixWord ++ tailWord_427828) baseStart_427828 baseEnd_427828 := by
    simpa [prefixWord, tailWord_427828, baseEnd_427828] using wordTrace_append hprefix tailTrace_427828
  have hstable : (prefixWord ++ tailWord_427828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427828).length < 2 ^ (prefixWord ++ tailWord_427828).sum := by decide
  have hdescent : baseEnd_427828 < baseStart_427828 := by decide
  rcases family_descends (prefixWord ++ tailWord_427828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427866 : List Nat := [3, 1, 1, 2, 1, 3, 5, 3]
def baseStart_427866 : Nat := 118140960795 + 427866 * 2 ^ 59
def prefixEnd_427866 : Nat := 4983230072969 + 3 ^ 40 * 427866 * 2
def baseEnd_427866 : Nat := 130193134054357455411725

theorem tailTrace_427866 : CollatzResearch.WordTrace tailWord_427866 prefixEnd_427866 130193134054357455411725 := by
  unfold tailWord_427866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3901388766980507635053863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10403703378614687026810301 3901388766980507635053863)
  ·
    refine ⟨5852083150470761452580795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3901388766980507635053863 5852083150470761452580795)
    ·
      refine ⟨8778124725706142178871193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5852083150470761452580795 8778124725706142178871193)
      ·
        refine ⟨6583593544279606634153395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8778124725706142178871193 6583593544279606634153395)
        ·
          refine ⟨9875390316419409951230093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6583593544279606634153395 9875390316419409951230093)
          ·
            refine ⟨3703271368657278731711285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9875390316419409951230093 3703271368657278731711285)
            ·
              refine ⟨347181690811619881097933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3703271368657278731711285 347181690811619881097933)
              ·
                refine ⟨130193134054357455411725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347181690811619881097933 130193134054357455411725)
                ·
                  rfl

theorem cell19_427866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_427866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427866 prefixEnd_427866 := by exact prefixLift 427866
  have htrace : WordTrace (prefixWord ++ tailWord_427866) baseStart_427866 baseEnd_427866 := by
    simpa [prefixWord, tailWord_427866, baseEnd_427866] using wordTrace_append hprefix tailTrace_427866
  have hstable : (prefixWord ++ tailWord_427866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427866).length < 2 ^ (prefixWord ++ tailWord_427866).sum := by decide
  have hdescent : baseEnd_427866 < baseStart_427866 := by decide
  rcases family_descends (prefixWord ++ tailWord_427866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427925 : List Nat := [1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_427925 : Nat := 118140960795 + 427925 * 2 ^ 59
def prefixEnd_427925 : Nat := 4983230072969 + 3 ^ 40 * 427925 * 2
def baseEnd_427925 : Nat := 130211086859462800100453

theorem tailTrace_427925 : CollatzResearch.WordTrace tailWord_427925 prefixEnd_427925 130211086859462800100453 := by
  unfold tailWord_427925
  simp only [CollatzResearch.WordTrace]
  refine ⟨15607706974708283616613229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10405137983138855744408819 15607706974708283616613229)
  ·
    refine ⟨5852890115515606356229961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15607706974708283616613229 5852890115515606356229961)
    ·
      refine ⟨4389667586636704767172471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5852890115515606356229961 4389667586636704767172471)
      ·
        refine ⟨6584501379955057150758707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4389667586636704767172471 6584501379955057150758707)
        ·
          refine ⟨9876752069932585726138061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584501379955057150758707 9876752069932585726138061)
          ·
            refine ⟨3703782026224719647301773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9876752069932585726138061 3703782026224719647301773)
            ·
              refine ⟨1388918259834269867738165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3703782026224719647301773 1388918259834269867738165)
              ·
                refine ⟨130211086859462800100453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1388918259834269867738165 130211086859462800100453)
                ·
                  rfl

theorem cell19_427925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_427925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427925 prefixEnd_427925 := by exact prefixLift 427925
  have htrace : WordTrace (prefixWord ++ tailWord_427925) baseStart_427925 baseEnd_427925 := by
    simpa [prefixWord, tailWord_427925, baseEnd_427925] using wordTrace_append hprefix tailTrace_427925
  have hstable : (prefixWord ++ tailWord_427925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427925).length < 2 ^ (prefixWord ++ tailWord_427925).sum := by decide
  have hdescent : baseEnd_427925 < baseStart_427925 := by decide
  rcases family_descends (prefixWord ++ tailWord_427925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427982 : List Nat := [4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_427982 : Nat := 118140960795 + 427982 * 2 ^ 59
def prefixEnd_427982 : Nat := 4983230072969 + 3 ^ 40 * 427982 * 2
def baseEnd_427982 : Nat := 130228431094903556833631

theorem tailTrace_427982 : CollatzResearch.WordTrace tailWord_427982 prefixEnd_427982 130228431094903556833631 := by
  unfold tailWord_427982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1951223241937722793929775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10406523957001188234292133 1951223241937722793929775)
  ·
    refine ⟨2926834862906584190894663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1951223241937722793929775 2926834862906584190894663)
    ·
      refine ⟨4390252294359876286341995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2926834862906584190894663 4390252294359876286341995)
      ·
        refine ⟨6585378441539814429512993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4390252294359876286341995 6585378441539814429512993)
        ·
          refine ⟨4939033831154860822134745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6585378441539814429512993 4939033831154860822134745)
          ·
            refine ⟨3704275373366145616601059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4939033831154860822134745 3704275373366145616601059)
            ·
              refine ⟨5556413060049218424901589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704275373366145616601059 5556413060049218424901589)
              ·
                refine ⟨130228431094903556833631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5556413060049218424901589 130228431094903556833631)
                ·
                  rfl

theorem cell19_427982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_427982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_427982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_427982 prefixEnd_427982 := by exact prefixLift 427982
  have htrace : WordTrace (prefixWord ++ tailWord_427982) baseStart_427982 baseEnd_427982 := by
    simpa [prefixWord, tailWord_427982, baseEnd_427982] using wordTrace_append hprefix tailTrace_427982
  have hstable : (prefixWord ++ tailWord_427982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427982).length < 2 ^ (prefixWord ++ tailWord_427982).sum := by decide
  have hdescent : baseEnd_427982 < baseStart_427982 := by decide
  rcases family_descends (prefixWord ++ tailWord_427982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428037 : List Nat := [1, 3, 1, 1, 2, 5, 3, 3]
def baseStart_428037 : Nat := 118140960795 + 428037 * 2 ^ 59
def prefixEnd_428037 : Nat := 4983230072969 + 3 ^ 40 * 428037 * 2
def baseEnd_428037 : Nat := 130245166760679725611259

theorem tailTrace_428037 : CollatzResearch.WordTrace tailWord_428037 prefixEnd_428037 130245166760679725611259 := by
  unfold tailWord_428037
  simp only [CollatzResearch.WordTrace]
  refine ⟨15611791950302526744690365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10407861300201684496460243 15611791950302526744690365)
  ·
    refine ⟨5854421981363447529258887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15611791950302526744690365 5854421981363447529258887)
    ·
      refine ⟨8781632972045171293888331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5854421981363447529258887 8781632972045171293888331)
      ·
        refine ⟨13172449458067756940832497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8781632972045171293888331 13172449458067756940832497)
        ·
          refine ⟨9879337093550817705624373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13172449458067756940832497 9879337093550817705624373)
          ·
            refine ⟨926187852520389159902285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9879337093550817705624373 926187852520389159902285)
            ·
              refine ⟨347320444695145934963357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 926187852520389159902285 347320444695145934963357)
              ·
                refine ⟨130245166760679725611259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347320444695145934963357 130245166760679725611259)
                ·
                  rfl

theorem cell19_428037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 3].length) (baseStart_428037 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428037 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428037 prefixEnd_428037 := by exact prefixLift 428037
  have htrace : WordTrace (prefixWord ++ tailWord_428037) baseStart_428037 baseEnd_428037 := by
    simpa [prefixWord, tailWord_428037, baseEnd_428037] using wordTrace_append hprefix tailTrace_428037
  have hstable : (prefixWord ++ tailWord_428037).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428037).length < 2 ^ (prefixWord ++ tailWord_428037).sum := by decide
  have hdescent : baseEnd_428037 < baseStart_428037 := by decide
  rcases family_descends (prefixWord ++ tailWord_428037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428058 : List Nat := [3, 1, 1, 3, 1, 4, 6]
def baseStart_428058 : Nat := 118140960795 + 428058 * 2 ^ 59
def prefixEnd_428058 : Nat := 4983230072969 + 3 ^ 40 * 428058 * 2
def baseEnd_428058 : Nat := 43417185580719299714845

theorem tailTrace_428058 : CollatzResearch.WordTrace tailWord_428058 prefixEnd_428058 43417185580719299714845 := by
  unfold tailWord_428058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903139470806611832801207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10408371922150964887469885 3903139470806611832801207)
  ·
    refine ⟨5854709206209917749201811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3903139470806611832801207 5854709206209917749201811)
    ·
      refine ⟨8782063809314876623802717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5854709206209917749201811 8782063809314876623802717)
      ·
        refine ⟨3293273928493078733926019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8782063809314876623802717 3293273928493078733926019)
        ·
          refine ⟨4939910892739618100889029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3293273928493078733926019 4939910892739618100889029)
          ·
            refine ⟨926233292388678393916693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4939910892739618100889029 926233292388678393916693)
            ·
              refine ⟨43417185580719299714845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 926233292388678393916693 43417185580719299714845)
              ·
                rfl

theorem cell19_428058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_428058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428058 prefixEnd_428058 := by exact prefixLift 428058
  have htrace : WordTrace (prefixWord ++ tailWord_428058) baseStart_428058 baseEnd_428058 := by
    simpa [prefixWord, tailWord_428058, baseEnd_428058] using wordTrace_append hprefix tailTrace_428058
  have hstable : (prefixWord ++ tailWord_428058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428058).length < 2 ^ (prefixWord ++ tailWord_428058).sum := by decide
  have hdescent : baseEnd_428058 < baseStart_428058 := by decide
  rcases family_descends (prefixWord ++ tailWord_428058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428096 : List Nat := [2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_428096 : Nat := 118140960795 + 428096 * 2 ^ 59
def prefixEnd_428096 : Nat := 4983230072969 + 3 ^ 40 * 428096 * 2
def baseEnd_428096 : Nat := 130263119565785070299987

theorem tailTrace_428096 : CollatzResearch.WordTrace tailWord_428096 prefixEnd_428096 130263119565785070299987 := by
  unfold tailWord_428096
  simp only [CollatzResearch.WordTrace]
  refine ⟨7806971928544389910544071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10409295904725853214058761 7806971928544389910544071)
  ·
    refine ⟨11710457892816584865816107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7806971928544389910544071 11710457892816584865816107)
    ·
      refine ⟨17565686839224877298724161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11710457892816584865816107 17565686839224877298724161)
      ·
        refine ⟨13174265129418657974043121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17565686839224877298724161 13174265129418657974043121)
        ·
          refine ⟨9880698847063993480532341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13174265129418657974043121 9880698847063993480532341)
          ·
            refine ⟨926315516912249388799907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9880698847063993480532341 926315516912249388799907)
            ·
              refine ⟨1389473275368374083199861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926315516912249388799907 1389473275368374083199861)
              ·
                refine ⟨130263119565785070299987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1389473275368374083199861 130263119565785070299987)
                ·
                  rfl

theorem cell19_428096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_428096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428096 prefixEnd_428096 := by exact prefixLift 428096
  have htrace : WordTrace (prefixWord ++ tailWord_428096) baseStart_428096 baseEnd_428096 := by
    simpa [prefixWord, tailWord_428096, baseEnd_428096] using wordTrace_append hprefix tailTrace_428096
  have hstable : (prefixWord ++ tailWord_428096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428096).length < 2 ^ (prefixWord ++ tailWord_428096).sum := by decide
  have hdescent : baseEnd_428096 < baseStart_428096 := by decide
  rcases family_descends (prefixWord ++ tailWord_428096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428130 : List Nat := [3, 3, 2, 2, 2, 1, 2, 4]
def baseStart_428130 : Nat := 118140960795 + 428130 * 2 ^ 59
def prefixEnd_428130 : Nat := 4983230072969 + 3 ^ 40 * 428130 * 2
def baseEnd_428130 : Nat := 130273465250083065544339

theorem tailTrace_428130 : CollatzResearch.WordTrace tailWord_428130 prefixEnd_428130 130273465250083065544339 := by
  unfold tailWord_428130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903795984741400906956461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10410122625977069085217229 3903795984741400906956461)
  ·
    refine ⟨1463923494278025340108673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3903795984741400906956461 1463923494278025340108673)
    ·
      refine ⟨1097942620708519005081505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1463923494278025340108673 1097942620708519005081505)
      ·
        refine ⟨823456965531389253811129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1097942620708519005081505 823456965531389253811129)
        ·
          refine ⟨617592724148541940358347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823456965531389253811129 617592724148541940358347)
          ·
            refine ⟨926389086222812910537521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617592724148541940358347 926389086222812910537521)
            ·
              refine ⟨694791814667109682903141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926389086222812910537521 694791814667109682903141)
              ·
                refine ⟨130273465250083065544339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 694791814667109682903141 130273465250083065544339)
                ·
                  rfl

theorem cell19_428130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_428130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428130 prefixEnd_428130 := by exact prefixLift 428130
  have htrace : WordTrace (prefixWord ++ tailWord_428130) baseStart_428130 baseEnd_428130 := by
    simpa [prefixWord, tailWord_428130, baseEnd_428130] using wordTrace_append hprefix tailTrace_428130
  have hstable : (prefixWord ++ tailWord_428130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428130).length < 2 ^ (prefixWord ++ tailWord_428130).sum := by decide
  have hdescent : baseEnd_428130 < baseStart_428130 := by decide
  rcases family_descends (prefixWord ++ tailWord_428130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428153 : List Nat := [1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_428153 : Nat := 118140960795 + 428153 * 2 ^ 59
def prefixEnd_428153 : Nat := 4983230072969 + 3 ^ 40 * 428153 * 2
def baseEnd_428153 : Nat := 130280463801225827033165

theorem tailTrace_428153 : CollatzResearch.WordTrace tailWord_428153 prefixEnd_428153 130280463801225827033165 := by
  unfold tailWord_428153
  simp only [CollatzResearch.WordTrace]
  refine ⟨15616022817882278555913113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10410681878588185703942075 15616022817882278555913113)
  ·
    refine ⟨11712017113411708916934835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15616022817882278555913113 11712017113411708916934835)
    ·
      refine ⟨17568025670117563375402253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11712017113411708916934835 17568025670117563375402253)
      ·
        refine ⟨6588009626294086265775845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17568025670117563375402253 6588009626294086265775845)
        ·
          refine ⟨1235251804930141174832971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6588009626294086265775845 1235251804930141174832971)
          ·
            refine ⟨1852877707395211762249457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235251804930141174832971 1852877707395211762249457)
            ·
              refine ⟨1389658280546408821687093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1852877707395211762249457 1389658280546408821687093)
              ·
                refine ⟨130280463801225827033165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1389658280546408821687093 130280463801225827033165)
                ·
                  rfl

theorem cell19_428153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_428153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428153 prefixEnd_428153 := by exact prefixLift 428153
  have htrace : WordTrace (prefixWord ++ tailWord_428153) baseStart_428153 baseEnd_428153 := by
    simpa [prefixWord, tailWord_428153, baseEnd_428153] using wordTrace_append hprefix tailTrace_428153
  have hstable : (prefixWord ++ tailWord_428153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428153).length < 2 ^ (prefixWord ++ tailWord_428153).sum := by decide
  have hdescent : baseEnd_428153 < baseStart_428153 := by decide
  rcases family_descends (prefixWord ++ tailWord_428153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428189 : List Nat := [1, 4, 2, 1, 1, 5, 1, 4]
def baseStart_428189 : Nat := 118140960795 + 428189 * 2 ^ 59
def prefixEnd_428189 : Nat := 4983230072969 + 3 ^ 40 * 428189 * 2
def baseEnd_428189 : Nat := 130291418055188410233067

theorem tailTrace_428189 : CollatzResearch.WordTrace tailWord_428189 prefixEnd_428189 130291418055188410233067 := by
  unfold tailWord_428189
  simp only [CollatzResearch.WordTrace]
  refine ⟨15617335845751856704223621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10411557230501237802815747 15617335845751856704223621)
  ·
    refine ⟨2928250471078473132041929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15617335845751856704223621 2928250471078473132041929)
    ·
      refine ⟨2196187853308854849031447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2928250471078473132041929 2196187853308854849031447)
      ·
        refine ⟨3294281779963282273547171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2196187853308854849031447 3294281779963282273547171)
        ·
          refine ⟨4941422669944923410320757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3294281779963282273547171 4941422669944923410320757)
          ·
            refine ⟨463258375307336569717571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4941422669944923410320757 463258375307336569717571)
            ·
              refine ⟨694887562961004854576357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463258375307336569717571 694887562961004854576357)
              ·
                refine ⟨130291418055188410233067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 694887562961004854576357 130291418055188410233067)
                ·
                  rfl

theorem cell19_428189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_428189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428189 prefixEnd_428189 := by exact prefixLift 428189
  have htrace : WordTrace (prefixWord ++ tailWord_428189) baseStart_428189 baseEnd_428189 := by
    simpa [prefixWord, tailWord_428189, baseEnd_428189] using wordTrace_append hprefix tailTrace_428189
  have hstable : (prefixWord ++ tailWord_428189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428189).length < 2 ^ (prefixWord ++ tailWord_428189).sum := by decide
  have hdescent : baseEnd_428189 < baseStart_428189 := by decide
  rcases family_descends (prefixWord ++ tailWord_428189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428263 : List Nat := [1, 1, 5, 3, 1, 3, 2, 3]
def baseStart_428263 : Nat := 118140960795 + 428263 * 2 ^ 59
def prefixEnd_428263 : Nat := 4983230072969 + 3 ^ 40 * 428263 * 2
def baseEnd_428263 : Nat := 130313935132778164588421

theorem tailTrace_428263 : CollatzResearch.WordTrace tailWord_428263 prefixEnd_428263 130313935132778164588421 := by
  unfold tailWord_428263
  simp only [CollatzResearch.WordTrace]
  refine ⟨15620034847483767342417443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10413356564989178228278295 15620034847483767342417443)
  ·
    refine ⟨23430052271225651013626165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15620034847483767342417443 23430052271225651013626165)
    ·
      refine ⟨2196567400427404782527453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23430052271225651013626165 2196567400427404782527453)
      ·
        refine ⟨823712775160276793447795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2196567400427404782527453 823712775160276793447795)
        ·
          refine ⟨1235569162740415190171693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823712775160276793447795 1235569162740415190171693)
          ·
            refine ⟨463338436027655696314385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1235569162740415190171693 463338436027655696314385)
            ·
              refine ⟨347503827020741772235789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463338436027655696314385 347503827020741772235789)
              ·
                refine ⟨130313935132778164588421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347503827020741772235789 130313935132778164588421)
                ·
                  rfl

theorem cell19_428263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 3].length) (baseStart_428263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428263 prefixEnd_428263 := by exact prefixLift 428263
  have htrace : WordTrace (prefixWord ++ tailWord_428263) baseStart_428263 baseEnd_428263 := by
    simpa [prefixWord, tailWord_428263, baseEnd_428263] using wordTrace_append hprefix tailTrace_428263
  have hstable : (prefixWord ++ tailWord_428263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428263).length < 2 ^ (prefixWord ++ tailWord_428263).sum := by decide
  have hdescent : baseEnd_428263 < baseStart_428263 := by decide
  rcases family_descends (prefixWord ++ tailWord_428263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428288 : List Nat := [2, 1, 1, 2, 1, 1, 11]
def baseStart_428288 : Nat := 118140960795 + 428288 * 2 ^ 59
def prefixEnd_428288 : Nat := 4983230072969 + 3 ^ 40 * 428288 * 2
def baseEnd_428288 : Nat := 43440514084528504677599

theorem tailTrace_428288 : CollatzResearch.WordTrace tailWord_428288 prefixEnd_428288 43440514084528504677599 := by
  unfold tailWord_428288
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810473336196598306038759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10413964448262131074718345 7810473336196598306038759)
  ·
    refine ⟨11715710004294897459058139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7810473336196598306038759 11715710004294897459058139)
    ·
      refine ⟨17573565006442346188587209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11715710004294897459058139 17573565006442346188587209)
      ·
        refine ⟨13180173754831759641440407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17573565006442346188587209 13180173754831759641440407)
        ·
          refine ⟨19770260632247639462160611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13180173754831759641440407 19770260632247639462160611)
          ·
            refine ⟨29655390948371459193240917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19770260632247639462160611 29655390948371459193240917)
            ·
              refine ⟨43440514084528504677599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29655390948371459193240917 43440514084528504677599)
              ·
                rfl

theorem cell19_428288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_428288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428288 prefixEnd_428288 := by exact prefixLift 428288
  have htrace : WordTrace (prefixWord ++ tailWord_428288) baseStart_428288 baseEnd_428288 := by
    simpa [prefixWord, tailWord_428288, baseEnd_428288] using wordTrace_append hprefix tailTrace_428288
  have hstable : (prefixWord ++ tailWord_428288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428288).length < 2 ^ (prefixWord ++ tailWord_428288).sum := by decide
  have hdescent : baseEnd_428288 < baseStart_428288 := by decide
  rcases family_descends (prefixWord ++ tailWord_428288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428305 : List Nat := [1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_428305 : Nat := 118140960795 + 428305 * 2 ^ 59
def prefixEnd_428305 : Nat := 4983230072969 + 3 ^ 40 * 428305 * 2
def baseEnd_428305 : Nat := 130326715095734511654973

theorem tailTrace_428305 : CollatzResearch.WordTrace tailWord_428305 prefixEnd_428305 130326715095734511654973 := by
  unfold tailWord_428305
  simp only [CollatzResearch.WordTrace]
  refine ⟨15621566713331608515446369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10414377808887739010297579 15621566713331608515446369)
  ·
    refine ⟨11716175034998706386584777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15621566713331608515446369 11716175034998706386584777)
    ·
      refine ⟨8787131276249029789938583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11716175034998706386584777 8787131276249029789938583)
      ·
        refine ⟨13180696914373544684907875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8787131276249029789938583 13180696914373544684907875)
        ·
          refine ⟨19771045371560317027361813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13180696914373544684907875 19771045371560317027361813)
          ·
            refine ⟨926767751791889860657585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19771045371560317027361813 926767751791889860657585)
            ·
              refine ⟨695075813843917395493189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926767751791889860657585 695075813843917395493189)
              ·
                refine ⟨130326715095734511654973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 695075813843917395493189 130326715095734511654973)
                ·
                  rfl

theorem cell19_428305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_428305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428305 prefixEnd_428305 := by exact prefixLift 428305
  have htrace : WordTrace (prefixWord ++ tailWord_428305) baseStart_428305 baseEnd_428305 := by
    simpa [prefixWord, tailWord_428305, baseEnd_428305] using wordTrace_append hprefix tailTrace_428305
  have hstable : (prefixWord ++ tailWord_428305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428305).length < 2 ^ (prefixWord ++ tailWord_428305).sum := by decide
  have hdescent : baseEnd_428305 < baseStart_428305 := by decide
  rcases family_descends (prefixWord ++ tailWord_428305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428324 : List Nat := [2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_428324 : Nat := 118140960795 + 428324 * 2 ^ 59
def prefixEnd_428324 : Nat := 4983230072969 + 3 ^ 40 * 428324 * 2
def baseEnd_428324 : Nat := 130332496507548097232699

theorem tailTrace_428324 : CollatzResearch.WordTrace tailWord_428324 prefixEnd_428324 130332496507548097232699 := by
  unfold tailWord_428324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7811129850131387380194013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10414839800175183173592017 7811129850131387380194013)
  ·
    refine ⟨2929173693799270267572755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7811129850131387380194013 2929173693799270267572755)
    ·
      refine ⟨4393760540698905401359133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2929173693799270267572755 4393760540698905401359133)
      ·
        refine ⟨1647660202762089525509675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4393760540698905401359133 1647660202762089525509675)
        ·
          refine ⟨2471490304143134288264513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647660202762089525509675 2471490304143134288264513)
          ·
            refine ⟨1853617728107350716198385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2471490304143134288264513 1853617728107350716198385)
            ·
              refine ⟨1390213296080513037148789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853617728107350716198385 1390213296080513037148789)
              ·
                refine ⟨130332496507548097232699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1390213296080513037148789 130332496507548097232699)
                ·
                  rfl

theorem cell19_428324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_428324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428324 prefixEnd_428324 := by exact prefixLift 428324
  have htrace : WordTrace (prefixWord ++ tailWord_428324) baseStart_428324 baseEnd_428324 := by
    simpa [prefixWord, tailWord_428324, baseEnd_428324] using wordTrace_append hprefix tailTrace_428324
  have hstable : (prefixWord ++ tailWord_428324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428324).length < 2 ^ (prefixWord ++ tailWord_428324).sum := by decide
  have hdescent : baseEnd_428324 < baseStart_428324 := by decide
  rcases family_descends (prefixWord ++ tailWord_428324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428356 : List Nat := [2, 3, 4, 1, 3, 1, 1, 4]
def baseStart_428356 : Nat := 118140960795 + 428356 * 2 ^ 59
def prefixEnd_428356 : Nat := 4983230072969 + 3 ^ 40 * 428356 * 2
def baseEnd_428356 : Nat := 130342233622181504521501

theorem tailTrace_428356 : CollatzResearch.WordTrace tailWord_428356 prefixEnd_428356 130342233622181504521501 := by
  unfold tailWord_428356
  simp only [CollatzResearch.WordTrace]
  refine ⟨7811713418073422112776461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10415617890764562817035281 7811713418073422112776461)
  ·
    refine ⟨2929392531777533292291173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7811713418073422112776461 2929392531777533292291173)
    ·
      refine ⟨549261099708287492304595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2929392531777533292291173 549261099708287492304595)
      ·
        refine ⟨823891649562431238456893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549261099708287492304595 823891649562431238456893)
        ·
          refine ⟨308959368585911714421335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 823891649562431238456893 308959368585911714421335)
          ·
            refine ⟨463439052878867571632003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308959368585911714421335 463439052878867571632003)
            ·
              refine ⟨695158579318301357448005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463439052878867571632003 695158579318301357448005)
              ·
                refine ⟨130342233622181504521501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 695158579318301357448005 130342233622181504521501)
                ·
                  rfl

theorem cell19_428356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_428356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428356 prefixEnd_428356 := by exact prefixLift 428356
  have htrace : WordTrace (prefixWord ++ tailWord_428356) baseStart_428356 baseEnd_428356 := by
    simpa [prefixWord, tailWord_428356, baseEnd_428356] using wordTrace_append hprefix tailTrace_428356
  have hstable : (prefixWord ++ tailWord_428356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428356).length < 2 ^ (prefixWord ++ tailWord_428356).sum := by decide
  have hdescent : baseEnd_428356 < baseStart_428356 := by decide
  rcases family_descends (prefixWord ++ tailWord_428356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428383 : List Nat := [1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_428383 : Nat := 118140960795 + 428383 * 2 ^ 59
def prefixEnd_428383 : Nat := 4983230072969 + 3 ^ 40 * 428383 * 2
def baseEnd_428383 : Nat := 130350449312653441921427

theorem tailTrace_428383 : CollatzResearch.WordTrace tailWord_428383 prefixEnd_428383 130350449312653441921427 := by
  unfold tailWord_428383
  simp only [CollatzResearch.WordTrace]
  refine ⟨15624411607049027836785803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10416274404699351891190535 15624411607049027836785803)
  ·
    refine ⟨23436617410573541755178705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15624411607049027836785803 23436617410573541755178705)
    ·
      refine ⟨17577463057930156316384029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23436617410573541755178705 17577463057930156316384029)
      ·
        refine ⟨6591548646723808618644011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17577463057930156316384029 6591548646723808618644011)
        ·
          refine ⟨9887322970085712927966017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6591548646723808618644011 9887322970085712927966017)
          ·
            refine ⟨7415492227564284695974513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9887322970085712927966017 7415492227564284695974513)
            ·
              refine ⟨5561619170673213521980885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415492227564284695974513 5561619170673213521980885)
              ·
                refine ⟨130350449312653441921427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5561619170673213521980885 130350449312653441921427)
                ·
                  rfl

theorem cell19_428383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_428383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428383 prefixEnd_428383 := by exact prefixLift 428383
  have htrace : WordTrace (prefixWord ++ tailWord_428383) baseStart_428383 baseEnd_428383 := by
    simpa [prefixWord, tailWord_428383, baseEnd_428383] using wordTrace_append hprefix tailTrace_428383
  have hstable : (prefixWord ++ tailWord_428383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428383).length < 2 ^ (prefixWord ++ tailWord_428383).sum := by decide
  have hdescent : baseEnd_428383 < baseStart_428383 := by decide
  rcases family_descends (prefixWord ++ tailWord_428383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428421 : List Nat := [1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_428421 : Nat := 118140960795 + 428421 * 2 ^ 59
def prefixEnd_428421 : Nat := 4983230072969 + 3 ^ 40 * 428421 * 2
def baseEnd_428421 : Nat := 130362012136280613076879

theorem tailTrace_428421 : CollatzResearch.WordTrace tailWord_428421 prefixEnd_428421 130362012136280613076879 := by
  unfold tailWord_428421
  simp only [CollatzResearch.WordTrace]
  refine ⟨15625797580911360326669117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10417198387274240217779411 15625797580911360326669117)
  ·
    refine ⟨5859674092841760122500919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15625797580911360326669117 5859674092841760122500919)
    ·
      refine ⟨8789511139262640183751379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5859674092841760122500919 8789511139262640183751379)
      ·
        refine ⟨13184266708893960275627069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8789511139262640183751379 13184266708893960275627069)
        ·
          refine ⟨4944100015835235103360151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13184266708893960275627069 4944100015835235103360151)
          ·
            refine ⟨7416150023752852655040227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4944100015835235103360151 7416150023752852655040227)
            ·
              refine ⟨11124225035629278982560341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7416150023752852655040227 11124225035629278982560341)
              ·
                refine ⟨130362012136280613076879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11124225035629278982560341 130362012136280613076879)
                ·
                  rfl

theorem cell19_428421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_428421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428421 prefixEnd_428421 := by exact prefixLift 428421
  have htrace : WordTrace (prefixWord ++ tailWord_428421) baseStart_428421 baseEnd_428421 := by
    simpa [prefixWord, tailWord_428421, baseEnd_428421] using wordTrace_append hprefix tailTrace_428421
  have hstable : (prefixWord ++ tailWord_428421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428421).length < 2 ^ (prefixWord ++ tailWord_428421).sum := by decide
  have hdescent : baseEnd_428421 < baseStart_428421 := by decide
  rcases family_descends (prefixWord ++ tailWord_428421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428436 : List Nat := [2, 4, 2, 1, 3, 1, 1, 5]
def baseStart_428436 : Nat := 118140960795 + 428436 * 2 ^ 59
def prefixEnd_428436 : Nat := 4983230072969 + 3 ^ 40 * 428436 * 2
def baseEnd_428436 : Nat := 130366576408765022743505

theorem tailTrace_428436 : CollatzResearch.WordTrace tailWord_428436 prefixEnd_428436 130366576408765022743505 := by
  unfold tailWord_428436
  simp only [CollatzResearch.WordTrace]
  refine ⟨7813172337928508944232581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10417563117238011925643441 7813172337928508944232581)
  ·
    refine ⟨1464969813361595427043609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7813172337928508944232581 1464969813361595427043609)
    ·
      refine ⟨1098727360021196570282707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1464969813361595427043609 1098727360021196570282707)
      ·
        refine ⟨1648091040031794855424061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098727360021196570282707 1648091040031794855424061)
        ·
          refine ⟨618034140011923070784023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1648091040031794855424061 618034140011923070784023)
          ·
            refine ⟨927051210017884606176035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618034140011923070784023 927051210017884606176035)
            ·
              refine ⟨1390576815026826909264053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927051210017884606176035 1390576815026826909264053)
              ·
                refine ⟨130366576408765022743505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1390576815026826909264053 130366576408765022743505)
                ·
                  rfl

theorem cell19_428436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_428436 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428436 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428436 prefixEnd_428436 := by exact prefixLift 428436
  have htrace : WordTrace (prefixWord ++ tailWord_428436) baseStart_428436 baseEnd_428436 := by
    simpa [prefixWord, tailWord_428436, baseEnd_428436] using wordTrace_append hprefix tailTrace_428436
  have hstable : (prefixWord ++ tailWord_428436).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428436).length < 2 ^ (prefixWord ++ tailWord_428436).sum := by decide
  have hdescent : baseEnd_428436 < baseStart_428436 := by decide
  rcases family_descends (prefixWord ++ tailWord_428436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428476 : List Nat := [2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_428476 : Nat := 118140960795 + 428476 * 2 ^ 59
def prefixEnd_428476 : Nat := 4983230072969 + 3 ^ 40 * 428476 * 2
def baseEnd_428476 : Nat := 130378747802056781854507

theorem tailTrace_428476 : CollatzResearch.WordTrace tailWord_428476 prefixEnd_428476 130378747802056781854507 := by
  unfold tailWord_428476
  simp only [CollatzResearch.WordTrace]
  refine ⟨7813901797856052359960641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10418535730474736479947521 7813901797856052359960641)
  ·
    refine ⟨5860426348392039269970481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7813901797856052359960641 5860426348392039269970481)
    ·
      refine ⟨4395319761294029452477861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5860426348392039269970481 4395319761294029452477861)
      ·
        refine ⟨824122455242630522339599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4395319761294029452477861 824122455242630522339599)
        ·
          refine ⟨1236183682863945783509399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824122455242630522339599 1236183682863945783509399)
          ·
            refine ⟨1854275524295918675264099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236183682863945783509399 1854275524295918675264099)
            ·
              refine ⟨2781413286443878012896149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854275524295918675264099 2781413286443878012896149)
              ·
                refine ⟨130378747802056781854507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2781413286443878012896149 130378747802056781854507)
                ·
                  rfl

theorem cell19_428476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_428476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428476 prefixEnd_428476 := by exact prefixLift 428476
  have htrace : WordTrace (prefixWord ++ tailWord_428476) baseStart_428476 baseEnd_428476 := by
    simpa [prefixWord, tailWord_428476, baseEnd_428476] using wordTrace_append hprefix tailTrace_428476
  have hstable : (prefixWord ++ tailWord_428476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428476).length < 2 ^ (prefixWord ++ tailWord_428476).sum := by decide
  have hdescent : baseEnd_428476 < baseStart_428476 := by decide
  rcases family_descends (prefixWord ++ tailWord_428476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428609 : List Nat := [1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_428609 : Nat := 118140960795 + 428609 * 2 ^ 59
def prefixEnd_428609 : Nat := 4983230072969 + 3 ^ 40 * 428609 * 2
def baseEnd_428609 : Nat := 130419217684751880898589

theorem tailTrace_428609 : CollatzResearch.WordTrace tailWord_428609 prefixEnd_428609 130419217684751880898589 := by
  unfold tailWord_428609
  simp only [CollatzResearch.WordTrace]
  refine ⟨15632654504230268434512881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10421769669486845623008587 15632654504230268434512881)
  ·
    refine ⟨11724490878172701325884661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15632654504230268434512881 11724490878172701325884661)
    ·
      refine ⟨1099171019828690749301687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11724490878172701325884661 1099171019828690749301687)
      ·
        refine ⟨1648756529743036123952531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099171019828690749301687 1648756529743036123952531)
        ·
          refine ⟨2473134794614554185928797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648756529743036123952531 2473134794614554185928797)
          ·
            refine ⟨927425547980457819723299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2473134794614554185928797 927425547980457819723299)
            ·
              refine ⟨1391138321970686729584949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927425547980457819723299 1391138321970686729584949)
              ·
                refine ⟨130419217684751880898589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1391138321970686729584949 130419217684751880898589)
                ·
                  rfl

theorem cell19_428609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_428609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428609 prefixEnd_428609 := by exact prefixLift 428609
  have htrace : WordTrace (prefixWord ++ tailWord_428609) baseStart_428609 baseEnd_428609 := by
    simpa [prefixWord, tailWord_428609, baseEnd_428609] using wordTrace_append hprefix tailTrace_428609
  have hstable : (prefixWord ++ tailWord_428609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428609).length < 2 ^ (prefixWord ++ tailWord_428609).sum := by decide
  have hdescent : baseEnd_428609 < baseStart_428609 := by decide
  rcases family_descends (prefixWord ++ tailWord_428609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428628 : List Nat := [2, 4, 1, 1, 1, 5, 5]
def baseStart_428628 : Nat := 118140960795 + 428628 * 2 ^ 59
def prefixEnd_428628 : Nat := 4983230072969 + 3 ^ 40 * 428628 * 2
def baseEnd_428628 : Nat := 43474999698855155492105

theorem tailTrace_428628 : CollatzResearch.WordTrace tailWord_428628 prefixEnd_428628 43474999698855155492105 := by
  unfold tailWord_428628
  simp only [CollatzResearch.WordTrace]
  refine ⟨7816673745580717339727269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10422231660774289786303025 7816673745580717339727269)
  ·
    refine ⟨1465626327296384501198863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7816673745580717339727269 1465626327296384501198863)
    ·
      refine ⟨2198439490944576751798295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1465626327296384501198863 2198439490944576751798295)
      ·
        refine ⟨3297659236416865127697443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2198439490944576751798295 3297659236416865127697443)
        ·
          refine ⟨4946488854625297691546165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297659236416865127697443 4946488854625297691546165)
          ·
            refine ⟨463733330121121658582453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4946488854625297691546165 463733330121121658582453)
            ·
              refine ⟨43474999698855155492105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 463733330121121658582453 43474999698855155492105)
              ·
                rfl

theorem cell19_428628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_428628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428628 prefixEnd_428628 := by exact prefixLift 428628
  have htrace : WordTrace (prefixWord ++ tailWord_428628) baseStart_428628 baseEnd_428628 := by
    simpa [prefixWord, tailWord_428628, baseEnd_428628] using wordTrace_append hprefix tailTrace_428628
  have hstable : (prefixWord ++ tailWord_428628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428628).length < 2 ^ (prefixWord ++ tailWord_428628).sum := by decide
  have hdescent : baseEnd_428628 < baseStart_428628 := by decide
  rcases family_descends (prefixWord ++ tailWord_428628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428668 : List Nat := [2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_428668 : Nat := 118140960795 + 428668 * 2 ^ 59
def prefixEnd_428668 : Nat := 4983230072969 + 3 ^ 40 * 428668 * 2
def baseEnd_428668 : Nat := 130437170489857225587317

theorem tailTrace_428668 : CollatzResearch.WordTrace tailWord_428668 prefixEnd_428668 130437170489857225587317 := by
  unfold tailWord_428668
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817403205508260755455329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10423204274011014340607105 7817403205508260755455329)
  ·
    refine ⟨5863052404131195566591497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7817403205508260755455329 5863052404131195566591497)
    ·
      refine ⟨4397289303098396674943623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5863052404131195566591497 4397289303098396674943623)
      ·
        refine ⟨6595933954647595012415435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4397289303098396674943623 6595933954647595012415435)
        ·
          refine ⟨9893900931971392518623153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595933954647595012415435 9893900931971392518623153)
          ·
            refine ⟨7420425698978544388967365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9893900931971392518623153 7420425698978544388967365)
            ·
              refine ⟨1391329818558477072931381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7420425698978544388967365 1391329818558477072931381)
              ·
                refine ⟨130437170489857225587317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1391329818558477072931381 130437170489857225587317)
                ·
                  rfl

theorem cell19_428668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_428668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428668 prefixEnd_428668 := by exact prefixLift 428668
  have htrace : WordTrace (prefixWord ++ tailWord_428668) baseStart_428668 baseEnd_428668 := by
    simpa [prefixWord, tailWord_428668, baseEnd_428668] using wordTrace_append hprefix tailTrace_428668
  have hstable : (prefixWord ++ tailWord_428668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428668).length < 2 ^ (prefixWord ++ tailWord_428668).sum := by decide
  have hdescent : baseEnd_428668 < baseStart_428668 := by decide
  rcases family_descends (prefixWord ++ tailWord_428668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428723 : List Nat := [1, 1, 1, 2, 3, 5, 3, 3]
def baseStart_428723 : Nat := 118140960795 + 428723 * 2 ^ 59
def prefixEnd_428723 : Nat := 4983230072969 + 3 ^ 40 * 428723 * 2
def baseEnd_428723 : Nat := 130453906155633394364945

theorem tailTrace_428723 : CollatzResearch.WordTrace tailWord_428723 prefixEnd_428723 130453906155633394364945 := by
  unfold tailWord_428723
  simp only [CollatzResearch.WordTrace]
  refine ⟨15636812425817265904162823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10424541617211510602775215 15636812425817265904162823)
  ·
    refine ⟨23455218638725898856244235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15636812425817265904162823 23455218638725898856244235)
    ·
      refine ⟨35182827958088848284366353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23455218638725898856244235 35182827958088848284366353)
      ·
        refine ⟨26387120968566636213274765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35182827958088848284366353 26387120968566636213274765)
        ·
          refine ⟨9895170363212488579978037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26387120968566636213274765 9895170363212488579978037)
          ·
            refine ⟨927672221551170804372941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9895170363212488579978037 927672221551170804372941)
            ·
              refine ⟨347877083081689051639853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 927672221551170804372941 347877083081689051639853)
              ·
                refine ⟨130453906155633394364945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347877083081689051639853 130453906155633394364945)
                ·
                  rfl

theorem cell19_428723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 3].length) (baseStart_428723 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428723 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428723 prefixEnd_428723 := by exact prefixLift 428723
  have htrace : WordTrace (prefixWord ++ tailWord_428723) baseStart_428723 baseEnd_428723 := by
    simpa [prefixWord, tailWord_428723, baseEnd_428723] using wordTrace_append hprefix tailTrace_428723
  have hstable : (prefixWord ++ tailWord_428723).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428723).length < 2 ^ (prefixWord ++ tailWord_428723).sum := by decide
  have hdescent : baseEnd_428723 < baseStart_428723 := by decide
  rcases family_descends (prefixWord ++ tailWord_428723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428744 : List Nat := [2, 1, 3, 1, 2, 4, 6]
def baseStart_428744 : Nat := 118140960795 + 428744 * 2 ^ 59
def prefixEnd_428744 : Nat := 4983230072969 + 3 ^ 40 * 428744 * 2
def baseEnd_428744 : Nat := 43486765379037189299407

theorem tailTrace_428744 : CollatzResearch.WordTrace tailWord_428744 prefixEnd_428744 43486765379037189299407 := by
  unfold tailWord_428744
  simp only [CollatzResearch.WordTrace]
  refine ⟨7818789179370593245338643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10425052239160790993784857 7818789179370593245338643)
  ·
    refine ⟨11728183769055889868007965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7818789179370593245338643 11728183769055889868007965)
    ·
      refine ⟨4398068913395958700502987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11728183769055889868007965 4398068913395958700502987)
      ·
        refine ⟨6597103370093938050754481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4398068913395958700502987 6597103370093938050754481)
        ·
          refine ⟨4947827527570453538065861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6597103370093938050754481 4947827527570453538065861)
          ·
            refine ⟨927717661419460038387349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4947827527570453538065861 927717661419460038387349)
            ·
              refine ⟨43486765379037189299407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 927717661419460038387349 43486765379037189299407)
              ·
                rfl

theorem cell19_428744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_428744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428744 prefixEnd_428744 := by exact prefixLift 428744
  have htrace : WordTrace (prefixWord ++ tailWord_428744) baseStart_428744 baseEnd_428744 := by
    simpa [prefixWord, tailWord_428744, baseEnd_428744] using wordTrace_append hprefix tailTrace_428744
  have hstable : (prefixWord ++ tailWord_428744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428744).length < 2 ^ (prefixWord ++ tailWord_428744).sum := by decide
  have hdescent : baseEnd_428744 < baseStart_428744 := by decide
  rcases family_descends (prefixWord ++ tailWord_428744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428776 : List Nat := [2, 1, 4, 1, 5, 1, 2, 3]
def baseStart_428776 : Nat := 118140960795 + 428776 * 2 ^ 59
def prefixEnd_428776 : Nat := 4983230072969 + 3 ^ 40 * 428776 * 2
def baseEnd_428776 : Nat := 130470033251744975187023

theorem tailTrace_428776 : CollatzResearch.WordTrace tailWord_428776 prefixEnd_428776 130470033251744975187023 := by
  unfold tailWord_428776
  simp only [CollatzResearch.WordTrace]
  refine ⟨7819372747312627977921091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10425830329750170637228121 7819372747312627977921091)
  ·
    refine ⟨11729059120968941966881637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7819372747312627977921091 11729059120968941966881637)
    ·
      refine ⟨2199198585181676618790307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11729059120968941966881637 2199198585181676618790307)
      ·
        refine ⟨3298797877772514928185461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2199198585181676618790307 3298797877772514928185461)
        ·
          refine ⟨309262301041173274517387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3298797877772514928185461 309262301041173274517387)
          ·
            refine ⟨463893451561759911776081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309262301041173274517387 463893451561759911776081)
            ·
              refine ⟨347920088671319933832061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463893451561759911776081 347920088671319933832061)
              ·
                refine ⟨130470033251744975187023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347920088671319933832061 130470033251744975187023)
                ·
                  rfl

theorem cell19_428776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_428776 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428776 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428776 prefixEnd_428776 := by exact prefixLift 428776
  have htrace : WordTrace (prefixWord ++ tailWord_428776) baseStart_428776 baseEnd_428776 := by
    simpa [prefixWord, tailWord_428776, baseEnd_428776] using wordTrace_append hprefix tailTrace_428776
  have hstable : (prefixWord ++ tailWord_428776).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428776).length < 2 ^ (prefixWord ++ tailWord_428776).sum := by decide
  have hdescent : baseEnd_428776 < baseStart_428776 := by decide
  rcases family_descends (prefixWord ++ tailWord_428776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428854 : List Nat := [5, 1, 2, 2, 3, 6]
def baseStart_428854 : Nat := 118140960795 + 428854 * 2 ^ 59
def prefixEnd_428854 : Nat := 4983230072969 + 3 ^ 40 * 428854 * 2
def baseEnd_428854 : Nat := 14499307496518211717053

theorem tailTrace_428854 : CollatzResearch.WordTrace tailWord_428854 prefixEnd_428854 14499307496518211717053 := by
  unfold tailWord_428854
  simp only [CollatzResearch.WordTrace]
  refine ⟨977599399271417204823851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10427726925561783518121077 977599399271417204823851)
  ·
    refine ⟨1466399098907125807235777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 977599399271417204823851 1466399098907125807235777)
    ·
      refine ⟨1099799324180344355426833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1466399098907125807235777 1099799324180344355426833)
      ·
        refine ⟨824849493135258266570125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1099799324180344355426833 824849493135258266570125)
        ·
          refine ⟨309318559925721849963797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 824849493135258266570125 309318559925721849963797)
          ·
            refine ⟨14499307496518211717053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 309318559925721849963797 14499307496518211717053)
            ·
              rfl

theorem cell19_428854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 6].length) (baseStart_428854 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428854 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428854 prefixEnd_428854 := by exact prefixLift 428854
  have htrace : WordTrace (prefixWord ++ tailWord_428854) baseStart_428854 baseEnd_428854 := by
    simpa [prefixWord, tailWord_428854, baseEnd_428854] using wordTrace_append hprefix tailTrace_428854
  have hstable : (prefixWord ++ tailWord_428854).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428854).length < 2 ^ (prefixWord ++ tailWord_428854).sum := by decide
  have hdescent : baseEnd_428854 < baseStart_428854 := by decide
  rcases family_descends (prefixWord ++ tailWord_428854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428858 : List Nat := [3, 1, 1, 1, 6, 7]
def baseStart_428858 : Nat := 118140960795 + 428858 * 2 ^ 59
def prefixEnd_428858 : Nat := 4983230072969 + 3 ^ 40 * 428858 * 2
def baseEnd_428858 : Nat := 14499442734221453484953

theorem tailTrace_428858 : CollatzResearch.WordTrace tailWord_428858 prefixEnd_428858 14499442734221453484953 := by
  unfold tailWord_428858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3910434070082045990081807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10427824186885455973551485 3910434070082045990081807)
  ·
    refine ⟨5865651105123068985122711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3910434070082045990081807 5865651105123068985122711)
    ·
      refine ⟨8798476657684603477684067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5865651105123068985122711 8798476657684603477684067)
      ·
        refine ⟨13197714986526905216526101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8798476657684603477684067 13197714986526905216526101)
        ·
          refine ⟨618642889993448682024661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13197714986526905216526101 618642889993448682024661)
          ·
            refine ⟨14499442734221453484953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 618642889993448682024661 14499442734221453484953)
            ·
              rfl

theorem cell19_428858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 7].length) (baseStart_428858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428858 prefixEnd_428858 := by exact prefixLift 428858
  have htrace : WordTrace (prefixWord ++ tailWord_428858) baseStart_428858 baseEnd_428858 := by
    simpa [prefixWord, tailWord_428858, baseEnd_428858] using wordTrace_append hprefix tailTrace_428858
  have hstable : (prefixWord ++ tailWord_428858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428858).length < 2 ^ (prefixWord ++ tailWord_428858).sum := by decide
  have hdescent : baseEnd_428858 < baseStart_428858 := by decide
  rcases family_descends (prefixWord ++ tailWord_428858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428892 : List Nat := [2, 2, 4, 2, 1, 2, 3, 3]
def baseStart_428892 : Nat := 118140960795 + 428892 * 2 ^ 59
def prefixEnd_428892 : Nat := 4983230072969 + 3 ^ 40 * 428892 * 2
def baseEnd_428892 : Nat := 130505330292291076608929

theorem tailTrace_428892 : CollatzResearch.WordTrace tailWord_428892 prefixEnd_428892 130505330292291076608929 := by
  unfold tailWord_428892
  simp only [CollatzResearch.WordTrace]
  refine ⟨7821488181102503883532465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10428650908136671844709953 7821488181102503883532465)
  ·
    refine ⟨5866116135826877912649349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7821488181102503883532465 5866116135826877912649349)
    ·
      refine ⟨1099896775467539608621753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5866116135826877912649349 1099896775467539608621753)
      ·
        refine ⟨824922581600654706466315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1099896775467539608621753 824922581600654706466315)
        ·
          refine ⟨1237383872400982059699473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824922581600654706466315 1237383872400982059699473)
          ·
            refine ⟨928037904300736544774605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237383872400982059699473 928037904300736544774605)
            ·
              refine ⟨348014214112776204290477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 928037904300736544774605 348014214112776204290477)
              ·
                refine ⟨130505330292291076608929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348014214112776204290477 130505330292291076608929)
                ·
                  rfl

theorem cell19_428892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_428892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428892 prefixEnd_428892 := by exact prefixLift 428892
  have htrace : WordTrace (prefixWord ++ tailWord_428892) baseStart_428892 baseEnd_428892 := by
    simpa [prefixWord, tailWord_428892, baseEnd_428892] using wordTrace_append hprefix tailTrace_428892
  have hstable : (prefixWord ++ tailWord_428892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428892).length < 2 ^ (prefixWord ++ tailWord_428892).sum := by decide
  have hdescent : baseEnd_428892 < baseStart_428892 := by decide
  rcases family_descends (prefixWord ++ tailWord_428892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428989 : List Nat := [1, 4, 1, 2, 4, 1, 2, 4]
def baseStart_428989 : Nat := 118140960795 + 428989 * 2 ^ 59
def prefixEnd_428989 : Nat := 4983230072969 + 3 ^ 40 * 428989 * 2
def baseEnd_428989 : Nat := 130534845921023592453109

theorem tailTrace_428989 : CollatzResearch.WordTrace tailWord_428989 prefixEnd_428989 130534845921023592453109 := by
  unfold tailWord_428989
  simp only [CollatzResearch.WordTrace]
  refine ⟨15646514242853593333346021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10431009495235728888897347 15646514242853593333346021)
  ·
    refine ⟨2933721420535048750002379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15646514242853593333346021 2933721420535048750002379)
    ·
      refine ⟨4400582130802573125003569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2933721420535048750002379 4400582130802573125003569)
      ·
        refine ⟨3300436598101929843752677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4400582130802573125003569 3300436598101929843752677)
        ·
          refine ⟨618831862144111845703627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3300436598101929843752677 618831862144111845703627)
          ·
            refine ⟨928247793216167768555441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618831862144111845703627 928247793216167768555441)
            ·
              refine ⟨696185844912125826416581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928247793216167768555441 696185844912125826416581)
              ·
                refine ⟨130534845921023592453109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 696185844912125826416581 130534845921023592453109)
                ·
                  rfl

theorem cell19_428989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_428989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_428989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_428989 prefixEnd_428989 := by exact prefixLift 428989
  have htrace : WordTrace (prefixWord ++ tailWord_428989) baseStart_428989 baseEnd_428989 := by
    simpa [prefixWord, tailWord_428989, baseEnd_428989] using wordTrace_append hprefix tailTrace_428989
  have hstable : (prefixWord ++ tailWord_428989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428989).length < 2 ^ (prefixWord ++ tailWord_428989).sum := by decide
  have hdescent : baseEnd_428989 < baseStart_428989 := by decide
  rcases family_descends (prefixWord ++ tailWord_428989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429029 : List Nat := [1, 3, 1, 6, 8]
def baseStart_429029 : Nat := 118140960795 + 429029 * 2 ^ 59
def prefixEnd_429029 : Nat := 4983230072969 + 3 ^ 40 * 429029 * 2
def baseEnd_429029 : Nat := 4835074715345013020893

theorem tailTrace_429029 : CollatzResearch.WordTrace tailWord_429029 prefixEnd_429029 4835074715345013020893 := by
  unfold tailWord_429029
  simp only [CollatzResearch.WordTrace]
  refine ⟨15647973162708680164802141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10431982108472453443201427 15647973162708680164802141)
  ·
    refine ⟨5867989936015755061800803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15647973162708680164802141 5867989936015755061800803)
    ·
      refine ⟨8801984904023632592701205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5867989936015755061800803 8801984904023632592701205)
      ·
        refine ⟨412593042376107777782869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8801984904023632592701205 412593042376107777782869)
        ·
          refine ⟨4835074715345013020893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 412593042376107777782869 4835074715345013020893)
          ·
            rfl

theorem cell19_429029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 8].length) (baseStart_429029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429029 prefixEnd_429029 := by exact prefixLift 429029
  have htrace : WordTrace (prefixWord ++ tailWord_429029) baseStart_429029 baseEnd_429029 := by
    simpa [prefixWord, tailWord_429029, baseEnd_429029] using wordTrace_append hprefix tailTrace_429029
  have hstable : (prefixWord ++ tailWord_429029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429029).length < 2 ^ (prefixWord ++ tailWord_429029).sum := by decide
  have hdescent : baseEnd_429029 < baseStart_429029 := by decide
  rcases family_descends (prefixWord ++ tailWord_429029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429042 : List Nat := [3, 2, 1, 5, 2, 1, 1, 4]
def baseStart_429042 : Nat := 118140960795 + 429042 * 2 ^ 59
def prefixEnd_429042 : Nat := 4983230072969 + 3 ^ 40 * 429042 * 2
def baseEnd_429042 : Nat := 130550973017135173275187

theorem tailTrace_429042 : CollatzResearch.WordTrace tailWord_429042 prefixEnd_429042 130550973017135173275187 := by
  unfold tailWord_429042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3912111827915395846256345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10432298207774388923350253 3912111827915395846256345)
  ·
    refine ⟨2934083870936546884692259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3912111827915395846256345 2934083870936546884692259)
    ·
      refine ⟨4401125806404820327038389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934083870936546884692259 4401125806404820327038389)
      ·
        refine ⟨412605544350451905659849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4401125806404820327038389 412605544350451905659849)
        ·
          refine ⟨309454158262838929244887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412605544350451905659849 309454158262838929244887)
          ·
            refine ⟨464181237394258393867331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309454158262838929244887 464181237394258393867331)
            ·
              refine ⟨696271856091387590800997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464181237394258393867331 696271856091387590800997)
              ·
                refine ⟨130550973017135173275187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 696271856091387590800997 130550973017135173275187)
                ·
                  rfl

theorem cell19_429042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_429042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429042 prefixEnd_429042 := by exact prefixLift 429042
  have htrace : WordTrace (prefixWord ++ tailWord_429042) baseStart_429042 baseEnd_429042 := by
    simpa [prefixWord, tailWord_429042, baseEnd_429042] using wordTrace_append hprefix tailTrace_429042
  have hstable : (prefixWord ++ tailWord_429042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429042).length < 2 ^ (prefixWord ++ tailWord_429042).sum := by decide
  have hdescent : baseEnd_429042 < baseStart_429042 := by decide
  rcases family_descends (prefixWord ++ tailWord_429042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429046 : List Nat := [5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_429046 : Nat := 118140960795 + 429046 * 2 ^ 59
def prefixEnd_429046 : Nat := 4983230072969 + 3 ^ 40 * 429046 * 2
def baseEnd_429046 : Nat := 130552190156464349186287

theorem tailTrace_429046 : CollatzResearch.WordTrace tailWord_429046 prefixEnd_429046 130552190156464349186287 := by
  unfold tailWord_429046
  simp only [CollatzResearch.WordTrace]
  refine ⟨978037075227943254260687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10432395469098061378780661 978037075227943254260687)
  ·
    refine ⟨1467055612841914881391031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 978037075227943254260687 1467055612841914881391031)
    ·
      refine ⟨2200583419262872322086547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1467055612841914881391031 2200583419262872322086547)
      ·
        refine ⟨3300875128894308483129821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200583419262872322086547 3300875128894308483129821)
        ·
          refine ⟨1237828173335365681173683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3300875128894308483129821 1237828173335365681173683)
          ·
            refine ⟨1856742260003048521760525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237828173335365681173683 1856742260003048521760525)
            ·
              refine ⟨696278347501143195660197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1856742260003048521760525 696278347501143195660197)
              ·
                refine ⟨130552190156464349186287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 696278347501143195660197 130552190156464349186287)
                ·
                  rfl

theorem cell19_429046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_429046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429046 prefixEnd_429046 := by exact prefixLift 429046
  have htrace : WordTrace (prefixWord ++ tailWord_429046) baseStart_429046 baseEnd_429046 := by
    simpa [prefixWord, tailWord_429046, baseEnd_429046] using wordTrace_append hprefix tailTrace_429046
  have hstable : (prefixWord ++ tailWord_429046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429046).length < 2 ^ (prefixWord ++ tailWord_429046).sum := by decide
  have hdescent : baseEnd_429046 < baseStart_429046 := by decide
  rcases family_descends (prefixWord ++ tailWord_429046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429107 : List Nat := [1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_429107 : Nat := 118140960795 + 429107 * 2 ^ 59
def prefixEnd_429107 : Nat := 4983230072969 + 3 ^ 40 * 429107 * 2
def baseEnd_429107 : Nat := 130570751531234281830565

theorem tailTrace_429107 : CollatzResearch.WordTrace tailWord_429107 prefixEnd_429107 130570751531234281830565 := by
  unfold tailWord_429107
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650818056426099486141575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10433878704284066324094383 15650818056426099486141575)
  ·
    refine ⟨23476227084639149229212363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15650818056426099486141575 23476227084639149229212363)
    ·
      refine ⟨35214340626958723843818545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23476227084639149229212363 35214340626958723843818545)
      ·
        refine ⟨26410755470219042882863909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35214340626958723843818545 26410755470219042882863909)
        ·
          refine ⟨4952016650666070540536983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26410755470219042882863909 4952016650666070540536983)
          ·
            refine ⟨7428024975999105810805475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952016650666070540536983 7428024975999105810805475)
            ·
              refine ⟨11142037463998658716208213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428024975999105810805475 11142037463998658716208213)
              ·
                refine ⟨130570751531234281830565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11142037463998658716208213 130570751531234281830565)
                ·
                  rfl

theorem cell19_429107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_429107 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429107 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429107 prefixEnd_429107 := by exact prefixLift 429107
  have htrace : WordTrace (prefixWord ++ tailWord_429107) baseStart_429107 baseEnd_429107 := by
    simpa [prefixWord, tailWord_429107, baseEnd_429107] using wordTrace_append hprefix tailTrace_429107
  have hstable : (prefixWord ++ tailWord_429107).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429107).length < 2 ^ (prefixWord ++ tailWord_429107).sum := by decide
  have hdescent : baseEnd_429107 < baseStart_429107 := by decide
  rcases family_descends (prefixWord ++ tailWord_429107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429162 : List Nat := [3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_429162 : Nat := 118140960795 + 429162 * 2 ^ 59
def prefixEnd_429162 : Nat := 4983230072969 + 3 ^ 40 * 429162 * 2
def baseEnd_429162 : Nat := 130587487197010450608193

theorem tailTrace_429162 : CollatzResearch.WordTrace tailWord_429162 prefixEnd_429162 130587487197010450608193 := by
  unfold tailWord_429162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3913206017806710969848435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10435216047484562586262493 3913206017806710969848435)
  ·
    refine ⟨5869809026710066454772653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3913206017806710969848435 5869809026710066454772653)
    ·
      refine ⟨2201178385016274920539745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5869809026710066454772653 2201178385016274920539745)
      ·
        refine ⟨1650883788762206190404809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2201178385016274920539745 1650883788762206190404809)
        ·
          refine ⟨1238162841571654642803607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1650883788762206190404809 1238162841571654642803607)
          ·
            refine ⟨1857244262357481964205411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238162841571654642803607 1857244262357481964205411)
            ·
              refine ⟨2785866393536222946308117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1857244262357481964205411 2785866393536222946308117)
              ·
                refine ⟨130587487197010450608193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2785866393536222946308117 130587487197010450608193)
                ·
                  rfl

theorem cell19_429162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_429162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429162 prefixEnd_429162 := by exact prefixLift 429162
  have htrace : WordTrace (prefixWord ++ tailWord_429162) baseStart_429162 baseEnd_429162 := by
    simpa [prefixWord, tailWord_429162, baseEnd_429162] using wordTrace_append hprefix tailTrace_429162
  have hstable : (prefixWord ++ tailWord_429162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429162).length < 2 ^ (prefixWord ++ tailWord_429162).sum := by decide
  have hdescent : baseEnd_429162 < baseStart_429162 := by decide
  rcases family_descends (prefixWord ++ tailWord_429162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429215 : List Nat := [1, 1, 2, 6, 3, 1, 1, 4]
def baseStart_429215 : Nat := 118140960795 + 429215 * 2 ^ 59
def prefixEnd_429215 : Nat := 4983230072969 + 3 ^ 40 * 429215 * 2
def baseEnd_429215 : Nat := 130603614293122031430271

theorem tailTrace_429215 : CollatzResearch.WordTrace tailWord_429215 prefixEnd_429215 130603614293122031430271 := by
  unfold tailWord_429215
  simp only [CollatzResearch.WordTrace]
  refine ⟨15654757140034833931073099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10436504760023222620715399 15654757140034833931073099)
  ·
    refine ⟨23482135710052250896609649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15654757140034833931073099 23482135710052250896609649)
    ·
      refine ⟨17611601782539188172457237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23482135710052250896609649 17611601782539188172457237)
      ·
        refine ⟨825543833556524445583933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17611601782539188172457237 825543833556524445583933)
        ·
          refine ⟨309578937583696667093975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 825543833556524445583933 309578937583696667093975)
          ·
            refine ⟨464368406375545000640963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309578937583696667093975 464368406375545000640963)
            ·
              refine ⟨696552609563317500961445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464368406375545000640963 696552609563317500961445)
              ·
                refine ⟨130603614293122031430271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 696552609563317500961445 130603614293122031430271)
                ·
                  rfl

theorem cell19_429215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 4].length) (baseStart_429215 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429215 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429215 prefixEnd_429215 := by exact prefixLift 429215
  have htrace : WordTrace (prefixWord ++ tailWord_429215) baseStart_429215 baseEnd_429215 := by
    simpa [prefixWord, tailWord_429215, baseEnd_429215] using wordTrace_append hprefix tailTrace_429215
  have hstable : (prefixWord ++ tailWord_429215).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429215).length < 2 ^ (prefixWord ++ tailWord_429215).sum := by decide
  have hdescent : baseEnd_429215 < baseStart_429215 := by decide
  rcases family_descends (prefixWord ++ tailWord_429215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429293 : List Nat := [1, 5, 1, 2, 2, 1, 4, 3]
def baseStart_429293 : Nat := 118140960795 + 429293 * 2 ^ 59
def prefixEnd_429293 : Nat := 4983230072969 + 3 ^ 40 * 429293 * 2
def baseEnd_429293 : Nat := 130627348510040961696725

theorem tailTrace_429293 : CollatzResearch.WordTrace tailWord_429293 prefixEnd_429293 130627348510040961696725 := by
  unfold tailWord_429293
  simp only [CollatzResearch.WordTrace]
  refine ⟨15657602033752253252412533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10438401355834835501608355 15657602033752253252412533)
  ·
    refine ⟨1467900190664273742413675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15657602033752253252412533 1467900190664273742413675)
    ·
      refine ⟨2201850285996410613620513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1467900190664273742413675 2201850285996410613620513)
      ·
        refine ⟨1651387714497307960215385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2201850285996410613620513 1651387714497307960215385)
        ·
          refine ⟨1238540785872980970161539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1651387714497307960215385 1238540785872980970161539)
          ·
            refine ⟨1857811178809471455242309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238540785872980970161539 1857811178809471455242309)
            ·
              refine ⟨348339596026775897857933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1857811178809471455242309 348339596026775897857933)
              ·
                refine ⟨130627348510040961696725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348339596026775897857933 130627348510040961696725)
                ·
                  rfl

theorem cell19_429293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 3].length) (baseStart_429293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429293 prefixEnd_429293 := by exact prefixLift 429293
  have htrace : WordTrace (prefixWord ++ tailWord_429293) baseStart_429293 baseEnd_429293 := by
    simpa [prefixWord, tailWord_429293, baseEnd_429293] using wordTrace_append hprefix tailTrace_429293
  have hstable : (prefixWord ++ tailWord_429293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429293).length < 2 ^ (prefixWord ++ tailWord_429293).sum := by decide
  have hdescent : baseEnd_429293 < baseStart_429293 := by decide
  rcases family_descends (prefixWord ++ tailWord_429293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429295 : List Nat := [1, 1, 2, 1, 7, 1, 1, 5]
def baseStart_429295 : Nat := 118140960795 + 429295 * 2 ^ 59
def prefixEnd_429295 : Nat := 4983230072969 + 3 ^ 40 * 429295 * 2
def baseEnd_429295 : Nat := 130627957079705549652275

theorem tailTrace_429295 : CollatzResearch.WordTrace tailWord_429295 prefixEnd_429295 130627957079705549652275 := by
  unfold tailWord_429295
  simp only [CollatzResearch.WordTrace]
  refine ⟨15657674979745007593985339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10438449986496671729323559 15657674979745007593985339)
  ·
    refine ⟨23486512469617511390978009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15657674979745007593985339 23486512469617511390978009)
    ·
      refine ⟨17614884352213133543233507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23486512469617511390978009 17614884352213133543233507)
      ·
        refine ⟨26422326528319700314850261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17614884352213133543233507 26422326528319700314850261)
        ·
          refine ⟨619273278007492976129303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26422326528319700314850261 619273278007492976129303)
          ·
            refine ⟨928909917011239464193955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619273278007492976129303 928909917011239464193955)
            ·
              refine ⟨1393364875516859196290933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928909917011239464193955 1393364875516859196290933)
              ·
                refine ⟨130627957079705549652275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1393364875516859196290933 130627957079705549652275)
                ·
                  rfl

theorem cell19_429295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_429295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429295 prefixEnd_429295 := by exact prefixLift 429295
  have htrace : WordTrace (prefixWord ++ tailWord_429295) baseStart_429295 baseEnd_429295 := by
    simpa [prefixWord, tailWord_429295, baseEnd_429295] using wordTrace_append hprefix tailTrace_429295
  have hstable : (prefixWord ++ tailWord_429295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429295).length < 2 ^ (prefixWord ++ tailWord_429295).sum := by decide
  have hdescent : baseEnd_429295 < baseStart_429295 := by decide
  rcases family_descends (prefixWord ++ tailWord_429295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429352 : List Nat := [2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_429352 : Nat := 118140960795 + 429352 * 2 ^ 59
def prefixEnd_429352 : Nat := 4983230072969 + 3 ^ 40 * 429352 * 2
def baseEnd_429352 : Nat := 130645301315146306385453

theorem tailTrace_429352 : CollatzResearch.WordTrace tailWord_429352 prefixEnd_429352 130645301315146306385453 := by
  unfold tailWord_429352
  simp only [CollatzResearch.WordTrace]
  refine ⟨7829876970269253164405155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10439835960359004219206873 7829876970269253164405155)
  ·
    refine ⟨11744815455403879746607733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7829876970269253164405155 11744815455403879746607733)
    ·
      refine ⟨1101076448944113726244475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11744815455403879746607733 1101076448944113726244475)
      ·
        refine ⟨1651614673416170589366713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1101076448944113726244475 1651614673416170589366713)
        ·
          refine ⟨1238711005062127942025035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1651614673416170589366713 1238711005062127942025035)
          ·
            refine ⟨1858066507593191913037553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238711005062127942025035 1858066507593191913037553)
            ·
              refine ⟨1393549880694893934778165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858066507593191913037553 1393549880694893934778165)
              ·
                refine ⟨130645301315146306385453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1393549880694893934778165 130645301315146306385453)
                ·
                  rfl

theorem cell19_429352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_429352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429352 prefixEnd_429352 := by exact prefixLift 429352
  have htrace : WordTrace (prefixWord ++ tailWord_429352) baseStart_429352 baseEnd_429352 := by
    simpa [prefixWord, tailWord_429352, baseEnd_429352] using wordTrace_append hprefix tailTrace_429352
  have hstable : (prefixWord ++ tailWord_429352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429352).length < 2 ^ (prefixWord ++ tailWord_429352).sum := by decide
  have hdescent : baseEnd_429352 < baseStart_429352 := by decide
  rcases family_descends (prefixWord ++ tailWord_429352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429382 : List Nat := [6, 1, 1, 3, 2, 1, 1, 4]
def baseStart_429382 : Nat := 118140960795 + 429382 * 2 ^ 59
def prefixEnd_429382 : Nat := 4983230072969 + 3 ^ 40 * 429382 * 2
def baseEnd_429382 : Nat := 130654429860115125718705

theorem tailTrace_429382 : CollatzResearch.WordTrace tailWord_429382 prefixEnd_429382 130654429860115125718705 := by
  unfold tailWord_429382
  simp only [CollatzResearch.WordTrace]
  refine ⟨489401504075931920387575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10440565420286547634934933 489401504075931920387575)
  ·
    refine ⟨734102256113897880581363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 489401504075931920387575 734102256113897880581363)
    ·
      refine ⟨1101153384170846820872045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 734102256113897880581363 1101153384170846820872045)
      ·
        refine ⟨412932519064067557827017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1101153384170846820872045 412932519064067557827017)
        ·
          refine ⟨309699389298050668370263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412932519064067557827017 309699389298050668370263)
          ·
            refine ⟨464549083947076002555395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309699389298050668370263 464549083947076002555395)
            ·
              refine ⟨696823625920614003833093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464549083947076002555395 696823625920614003833093)
              ·
                refine ⟨130654429860115125718705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 696823625920614003833093 130654429860115125718705)
                ·
                  rfl

theorem cell19_429382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_429382 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429382 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429382 prefixEnd_429382 := by exact prefixLift 429382
  have htrace : WordTrace (prefixWord ++ tailWord_429382) baseStart_429382 baseEnd_429382 := by
    simpa [prefixWord, tailWord_429382, baseEnd_429382] using wordTrace_append hprefix tailTrace_429382
  have hstable : (prefixWord ++ tailWord_429382).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429382).length < 2 ^ (prefixWord ++ tailWord_429382).sum := by decide
  have hdescent : baseEnd_429382 < baseStart_429382 := by decide
  rcases family_descends (prefixWord ++ tailWord_429382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429485 : List Nat := [1, 5, 2, 2, 1, 1, 7]
def baseStart_429485 : Nat := 118140960795 + 429485 * 2 ^ 59
def prefixEnd_429485 : Nat := 4983230072969 + 3 ^ 40 * 429485 * 2
def baseEnd_429485 : Nat := 43561923732613801809845

theorem tailTrace_429485 : CollatzResearch.WordTrace tailWord_429485 prefixEnd_429485 43561923732613801809845 := by
  unfold tailWord_429485
  simp only [CollatzResearch.WordTrace]
  refine ⟨15664604849056670043401909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10443069899371113362267939 15664604849056670043401909)
  ·
    refine ⟨1468556704599062816568929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15664604849056670043401909 1468556704599062816568929)
    ·
      refine ⟨1101417528449297112426697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1468556704599062816568929 1101417528449297112426697)
      ·
        refine ⟨826063146336972834320023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1101417528449297112426697 826063146336972834320023)
        ·
          refine ⟨1239094719505459251480035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826063146336972834320023 1239094719505459251480035)
          ·
            refine ⟨1858642079258188877220053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239094719505459251480035 1858642079258188877220053)
            ·
              refine ⟨43561923732613801809845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1858642079258188877220053 43561923732613801809845)
              ·
                rfl

theorem cell19_429485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_429485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429485 prefixEnd_429485 := by exact prefixLift 429485
  have htrace : WordTrace (prefixWord ++ tailWord_429485) baseStart_429485 baseEnd_429485 := by
    simpa [prefixWord, tailWord_429485, baseEnd_429485] using wordTrace_append hprefix tailTrace_429485
  have hstable : (prefixWord ++ tailWord_429485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429485).length < 2 ^ (prefixWord ++ tailWord_429485).sum := by decide
  have hdescent : baseEnd_429485 < baseStart_429485 := by decide
  rcases family_descends (prefixWord ++ tailWord_429485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429525 : List Nat := [1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_429525 : Nat := 118140960795 + 429525 * 2 ^ 59
def prefixEnd_429525 : Nat := 4983230072969 + 3 ^ 40 * 429525 * 2
def baseEnd_429525 : Nat := 130697942591133164540537

theorem tailTrace_429525 : CollatzResearch.WordTrace tailWord_429525 prefixEnd_429525 130697942591133164540537 := by
  unfold tailWord_429525
  simp only [CollatzResearch.WordTrace]
  refine ⟨15666063768911756874858029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10444042512607837916572019 15666063768911756874858029)
  ·
    refine ⟨5874773913341908828071761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15666063768911756874858029 5874773913341908828071761)
    ·
      refine ⟨4406080435006431621053821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5874773913341908828071761 4406080435006431621053821)
      ·
        refine ⟨1652280163127411857895183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4406080435006431621053821 1652280163127411857895183)
        ·
          refine ⟨2478420244691117786842775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652280163127411857895183 2478420244691117786842775)
          ·
            refine ⟨3717630367036676680264163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478420244691117786842775 3717630367036676680264163)
            ·
              refine ⟨5576445550555015020396245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3717630367036676680264163 5576445550555015020396245)
              ·
                refine ⟨130697942591133164540537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5576445550555015020396245 130697942591133164540537)
                ·
                  rfl

theorem cell19_429525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_429525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429525 prefixEnd_429525 := by exact prefixLift 429525
  have htrace : WordTrace (prefixWord ++ tailWord_429525) baseStart_429525 baseEnd_429525 := by
    simpa [prefixWord, tailWord_429525, baseEnd_429525] using wordTrace_append hprefix tailTrace_429525
  have hstable : (prefixWord ++ tailWord_429525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429525).length < 2 ^ (prefixWord ++ tailWord_429525).sum := by decide
  have hdescent : baseEnd_429525 < baseStart_429525 := by decide
  rcases family_descends (prefixWord ++ tailWord_429525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429601 : List Nat := [1, 2, 3, 2, 2, 3, 6]
def baseStart_429601 : Nat := 118140960795 + 429601 * 2 ^ 59
def prefixEnd_429601 : Nat := 4983230072969 + 3 ^ 40 * 429601 * 2
def baseEnd_429601 : Nat := 43573689412795835617147

theorem tailTrace_429601 : CollatzResearch.WordTrace tailWord_429601 prefixEnd_429601 43573689412795835617147 := by
  unfold tailWord_429601
  simp only [CollatzResearch.WordTrace]
  refine ⟨15668835716636421854624657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10445890477757614569749771 15668835716636421854624657)
  ·
    refine ⟨11751626787477316390968493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15668835716636421854624657 11751626787477316390968493)
    ·
      refine ⟨4406860045303993646613185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11751626787477316390968493 4406860045303993646613185)
      ·
        refine ⟨3305145033977995234959889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4406860045303993646613185 3305145033977995234959889)
        ·
          refine ⟨2478858775483496426219917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3305145033977995234959889 2478858775483496426219917)
          ·
            refine ⟨929572040806311159832469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2478858775483496426219917 929572040806311159832469)
            ·
              refine ⟨43573689412795835617147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 929572040806311159832469 43573689412795835617147)
              ·
                rfl

theorem cell19_429601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_429601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429601 prefixEnd_429601 := by exact prefixLift 429601
  have htrace : WordTrace (prefixWord ++ tailWord_429601) baseStart_429601 baseEnd_429601 := by
    simpa [prefixWord, tailWord_429601, baseEnd_429601] using wordTrace_append hprefix tailTrace_429601
  have hstable : (prefixWord ++ tailWord_429601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429601).length < 2 ^ (prefixWord ++ tailWord_429601).sum := by decide
  have hdescent : baseEnd_429601 < baseStart_429601 := by decide
  rcases family_descends (prefixWord ++ tailWord_429601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429732 : List Nat := [2, 3, 1, 2, 2, 4, 1, 4]
def baseStart_429732 : Nat := 118140960795 + 429732 * 2 ^ 59
def prefixEnd_429732 : Nat := 4983230072969 + 3 ^ 40 * 429732 * 2
def baseEnd_429732 : Nat := 130760929551418017939973

theorem tailTrace_429732 : CollatzResearch.WordTrace tailWord_429732 prefixEnd_429732 130760929551418017939973 := by
  unfold tailWord_429732
  simp only [CollatzResearch.WordTrace]
  refine ⟨7836806839580915613821725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10449075786107887485095633 7836806839580915613821725)
  ·
    refine ⟨2938802564842843355183147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7836806839580915613821725 2938802564842843355183147)
    ·
      refine ⟨4408203847264265032774721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2938802564842843355183147 4408203847264265032774721)
      ·
        refine ⟨3306152885448198774581041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4408203847264265032774721 3306152885448198774581041)
        ·
          refine ⟨2479614664086149080935781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3306152885448198774581041 2479614664086149080935781)
          ·
            refine ⟨464927749516152952675459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2479614664086149080935781 464927749516152952675459)
            ·
              refine ⟨697391624274229429013189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464927749516152952675459 697391624274229429013189)
              ·
                refine ⟨130760929551418017939973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697391624274229429013189 130760929551418017939973)
                ·
                  rfl

theorem cell19_429732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_429732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429732 prefixEnd_429732 := by exact prefixLift 429732
  have htrace : WordTrace (prefixWord ++ tailWord_429732) baseStart_429732 baseEnd_429732 := by
    simpa [prefixWord, tailWord_429732, baseEnd_429732] using wordTrace_append hprefix tailTrace_429732
  have hstable : (prefixWord ++ tailWord_429732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429732).length < 2 ^ (prefixWord ++ tailWord_429732).sum := by decide
  have hdescent : baseEnd_429732 < baseStart_429732 := by decide
  rcases family_descends (prefixWord ++ tailWord_429732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429749 : List Nat := [1, 3, 3, 3, 2, 1, 3, 3]
def baseStart_429749 : Nat := 118140960795 + 429749 * 2 ^ 59
def prefixEnd_429749 : Nat := 4983230072969 + 3 ^ 40 * 429749 * 2
def baseEnd_429749 : Nat := 130766102393567015562149

theorem tailTrace_429749 : CollatzResearch.WordTrace tailWord_429749 prefixEnd_429749 130766102393567015562149 := by
  unfold tailWord_429749
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674233720100243131012301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10449489146733495420674867 15674233720100243131012301)
  ·
    refine ⟨5877837645037591174129613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15674233720100243131012301 5877837645037591174129613)
    ·
      refine ⟨2204189116889096690298605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5877837645037591174129613 2204189116889096690298605)
      ·
        refine ⟨826570918833411258861977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2204189116889096690298605 826570918833411258861977)
        ·
          refine ⟨619928189125058444146483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826570918833411258861977 619928189125058444146483)
          ·
            refine ⟨929892283687587666219725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619928189125058444146483 929892283687587666219725)
            ·
              refine ⟨348709606382845374832397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 929892283687587666219725 348709606382845374832397)
              ·
                refine ⟨130766102393567015562149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348709606382845374832397 130766102393567015562149)
                ·
                  rfl

theorem cell19_429749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 3].length) (baseStart_429749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429749 prefixEnd_429749 := by exact prefixLift 429749
  have htrace : WordTrace (prefixWord ++ tailWord_429749) baseStart_429749 baseEnd_429749 := by
    simpa [prefixWord, tailWord_429749, baseEnd_429749] using wordTrace_append hprefix tailTrace_429749
  have hstable : (prefixWord ++ tailWord_429749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429749).length < 2 ^ (prefixWord ++ tailWord_429749).sum := by decide
  have hdescent : baseEnd_429749 < baseStart_429749 := by decide
  rcases family_descends (prefixWord ++ tailWord_429749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429751 : List Nat := [1, 1, 3, 1, 5, 2, 3, 3]
def baseStart_429751 : Nat := 118140960795 + 429751 * 2 ^ 59
def prefixEnd_429751 : Nat := 4983230072969 + 3 ^ 40 * 429751 * 2
def baseEnd_429751 : Nat := 130766710963231603517699

theorem tailTrace_429751 : CollatzResearch.WordTrace tailWord_429751 prefixEnd_429751 130766710963231603517699 := by
  unfold tailWord_429751
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674306666092997472585107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10449537777395331648390071 15674306666092997472585107)
  ·
    refine ⟨23511459999139496208877661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15674306666092997472585107 23511459999139496208877661)
    ·
      refine ⟨8816797499677311078329123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23511459999139496208877661 8816797499677311078329123)
      ·
        refine ⟨13225196249515966617493685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8816797499677311078329123 13225196249515966617493685)
        ·
          refine ⟨1239862148392121870390033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13225196249515966617493685 1239862148392121870390033)
          ·
            refine ⟨929896611294091402792525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1239862148392121870390033 929896611294091402792525)
            ·
              refine ⟨348711229235284276047197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 929896611294091402792525 348711229235284276047197)
              ·
                refine ⟨130766710963231603517699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348711229235284276047197 130766710963231603517699)
                ·
                  rfl

theorem cell19_429751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 3].length) (baseStart_429751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429751 prefixEnd_429751 := by exact prefixLift 429751
  have htrace : WordTrace (prefixWord ++ tailWord_429751) baseStart_429751 baseEnd_429751 := by
    simpa [prefixWord, tailWord_429751, baseEnd_429751] using wordTrace_append hprefix tailTrace_429751
  have hstable : (prefixWord ++ tailWord_429751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429751).length < 2 ^ (prefixWord ++ tailWord_429751).sum := by decide
  have hdescent : baseEnd_429751 < baseStart_429751 := by decide
  rcases family_descends (prefixWord ++ tailWord_429751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429755 : List Nat := [1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_429755 : Nat := 118140960795 + 429755 * 2 ^ 59
def prefixEnd_429755 : Nat := 4983230072969 + 3 ^ 40 * 429755 * 2
def baseEnd_429755 : Nat := 130767928102560779428799

theorem tailTrace_429755 : CollatzResearch.WordTrace tailWord_429755 prefixEnd_429755 130767928102560779428799 := by
  unfold tailWord_429755
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674452558078506155730719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10449635038719004103820479 15674452558078506155730719)
  ·
    refine ⟨23511678837117759233596079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15674452558078506155730719 23511678837117759233596079)
    ·
      refine ⟨35267518255676638850394119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23511678837117759233596079 35267518255676638850394119)
      ·
        refine ⟨52901277383514958275591179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35267518255676638850394119 52901277383514958275591179)
        ·
          refine ⟨79351916075272437413386769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52901277383514958275591179 79351916075272437413386769)
          ·
            refine ⟨59513937056454328060040077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79351916075272437413386769 59513937056454328060040077)
            ·
              refine ⟨22317726396170373022515029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59513937056454328060040077 22317726396170373022515029)
              ·
                refine ⟨130767928102560779428799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22317726396170373022515029 130767928102560779428799)
                ·
                  rfl

theorem cell19_429755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_429755 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429755 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429755 prefixEnd_429755 := by exact prefixLift 429755
  have htrace : WordTrace (prefixWord ++ tailWord_429755) baseStart_429755 baseEnd_429755 := by
    simpa [prefixWord, tailWord_429755, baseEnd_429755] using wordTrace_append hprefix tailTrace_429755
  have hstable : (prefixWord ++ tailWord_429755).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429755).length < 2 ^ (prefixWord ++ tailWord_429755).sum := by decide
  have hdescent : baseEnd_429755 < baseStart_429755 := by decide
  rcases family_descends (prefixWord ++ tailWord_429755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429810 : List Nat := [3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_429810 : Nat := 118140960795 + 429810 * 2 ^ 59
def prefixEnd_429810 : Nat := 4983230072969 + 3 ^ 40 * 429810 * 2
def baseEnd_429810 : Nat := 130784663768336948206427

theorem tailTrace_429810 : CollatzResearch.WordTrace tailWord_429810 prefixEnd_429810 130784663768336948206427 := by
  unfold tailWord_429810
  simp only [CollatzResearch.WordTrace]
  refine ⟨3919114643219812637245721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10450972381919500365988589 3919114643219812637245721)
  ·
    refine ⟨2939335982414859477934291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3919114643219812637245721 2939335982414859477934291)
    ·
      refine ⟨4409003973622289216901437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2939335982414859477934291 4409003973622289216901437)
      ·
        refine ⟨1653376490108358456338039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4409003973622289216901437 1653376490108358456338039)
        ·
          refine ⟨2480064735162537684507059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653376490108358456338039 2480064735162537684507059)
          ·
            refine ⟨3720097102743806526760589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480064735162537684507059 3720097102743806526760589)
            ·
              refine ⟨1395036413528927447535221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3720097102743806526760589 1395036413528927447535221)
              ·
                refine ⟨130784663768336948206427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1395036413528927447535221 130784663768336948206427)
                ·
                  rfl

theorem cell19_429810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_429810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429810 prefixEnd_429810 := by exact prefixLift 429810
  have htrace : WordTrace (prefixWord ++ tailWord_429810) baseStart_429810 baseEnd_429810 := by
    simpa [prefixWord, tailWord_429810, baseEnd_429810] using wordTrace_append hprefix tailTrace_429810
  have hstable : (prefixWord ++ tailWord_429810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429810).length < 2 ^ (prefixWord ++ tailWord_429810).sum := by decide
  have hdescent : baseEnd_429810 < baseStart_429810 := by decide
  rcases family_descends (prefixWord ++ tailWord_429810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429886 : List Nat := [4, 2, 1, 2, 2, 8]
def baseStart_429886 : Nat := 118140960795 + 429886 * 2 ^ 59
def prefixEnd_429886 : Nat := 4983230072969 + 3 ^ 40 * 429886 * 2
def baseEnd_429886 : Nat := 14534198823954587835259

theorem tailTrace_429886 : CollatzResearch.WordTrace tailWord_429886 prefixEnd_429886 14534198823954587835259 := by
  unfold tailWord_429886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959903815075489441093689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10452820347069277019166341 1959903815075489441093689)
  ·
    refine ⟨1469927861306617080820267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1959903815075489441093689 1469927861306617080820267)
    ·
      refine ⟨2204891791959925621230401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1469927861306617080820267 2204891791959925621230401)
      ·
        refine ⟨1653668843969944215922801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2204891791959925621230401 1653668843969944215922801)
        ·
          refine ⟨1240251632977458161942101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1653668843969944215922801 1240251632977458161942101)
          ·
            refine ⟨14534198823954587835259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1240251632977458161942101 14534198823954587835259)
            ·
              rfl

theorem cell19_429886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 8].length) (baseStart_429886 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429886 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429886 prefixEnd_429886 := by exact prefixLift 429886
  have htrace : WordTrace (prefixWord ++ tailWord_429886) baseStart_429886 baseEnd_429886 := by
    simpa [prefixWord, tailWord_429886, baseEnd_429886] using wordTrace_append hprefix tailTrace_429886
  have hstable : (prefixWord ++ tailWord_429886).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429886).length < 2 ^ (prefixWord ++ tailWord_429886).sum := by decide
  have hdescent : baseEnd_429886 < baseStart_429886 := by decide
  rcases family_descends (prefixWord ++ tailWord_429886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429901 : List Nat := [1, 6, 1, 2, 1, 3, 1, 4]
def baseStart_429901 : Nat := 118140960795 + 429901 * 2 ^ 59
def prefixEnd_429901 : Nat := 4983230072969 + 3 ^ 40 * 429901 * 2
def baseEnd_429901 : Nat := 130812353688075700183957

theorem tailTrace_429901 : CollatzResearch.WordTrace tailWord_429901 prefixEnd_429901 130812353688075700183957 := by
  unfold tailWord_429901
  simp only [CollatzResearch.WordTrace]
  refine ⟨15679777615549573090545557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10453185077033048727030371 15679777615549573090545557)
  ·
    refine ⟨734989575728886238619323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15679777615549573090545557 734989575728886238619323)
    ·
      refine ⟨1102484363593329357928985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 734989575728886238619323 1102484363593329357928985)
      ·
        refine ⟨826863272694997018446739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1102484363593329357928985 826863272694997018446739)
        ·
          refine ⟨1240294909042495527670109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826863272694997018446739 1240294909042495527670109)
          ·
            refine ⟨465110590890935822876291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1240294909042495527670109 465110590890935822876291)
            ·
              refine ⟨697665886336403734314437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465110590890935822876291 697665886336403734314437)
              ·
                refine ⟨130812353688075700183957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697665886336403734314437 130812353688075700183957)
                ·
                  rfl

theorem cell19_429901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_429901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429901 prefixEnd_429901 := by exact prefixLift 429901
  have htrace : WordTrace (prefixWord ++ tailWord_429901) baseStart_429901 baseEnd_429901 := by
    simpa [prefixWord, tailWord_429901, baseEnd_429901] using wordTrace_append hprefix tailTrace_429901
  have hstable : (prefixWord ++ tailWord_429901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429901).length < 2 ^ (prefixWord ++ tailWord_429901).sum := by decide
  have hdescent : baseEnd_429901 < baseStart_429901 := by decide
  rcases family_descends (prefixWord ++ tailWord_429901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429905 : List Nat := [1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_429905 : Nat := 118140960795 + 429905 * 2 ^ 59
def prefixEnd_429905 : Nat := 4983230072969 + 3 ^ 40 * 429905 * 2
def baseEnd_429905 : Nat := 130813570827404876095057

theorem tailTrace_429905 : CollatzResearch.WordTrace tailWord_429905 prefixEnd_429905 130813570827404876095057 := by
  unfold tailWord_429905
  simp only [CollatzResearch.WordTrace]
  refine ⟨15679923507535081773691169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10453282338356721182460779 15679923507535081773691169)
  ·
    refine ⟨11759942630651311330268377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15679923507535081773691169 11759942630651311330268377)
    ·
      refine ⟨8819956972988483497701283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11759942630651311330268377 8819956972988483497701283)
      ·
        refine ⟨13229935459482725246551925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8819956972988483497701283 13229935459482725246551925)
        ·
          refine ⟨1240306449326505491864243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13229935459482725246551925 1240306449326505491864243)
          ·
            refine ⟨1860459673989758237796365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240306449326505491864243 1860459673989758237796365)
            ·
              refine ⟨697672377746159339173637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1860459673989758237796365 697672377746159339173637)
              ·
                refine ⟨130813570827404876095057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697672377746159339173637 130813570827404876095057)
                ·
                  rfl

theorem cell19_429905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_429905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429905 prefixEnd_429905 := by exact prefixLift 429905
  have htrace : WordTrace (prefixWord ++ tailWord_429905) baseStart_429905 baseEnd_429905 := by
    simpa [prefixWord, tailWord_429905, baseEnd_429905] using wordTrace_append hprefix tailTrace_429905
  have hstable : (prefixWord ++ tailWord_429905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429905).length < 2 ^ (prefixWord ++ tailWord_429905).sum := by decide
  have hdescent : baseEnd_429905 < baseStart_429905 := by decide
  rcases family_descends (prefixWord ++ tailWord_429905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429945 : List Nat := [1, 2, 1, 3, 2, 2, 8]
def baseStart_429945 : Nat := 118140960795 + 429945 * 2 ^ 59
def prefixEnd_429945 : Nat := 4983230072969 + 3 ^ 40 * 429945 * 2
def baseEnd_429945 : Nat := 43608580740232211735353

theorem tailTrace_429945 : CollatzResearch.WordTrace tailWord_429945 prefixEnd_429945 43608580740232211735353 := by
  unfold tailWord_429945
  simp only [CollatzResearch.WordTrace]
  refine ⟨15681382427390168605147289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10454254951593445736764859 15681382427390168605147289)
  ·
    refine ⟨11761036820542626453860467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15681382427390168605147289 11761036820542626453860467)
    ·
      refine ⟨17641555230813939680790701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11761036820542626453860467 17641555230813939680790701)
      ·
        refine ⟨6615583211555227380296513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17641555230813939680790701 6615583211555227380296513)
        ·
          refine ⟨4961687408666420535222385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6615583211555227380296513 4961687408666420535222385)
          ·
            refine ⟨3721265556499815401416789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4961687408666420535222385 3721265556499815401416789)
            ·
              refine ⟨43608580740232211735353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3721265556499815401416789 43608580740232211735353)
              ·
                rfl

theorem cell19_429945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_429945 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429945 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429945 prefixEnd_429945 := by exact prefixLift 429945
  have htrace : WordTrace (prefixWord ++ tailWord_429945) baseStart_429945 baseEnd_429945 := by
    simpa [prefixWord, tailWord_429945, baseEnd_429945] using wordTrace_append hprefix tailTrace_429945
  have hstable : (prefixWord ++ tailWord_429945).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429945).length < 2 ^ (prefixWord ++ tailWord_429945).sum := by decide
  have hdescent : baseEnd_429945 < baseStart_429945 := by decide
  rcases family_descends (prefixWord ++ tailWord_429945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429964 : List Nat := [2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_429964 : Nat := 118140960795 + 429964 * 2 ^ 59
def prefixEnd_429964 : Nat := 4983230072969 + 3 ^ 40 * 429964 * 2
def baseEnd_429964 : Nat := 130831523632510220783785

theorem tailTrace_429964 : CollatzResearch.WordTrace tailWord_429964 prefixEnd_429964 130831523632510220783785 := by
  unfold tailWord_429964
  simp only [CollatzResearch.WordTrace]
  refine ⟨7841037707160667425044473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10454716942880889900059297 7841037707160667425044473)
  ·
    refine ⟨5880778280370500568783355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7841037707160667425044473 5880778280370500568783355)
    ·
      refine ⟨8821167420555750853175033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5880778280370500568783355 8821167420555750853175033)
      ·
        refine ⟨6615875565416813139881275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8821167420555750853175033 6615875565416813139881275)
        ·
          refine ⟨9923813348125219709821913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6615875565416813139881275 9923813348125219709821913)
          ·
            refine ⟨7442860011093914782366435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9923813348125219709821913 7442860011093914782366435)
            ·
              refine ⟨11164290016640872173549653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442860011093914782366435 11164290016640872173549653)
              ·
                refine ⟨130831523632510220783785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11164290016640872173549653 130831523632510220783785)
                ·
                  rfl

theorem cell19_429964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_429964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429964 prefixEnd_429964 := by exact prefixLift 429964
  have htrace : WordTrace (prefixWord ++ tailWord_429964) baseStart_429964 baseEnd_429964 := by
    simpa [prefixWord, tailWord_429964, baseEnd_429964] using wordTrace_append hprefix tailTrace_429964
  have hstable : (prefixWord ++ tailWord_429964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429964).length < 2 ^ (prefixWord ++ tailWord_429964).sum := by decide
  have hdescent : baseEnd_429964 < baseStart_429964 := by decide
  rcases family_descends (prefixWord ++ tailWord_429964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429981 : List Nat := [1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_429981 : Nat := 118140960795 + 429981 * 2 ^ 59
def prefixEnd_429981 : Nat := 4983230072969 + 3 ^ 40 * 429981 * 2
def baseEnd_429981 : Nat := 130836696474659218405961

theorem tailTrace_429981 : CollatzResearch.WordTrace tailWord_429981 prefixEnd_429981 130836696474659218405961 := by
  unfold tailWord_429981
  simp only [CollatzResearch.WordTrace]
  refine ⟨15682695455259746753457797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10455130303506497835638531 15682695455259746753457797)
  ·
    refine ⟨2940505397861202516273337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15682695455259746753457797 2940505397861202516273337)
    ·
      refine ⟨2205379048395901887205003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2940505397861202516273337 2205379048395901887205003)
      ·
        refine ⟨3308068572593852830807505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205379048395901887205003 3308068572593852830807505)
        ·
          refine ⟨2481051429445389623105629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308068572593852830807505 2481051429445389623105629)
          ·
            refine ⟨930394286042021108664611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2481051429445389623105629 930394286042021108664611)
            ·
              refine ⟨1395591429063031662996917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930394286042021108664611 1395591429063031662996917)
              ·
                refine ⟨130836696474659218405961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1395591429063031662996917 130836696474659218405961)
                ·
                  rfl

theorem cell19_429981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_429981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_429981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_429981 prefixEnd_429981 := by exact prefixLift 429981
  have htrace : WordTrace (prefixWord ++ tailWord_429981) baseStart_429981 baseEnd_429981 := by
    simpa [prefixWord, tailWord_429981, baseEnd_429981] using wordTrace_append hprefix tailTrace_429981
  have hstable : (prefixWord ++ tailWord_429981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429981).length < 2 ^ (prefixWord ++ tailWord_429981).sum := by decide
  have hdescent : baseEnd_429981 < baseStart_429981 := by decide
  rcases family_descends (prefixWord ++ tailWord_429981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430040 : List Nat := [2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_430040 : Nat := 118140960795 + 430040 * 2 ^ 59
def prefixEnd_430040 : Nat := 4983230072969 + 3 ^ 40 * 430040 * 2
def baseEnd_430040 : Nat := 130854649279764563094689

theorem tailTrace_430040 : CollatzResearch.WordTrace tailWord_430040 prefixEnd_430040 130854649279764563094689 := by
  unfold tailWord_430040
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842423681022999914927787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10456564908030666553237049 7842423681022999914927787)
  ·
    refine ⟨11763635521534499872391681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7842423681022999914927787 11763635521534499872391681)
    ·
      refine ⟨8822726641150874904293761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11763635521534499872391681 8822726641150874904293761)
      ·
        refine ⟨6617044980863156178220321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8822726641150874904293761 6617044980863156178220321)
        ·
          refine ⟨4962783735647367133665241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6617044980863156178220321 4962783735647367133665241)
          ·
            refine ⟨3722087801735525350248931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4962783735647367133665241 3722087801735525350248931)
            ·
              refine ⟨5583131702603288025373397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722087801735525350248931 5583131702603288025373397)
              ·
                refine ⟨130854649279764563094689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5583131702603288025373397 130854649279764563094689)
                ·
                  rfl

theorem cell19_430040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_430040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430040 prefixEnd_430040 := by exact prefixLift 430040
  have htrace : WordTrace (prefixWord ++ tailWord_430040) baseStart_430040 baseEnd_430040 := by
    simpa [prefixWord, tailWord_430040, baseEnd_430040] using wordTrace_append hprefix tailTrace_430040
  have hstable : (prefixWord ++ tailWord_430040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430040).length < 2 ^ (prefixWord ++ tailWord_430040).sum := by decide
  have hdescent : baseEnd_430040 < baseStart_430040 := by decide
  rcases family_descends (prefixWord ++ tailWord_430040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430150 : List Nat := [6, 1, 1, 1, 1, 1, 3, 5]
def baseStart_430150 : Nat := 118140960795 + 430150 * 2 ^ 59
def prefixEnd_430150 : Nat := 4983230072969 + 3 ^ 40 * 430150 * 2
def baseEnd_430150 : Nat := 130888120611316900649945

theorem tailTrace_430150 : CollatzResearch.WordTrace tailWord_430150 prefixEnd_430150 130888120611316900649945 := by
  unfold tailWord_430150
  simp only [CollatzResearch.WordTrace]
  refine ⟨490276855988984019261247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10459239594431659077573269 490276855988984019261247)
  ·
    refine ⟨735415283983476028891871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 490276855988984019261247 735415283983476028891871)
    ·
      refine ⟨1103122925975214043337807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 735415283983476028891871 1103122925975214043337807)
      ·
        refine ⟨1654684388962821065006711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103122925975214043337807 1654684388962821065006711)
        ·
          refine ⟨2482026583444231597510067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1654684388962821065006711 2482026583444231597510067)
          ·
            refine ⟨3723039875166347396265101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482026583444231597510067 3723039875166347396265101)
            ·
              refine ⟨1396139953187380273599413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3723039875166347396265101 1396139953187380273599413)
              ·
                refine ⟨130888120611316900649945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1396139953187380273599413 130888120611316900649945)
                ·
                  rfl

theorem cell19_430150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_430150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430150 prefixEnd_430150 := by exact prefixLift 430150
  have htrace : WordTrace (prefixWord ++ tailWord_430150) baseStart_430150 baseEnd_430150 := by
    simpa [prefixWord, tailWord_430150, baseEnd_430150] using wordTrace_append hprefix tailTrace_430150
  have hstable : (prefixWord ++ tailWord_430150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430150).length < 2 ^ (prefixWord ++ tailWord_430150).sum := by decide
  have hdescent : baseEnd_430150 < baseStart_430150 := by decide
  rcases family_descends (prefixWord ++ tailWord_430150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430190 : List Nat := [4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_430190 : Nat := 118140960795 + 430190 * 2 ^ 59
def prefixEnd_430190 : Nat := 4983230072969 + 3 ^ 40 * 430190 * 2
def baseEnd_430190 : Nat := 130900292004608659760947

theorem tailTrace_430190 : CollatzResearch.WordTrace tailWord_430190 prefixEnd_430190 130900292004608659760947 := by
  unfold tailWord_430190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961289788937821930977003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10460212207668383631877349 1961289788937821930977003)
  ·
    refine ⟨2941934683406732896465505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1961289788937821930977003 2941934683406732896465505)
    ·
      refine ⟨2206451012555049672349129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2941934683406732896465505 2206451012555049672349129)
      ·
        refine ⟨1654838259416287254261847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2206451012555049672349129 1654838259416287254261847)
        ·
          refine ⟨2482257389124430881392771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1654838259416287254261847 2482257389124430881392771)
          ·
            refine ⟨3723386083686646322089157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482257389124430881392771 3723386083686646322089157)
            ·
              refine ⟨698134890691246185391717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3723386083686646322089157 698134890691246185391717)
              ·
                refine ⟨130900292004608659760947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 698134890691246185391717 130900292004608659760947)
                ·
                  rfl

theorem cell19_430190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_430190 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430190 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430190 prefixEnd_430190 := by exact prefixLift 430190
  have htrace : WordTrace (prefixWord ++ tailWord_430190) baseStart_430190 baseEnd_430190 := by
    simpa [prefixWord, tailWord_430190, baseEnd_430190] using wordTrace_append hprefix tailTrace_430190
  have hstable : (prefixWord ++ tailWord_430190).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430190).length < 2 ^ (prefixWord ++ tailWord_430190).sum := by decide
  have hdescent : baseEnd_430190 < baseStart_430190 := by decide
  rcases family_descends (prefixWord ++ tailWord_430190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430192 : List Nat := [2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_430192 : Nat := 118140960795 + 430192 * 2 ^ 59
def prefixEnd_430192 : Nat := 4983230072969 + 3 ^ 40 * 430192 * 2
def baseEnd_430192 : Nat := 130900900574273247716497

theorem tailTrace_430192 : CollatzResearch.WordTrace tailWord_430192 prefixEnd_430192 130900900574273247716497 := by
  unfold tailWord_430192
  simp only [CollatzResearch.WordTrace]
  refine ⟨7845195628747664894694415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10460260838330219859592553 7845195628747664894694415)
  ·
    refine ⟨11767793443121497342041623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7845195628747664894694415 11767793443121497342041623)
    ·
      refine ⟨17651690164682246013062435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11767793443121497342041623 17651690164682246013062435)
      ·
        refine ⟨26477535247023369019593653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17651690164682246013062435 26477535247023369019593653)
        ·
          refine ⟨2482268929408440845586905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26477535247023369019593653 2482268929408440845586905)
          ·
            refine ⟨1861701697056330634190179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2482268929408440845586905 1861701697056330634190179)
            ·
              refine ⟨2792552545584495951285269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861701697056330634190179 2792552545584495951285269)
              ·
                refine ⟨130900900574273247716497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2792552545584495951285269 130900900574273247716497)
                ·
                  rfl

theorem cell19_430192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_430192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430192 prefixEnd_430192 := by exact prefixLift 430192
  have htrace : WordTrace (prefixWord ++ tailWord_430192) baseStart_430192 baseEnd_430192 := by
    simpa [prefixWord, tailWord_430192, baseEnd_430192] using wordTrace_append hprefix tailTrace_430192
  have hstable : (prefixWord ++ tailWord_430192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430192).length < 2 ^ (prefixWord ++ tailWord_430192).sum := by decide
  have hdescent : baseEnd_430192 < baseStart_430192 := by decide
  rcases family_descends (prefixWord ++ tailWord_430192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430211 : List Nat := [1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_430211 : Nat := 118140960795 + 430211 * 2 ^ 59
def prefixEnd_430211 : Nat := 4983230072969 + 3 ^ 40 * 430211 * 2
def baseEnd_430211 : Nat := 130906681986086833294223

theorem tailTrace_430211 : CollatzResearch.WordTrace tailWord_430211 prefixEnd_430211 130906681986086833294223 := by
  unfold tailWord_430211
  simp only [CollatzResearch.WordTrace]
  refine ⟨15691084244426496034330487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10460722829617664022886991 15691084244426496034330487)
  ·
    refine ⟨23536626366639744051495731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15691084244426496034330487 23536626366639744051495731)
    ·
      refine ⟨35304939549959616077243597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23536626366639744051495731 35304939549959616077243597)
      ·
        refine ⟨13239352331234856028966349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35304939549959616077243597 13239352331234856028966349)
        ·
          refine ⟨4964757124213071010862381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13239352331234856028966349 4964757124213071010862381)
          ·
            refine ⟨1861783921579901629073393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4964757124213071010862381 1861783921579901629073393)
            ·
              refine ⟨1396337941184926221805045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861783921579901629073393 1396337941184926221805045)
              ·
                refine ⟨130906681986086833294223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1396337941184926221805045 130906681986086833294223)
                ·
                  rfl

theorem cell19_430211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_430211 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430211 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430211 prefixEnd_430211 := by exact prefixLift 430211
  have htrace : WordTrace (prefixWord ++ tailWord_430211) baseStart_430211 baseEnd_430211 := by
    simpa [prefixWord, tailWord_430211, baseEnd_430211] using wordTrace_append hprefix tailTrace_430211
  have hstable : (prefixWord ++ tailWord_430211).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430211).length < 2 ^ (prefixWord ++ tailWord_430211).sum := by decide
  have hdescent : baseEnd_430211 < baseStart_430211 := by decide
  rcases family_descends (prefixWord ++ tailWord_430211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430228 : List Nat := [2, 4, 2, 3, 8]
def baseStart_430228 : Nat := 118140960795 + 430228 * 2 ^ 59
def prefixEnd_430228 : Nat := 4983230072969 + 3 ^ 40 * 430228 * 2
def baseEnd_430228 : Nat := 4848587215860586330237

theorem tailTrace_430228 : CollatzResearch.WordTrace tailWord_430228 prefixEnd_430228 4848587215860586330237 := by
  unfold tailWord_430228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7845852142682453968849669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10461136190243271958466225 7845852142682453968849669)
  ·
    refine ⟨1471097276752960119159313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7845852142682453968849669 1471097276752960119159313)
    ·
      refine ⟨1103322957564720089369485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1471097276752960119159313 1103322957564720089369485)
      ·
        refine ⟨413746109086770033513557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1103322957564720089369485 413746109086770033513557)
        ·
          refine ⟨4848587215860586330237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 413746109086770033513557 4848587215860586330237)
          ·
            rfl

theorem cell19_430228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 8].length) (baseStart_430228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430228 prefixEnd_430228 := by exact prefixLift 430228
  have htrace : WordTrace (prefixWord ++ tailWord_430228) baseStart_430228 baseEnd_430228 := by
    simpa [prefixWord, tailWord_430228, baseEnd_430228] using wordTrace_append hprefix tailTrace_430228
  have hstable : (prefixWord ++ tailWord_430228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430228).length < 2 ^ (prefixWord ++ tailWord_430228).sum := by decide
  have hdescent : baseEnd_430228 < baseStart_430228 := by decide
  rcases family_descends (prefixWord ++ tailWord_430228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430340 : List Nat := [2, 3, 2, 2, 4, 1, 5]
def baseStart_430340 : Nat := 118140960795 + 430340 * 2 ^ 59
def prefixEnd_430340 : Nat := 4983230072969 + 3 ^ 40 * 430340 * 2
def baseEnd_430340 : Nat := 43648644909817585475735

theorem tailTrace_430340 : CollatzResearch.WordTrace tailWord_430340 prefixEnd_430340 43648644909817585475735 := by
  unfold tailWord_430340
  simp only [CollatzResearch.WordTrace]
  refine ⟨7847894630479575532888237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10463859507306100710517649 7847894630479575532888237)
  ·
    refine ⟨2942960486429840824833089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7847894630479575532888237 2942960486429840824833089)
    ·
      refine ⟨2207220364822380618624817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2942960486429840824833089 2207220364822380618624817)
      ·
        refine ⟨1655415273616785463968613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2207220364822380618624817 1655415273616785463968613)
        ·
          refine ⟨310390363803147274494115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1655415273616785463968613 310390363803147274494115)
          ·
            refine ⟨465585545704720911741173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310390363803147274494115 465585545704720911741173)
            ·
              refine ⟨43648644909817585475735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 465585545704720911741173 43648644909817585475735)
              ·
                rfl

theorem cell19_430340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 5].length) (baseStart_430340 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430340 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430340 prefixEnd_430340 := by exact prefixLift 430340
  have htrace : WordTrace (prefixWord ++ tailWord_430340) baseStart_430340 baseEnd_430340 := by
    simpa [prefixWord, tailWord_430340, baseEnd_430340] using wordTrace_append hprefix tailTrace_430340
  have hstable : (prefixWord ++ tailWord_430340).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430340).length < 2 ^ (prefixWord ++ tailWord_430340).sum := by decide
  have hdescent : baseEnd_430340 < baseStart_430340 := by decide
  rcases family_descends (prefixWord ++ tailWord_430340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430344 : List Nat := [2, 1, 3, 2, 3, 1, 7]
def baseStart_430344 : Nat := 118140960795 + 430344 * 2 ^ 59
def prefixEnd_430344 : Nat := 4983230072969 + 3 ^ 40 * 430344 * 2
def baseEnd_430344 : Nat := 43649050622927310779435

theorem tailTrace_430344 : CollatzResearch.WordTrace tailWord_430344 prefixEnd_430344 43649050622927310779435 := by
  unfold tailWord_430344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7847967576472329874461043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10463956768629773165948057 7847967576472329874461043)
  ·
    refine ⟨11771951364708494811691565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7847967576472329874461043 11771951364708494811691565)
    ·
      refine ⟨4414481761765685554384337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11771951364708494811691565 4414481761765685554384337)
      ·
        refine ⟨3310861321324264165788253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4414481761765685554384337 3310861321324264165788253)
        ·
          refine ⟨1241572995496599062170595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3310861321324264165788253 1241572995496599062170595)
          ·
            refine ⟨1862359493244898593255893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241572995496599062170595 1862359493244898593255893)
            ·
              refine ⟨43649050622927310779435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1862359493244898593255893 43649050622927310779435)
              ·
                rfl

theorem cell19_430344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_430344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430344 prefixEnd_430344 := by exact prefixLift 430344
  have htrace : WordTrace (prefixWord ++ tailWord_430344) baseStart_430344 baseEnd_430344 := by
    simpa [prefixWord, tailWord_430344, baseEnd_430344] using wordTrace_append hprefix tailTrace_430344
  have hstable : (prefixWord ++ tailWord_430344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430344).length < 2 ^ (prefixWord ++ tailWord_430344).sum := by decide
  have hdescent : baseEnd_430344 < baseStart_430344 := by decide
  rcases family_descends (prefixWord ++ tailWord_430344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430401 : List Nat := [1, 2, 5, 2, 9]
def baseStart_430401 : Nat := 118140960795 + 430401 * 2 ^ 59
def prefixEnd_430401 : Nat := 4983230072969 + 3 ^ 40 * 430401 * 2
def baseEnd_430401 : Nat := 4850536892748988484129

theorem tailTrace_430401 : CollatzResearch.WordTrace tailWord_430401 prefixEnd_430401 4850536892748988484129 := by
  unfold tailWord_430401
  simp only [CollatzResearch.WordTrace]
  refine ⟨15698014113738158483747057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10465342742492105655831371 15698014113738158483747057)
  ·
    refine ⟨11773510585303618862810293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15698014113738158483747057 11773510585303618862810293)
    ·
      refine ⟨1103766617372214268388465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11773510585303618862810293 1103766617372214268388465)
      ·
        refine ⟨827824963029160701291349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1103766617372214268388465 827824963029160701291349)
        ·
          refine ⟨4850536892748988484129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 827824963029160701291349 4850536892748988484129)
          ·
            rfl

theorem cell19_430401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 9].length) (baseStart_430401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430401 prefixEnd_430401 := by exact prefixLift 430401
  have htrace : WordTrace (prefixWord ++ tailWord_430401) baseStart_430401 baseEnd_430401 := by
    simpa [prefixWord, tailWord_430401, baseEnd_430401] using wordTrace_append hprefix tailTrace_430401
  have hstable : (prefixWord ++ tailWord_430401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430401).length < 2 ^ (prefixWord ++ tailWord_430401).sum := by decide
  have hdescent : baseEnd_430401 < baseStart_430401 := by decide
  rcases family_descends (prefixWord ++ tailWord_430401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430437 : List Nat := [1, 3, 1, 3, 1, 4, 3, 3]
def baseStart_430437 : Nat := 118140960795 + 430437 * 2 ^ 59
def prefixEnd_430437 : Nat := 4983230072969 + 3 ^ 40 * 430437 * 2
def baseEnd_430437 : Nat := 130975450358185272271385

theorem tailTrace_430437 : CollatzResearch.WordTrace tailWord_430437 prefixEnd_430437 130975450358185272271385 := by
  unfold tailWord_430437
  simp only [CollatzResearch.WordTrace]
  refine ⟨15699327141607736632057565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10466218094405157754705043 15699327141607736632057565)
  ·
    refine ⟨5887247678102901237021587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15699327141607736632057565 5887247678102901237021587)
    ·
      refine ⟨8830871517154351855532381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5887247678102901237021587 8830871517154351855532381)
      ·
        refine ⟨3311576818932881945824643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8830871517154351855532381 3311576818932881945824643)
        ·
          refine ⟨4967365228399322918736965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311576818932881945824643 4967365228399322918736965)
          ·
            refine ⟨931380980324873047263181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4967365228399322918736965 931380980324873047263181)
            ·
              refine ⟨349267867621827392723693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 931380980324873047263181 349267867621827392723693)
              ·
                refine ⟨130975450358185272271385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349267867621827392723693 130975450358185272271385)
                ·
                  rfl

theorem cell19_430437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 3].length) (baseStart_430437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430437 prefixEnd_430437 := by exact prefixLift 430437
  have htrace : WordTrace (prefixWord ++ tailWord_430437) baseStart_430437 baseEnd_430437 := by
    simpa [prefixWord, tailWord_430437, baseEnd_430437] using wordTrace_append hprefix tailTrace_430437
  have hstable : (prefixWord ++ tailWord_430437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430437).length < 2 ^ (prefixWord ++ tailWord_430437).sum := by decide
  have hdescent : baseEnd_430437 < baseStart_430437 := by decide
  rcases family_descends (prefixWord ++ tailWord_430437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430454 : List Nat := [5, 1, 1, 4, 1, 1, 6]
def baseStart_430454 : Nat := 118140960795 + 430454 * 2 ^ 59
def prefixEnd_430454 : Nat := 4983230072969 + 3 ^ 40 * 430454 * 2
def baseEnd_430454 : Nat := 43660207733444756631187

theorem tailTrace_430454 : CollatzResearch.WordTrace tailWord_430454 prefixEnd_430454 43660207733444756631187 := by
  unfold tailWord_430454
  simp only [CollatzResearch.WordTrace]
  refine ⟨981246698909134283464151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10466631455030765690284277 981246698909134283464151)
  ·
    refine ⟨1471870048363701425196227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 981246698909134283464151 1471870048363701425196227)
    ·
      refine ⟨2207805072545552137794341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1471870048363701425196227 2207805072545552137794341)
      ·
        refine ⟨413963451102291025836439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2207805072545552137794341 413963451102291025836439)
        ·
          refine ⟨620945176653436538754659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413963451102291025836439 620945176653436538754659)
          ·
            refine ⟨931417764980154808131989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620945176653436538754659 931417764980154808131989)
            ·
              refine ⟨43660207733444756631187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 931417764980154808131989 43660207733444756631187)
              ·
                rfl

theorem cell19_430454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 6].length) (baseStart_430454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430454 prefixEnd_430454 := by exact prefixLift 430454
  have htrace : WordTrace (prefixWord ++ tailWord_430454) baseStart_430454 baseEnd_430454 := by
    simpa [prefixWord, tailWord_430454, baseEnd_430454] using wordTrace_append hprefix tailTrace_430454
  have hstable : (prefixWord ++ tailWord_430454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430454).length < 2 ^ (prefixWord ++ tailWord_430454).sum := by decide
  have hdescent : baseEnd_430454 < baseStart_430454 := by decide
  rcases family_descends (prefixWord ++ tailWord_430454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430486 : List Nat := [5, 3, 1, 2, 1, 2, 2, 3]
def baseStart_430486 : Nat := 118140960795 + 430486 * 2 ^ 59
def prefixEnd_430486 : Nat := 4983230072969 + 3 ^ 40 * 430486 * 2
def baseEnd_430486 : Nat := 130990360314967677182363

theorem tailTrace_430486 : CollatzResearch.WordTrace tailWord_430486 prefixEnd_430486 130990360314967677182363 := by
  unfold tailWord_430486
  simp only [CollatzResearch.WordTrace]
  refine ⟨981319644901888625036957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10467409545620145333727541 981319644901888625036957)
  ·
    refine ⟨367994866838208234388859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 981319644901888625036957 367994866838208234388859)
    ·
      refine ⟨551992300257312351583289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367994866838208234388859 551992300257312351583289)
      ·
        refine ⟨413994225192984263687467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551992300257312351583289 413994225192984263687467)
        ·
          refine ⟨620991337789476395531201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413994225192984263687467 620991337789476395531201)
          ·
            refine ⟨465743503342107296648401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620991337789476395531201 465743503342107296648401)
            ·
              refine ⟨349307627506580472486301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465743503342107296648401 349307627506580472486301)
              ·
                refine ⟨130990360314967677182363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349307627506580472486301 130990360314967677182363)
                ·
                  rfl

theorem cell19_430486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_430486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430486 prefixEnd_430486 := by exact prefixLift 430486
  have htrace : WordTrace (prefixWord ++ tailWord_430486) baseStart_430486 baseEnd_430486 := by
    simpa [prefixWord, tailWord_430486, baseEnd_430486] using wordTrace_append hprefix tailTrace_430486
  have hstable : (prefixWord ++ tailWord_430486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430486).length < 2 ^ (prefixWord ++ tailWord_430486).sum := by decide
  have hdescent : baseEnd_430486 < baseStart_430486 := by decide
  rcases family_descends (prefixWord ++ tailWord_430486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430496 : List Nat := [2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_430496 : Nat := 118140960795 + 430496 * 2 ^ 59
def prefixEnd_430496 : Nat := 4983230072969 + 3 ^ 40 * 430496 * 2
def baseEnd_430496 : Nat := 130993403163290616960113

theorem tailTrace_430496 : CollatzResearch.WordTrace tailWord_430496 prefixEnd_430496 130993403163290616960113 := by
  unfold tailWord_430496
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850739524196994854227671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10467652698929326472303561 7850739524196994854227671)
  ·
    refine ⟨11776109286295492281341507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7850739524196994854227671 11776109286295492281341507)
    ·
      refine ⟨17664163929443238422012261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11776109286295492281341507 17664163929443238422012261)
      ·
        refine ⟨3312030736770607204127299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17664163929443238422012261 3312030736770607204127299)
        ·
          refine ⟨4968046105155910806190949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3312030736770607204127299 4968046105155910806190949)
          ·
            refine ⟨931508644716733276160803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4968046105155910806190949 931508644716733276160803)
            ·
              refine ⟨1397262967075099914241205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931508644716733276160803 1397262967075099914241205)
              ·
                refine ⟨130993403163290616960113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1397262967075099914241205 130993403163290616960113)
                ·
                  rfl

theorem cell19_430496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_430496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430496 prefixEnd_430496 := by exact prefixLift 430496
  have htrace : WordTrace (prefixWord ++ tailWord_430496) baseStart_430496 baseEnd_430496 := by
    simpa [prefixWord, tailWord_430496, baseEnd_430496] using wordTrace_append hprefix tailTrace_430496
  have hstable : (prefixWord ++ tailWord_430496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430496).length < 2 ^ (prefixWord ++ tailWord_430496).sum := by decide
  have hdescent : baseEnd_430496 < baseStart_430496 := by decide
  rcases family_descends (prefixWord ++ tailWord_430496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430667 : List Nat := [1, 1, 1, 1, 3, 1, 8, 3]
def baseStart_430667 : Nat := 118140960795 + 430667 * 2 ^ 59
def prefixEnd_430667 : Nat := 4983230072969 + 3 ^ 40 * 430667 * 2
def baseEnd_430667 : Nat := 131045435869612887159647

theorem tailTrace_430667 : CollatzResearch.WordTrace tailWord_430667 prefixEnd_430667 131045435869612887159647 := by
  unfold tailWord_430667
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707715930774485912930255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10471810620516323941953503 15707715930774485912930255)
  ·
    refine ⟨23561573896161728869395383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15707715930774485912930255 23561573896161728869395383)
    ·
      refine ⟨35342360844242593304093075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23561573896161728869395383 35342360844242593304093075)
      ·
        refine ⟨53013541266363889956139613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35342360844242593304093075 53013541266363889956139613)
        ·
          refine ⟨19880077974886458733552355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53013541266363889956139613 19880077974886458733552355)
          ·
            refine ⟨29820116962329688100328533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19880077974886458733552355 29820116962329688100328533)
            ·
              refine ⟨349454495652301032425725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 29820116962329688100328533 349454495652301032425725)
              ·
                refine ⟨131045435869612887159647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349454495652301032425725 131045435869612887159647)
                ·
                  rfl

theorem cell19_430667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 3].length) (baseStart_430667 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430667 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430667 prefixEnd_430667 := by exact prefixLift 430667
  have htrace : WordTrace (prefixWord ++ tailWord_430667) baseStart_430667 baseEnd_430667 := by
    simpa [prefixWord, tailWord_430667, baseEnd_430667] using wordTrace_append hprefix tailTrace_430667
  have hstable : (prefixWord ++ tailWord_430667).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430667).length < 2 ^ (prefixWord ++ tailWord_430667).sum := by decide
  have hdescent : baseEnd_430667 < baseStart_430667 := by decide
  rcases family_descends (prefixWord ++ tailWord_430667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430684 : List Nat := [2, 2, 4, 1, 3, 2, 5]
def baseStart_430684 : Nat := 118140960795 + 430684 * 2 ^ 59
def prefixEnd_430684 : Nat := 4983230072969 + 3 ^ 40 * 430684 * 2
def baseEnd_430684 : Nat := 43683536237253961593941

theorem tailTrace_430684 : CollatzResearch.WordTrace tailWord_430684 prefixEnd_430684 43683536237253961593941 := by
  unfold tailWord_430684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854167985856448908149553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10472223981141931877532737 7854167985856448908149553)
  ·
    refine ⟨5890625989392336681112165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7854167985856448908149553 5890625989392336681112165)
    ·
      refine ⟨1104492373011063127708531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5890625989392336681112165 1104492373011063127708531)
      ·
        refine ⟨1656738559516594691562797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104492373011063127708531 1656738559516594691562797)
        ·
          refine ⟨621276959818723009336049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1656738559516594691562797 621276959818723009336049)
          ·
            refine ⟨465957719864042257002037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621276959818723009336049 465957719864042257002037)
            ·
              refine ⟨43683536237253961593941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 465957719864042257002037 43683536237253961593941)
              ·
                rfl

theorem cell19_430684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_430684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430684 prefixEnd_430684 := by exact prefixLift 430684
  have htrace : WordTrace (prefixWord ++ tailWord_430684) baseStart_430684 baseEnd_430684 := by
    simpa [prefixWord, tailWord_430684, baseEnd_430684] using wordTrace_append hprefix tailTrace_430684
  have hstable : (prefixWord ++ tailWord_430684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430684).length < 2 ^ (prefixWord ++ tailWord_430684).sum := by decide
  have hdescent : baseEnd_430684 < baseStart_430684 := by decide
  rcases family_descends (prefixWord ++ tailWord_430684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430688 : List Nat := [2, 1, 1, 3, 2, 1, 9]
def baseStart_430688 : Nat := 118140960795 + 430688 * 2 ^ 59
def prefixEnd_430688 : Nat := 4983230072969 + 3 ^ 40 * 430688 * 2
def baseEnd_430688 : Nat := 43683941950363686897641

theorem tailTrace_430688 : CollatzResearch.WordTrace tailWord_430688 prefixEnd_430688 43683941950363686897641 := by
  unfold tailWord_430688
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854240931849203249722359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10472321242465604332963145 7854240931849203249722359)
  ·
    refine ⟨11781361397773804874583539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7854240931849203249722359 11781361397773804874583539)
    ·
      refine ⟨17672042096660707311875309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11781361397773804874583539 17672042096660707311875309)
      ·
        refine ⟨6627015786247765241953241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17672042096660707311875309 6627015786247765241953241)
        ·
          refine ⟨4970261839685823931464931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6627015786247765241953241 4970261839685823931464931)
          ·
            refine ⟨7455392759528735897197397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970261839685823931464931 7455392759528735897197397)
            ·
              refine ⟨43683941950363686897641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7455392759528735897197397 43683941950363686897641)
              ·
                rfl

theorem cell19_430688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_430688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430688 prefixEnd_430688 := by exact prefixLift 430688
  have htrace : WordTrace (prefixWord ++ tailWord_430688) baseStart_430688 baseEnd_430688 := by
    simpa [prefixWord, tailWord_430688, baseEnd_430688] using wordTrace_append hprefix tailTrace_430688
  have hstable : (prefixWord ++ tailWord_430688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430688).length < 2 ^ (prefixWord ++ tailWord_430688).sum := by decide
  have hdescent : baseEnd_430688 < baseStart_430688 := by decide
  rcases family_descends (prefixWord ++ tailWord_430688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430724 : List Nat := [2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_430724 : Nat := 118140960795 + 430724 * 2 ^ 59
def prefixEnd_430724 : Nat := 4983230072969 + 3 ^ 40 * 430724 * 2
def baseEnd_430724 : Nat := 131062780105053643892825

theorem tailTrace_430724 : CollatzResearch.WordTrace tailWord_430724 prefixEnd_430724 131062780105053643892825 := by
  unfold tailWord_430724
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854897445783992323877613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10473196594378656431836817 7854897445783992323877613)
  ·
    refine ⟨2945586542168997121454105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7854897445783992323877613 2945586542168997121454105)
    ·
      refine ⟨2209189906626747841090579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2945586542168997121454105 2209189906626747841090579)
      ·
        refine ⟨3313784859940121761635869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209189906626747841090579 3313784859940121761635869)
        ·
          refine ⟨1242669322477545660613451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3313784859940121761635869 1242669322477545660613451)
          ·
            refine ⟨1864003983716318490920177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242669322477545660613451 1864003983716318490920177)
            ·
              refine ⟨1398002987787238868190133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864003983716318490920177 1398002987787238868190133)
              ·
                refine ⟨131062780105053643892825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1398002987787238868190133 131062780105053643892825)
                ·
                  rfl

theorem cell19_430724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_430724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430724 prefixEnd_430724 := by exact prefixLift 430724
  have htrace : WordTrace (prefixWord ++ tailWord_430724) baseStart_430724 baseEnd_430724 := by
    simpa [prefixWord, tailWord_430724, baseEnd_430724] using wordTrace_append hprefix tailTrace_430724
  have hstable : (prefixWord ++ tailWord_430724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430724).length < 2 ^ (prefixWord ++ tailWord_430724).sum := by decide
  have hdescent : baseEnd_430724 < baseStart_430724 := by decide
  rcases family_descends (prefixWord ++ tailWord_430724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430838 : List Nat := [5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_430838 : Nat := 118140960795 + 430838 * 2 ^ 59
def prefixEnd_430838 : Nat := 4983230072969 + 3 ^ 40 * 430838 * 2
def baseEnd_430838 : Nat := 131097468575935157359181

theorem tailTrace_430838 : CollatzResearch.WordTrace tailWord_430838 prefixEnd_430838 131097468575935157359181 := by
  unfold tailWord_430838
  simp only [CollatzResearch.WordTrace]
  refine ⟨982122050822186382337823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10475968542103321411603445 982122050822186382337823)
  ·
    refine ⟨1473183076233279573506735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 982122050822186382337823 1473183076233279573506735)
    ·
      refine ⟨2209774614349919360260103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473183076233279573506735 2209774614349919360260103)
      ·
        refine ⟨3314661921524879040390155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209774614349919360260103 3314661921524879040390155)
        ·
          refine ⟨4971992882287318560585233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314661921524879040390155 4971992882287318560585233)
          ·
            refine ⟨3728994661715488920438925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4971992882287318560585233 3728994661715488920438925)
            ·
              refine ⟨1398372998143308345164597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3728994661715488920438925 1398372998143308345164597)
              ·
                refine ⟨131097468575935157359181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1398372998143308345164597 131097468575935157359181)
                ·
                  rfl

theorem cell19_430838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_430838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430838 prefixEnd_430838 := by exact prefixLift 430838
  have htrace : WordTrace (prefixWord ++ tailWord_430838) baseStart_430838 baseEnd_430838 := by
    simpa [prefixWord, tailWord_430838, baseEnd_430838] using wordTrace_append hprefix tailTrace_430838
  have hstable : (prefixWord ++ tailWord_430838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430838).length < 2 ^ (prefixWord ++ tailWord_430838).sum := by decide
  have hdescent : baseEnd_430838 < baseStart_430838 := by decide
  rcases family_descends (prefixWord ++ tailWord_430838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430840 : List Nat := [2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_430840 : Nat := 118140960795 + 430840 * 2 ^ 59
def prefixEnd_430840 : Nat := 4983230072969 + 3 ^ 40 * 430840 * 2
def baseEnd_430840 : Nat := 131098077145599745314731

theorem tailTrace_430840 : CollatzResearch.WordTrace tailWord_430840 prefixEnd_430840 131098077145599745314731 := by
  unfold tailWord_430840
  simp only [CollatzResearch.WordTrace]
  refine ⟨7857012879573868229488987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10476017172765157639318649 7857012879573868229488987)
  ·
    refine ⟨11785519319360802344233481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7857012879573868229488987 11785519319360802344233481)
    ·
      refine ⟨8839139489520601758175111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11785519319360802344233481 8839139489520601758175111)
      ·
        refine ⟨13258709234280902637262667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8839139489520601758175111 13258709234280902637262667)
        ·
          refine ⟨19888063851421353955894001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13258709234280902637262667 19888063851421353955894001)
          ·
            refine ⟨14916047888566015466920501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19888063851421353955894001 14916047888566015466920501)
            ·
              refine ⟨1398379489553063950023797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14916047888566015466920501 1398379489553063950023797)
              ·
                refine ⟨131098077145599745314731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1398379489553063950023797 131098077145599745314731)
                ·
                  rfl

theorem cell19_430840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_430840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430840 prefixEnd_430840 := by exact prefixLift 430840
  have htrace : WordTrace (prefixWord ++ tailWord_430840) baseStart_430840 baseEnd_430840 := by
    simpa [prefixWord, tailWord_430840, baseEnd_430840] using wordTrace_append hprefix tailTrace_430840
  have hstable : (prefixWord ++ tailWord_430840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430840).length < 2 ^ (prefixWord ++ tailWord_430840).sum := by decide
  have hdescent : baseEnd_430840 < baseStart_430840 := by decide
  rcases family_descends (prefixWord ++ tailWord_430840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430876 : List Nat := [2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_430876 : Nat := 118140960795 + 430876 * 2 ^ 59
def prefixEnd_430876 : Nat := 4983230072969 + 3 ^ 40 * 430876 * 2
def baseEnd_430876 : Nat := 131109031399562328514633

theorem tailTrace_430876 : CollatzResearch.WordTrace tailWord_430876 prefixEnd_430876 131109031399562328514633 := by
  unfold tailWord_430876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7857669393508657303644241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10476892524678209738192321 7857669393508657303644241)
  ·
    refine ⟨5893252045131492977733181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7857669393508657303644241 5893252045131492977733181)
    ·
      refine ⟨2209969516924309866649943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5893252045131492977733181 2209969516924309866649943)
      ·
        refine ⟨3314954275386464799974915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209969516924309866649943 3314954275386464799974915)
        ·
          refine ⟨4972431413079697199962373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314954275386464799974915 4972431413079697199962373)
          ·
            refine ⟨932330889952443224992945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4972431413079697199962373 932330889952443224992945)
            ·
              refine ⟨699248167464332418744709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932330889952443224992945 699248167464332418744709)
              ·
                refine ⟨131109031399562328514633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 699248167464332418744709 131109031399562328514633)
                ·
                  rfl

theorem cell19_430876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_430876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430876 prefixEnd_430876 := by exact prefixLift 430876
  have htrace : WordTrace (prefixWord ++ tailWord_430876) baseStart_430876 baseEnd_430876 := by
    simpa [prefixWord, tailWord_430876, baseEnd_430876] using wordTrace_append hprefix tailTrace_430876
  have hstable : (prefixWord ++ tailWord_430876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430876).length < 2 ^ (prefixWord ++ tailWord_430876).sum := by decide
  have hdescent : baseEnd_430876 < baseStart_430876 := by decide
  rcases family_descends (prefixWord ++ tailWord_430876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430897 : List Nat := [1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_430897 : Nat := 118140960795 + 430897 * 2 ^ 59
def prefixEnd_430897 : Nat := 4983230072969 + 3 ^ 40 * 430897 * 2
def baseEnd_430897 : Nat := 131115421381040502047909

theorem tailTrace_430897 : CollatzResearch.WordTrace tailWord_430897 prefixEnd_430897 131115421381040502047909 := by
  unfold tailWord_430897
  simp only [CollatzResearch.WordTrace]
  refine ⟨15716104719941235193802945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10477403146627490129201963 15716104719941235193802945)
  ·
    refine ⟨11787078539955926395352209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15716104719941235193802945 11787078539955926395352209)
    ·
      refine ⟨8840308904966944796514157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11787078539955926395352209 8840308904966944796514157)
      ·
        refine ⟨3315115839362604298692809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8840308904966944796514157 3315115839362604298692809)
        ·
          refine ⟨2486336879521953224019607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3315115839362604298692809 2486336879521953224019607)
          ·
            refine ⟨3729505319282929836029411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2486336879521953224019607 3729505319282929836029411)
            ·
              refine ⟨5594257978924394754044117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729505319282929836029411 5594257978924394754044117)
              ·
                refine ⟨131115421381040502047909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5594257978924394754044117 131115421381040502047909)
                ·
                  rfl

theorem cell19_430897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_430897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_430897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_430897 prefixEnd_430897 := by exact prefixLift 430897
  have htrace : WordTrace (prefixWord ++ tailWord_430897) baseStart_430897 baseEnd_430897 := by
    simpa [prefixWord, tailWord_430897, baseEnd_430897] using wordTrace_append hprefix tailTrace_430897
  have hstable : (prefixWord ++ tailWord_430897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430897).length < 2 ^ (prefixWord ++ tailWord_430897).sum := by decide
  have hdescent : baseEnd_430897 < baseStart_430897 := by decide
  rcases family_descends (prefixWord ++ tailWord_430897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431007 : List Nat := [1, 1, 2, 5, 2, 3, 2, 3]
def baseStart_431007 : Nat := 118140960795 + 431007 * 2 ^ 59
def prefixEnd_431007 : Nat := 4983230072969 + 3 ^ 40 * 431007 * 2
def baseEnd_431007 : Nat := 131148892712592839603165

theorem tailTrace_431007 : CollatzResearch.WordTrace tailWord_431007 prefixEnd_431007 131148892712592839603165 := by
  unfold tailWord_431007
  simp only [CollatzResearch.WordTrace]
  refine ⟨15720116749542723980307275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10480077833028482653538183 15720116749542723980307275)
  ·
    refine ⟨23580175124314085970460913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15720116749542723980307275 23580175124314085970460913)
    ·
      refine ⟨17685131343235564477845685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23580175124314085970460913 17685131343235564477845685)
      ·
        refine ⟨1657981063428334169798033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17685131343235564477845685 1657981063428334169798033)
        ·
          refine ⟨1243485797571250627348525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657981063428334169798033 1243485797571250627348525)
          ·
            refine ⟨466307174089218985255697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1243485797571250627348525 466307174089218985255697)
            ·
              refine ⟨349730380566914238941773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466307174089218985255697 349730380566914238941773)
              ·
                refine ⟨131148892712592839603165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349730380566914238941773 131148892712592839603165)
                ·
                  rfl

theorem cell19_431007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 3].length) (baseStart_431007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431007 prefixEnd_431007 := by exact prefixLift 431007
  have htrace : WordTrace (prefixWord ++ tailWord_431007) baseStart_431007 baseEnd_431007 := by
    simpa [prefixWord, tailWord_431007, baseEnd_431007] using wordTrace_append hprefix tailTrace_431007
  have hstable : (prefixWord ++ tailWord_431007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431007).length < 2 ^ (prefixWord ++ tailWord_431007).sum := by decide
  have hdescent : baseEnd_431007 < baseStart_431007 := by decide
  rcases family_descends (prefixWord ++ tailWord_431007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431009 : List Nat := [1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_431009 : Nat := 118140960795 + 431009 * 2 ^ 59
def prefixEnd_431009 : Nat := 4983230072969 + 3 ^ 40 * 431009 * 2
def baseEnd_431009 : Nat := 131149501282257427558715

theorem tailTrace_431009 : CollatzResearch.WordTrace tailWord_431009 prefixEnd_431009 131149501282257427558715 := by
  unfold tailWord_431009
  simp only [CollatzResearch.WordTrace]
  refine ⟨15720189695535478321880081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10480126463690318881253387 15720189695535478321880081)
  ·
    refine ⟨11790142271651608741410061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15720189695535478321880081 11790142271651608741410061)
    ·
      refine ⟨4421303351869353278028773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11790142271651608741410061 4421303351869353278028773)
      ·
        refine ⟨828994378475503739630395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4421303351869353278028773 828994378475503739630395)
        ·
          refine ⟨1243491567713255609445593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828994378475503739630395 1243491567713255609445593)
          ·
            refine ⟨932618675784941707084195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1243491567713255609445593 932618675784941707084195)
            ·
              refine ⟨1398928013677412560626293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932618675784941707084195 1398928013677412560626293)
              ·
                refine ⟨131149501282257427558715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1398928013677412560626293 131149501282257427558715)
                ·
                  rfl

theorem cell19_431009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_431009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431009 prefixEnd_431009 := by exact prefixLift 431009
  have htrace : WordTrace (prefixWord ++ tailWord_431009) baseStart_431009 baseEnd_431009 := by
    simpa [prefixWord, tailWord_431009, baseEnd_431009] using wordTrace_append hprefix tailTrace_431009
  have hstable : (prefixWord ++ tailWord_431009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431009).length < 2 ^ (prefixWord ++ tailWord_431009).sum := by decide
  have hdescent : baseEnd_431009 < baseStart_431009 := by decide
  rcases family_descends (prefixWord ++ tailWord_431009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431182 : List Nat := [4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_431182 : Nat := 118140960795 + 431182 * 2 ^ 59
def prefixEnd_431182 : Nat := 4983230072969 + 3 ^ 40 * 431182 * 2
def baseEnd_431182 : Nat := 131202142558244285713799

theorem tailTrace_431182 : CollatzResearch.WordTrace tailWord_431182 prefixEnd_431182 131202142558244285713799 := by
  unfold tailWord_431182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965812440488591108490975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10484333015939152578618533 1965812440488591108490975)
  ·
    refine ⟨2948718660732886662736463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1965812440488591108490975 2948718660732886662736463)
    ·
      refine ⟨4423077991099329994104695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948718660732886662736463 4423077991099329994104695)
      ·
        refine ⟨6634616986648994991157043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4423077991099329994104695 6634616986648994991157043)
        ·
          refine ⟨9951925479973492486735565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6634616986648994991157043 9951925479973492486735565)
          ·
            refine ⟨3731972054990059682525837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9951925479973492486735565 3731972054990059682525837)
            ·
              refine ⟨1399489520621272380947189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3731972054990059682525837 1399489520621272380947189)
              ·
                refine ⟨131202142558244285713799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1399489520621272380947189 131202142558244285713799)
                ·
                  rfl

theorem cell19_431182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_431182 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431182 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431182 prefixEnd_431182 := by exact prefixLift 431182
  have htrace : WordTrace (prefixWord ++ tailWord_431182) baseStart_431182 baseEnd_431182 := by
    simpa [prefixWord, tailWord_431182, baseEnd_431182] using wordTrace_append hprefix tailTrace_431182
  have hstable : (prefixWord ++ tailWord_431182).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431182).length < 2 ^ (prefixWord ++ tailWord_431182).sum := by decide
  have hdescent : baseEnd_431182 < baseStart_431182 := by decide
  rcases family_descends (prefixWord ++ tailWord_431182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431197 : List Nat := [1, 4, 4, 1, 2, 2, 5]
def baseStart_431197 : Nat := 118140960795 + 431197 * 2 ^ 59
def prefixEnd_431197 : Nat := 4983230072969 + 3 ^ 40 * 431197 * 2
def baseEnd_431197 : Nat := 43735568943576231793475

theorem tailTrace_431197 : CollatzResearch.WordTrace tailWord_431197 prefixEnd_431197 43735568943576231793475 := by
  unfold tailWord_431197
  simp only [CollatzResearch.WordTrace]
  refine ⟨15727046618854386429723845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10484697745902924286482563 15727046618854386429723845)
  ·
    refine ⟨2948821241035197455573221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15727046618854386429723845 2948821241035197455573221)
    ·
      refine ⟨552903982694099522919979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2948821241035197455573221 552903982694099522919979)
      ·
        refine ⟨829355974041149284379969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552903982694099522919979 829355974041149284379969)
        ·
          refine ⟨622016980530861963284977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 829355974041149284379969 622016980530861963284977)
          ·
            refine ⟨466512735398146472463733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622016980530861963284977 466512735398146472463733)
            ·
              refine ⟨43735568943576231793475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 466512735398146472463733 43735568943576231793475)
              ·
                rfl

theorem cell19_431197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_431197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431197 prefixEnd_431197 := by exact prefixLift 431197
  have htrace : WordTrace (prefixWord ++ tailWord_431197) baseStart_431197 baseEnd_431197 := by
    simpa [prefixWord, tailWord_431197, baseEnd_431197] using wordTrace_append hprefix tailTrace_431197
  have hstable : (prefixWord ++ tailWord_431197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431197).length < 2 ^ (prefixWord ++ tailWord_431197).sum := by decide
  have hdescent : baseEnd_431197 < baseStart_431197 := by decide
  rcases family_descends (prefixWord ++ tailWord_431197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431254 : List Nat := [5, 3, 2, 9]
def baseStart_431254 : Nat := 118140960795 + 431254 * 2 ^ 59
def prefixEnd_431254 : Nat := 4983230072969 + 3 ^ 40 * 431254 * 2
def baseEnd_431254 : Nat := 1620050013162585828563

theorem tailTrace_431254 : CollatzResearch.WordTrace tailWord_431254 prefixEnd_431254 1620050013162585828563 := by
  unfold tailWord_431254
  simp only [CollatzResearch.WordTrace]
  refine ⟨983070348727992822784301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10486083719765256776365877 983070348727992822784301)
  ·
    refine ⟨368651380772997308544113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 983070348727992822784301 368651380772997308544113)
    ·
      refine ⟨276488535579747981408085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368651380772997308544113 276488535579747981408085)
      ·
        refine ⟨1620050013162585828563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 276488535579747981408085 1620050013162585828563)
        ·
          rfl

theorem cell19_431254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 9].length) (baseStart_431254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431254 prefixEnd_431254 := by exact prefixLift 431254
  have htrace : WordTrace (prefixWord ++ tailWord_431254) baseStart_431254 baseEnd_431254 := by
    simpa [prefixWord, tailWord_431254, baseEnd_431254] using wordTrace_append hprefix tailTrace_431254
  have hstable : (prefixWord ++ tailWord_431254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431254).length < 2 ^ (prefixWord ++ tailWord_431254).sum := by decide
  have hdescent : baseEnd_431254 < baseStart_431254 := by decide
  rcases family_descends (prefixWord ++ tailWord_431254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431258 : List Nat := [3, 1, 1, 5, 1, 8]
def baseStart_431258 : Nat := 118140960795 + 431258 * 2 ^ 59
def prefixEnd_431258 : Nat := 4983230072969 + 3 ^ 40 * 431258 * 2
def baseEnd_431258 : Nat := 14580585356166514224967

theorem tailTrace_431258 : CollatzResearch.WordTrace tailWord_431258 prefixEnd_431258 14580585356166514224967 := by
  unfold tailWord_431258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3932317867908348461923607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10486180981088929231796285 3932317867908348461923607)
  ·
    refine ⟨5898476801862522692885411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3932317867908348461923607 5898476801862522692885411)
    ·
      refine ⟨8847715202793784039328117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5898476801862522692885411 8847715202793784039328117)
      ·
        refine ⟨829473300261917253687011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8847715202793784039328117 829473300261917253687011)
        ·
          refine ⟨1244209950392875880530517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829473300261917253687011 1244209950392875880530517)
          ·
            refine ⟨14580585356166514224967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1244209950392875880530517 14580585356166514224967)
            ·
              rfl

theorem cell19_431258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 8].length) (baseStart_431258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431258 prefixEnd_431258 := by exact prefixLift 431258
  have htrace : WordTrace (prefixWord ++ tailWord_431258) baseStart_431258 baseEnd_431258 := by
    simpa [prefixWord, tailWord_431258, baseEnd_431258] using wordTrace_append hprefix tailTrace_431258
  have hstable : (prefixWord ++ tailWord_431258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431258).length < 2 ^ (prefixWord ++ tailWord_431258).sum := by decide
  have hdescent : baseEnd_431258 < baseStart_431258 := by decide
  rcases family_descends (prefixWord ++ tailWord_431258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431372 : List Nat := [2, 2, 1, 2, 2, 5, 5]
def baseStart_431372 : Nat := 118140960795 + 431372 * 2 ^ 59
def prefixEnd_431372 : Nat := 4983230072969 + 3 ^ 40 * 431372 * 2
def baseEnd_431372 : Nat := 43753318892126713830353

theorem tailTrace_431372 : CollatzResearch.WordTrace tailWord_431372 prefixEnd_431372 43753318892126713830353 := by
  unfold tailWord_431372
  simp only [CollatzResearch.WordTrace]
  refine ⟨7866714696610195658672185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10488952928813594211562913 7866714696610195658672185)
  ·
    refine ⟨5900036022457646744004139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7866714696610195658672185 5900036022457646744004139)
    ·
      refine ⟨8850054033686470116006209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5900036022457646744004139 8850054033686470116006209)
      ·
        refine ⟨6637540525264852587004657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8850054033686470116006209 6637540525264852587004657)
        ·
          refine ⟨4978155393948639440253493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6637540525264852587004657 4978155393948639440253493)
          ·
            refine ⟨466702068182684947523765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4978155393948639440253493 466702068182684947523765)
            ·
              refine ⟨43753318892126713830353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 466702068182684947523765 43753318892126713830353)
              ·
                rfl

theorem cell19_431372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_431372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431372 prefixEnd_431372 := by exact prefixLift 431372
  have htrace : WordTrace (prefixWord ++ tailWord_431372) baseStart_431372 baseEnd_431372 := by
    simpa [prefixWord, tailWord_431372, baseEnd_431372] using wordTrace_append hprefix tailTrace_431372
  have hstable : (prefixWord ++ tailWord_431372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431372).length < 2 ^ (prefixWord ++ tailWord_431372).sum := by decide
  have hdescent : baseEnd_431372 < baseStart_431372 := by decide
  rcases family_descends (prefixWord ++ tailWord_431372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431389 : List Nat := [1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_431389 : Nat := 118140960795 + 431389 * 2 ^ 59
def prefixEnd_431389 : Nat := 4983230072969 + 3 ^ 40 * 431389 * 2
def baseEnd_431389 : Nat := 131265129518529139113235

theorem tailTrace_431389 : CollatzResearch.WordTrace tailWord_431389 prefixEnd_431389 131265129518529139113235 := by
  unfold tailWord_431389
  simp only [CollatzResearch.WordTrace]
  refine ⟨15734049434158803220713221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10489366289439202147142147 15734049434158803220713221)
  ·
    refine ⟨2950134268904775603883729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15734049434158803220713221 2950134268904775603883729)
    ·
      refine ⟨2212600701678581702912797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2950134268904775603883729 2212600701678581702912797)
      ·
        refine ⟨829725263129468138592299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2212600701678581702912797 829725263129468138592299)
        ·
          refine ⟨1244587894694202207888449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829725263129468138592299 1244587894694202207888449)
          ·
            refine ⟨933440921020651655916337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244587894694202207888449 933440921020651655916337)
            ·
              refine ⟨700080690765488741937253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933440921020651655916337 700080690765488741937253)
              ·
                refine ⟨131265129518529139113235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700080690765488741937253 131265129518529139113235)
                ·
                  rfl

theorem cell19_431389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_431389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431389 prefixEnd_431389 := by exact prefixLift 431389
  have htrace : WordTrace (prefixWord ++ tailWord_431389) baseStart_431389 baseEnd_431389 := by
    simpa [prefixWord, tailWord_431389, baseEnd_431389] using wordTrace_append hprefix tailTrace_431389
  have hstable : (prefixWord ++ tailWord_431389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431389).length < 2 ^ (prefixWord ++ tailWord_431389).sum := by decide
  have hdescent : baseEnd_431389 < baseStart_431389 := by decide
  rcases family_descends (prefixWord ++ tailWord_431389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431410 : List Nat := [3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_431410 : Nat := 118140960795 + 431410 * 2 ^ 59
def prefixEnd_431410 : Nat := 4983230072969 + 3 ^ 40 * 431410 * 2
def baseEnd_431410 : Nat := 131271519500007312646511

theorem tailTrace_431410 : CollatzResearch.WordTrace tailWord_431410 prefixEnd_431410 131271519500007312646511 := by
  unfold tailWord_431410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3933703841770680951806921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10489876911388482538151789 3933703841770680951806921)
  ·
    refine ⟨2950277881328010713855191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3933703841770680951806921 2950277881328010713855191)
    ·
      refine ⟨4425416821992016070782787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2950277881328010713855191 4425416821992016070782787)
      ·
        refine ⟨6638125232988024106174181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4425416821992016070782787 6638125232988024106174181)
        ·
          refine ⟨1244648481185254519907659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6638125232988024106174181 1244648481185254519907659)
          ·
            refine ⟨1866972721777881779861489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244648481185254519907659 1866972721777881779861489)
            ·
              refine ⟨1400229541333411334896117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866972721777881779861489 1400229541333411334896117)
              ·
                refine ⟨131271519500007312646511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1400229541333411334896117 131271519500007312646511)
                ·
                  rfl

theorem cell19_431410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_431410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431410 prefixEnd_431410 := by exact prefixLift 431410
  have htrace : WordTrace (prefixWord ++ tailWord_431410) baseStart_431410 baseEnd_431410 := by
    simpa [prefixWord, tailWord_431410, baseEnd_431410] using wordTrace_append hprefix tailTrace_431410
  have hstable : (prefixWord ++ tailWord_431410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431410).length < 2 ^ (prefixWord ++ tailWord_431410).sum := by decide
  have hdescent : baseEnd_431410 < baseStart_431410 := by decide
  rcases family_descends (prefixWord ++ tailWord_431410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431431 : List Nat := [1, 1, 4, 1, 2, 10]
def baseStart_431431 : Nat := 118140960795 + 431431 * 2 ^ 59
def prefixEnd_431431 : Nat := 4983230072969 + 3 ^ 40 * 431431 * 2
def baseEnd_431431 : Nat := 14586434386831720686643

theorem tailTrace_431431 : CollatzResearch.WordTrace tailWord_431431 prefixEnd_431431 14586434386831720686643 := by
  unfold tailWord_431431
  simp only [CollatzResearch.WordTrace]
  refine ⟨15735581300006644393742147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10490387533337762929161431 15735581300006644393742147)
  ·
    refine ⟨23603371950009966590613221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15735581300006644393742147 23603371950009966590613221)
    ·
      refine ⟨4425632240626868735739979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23603371950009966590613221 4425632240626868735739979)
      ·
        refine ⟨6638448360940303103609969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4425632240626868735739979 6638448360940303103609969)
        ·
          refine ⟨4978836270705227327707477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6638448360940303103609969 4978836270705227327707477)
          ·
            refine ⟨14586434386831720686643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4978836270705227327707477 14586434386831720686643)
            ·
              rfl

theorem cell19_431431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 10].length) (baseStart_431431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431431 prefixEnd_431431 := by exact prefixLift 431431
  have htrace : WordTrace (prefixWord ++ tailWord_431431) baseStart_431431 baseEnd_431431 := by
    simpa [prefixWord, tailWord_431431, baseEnd_431431] using wordTrace_append hprefix tailTrace_431431
  have hstable : (prefixWord ++ tailWord_431431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431431).length < 2 ^ (prefixWord ++ tailWord_431431).sum := by decide
  have hdescent : baseEnd_431431 < baseStart_431431 := by decide
  rcases family_descends (prefixWord ++ tailWord_431431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431518 : List Nat := [4, 3, 1, 2, 2, 2, 2, 3]
def baseStart_431518 : Nat := 118140960795 + 431518 * 2 ^ 59
def prefixEnd_431518 : Nat := 4983230072969 + 3 ^ 40 * 431518 * 2
def baseEnd_431518 : Nat := 131304382261895062246217

theorem tailTrace_431518 : CollatzResearch.WordTrace tailWord_431518 prefixEnd_431518 131304382261895062246217 := by
  unfold tailWord_431518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967344306336432281519901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10492502967127638834772805 1967344306336432281519901)
  ·
    refine ⟨737754114876162105569963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1967344306336432281519901 737754114876162105569963)
    ·
      refine ⟨1106631172314243158354945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 737754114876162105569963 1106631172314243158354945)
      ·
        refine ⟨829973379235682368766209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1106631172314243158354945 829973379235682368766209)
        ·
          refine ⟨622480034426761776574657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 829973379235682368766209 622480034426761776574657)
          ·
            refine ⟨466860025820071332430993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622480034426761776574657 466860025820071332430993)
            ·
              refine ⟨350145019365053499323245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466860025820071332430993 350145019365053499323245)
              ·
                refine ⟨131304382261895062246217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350145019365053499323245 131304382261895062246217)
                ·
                  rfl

theorem cell19_431518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_431518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431518 prefixEnd_431518 := by exact prefixLift 431518
  have htrace : WordTrace (prefixWord ++ tailWord_431518) baseStart_431518 baseEnd_431518 := by
    simpa [prefixWord, tailWord_431518, baseEnd_431518] using wordTrace_append hprefix tailTrace_431518
  have hstable : (prefixWord ++ tailWord_431518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431518).length < 2 ^ (prefixWord ++ tailWord_431518).sum := by decide
  have hdescent : baseEnd_431518 < baseStart_431518 := by decide
  rcases family_descends (prefixWord ++ tailWord_431518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431522 : List Nat := [3, 3, 1, 2, 1, 2, 4, 3]
def baseStart_431522 : Nat := 118140960795 + 431522 * 2 ^ 59
def prefixEnd_431522 : Nat := 4983230072969 + 3 ^ 40 * 431522 * 2
def baseEnd_431522 : Nat := 131305599401224238157317

theorem tailTrace_431522 : CollatzResearch.WordTrace tailWord_431522 prefixEnd_431522 131305599401224238157317 := by
  unfold tailWord_431522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3934725085669241733826205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10492600228451311290203213 3934725085669241733826205)
  ·
    refine ⟨1475521907125965650184827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3934725085669241733826205 1475521907125965650184827)
    ·
      refine ⟨2213282860688948475277241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475521907125965650184827 2213282860688948475277241)
      ·
        refine ⟨1659962145516711356457931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2213282860688948475277241 1659962145516711356457931)
        ·
          refine ⟨2489943218275067034686897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659962145516711356457931 2489943218275067034686897)
          ·
            refine ⟨1867457413706300276015173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2489943218275067034686897 1867457413706300276015173)
            ·
              refine ⟨350148265069931301752845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1867457413706300276015173 350148265069931301752845)
              ·
                refine ⟨131305599401224238157317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350148265069931301752845 131305599401224238157317)
                ·
                  rfl

theorem cell19_431522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_431522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431522 prefixEnd_431522 := by exact prefixLift 431522
  have htrace : WordTrace (prefixWord ++ tailWord_431522) baseStart_431522 baseEnd_431522 := by
    simpa [prefixWord, tailWord_431522, baseEnd_431522] using wordTrace_append hprefix tailTrace_431522
  have hstable : (prefixWord ++ tailWord_431522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431522).length < 2 ^ (prefixWord ++ tailWord_431522).sum := by decide
  have hdescent : baseEnd_431522 < baseStart_431522 := by decide
  rcases family_descends (prefixWord ++ tailWord_431522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431554 : List Nat := [3, 5, 2, 1, 1, 1, 2, 4]
def baseStart_431554 : Nat := 118140960795 + 431554 * 2 ^ 59
def prefixEnd_431554 : Nat := 4983230072969 + 3 ^ 40 * 431554 * 2
def baseEnd_431554 : Nat := 131315336515857645446119

theorem tailTrace_431554 : CollatzResearch.WordTrace tailWord_431554 prefixEnd_431554 131315336515857645446119 := by
  unfold tailWord_431554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935016869640259100117429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10493378319040690933646477 3935016869640259100117429)
  ·
    refine ⟨368907831528774290636009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3935016869640259100117429 368907831528774290636009)
    ·
      refine ⟨276680873646580717977007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368907831528774290636009 276680873646580717977007)
      ·
        refine ⟨415021310469871076965511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276680873646580717977007 415021310469871076965511)
        ·
          refine ⟨622531965704806615448267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415021310469871076965511 622531965704806615448267)
          ·
            refine ⟨933797948557209923172401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622531965704806615448267 933797948557209923172401)
            ·
              refine ⟨700348461417907442379301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933797948557209923172401 700348461417907442379301)
              ·
                refine ⟨131315336515857645446119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700348461417907442379301 131315336515857645446119)
                ·
                  rfl

theorem cell19_431554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_431554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431554 prefixEnd_431554 := by exact prefixLift 431554
  have htrace : WordTrace (prefixWord ++ tailWord_431554) baseStart_431554 baseEnd_431554 := by
    simpa [prefixWord, tailWord_431554, baseEnd_431554] using wordTrace_append hprefix tailTrace_431554
  have hstable : (prefixWord ++ tailWord_431554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431554).length < 2 ^ (prefixWord ++ tailWord_431554).sum := by decide
  have hdescent : baseEnd_431554 < baseStart_431554 := by decide
  rcases family_descends (prefixWord ++ tailWord_431554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431562 : List Nat := [3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_431562 : Nat := 118140960795 + 431562 * 2 ^ 59
def prefixEnd_431562 : Nat := 4983230072969 + 3 ^ 40 * 431562 * 2
def baseEnd_431562 : Nat := 131317770794515997268319

theorem tailTrace_431562 : CollatzResearch.WordTrace tailWord_431562 prefixEnd_431562 131317770794515997268319 := by
  unfold tailWord_431562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935089815633013441690235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10493572841688035844507293 3935089815633013441690235)
  ·
    refine ⟨5902634723449520162535353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3935089815633013441690235 5902634723449520162535353)
    ·
      refine ⟨4426976042587140121901515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5902634723449520162535353 4426976042587140121901515)
      ·
        refine ⟨6640464063880710182852273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426976042587140121901515 6640464063880710182852273)
        ·
          refine ⟨4980348047910532637139205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6640464063880710182852273 4980348047910532637139205)
          ·
            refine ⟨933815258983224869463601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4980348047910532637139205 933815258983224869463601)
            ·
              refine ⟨700361444237418652097701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933815258983224869463601 700361444237418652097701)
              ·
                refine ⟨131317770794515997268319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700361444237418652097701 131317770794515997268319)
                ·
                  rfl

theorem cell19_431562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_431562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431562 prefixEnd_431562 := by exact prefixLift 431562
  have htrace : WordTrace (prefixWord ++ tailWord_431562) baseStart_431562 baseEnd_431562 := by
    simpa [prefixWord, tailWord_431562, baseEnd_431562] using wordTrace_append hprefix tailTrace_431562
  have hstable : (prefixWord ++ tailWord_431562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431562).length < 2 ^ (prefixWord ++ tailWord_431562).sum := by decide
  have hdescent : baseEnd_431562 < baseStart_431562 := by decide
  rcases family_descends (prefixWord ++ tailWord_431562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431581 : List Nat := [1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_431581 : Nat := 118140960795 + 431581 * 2 ^ 59
def prefixEnd_431581 : Nat := 4983230072969 + 3 ^ 40 * 431581 * 2
def baseEnd_431581 : Nat := 131323552206329582846045

theorem tailTrace_431581 : CollatzResearch.WordTrace tailWord_431581 prefixEnd_431581 131323552206329582846045 := by
  unfold tailWord_431581
  simp only [CollatzResearch.WordTrace]
  refine ⟨15741052249463220011702597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10494034832975480007801731 15741052249463220011702597)
  ·
    refine ⟨2951447296774353752194237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15741052249463220011702597 2951447296774353752194237)
    ·
      refine ⟨1106792736290382657072839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2951447296774353752194237 1106792736290382657072839)
      ·
        refine ⟨1660189104435573985609259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106792736290382657072839 1660189104435573985609259)
        ·
          refine ⟨2490283656653360978413889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660189104435573985609259 2490283656653360978413889)
          ·
            refine ⟨1867712742490020733810417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490283656653360978413889 1867712742490020733810417)
            ·
              refine ⟨1400784556867515550357813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867712742490020733810417 1400784556867515550357813)
              ·
                refine ⟨131323552206329582846045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1400784556867515550357813 131323552206329582846045)
                ·
                  rfl

theorem cell19_431581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_431581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431581 prefixEnd_431581 := by exact prefixLift 431581
  have htrace : WordTrace (prefixWord ++ tailWord_431581) baseStart_431581 baseEnd_431581 := by
    simpa [prefixWord, tailWord_431581, baseEnd_431581] using wordTrace_append hprefix tailTrace_431581
  have hstable : (prefixWord ++ tailWord_431581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431581).length < 2 ^ (prefixWord ++ tailWord_431581).sum := by decide
  have hdescent : baseEnd_431581 < baseStart_431581 := by decide
  rcases family_descends (prefixWord ++ tailWord_431581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431583 : List Nat := [1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_431583 : Nat := 118140960795 + 431583 * 2 ^ 59
def prefixEnd_431583 : Nat := 4983230072969 + 3 ^ 40 * 431583 * 2
def baseEnd_431583 : Nat := 131324160775994170801595

theorem tailTrace_431583 : CollatzResearch.WordTrace tailWord_431583 prefixEnd_431583 131324160775994170801595 := by
  unfold tailWord_431583
  simp only [CollatzResearch.WordTrace]
  refine ⟨15741125195455974353275403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10494083463637316235516935 15741125195455974353275403)
  ·
    refine ⟨23611687793183961529913105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15741125195455974353275403 23611687793183961529913105)
    ·
      refine ⟨17708765844887971147434829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23611687793183961529913105 17708765844887971147434829)
      ·
        refine ⟨6640787191832989180288061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17708765844887971147434829 6640787191832989180288061)
        ·
          refine ⟨2490295196937370942608023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6640787191832989180288061 2490295196937370942608023)
          ·
            refine ⟨3735442795406056413912035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490295196937370942608023 3735442795406056413912035)
            ·
              refine ⟨5603164193109084620868053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735442795406056413912035 5603164193109084620868053)
              ·
                refine ⟨131324160775994170801595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5603164193109084620868053 131324160775994170801595)
                ·
                  rfl

theorem cell19_431583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_431583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431583 prefixEnd_431583 := by exact prefixLift 431583
  have htrace : WordTrace (prefixWord ++ tailWord_431583) baseStart_431583 baseEnd_431583 := by
    simpa [prefixWord, tailWord_431583, baseEnd_431583] using wordTrace_append hprefix tailTrace_431583
  have hstable : (prefixWord ++ tailWord_431583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431583).length < 2 ^ (prefixWord ++ tailWord_431583).sum := by decide
  have hdescent : baseEnd_431583 < baseStart_431583 := by decide
  rcases family_descends (prefixWord ++ tailWord_431583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431617 : List Nat := [1, 2, 4, 1, 4, 2, 1, 4]
def baseStart_431617 : Nat := 118140960795 + 431617 * 2 ^ 59
def prefixEnd_431617 : Nat := 4983230072969 + 3 ^ 40 * 431617 * 2
def baseEnd_431617 : Nat := 131334506460292166045947

theorem tailTrace_431617 : CollatzResearch.WordTrace tailWord_431617 prefixEnd_431617 131334506460292166045947 := by
  unfold tailWord_431617
  simp only [CollatzResearch.WordTrace]
  refine ⟨15742365277332798160013105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10494910184888532106675403 15742365277332798160013105)
  ·
    refine ⟨11806773957999598620009829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15742365277332798160013105 11806773957999598620009829)
    ·
      refine ⟨2213770117124924741251843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11806773957999598620009829 2213770117124924741251843)
      ·
        refine ⟨3320655175687387111877765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213770117124924741251843 3320655175687387111877765)
        ·
          refine ⟨622622845441385083477081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3320655175687387111877765 622622845441385083477081)
          ·
            refine ⟨466967134081038812607811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622622845441385083477081 466967134081038812607811)
            ·
              refine ⟨700450701121558218911717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466967134081038812607811 700450701121558218911717)
              ·
                refine ⟨131334506460292166045947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700450701121558218911717 131334506460292166045947)
                ·
                  rfl

theorem cell19_431617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_431617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431617 prefixEnd_431617 := by exact prefixLift 431617
  have htrace : WordTrace (prefixWord ++ tailWord_431617) baseStart_431617 baseEnd_431617 := by
    simpa [prefixWord, tailWord_431617, baseEnd_431617] using wordTrace_append hprefix tailTrace_431617
  have hstable : (prefixWord ++ tailWord_431617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431617).length < 2 ^ (prefixWord ++ tailWord_431617).sum := by decide
  have hdescent : baseEnd_431617 < baseStart_431617 := by decide
  rcases family_descends (prefixWord ++ tailWord_431617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431693 : List Nat := [1, 6, 1, 1, 3, 1, 1, 5]
def baseStart_431693 : Nat := 118140960795 + 431693 * 2 ^ 59
def prefixEnd_431693 : Nat := 4983230072969 + 3 ^ 40 * 431693 * 2
def baseEnd_431693 : Nat := 131357632107546508356851

theorem tailTrace_431693 : CollatzResearch.WordTrace tailWord_431693 prefixEnd_431693 131357632107546508356851 := by
  unfold tailWord_431693
  simp only [CollatzResearch.WordTrace]
  refine ⟨15745137225057463139779733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10496758150038308759853155 15745137225057463139779733)
  ·
    refine ⟨738053307424568584677175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15745137225057463139779733 738053307424568584677175)
    ·
      refine ⟨1107079961136852877015763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738053307424568584677175 1107079961136852877015763)
      ·
        refine ⟨1660619941705279315523645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107079961136852877015763 1660619941705279315523645)
        ·
          refine ⟨622732478139479743321367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1660619941705279315523645 622732478139479743321367)
          ·
            refine ⟨934098717209219614982051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622732478139479743321367 934098717209219614982051)
            ·
              refine ⟨1401148075813829422473077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934098717209219614982051 1401148075813829422473077)
              ·
                refine ⟨131357632107546508356851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1401148075813829422473077 131357632107546508356851)
                ·
                  rfl

theorem cell19_431693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_431693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431693 prefixEnd_431693 := by exact prefixLift 431693
  have htrace : WordTrace (prefixWord ++ tailWord_431693) baseStart_431693 baseEnd_431693 := by
    simpa [prefixWord, tailWord_431693, baseEnd_431693] using wordTrace_append hprefix tailTrace_431693
  have hstable : (prefixWord ++ tailWord_431693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431693).length < 2 ^ (prefixWord ++ tailWord_431693).sum := by decide
  have hdescent : baseEnd_431693 < baseStart_431693 := by decide
  rcases family_descends (prefixWord ++ tailWord_431693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431697 : List Nat := [1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_431697 : Nat := 118140960795 + 431697 * 2 ^ 59
def prefixEnd_431697 : Nat := 4983230072969 + 3 ^ 40 * 431697 * 2
def baseEnd_431697 : Nat := 131358849246875684267951

theorem tailTrace_431697 : CollatzResearch.WordTrace tailWord_431697 prefixEnd_431697 131358849246875684267951 := by
  unfold tailWord_431697
  simp only [CollatzResearch.WordTrace]
  refine ⟨15745283117042971822925345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10496855411361981215283563 15745283117042971822925345)
  ·
    refine ⟨11808962337782228867194009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15745283117042971822925345 11808962337782228867194009)
    ·
      refine ⟨8856721753336671650395507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11808962337782228867194009 8856721753336671650395507)
      ·
        refine ⟨13285082630005007475593261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8856721753336671650395507 13285082630005007475593261)
        ·
          refine ⟨4981905986251877803347473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13285082630005007475593261 4981905986251877803347473)
          ·
            refine ⟨3736429489688908352510605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4981905986251877803347473 3736429489688908352510605)
            ·
              refine ⟨1401161058633340632191477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3736429489688908352510605 1401161058633340632191477)
              ·
                refine ⟨131358849246875684267951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1401161058633340632191477 131358849246875684267951)
                ·
                  rfl

theorem cell19_431697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_431697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431697 prefixEnd_431697 := by exact prefixLift 431697
  have htrace : WordTrace (prefixWord ++ tailWord_431697) baseStart_431697 baseEnd_431697 := by
    simpa [prefixWord, tailWord_431697, baseEnd_431697] using wordTrace_append hprefix tailTrace_431697
  have hstable : (prefixWord ++ tailWord_431697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431697).length < 2 ^ (prefixWord ++ tailWord_431697).sum := by decide
  have hdescent : baseEnd_431697 < baseStart_431697 := by decide
  rcases family_descends (prefixWord ++ tailWord_431697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431716 : List Nat := [2, 3, 1, 1, 2, 3, 7]
def baseStart_431716 : Nat := 118140960795 + 431716 * 2 ^ 59
def prefixEnd_431716 : Nat := 4983230072969 + 3 ^ 40 * 431716 * 2
def baseEnd_431716 : Nat := 43788210219563089948559

theorem tailTrace_431716 : CollatzResearch.WordTrace tailWord_431716 prefixEnd_431716 43788210219563089948559 := by
  unfold tailWord_431716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7872988051987069033933501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10497317402649425378578001 7872988051987069033933501)
  ·
    refine ⟨2952370519495150887725063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7872988051987069033933501 2952370519495150887725063)
    ·
      refine ⟨4428555779242726331587595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2952370519495150887725063 4428555779242726331587595)
      ·
        refine ⟨6642833668864089497381393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4428555779242726331587595 6642833668864089497381393)
        ·
          refine ⟨4982125251648067123036045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6642833668864089497381393 4982125251648067123036045)
          ·
            refine ⟨1868296969368025171138517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4982125251648067123036045 1868296969368025171138517)
            ·
              refine ⟨43788210219563089948559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1868296969368025171138517 43788210219563089948559)
              ·
                rfl

theorem cell19_431716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_431716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431716 prefixEnd_431716 := by exact prefixLift 431716
  have htrace : WordTrace (prefixWord ++ tailWord_431716) baseStart_431716 baseEnd_431716 := by
    simpa [prefixWord, tailWord_431716, baseEnd_431716] using wordTrace_append hprefix tailTrace_431716
  have hstable : (prefixWord ++ tailWord_431716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431716).length < 2 ^ (prefixWord ++ tailWord_431716).sum := by decide
  have hdescent : baseEnd_431716 < baseStart_431716 := by decide
  rcases family_descends (prefixWord ++ tailWord_431716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431733 : List Nat := [1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_431733 : Nat := 118140960795 + 431733 * 2 ^ 59
def prefixEnd_431733 : Nat := 4983230072969 + 3 ^ 40 * 431733 * 2
def baseEnd_431733 : Nat := 131369803500838267467853

theorem tailTrace_431733 : CollatzResearch.WordTrace tailWord_431733 prefixEnd_431733 131369803500838267467853 := by
  unfold tailWord_431733
  simp only [CollatzResearch.WordTrace]
  refine ⟨15746596144912549971235853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10497730763275033314157235 15746596144912549971235853)
  ·
    refine ⟨5904973554342206239213445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15746596144912549971235853 5904973554342206239213445)
    ·
      refine ⟨1107182541439163669852521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5904973554342206239213445 1107182541439163669852521)
      ·
        refine ⟨830386906079372752389391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1107182541439163669852521 830386906079372752389391)
        ·
          refine ⟨1245580359119059128584087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830386906079372752389391 1245580359119059128584087)
          ·
            refine ⟨1868370538678588692876131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245580359119059128584087 1868370538678588692876131)
            ·
              refine ⟨2802555808017883039314197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868370538678588692876131 2802555808017883039314197)
              ·
                refine ⟨131369803500838267467853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2802555808017883039314197 131369803500838267467853)
                ·
                  rfl

theorem cell19_431733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_431733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431733 prefixEnd_431733 := by exact prefixLift 431733
  have htrace : WordTrace (prefixWord ++ tailWord_431733) baseStart_431733 baseEnd_431733 := by
    simpa [prefixWord, tailWord_431733, baseEnd_431733] using wordTrace_append hprefix tailTrace_431733
  have hstable : (prefixWord ++ tailWord_431733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431733).length < 2 ^ (prefixWord ++ tailWord_431733).sum := by decide
  have hdescent : baseEnd_431733 < baseStart_431733 := by decide
  rcases family_descends (prefixWord ++ tailWord_431733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
