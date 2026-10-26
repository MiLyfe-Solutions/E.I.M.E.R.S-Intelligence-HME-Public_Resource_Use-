import V185TrunkScan23Chunk0293

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1739150 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1739150 : Nat := 118140960795 + 1739150 * 2 ^ 59
def prefixEnd_1739150 : Nat := 4983230072969 + 3 ^ 40 * 1739150 * 2
def baseEnd_1739150 : Nat := 893019880266975801326801

theorem tailTrace_1739150 : CollatzResearch.WordTrace tailWord_1739150 prefixEnd_1739150 893019880266975801326801 := by
  unfold tailWord_1739150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7929001456170506002235863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42288007766242698678591269 7929001456170506002235863)
  ·
    refine ⟨11893502184255759003353795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7929001456170506002235863 11893502184255759003353795)
    ·
      refine ⟨17840253276383638505030693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11893502184255759003353795 17840253276383638505030693)
      ·
        refine ⟨3345047489321932219693255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17840253276383638505030693 3345047489321932219693255)
        ·
          refine ⟨5017571233982898329539883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3345047489321932219693255 5017571233982898329539883)
          ·
            refine ⟨7526356850974347494309825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5017571233982898329539883 7526356850974347494309825)
            ·
              refine ⟨5644767638230760620732369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7526356850974347494309825 5644767638230760620732369)
              ·
                refine ⟨4233575728673070465549277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5644767638230760620732369 4233575728673070465549277)
                ·
                  refine ⟨1587590898252401424580979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4233575728673070465549277 1587590898252401424580979)
                  ·
                    refine ⟨2381386347378602136871469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1587590898252401424580979 2381386347378602136871469)
                    ·
                      refine ⟨893019880266975801326801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2381386347378602136871469 893019880266975801326801)
                      ·
                        rfl

theorem cell23_1739150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1739150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739150 prefixEnd_1739150 := by exact prefixLift 1739150
  have htrace : WordTrace (prefixWord ++ tailWord_1739150) baseStart_1739150 baseEnd_1739150 := by
    simpa [prefixWord, tailWord_1739150, baseEnd_1739150] using wordTrace_append hprefix tailTrace_1739150
  have hstable : (prefixWord ++ tailWord_1739150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739150).length < 2 ^ (prefixWord ++ tailWord_1739150).sum := by decide
  have hdescent : baseEnd_1739150 < baseStart_1739150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739196 : List Nat := [2, 2, 2, 4, 1, 1, 1, 10]
def baseStart_1739196 : Nat := 118140960795 + 1739196 * 2 ^ 59
def prefixEnd_1739196 : Nat := 4983230072969 + 3 ^ 40 * 1739196 * 2
def baseEnd_1739196 : Nat := 33075685199151208198207

theorem tailTrace_1739196 : CollatzResearch.WordTrace tailWord_1739196 prefixEnd_1739196 33075685199151208198207 := by
  unfold tailWord_1739196
  simp only [CollatzResearch.WordTrace]
  refine ⟨31716844703598698937030721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42289126271464931916040961 31716844703598698937030721)
  ·
    refine ⟨23787633527699024202773041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31716844703598698937030721 23787633527699024202773041)
    ·
      refine ⟨17840725145774268152079781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23787633527699024202773041 17840725145774268152079781)
      ·
        refine ⟨3345135964832675278514959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17840725145774268152079781 3345135964832675278514959)
        ·
          refine ⟨5017703947249012917772439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3345135964832675278514959 5017703947249012917772439)
          ·
            refine ⟨7526555920873519376658659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5017703947249012917772439 7526555920873519376658659)
            ·
              refine ⟨11289833881310279064987989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7526555920873519376658659 11289833881310279064987989)
              ·
                refine ⟨33075685199151208198207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11289833881310279064987989 33075685199151208198207)
                ·
                  rfl

theorem cell23_1739196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 10].length) (baseStart_1739196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739196 prefixEnd_1739196 := by exact prefixLift 1739196
  have htrace : WordTrace (prefixWord ++ tailWord_1739196) baseStart_1739196 baseEnd_1739196 := by
    simpa [prefixWord, tailWord_1739196, baseEnd_1739196] using wordTrace_append hprefix tailTrace_1739196
  have hstable : (prefixWord ++ tailWord_1739196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739196).length < 2 ^ (prefixWord ++ tailWord_1739196).sum := by decide
  have hdescent : baseEnd_1739196 < baseStart_1739196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739219 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 7]
def baseStart_1739219 : Nat := 118140960795 + 1739219 * 2 ^ 59
def prefixEnd_1739219 : Nat := 4983230072969 + 3 ^ 40 * 1739219 * 2
def baseEnd_1739219 : Nat := 893055310432136031363983

theorem tailTrace_1739219 : CollatzResearch.WordTrace tailWord_1739219 prefixEnd_1739219 893055310432136031363983 := by
  unfold tailWord_1739219
  simp only [CollatzResearch.WordTrace]
  refine ⟨63434528286114072802148711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42289685524076048534765807 63434528286114072802148711)
  ·
    refine ⟨95151792429171109203223067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63434528286114072802148711 95151792429171109203223067)
    ·
      refine ⟨142727688643756663804834601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95151792429171109203223067 142727688643756663804834601)
      ·
        refine ⟨107045766482817497853625951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142727688643756663804834601 107045766482817497853625951)
        ·
          refine ⟨160568649724226246780438927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107045766482817497853625951 160568649724226246780438927)
          ·
            refine ⟨240852974586339370170658391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160568649724226246780438927 240852974586339370170658391)
            ·
              refine ⟨361279461879509055255987587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240852974586339370170658391 361279461879509055255987587)
              ·
                refine ⟨541919192819263582883981381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361279461879509055255987587 541919192819263582883981381)
                ·
                  refine ⟨101609848653611921790746509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 541919192819263582883981381 101609848653611921790746509)
                  ·
                    refine ⟨38103693245104470671529941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101609848653611921790746509 38103693245104470671529941)
                    ·
                      refine ⟨893055310432136031363983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38103693245104470671529941 893055310432136031363983)
                      ·
                        rfl

theorem cell23_1739219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_1739219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739219 prefixEnd_1739219 := by exact prefixLift 1739219
  have htrace : WordTrace (prefixWord ++ tailWord_1739219) baseStart_1739219 baseEnd_1739219 := by
    simpa [prefixWord, tailWord_1739219, baseEnd_1739219] using wordTrace_append hprefix tailTrace_1739219
  have hstable : (prefixWord ++ tailWord_1739219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739219).length < 2 ^ (prefixWord ++ tailWord_1739219).sum := by decide
  have hdescent : baseEnd_1739219 < baseStart_1739219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739234 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1739234 : Nat := 118140960795 + 1739234 * 2 ^ 59
def prefixEnd_1739234 : Nat := 4983230072969 + 3 ^ 40 * 1739234 * 2
def baseEnd_1739234 : Nat := 297687670880651157558805

theorem tailTrace_1739234 : CollatzResearch.WordTrace tailWord_1739234 prefixEnd_1739234 297687670880651157558805 := by
  unfold tailWord_1739234
  simp only [CollatzResearch.WordTrace]
  refine ⟨15858768845264932590986189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42290050254039820242629837 15858768845264932590986189)
  ·
    refine ⟨5947038316974349721619821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15858768845264932590986189 5947038316974349721619821)
    ·
      refine ⟨2230139368865381145607433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5947038316974349721619821 2230139368865381145607433)
      ·
        refine ⟨1672604526649035859205575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2230139368865381145607433 1672604526649035859205575)
        ·
          refine ⟨2508906789973553788808363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672604526649035859205575 2508906789973553788808363)
          ·
            refine ⟨3763360184960330683212545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508906789973553788808363 3763360184960330683212545)
            ·
              refine ⟨2822520138720248012409409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3763360184960330683212545 2822520138720248012409409)
              ·
                refine ⟨2116890104040186009307057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822520138720248012409409 2116890104040186009307057)
                ·
                  refine ⟨1587667578030139506980293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2116890104040186009307057 1587667578030139506980293)
                  ·
                    refine ⟨297687670880651157558805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1587667578030139506980293 297687670880651157558805)
                    ·
                      rfl

theorem cell23_1739234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1739234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739234 prefixEnd_1739234 := by exact prefixLift 1739234
  have htrace : WordTrace (prefixWord ++ tailWord_1739234) baseStart_1739234 baseEnd_1739234 := by
    simpa [prefixWord, tailWord_1739234, baseEnd_1739234] using wordTrace_append hprefix tailTrace_1739234
  have hstable : (prefixWord ++ tailWord_1739234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739234).length < 2 ^ (prefixWord ++ tailWord_1739234).sum := by decide
  have hdescent : baseEnd_1739234 < baseStart_1739234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739240 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_1739240 : Nat := 118140960795 + 1739240 * 2 ^ 59
def prefixEnd_1739240 : Nat := 4983230072969 + 3 ^ 40 * 1739240 * 2
def baseEnd_1739240 : Nat := 893066093525880449201387

theorem tailTrace_1739240 : CollatzResearch.WordTrace tailWord_1739240 prefixEnd_1739240 893066093525880449201387 := by
  unfold tailWord_1739240
  simp only [CollatzResearch.WordTrace]
  refine ⟨31717647109518996694331587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42290196146025328925775449 31717647109518996694331587)
  ·
    refine ⟨47576470664278495041497381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31717647109518996694331587 47576470664278495041497381)
    ·
      refine ⟨8920588249552217820280759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47576470664278495041497381 8920588249552217820280759)
      ·
        refine ⟨13380882374328326730421139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8920588249552217820280759 13380882374328326730421139)
        ·
          refine ⟨20071323561492490095631709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13380882374328326730421139 20071323561492490095631709)
          ·
            refine ⟨7526746335559683785861891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20071323561492490095631709 7526746335559683785861891)
            ·
              refine ⟨11290119503339525678792837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7526746335559683785861891 11290119503339525678792837)
              ·
                refine ⟨2116897406876161064773657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11290119503339525678792837 2116897406876161064773657)
                ·
                  refine ⟨1587673055157120798580243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2116897406876161064773657 1587673055157120798580243)
                  ·
                    refine ⟨2381509582735681197870365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1587673055157120798580243 2381509582735681197870365)
                    ·
                      refine ⟨893066093525880449201387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2381509582735681197870365 893066093525880449201387)
                      ·
                        rfl

theorem cell23_1739240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_1739240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739240 prefixEnd_1739240 := by exact prefixLift 1739240
  have htrace : WordTrace (prefixWord ++ tailWord_1739240) baseStart_1739240 baseEnd_1739240 := by
    simpa [prefixWord, tailWord_1739240, baseEnd_1739240] using wordTrace_append hprefix tailTrace_1739240
  have hstable : (prefixWord ++ tailWord_1739240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739240).length < 2 ^ (prefixWord ++ tailWord_1739240).sum := by decide
  have hdescent : baseEnd_1739240 < baseStart_1739240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739256 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 2, 6]
def baseStart_1739256 : Nat := 118140960795 + 1739256 * 2 ^ 59
def prefixEnd_1739256 : Nat := 4983230072969 + 3 ^ 40 * 1739256 * 2
def baseEnd_1739256 : Nat := 297691436405450795533771

theorem tailTrace_1739256 : CollatzResearch.WordTrace tailWord_1739256 prefixEnd_1739256 297691436405450795533771 := by
  unfold tailWord_1739256
  simp only [CollatzResearch.WordTrace]
  refine ⟨31717938893490014060622811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42290585191320018747497081 31717938893490014060622811)
  ·
    refine ⟨47576908340235021090934217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31717938893490014060622811 47576908340235021090934217)
    ·
      refine ⟨35682681255176265818200663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47576908340235021090934217 35682681255176265818200663)
      ·
        refine ⟨53524021882764398727300995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35682681255176265818200663 53524021882764398727300995)
        ·
          refine ⟨80286032824146598090951493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53524021882764398727300995 80286032824146598090951493)
          ·
            refine ⟨15053631154527487142053405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80286032824146598090951493 15053631154527487142053405)
            ·
              refine ⟨5645111682947807678270027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15053631154527487142053405 5645111682947807678270027)
              ·
                refine ⟨8467667524421711517405041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645111682947807678270027 8467667524421711517405041)
                ·
                  refine ⟨6350750643316283638053781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8467667524421711517405041 6350750643316283638053781)
                  ·
                    refine ⟨297691436405450795533771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6350750643316283638053781 297691436405450795533771)
                    ·
                      rfl

theorem cell23_1739256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_1739256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739256 prefixEnd_1739256 := by exact prefixLift 1739256
  have htrace : WordTrace (prefixWord ++ tailWord_1739256) baseStart_1739256 baseEnd_1739256 := by
    simpa [prefixWord, tailWord_1739256, baseEnd_1739256] using wordTrace_append hprefix tailTrace_1739256
  have hstable : (prefixWord ++ tailWord_1739256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739256).length < 2 ^ (prefixWord ++ tailWord_1739256).sum := by decide
  have hdescent : baseEnd_1739256 < baseStart_1739256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739284 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_1739284 : Nat := 118140960795 + 1739284 * 2 ^ 59
def prefixEnd_1739284 : Nat := 4983230072969 + 3 ^ 40 * 1739284 * 2
def baseEnd_1739284 : Nat := 893088686674678277051185

theorem tailTrace_1739284 : CollatzResearch.WordTrace tailWord_1739284 prefixEnd_1739284 893088686674678277051185 := by
  unfold tailWord_1739284
  simp only [CollatzResearch.WordTrace]
  refine ⟨31718449515439294451632453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42291266020585725935509937 31718449515439294451632453)
  ·
    refine ⟨5947209284144867709681085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31718449515439294451632453 5947209284144867709681085)
    ·
      refine ⟨2230203481554325391130407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5947209284144867709681085 2230203481554325391130407)
      ·
        refine ⟨3345305222331488086695611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230203481554325391130407 3345305222331488086695611)
        ·
          refine ⟨5017957833497232130043417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3345305222331488086695611 5017957833497232130043417)
          ·
            refine ⟨3763468375122924097532563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5017957833497232130043417 3763468375122924097532563)
            ·
              refine ⟨5645202562684386146298845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763468375122924097532563 5645202562684386146298845)
              ·
                refine ⟨2116950961006644804862067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5645202562684386146298845 2116950961006644804862067)
                ·
                  refine ⟨3175426441509967207293101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116950961006644804862067 3175426441509967207293101)
                  ·
                    refine ⟨1190784915566237702734913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3175426441509967207293101 1190784915566237702734913)
                    ·
                      refine ⟨893088686674678277051185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190784915566237702734913 893088686674678277051185)
                      ·
                        rfl

theorem cell23_1739284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_1739284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739284 prefixEnd_1739284 := by exact prefixLift 1739284
  have htrace : WordTrace (prefixWord ++ tailWord_1739284) baseStart_1739284 baseEnd_1739284 := by
    simpa [prefixWord, tailWord_1739284, baseEnd_1739284] using wordTrace_append hprefix tailTrace_1739284
  have hstable : (prefixWord ++ tailWord_1739284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739284).length < 2 ^ (prefixWord ++ tailWord_1739284).sum := by decide
  have hdescent : baseEnd_1739284 < baseStart_1739284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739293 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1739293 : Nat := 118140960795 + 1739293 * 2 ^ 59
def prefixEnd_1739293 : Nat := 4983230072969 + 3 ^ 40 * 1739293 * 2
def baseEnd_1739293 : Nat := 893093308000568741838643

theorem tailTrace_1739293 : CollatzResearch.WordTrace tailWord_1739293 prefixEnd_1739293 893093308000568741838643 := by
  unfold tailWord_1739293
  simp only [CollatzResearch.WordTrace]
  refine ⟨63437227287845983440342533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42291484858563988960228355 63437227287845983440342533)
  ·
    refine ⟨11894480116471121895064225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63437227287845983440342533 11894480116471121895064225)
    ·
      refine ⟨8920860087353341421298169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11894480116471121895064225 8920860087353341421298169)
      ·
        refine ⟨6690645065515006065973627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8920860087353341421298169 6690645065515006065973627)
        ·
          refine ⟨10035967598272509098960441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6690645065515006065973627 10035967598272509098960441)
          ·
            refine ⟨7526975698704381824220331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10035967598272509098960441 7526975698704381824220331)
            ·
              refine ⟨11290463548056572736330497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7526975698704381824220331 11290463548056572736330497)
              ·
                refine ⟨8467847661042429552247873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11290463548056572736330497 8467847661042429552247873)
                ·
                  refine ⟨6350885745781822164185905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8467847661042429552247873 6350885745781822164185905)
                  ·
                    refine ⟨4763164309336366623139429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6350885745781822164185905 4763164309336366623139429)
                    ·
                      refine ⟨893093308000568741838643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4763164309336366623139429 893093308000568741838643)
                      ·
                        rfl

theorem cell23_1739293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1739293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739293 prefixEnd_1739293 := by exact prefixLift 1739293
  have htrace : WordTrace (prefixWord ++ tailWord_1739293) baseStart_1739293 baseEnd_1739293 := by
    simpa [prefixWord, tailWord_1739293, baseEnd_1739293] using wordTrace_append hprefix tailTrace_1739293
  have hstable : (prefixWord ++ tailWord_1739293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739293).length < 2 ^ (prefixWord ++ tailWord_1739293).sum := by decide
  have hdescent : baseEnd_1739293 < baseStart_1739293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739313 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 2, 3, 3]
def baseStart_1739313 : Nat := 118140960795 + 1739313 * 2 ^ 59
def prefixEnd_1739313 : Nat := 4983230072969 + 3 ^ 40 * 1739313 * 2
def baseEnd_1739313 : Nat := 893103577613658663588551

theorem tailTrace_1739313 : CollatzResearch.WordTrace tailWord_1739313 prefixEnd_1739313 893103577613658663588551 := by
  unfold tailWord_1739313
  simp only [CollatzResearch.WordTrace]
  refine ⟨63437956747773526856070593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42291971165182351237380395 63437956747773526856070593)
  ·
    refine ⟨47578467560830145142052945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63437956747773526856070593 47578467560830145142052945)
    ·
      refine ⟨35683850670622608856539709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47578467560830145142052945 35683850670622608856539709)
      ·
        refine ⟨13381444001483478321202391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35683850670622608856539709 13381444001483478321202391)
        ·
          refine ⟨20072166002225217481803587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13381444001483478321202391 20072166002225217481803587)
          ·
            refine ⟨30108249003337826222705381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20072166002225217481803587 30108249003337826222705381)
            ·
              refine ⟨5645296688125842416757259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30108249003337826222705381 5645296688125842416757259)
              ·
                refine ⟨8467945032188763625135889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645296688125842416757259 8467945032188763625135889)
                ·
                  refine ⟨6350958774141572718851917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8467945032188763625135889 6350958774141572718851917)
                  ·
                    refine ⟨2381609540303089769569469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6350958774141572718851917 2381609540303089769569469)
                    ·
                      refine ⟨893103577613658663588551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2381609540303089769569469 893103577613658663588551)
                      ·
                        rfl

theorem cell23_1739313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_1739313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739313 prefixEnd_1739313 := by exact prefixLift 1739313
  have htrace : WordTrace (prefixWord ++ tailWord_1739313) baseStart_1739313 baseEnd_1739313 := by
    simpa [prefixWord, tailWord_1739313, baseEnd_1739313] using wordTrace_append hprefix tailTrace_1739313
  have hstable : (prefixWord ++ tailWord_1739313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739313).length < 2 ^ (prefixWord ++ tailWord_1739313).sum := by decide
  have hdescent : baseEnd_1739313 < baseStart_1739313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739370 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_1739370 : Nat := 118140960795 + 1739370 * 2 ^ 59
def prefixEnd_1739370 : Nat := 4983230072969 + 3 ^ 40 * 1739370 * 2
def baseEnd_1739370 : Nat := 893132846010964940575789

theorem tailTrace_1739370 : CollatzResearch.WordTrace tailWord_1739370 prefixEnd_1739370 893132846010964940575789 := by
  unfold tailWord_1739370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15860008927141756397723891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42293357139044683727263709 15860008927141756397723891)
  ·
    refine ⟨23790013390712634596585837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15860008927141756397723891 23790013390712634596585837)
    ·
      refine ⟨8921255021517237973719689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23790013390712634596585837 8921255021517237973719689)
      ·
        refine ⟨6690941266137928480289767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8921255021517237973719689 6690941266137928480289767)
        ·
          refine ⟨10036411899206892720434651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6690941266137928480289767 10036411899206892720434651)
          ·
            refine ⟨15054617848810339080651977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10036411899206892720434651 15054617848810339080651977)
            ·
              refine ⟨11290963386607754310488983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15054617848810339080651977 11290963386607754310488983)
              ·
                refine ⟨16936445079911631465733475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11290963386607754310488983 16936445079911631465733475)
                ·
                  refine ⟨25404667619867447198600213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16936445079911631465733475 25404667619867447198600213)
                  ·
                    refine ⟨1190843794681286587434385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25404667619867447198600213 1190843794681286587434385)
                    ·
                      refine ⟨893132846010964940575789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190843794681286587434385 893132846010964940575789)
                      ·
                        rfl

theorem cell23_1739370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_1739370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739370 prefixEnd_1739370 := by exact prefixLift 1739370
  have htrace : WordTrace (prefixWord ++ tailWord_1739370) baseStart_1739370 baseEnd_1739370 := by
    simpa [prefixWord, tailWord_1739370, baseEnd_1739370] using wordTrace_append hprefix tailTrace_1739370
  have hstable : (prefixWord ++ tailWord_1739370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739370).length < 2 ^ (prefixWord ++ tailWord_1739370).sum := by decide
  have hdescent : baseEnd_1739370 < baseStart_1739370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739410 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 6]
def baseStart_1739410 : Nat := 118140960795 + 1739410 * 2 ^ 59
def prefixEnd_1739410 : Nat := 4983230072969 + 3 ^ 40 * 1739410 * 2
def baseEnd_1739410 : Nat := 99239265026349420452845

theorem tailTrace_1739410 : CollatzResearch.WordTrace tailWord_1739410 prefixEnd_1739410 99239265026349420452845 := by
  unfold tailWord_1739410
  simp only [CollatzResearch.WordTrace]
  refine ⟨15860373657105528105587921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42294329752281408281567789 15860373657105528105587921)
  ·
    refine ⟨11895280242829146079190941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15860373657105528105587921 11895280242829146079190941)
    ·
      refine ⟨4460730091060929779696603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11895280242829146079190941 4460730091060929779696603)
      ·
        refine ⟨6691095136591394669544905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4460730091060929779696603 6691095136591394669544905)
        ·
          refine ⟨5018321352443546002158679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6691095136591394669544905 5018321352443546002158679)
          ·
            refine ⟨7527482028665319003238019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5018321352443546002158679 7527482028665319003238019)
            ·
              refine ⟨11291223042997978504857029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7527482028665319003238019 11291223042997978504857029)
              ·
                refine ⟨2117104320562120969660693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11291223042997978504857029 2117104320562120969660693)
                ·
                  refine ⟨99239265026349420452845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2117104320562120969660693 99239265026349420452845)
                  ·
                    rfl

theorem cell23_1739410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_1739410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739410 prefixEnd_1739410 := by exact prefixLift 1739410
  have htrace : WordTrace (prefixWord ++ tailWord_1739410) baseStart_1739410 baseEnd_1739410 := by
    simpa [prefixWord, tailWord_1739410, baseEnd_1739410] using wordTrace_append hprefix tailTrace_1739410
  have hstable : (prefixWord ++ tailWord_1739410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739410).length < 2 ^ (prefixWord ++ tailWord_1739410).sum := by decide
  have hdescent : baseEnd_1739410 < baseStart_1739410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739437 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_1739437 : Nat := 118140960795 + 1739437 * 2 ^ 59
def prefixEnd_1739437 : Nat := 4983230072969 + 3 ^ 40 * 1739437 * 2
def baseEnd_1739437 : Nat := 893167249214816178437981

theorem tailTrace_1739437 : CollatzResearch.WordTrace tailWord_1739437 prefixEnd_1739437 893167249214816178437981 := by
  unfold tailWord_1739437
  simp only [CollatzResearch.WordTrace]
  refine ⟨63442479399324296033584565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42294986266216197355723043 63442479399324296033584565)
  ·
    refine ⟨5947732443686652753148553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63442479399324296033584565 5947732443686652753148553)
    ·
      refine ⟨4460799332764989564861415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5947732443686652753148553 4460799332764989564861415)
      ·
        refine ⟨6691198999147484347292123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4460799332764989564861415 6691198999147484347292123)
        ·
          refine ⟨10036798498721226520938185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6691198999147484347292123 10036798498721226520938185)
          ·
            refine ⟨7527598874040919890703639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10036798498721226520938185 7527598874040919890703639)
            ·
              refine ⟨11291398311061379836055459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7527598874040919890703639 11291398311061379836055459)
              ·
                refine ⟨16937097466592069754083189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11291398311061379836055459 16937097466592069754083189)
                ·
                  refine ⟨1587852887493006539445299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16937097466592069754083189 1587852887493006539445299)
                  ·
                    refine ⟨2381779331239509809167949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1587852887493006539445299 2381779331239509809167949)
                    ·
                      refine ⟨893167249214816178437981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2381779331239509809167949 893167249214816178437981)
                      ·
                        rfl

theorem cell23_1739437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_1739437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739437 prefixEnd_1739437 := by exact prefixLift 1739437
  have htrace : WordTrace (prefixWord ++ tailWord_1739437) baseStart_1739437 baseEnd_1739437 := by
    simpa [prefixWord, tailWord_1739437, baseEnd_1739437] using wordTrace_append hprefix tailTrace_1739437
  have hstable : (prefixWord ++ tailWord_1739437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739437).length < 2 ^ (prefixWord ++ tailWord_1739437).sum := by decide
  have hdescent : baseEnd_1739437 < baseStart_1739437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739441 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1739441 : Nat := 118140960795 + 1739441 * 2 ^ 59
def prefixEnd_1739441 : Nat := 4983230072969 + 3 ^ 40 * 1739441 * 2
def baseEnd_1739441 : Nat := 893169303137434162787963

theorem tailTrace_1739441 : CollatzResearch.WordTrace tailWord_1739441 prefixEnd_1739441 893169303137434162787963 := by
  unfold tailWord_1739441
  simp only [CollatzResearch.WordTrace]
  refine ⟨63442625291309804716730177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42295083527539869811153451 63442625291309804716730177)
  ·
    refine ⟨47581968968482353537547633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63442625291309804716730177 47581968968482353537547633)
    ·
      refine ⟨35686476726361765153160725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47581968968482353537547633 35686476726361765153160725)
      ·
        refine ⟨1672803596548207741554409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35686476726361765153160725 1672803596548207741554409)
        ·
          refine ⟨1254602697411155806165807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1672803596548207741554409 1254602697411155806165807)
          ·
            refine ⟨1881904046116733709248711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254602697411155806165807 1881904046116733709248711)
            ·
              refine ⟨2822856069175100563873067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881904046116733709248711 2822856069175100563873067)
              ·
                refine ⟨4234284103762650845809601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2822856069175100563873067 4234284103762650845809601)
                ·
                  refine ⟨3175713077821988134357201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4234284103762650845809601 3175713077821988134357201)
                  ·
                    refine ⟨2381784808366491100767901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3175713077821988134357201 2381784808366491100767901)
                    ·
                      refine ⟨893169303137434162787963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2381784808366491100767901 893169303137434162787963)
                      ·
                        rfl

theorem cell23_1739441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1739441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739441 prefixEnd_1739441 := by exact prefixLift 1739441
  have htrace : WordTrace (prefixWord ++ tailWord_1739441) baseStart_1739441 baseEnd_1739441 := by
    simpa [prefixWord, tailWord_1739441, baseEnd_1739441] using wordTrace_append hprefix tailTrace_1739441
  have hstable : (prefixWord ++ tailWord_1739441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739441).length < 2 ^ (prefixWord ++ tailWord_1739441).sum := by decide
  have hdescent : baseEnd_1739441 < baseStart_1739441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739447 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 1, 5, 2]
def baseStart_1739447 : Nat := 118140960795 + 1739447 * 2 ^ 59
def prefixEnd_1739447 : Nat := 4983230072969 + 3 ^ 40 * 1739447 * 2
def baseEnd_1739447 : Nat := 893172384021361139312935

theorem tailTrace_1739447 : CollatzResearch.WordTrace tailWord_1739447 prefixEnd_1739447 893172384021361139312935 := by
  unfold tailWord_1739447
  simp only [CollatzResearch.WordTrace]
  refine ⟨63442844129288067741448595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42295229419525378494299063 63442844129288067741448595)
  ·
    refine ⟨95164266193932101612172893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63442844129288067741448595 95164266193932101612172893)
    ·
      refine ⟨35686599822724538104564835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95164266193932101612172893 35686599822724538104564835)
      ·
        refine ⟨53529899734086807156847253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35686599822724538104564835 53529899734086807156847253)
        ·
          refine ⟨2509214050035319085477215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53529899734086807156847253 2509214050035319085477215)
          ·
            refine ⟨3763821075052978628215823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509214050035319085477215 3763821075052978628215823)
            ·
              refine ⟨5645731612579467942323735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763821075052978628215823 5645731612579467942323735)
              ·
                refine ⟨8468597418869201913485603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645731612579467942323735 8468597418869201913485603)
                ·
                  refine ⟨12702896128303802870228405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8468597418869201913485603 12702896128303802870228405)
                  ·
                    refine ⟨1190896512028481519083913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12702896128303802870228405 1190896512028481519083913)
                    ·
                      refine ⟨893172384021361139312935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190896512028481519083913 893172384021361139312935)
                      ·
                        rfl

theorem cell23_1739447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_1739447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739447 prefixEnd_1739447 := by exact prefixLift 1739447
  have htrace : WordTrace (prefixWord ++ tailWord_1739447) baseStart_1739447 baseEnd_1739447 := by
    simpa [prefixWord, tailWord_1739447, baseEnd_1739447] using wordTrace_append hprefix tailTrace_1739447
  have hstable : (prefixWord ++ tailWord_1739447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739447).length < 2 ^ (prefixWord ++ tailWord_1739447).sum := by decide
  have hdescent : baseEnd_1739447 < baseStart_1739447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739473 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_1739473 : Nat := 118140960795 + 1739473 * 2 ^ 59
def prefixEnd_1739473 : Nat := 4983230072969 + 3 ^ 40 * 1739473 * 2
def baseEnd_1739473 : Nat := 893185734518378037587815

theorem tailTrace_1739473 : CollatzResearch.WordTrace tailWord_1739473 prefixEnd_1739473 893185734518378037587815 := by
  unfold tailWord_1739473
  simp only [CollatzResearch.WordTrace]
  refine ⟨63443792427193874181895073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42295861618129249454596715 63443792427193874181895073)
  ·
    refine ⟨47582844320395405636421305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63443792427193874181895073 47582844320395405636421305)
    ·
      refine ⟨35687133240296554227315979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47582844320395405636421305 35687133240296554227315979)
      ·
        refine ⟨53530699860444831340973969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35687133240296554227315979 53530699860444831340973969)
        ·
          refine ⟨40148024895333623505730477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53530699860444831340973969 40148024895333623505730477)
          ·
            refine ⟨15055509335750108814648929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40148024895333623505730477 15055509335750108814648929)
            ·
              refine ⟨11291632001812581610986697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15055509335750108814648929 11291632001812581610986697)
              ·
                refine ⟨8468724001359436208240023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11291632001812581610986697 8468724001359436208240023)
                ·
                  refine ⟨12703086002039154312360035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8468724001359436208240023 12703086002039154312360035)
                  ·
                    refine ⟨19054629003058731468540053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12703086002039154312360035 19054629003058731468540053)
                    ·
                      refine ⟨893185734518378037587815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19054629003058731468540053 893185734518378037587815)
                      ·
                        rfl

theorem cell23_1739473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_1739473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739473 prefixEnd_1739473 := by exact prefixLift 1739473
  have htrace : WordTrace (prefixWord ++ tailWord_1739473) baseStart_1739473 baseEnd_1739473 := by
    simpa [prefixWord, tailWord_1739473, baseEnd_1739473] using wordTrace_append hprefix tailTrace_1739473
  have hstable : (prefixWord ++ tailWord_1739473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739473).length < 2 ^ (prefixWord ++ tailWord_1739473).sum := by decide
  have hdescent : baseEnd_1739473 < baseStart_1739473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739480 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_1739480 : Nat := 118140960795 + 1739480 * 2 ^ 59
def prefixEnd_1739480 : Nat := 4983230072969 + 3 ^ 40 * 1739480 * 2
def baseEnd_1739480 : Nat := 893189328882959510200283

theorem tailTrace_1739480 : CollatzResearch.WordTrace tailWord_1739480 prefixEnd_1739480 893189328882959510200283 := by
  unfold tailWord_1739480
  simp only [CollatzResearch.WordTrace]
  refine ⟨31722023869084257188699947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42296031825445676251599929 31722023869084257188699947)
  ·
    refine ⟨47583035803626385783049921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31722023869084257188699947 47583035803626385783049921)
    ·
      refine ⟨35687276852719789337287441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47583035803626385783049921 35687276852719789337287441)
      ·
        refine ⟨26765457639539842002965581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35687276852719789337287441 26765457639539842002965581)
        ·
          refine ⟨10037046614827440751112093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26765457639539842002965581 10037046614827440751112093)
          ·
            refine ⟨3763892480560290281667035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10037046614827440751112093 3763892480560290281667035)
            ·
              refine ⟨5645838720840435422500553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763892480560290281667035 5645838720840435422500553)
              ·
                refine ⟨4234379040630326566875415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5645838720840435422500553 4234379040630326566875415)
                ·
                  refine ⟨6351568560945489850313123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234379040630326566875415 6351568560945489850313123)
                  ·
                    refine ⟨9527352841418234775469685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6351568560945489850313123 9527352841418234775469685)
                    ·
                      refine ⟨893189328882959510200283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9527352841418234775469685 893189328882959510200283)
                      ·
                        rfl

theorem cell23_1739480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_1739480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739480 prefixEnd_1739480 := by exact prefixLift 1739480
  have htrace : WordTrace (prefixWord ++ tailWord_1739480) baseStart_1739480 baseEnd_1739480 := by
    simpa [prefixWord, tailWord_1739480, baseEnd_1739480] using wordTrace_append hprefix tailTrace_1739480
  have hstable : (prefixWord ++ tailWord_1739480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739480).length < 2 ^ (prefixWord ++ tailWord_1739480).sum := by decide
  have hdescent : baseEnd_1739480 < baseStart_1739480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739523 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 5]
def baseStart_1739523 : Nat := 118140960795 + 1739523 * 2 ^ 59
def prefixEnd_1739523 : Nat := 4983230072969 + 3 ^ 40 * 1739523 * 2
def baseEnd_1739523 : Nat := 893211408551102841962585

theorem tailTrace_1739523 : CollatzResearch.WordTrace tailWord_1739523 prefixEnd_1739523 893211408551102841962585 := by
  unfold tailWord_1739523
  simp only [CollatzResearch.WordTrace]
  refine ⟨63445616077012732721215223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42297077384675155147476815 63445616077012732721215223)
  ·
    refine ⟨95168424115519099081822835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63445616077012732721215223 95168424115519099081822835)
    ·
      refine ⟨142752636173278648622734253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95168424115519099081822835 142752636173278648622734253)
      ·
        refine ⟨53532238564979493233525345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142752636173278648622734253 53532238564979493233525345)
        ·
          refine ⟨40149178923734619925144009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53532238564979493233525345 40149178923734619925144009)
          ·
            refine ⟨30111884192800964943858007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40149178923734619925144009 30111884192800964943858007)
            ·
              refine ⟨45167826289201447415787011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30111884192800964943858007 45167826289201447415787011)
              ·
                refine ⟨67751739433802171123680517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45167826289201447415787011 67751739433802171123680517)
                ·
                  refine ⟨12703451143837907085690097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67751739433802171123680517 12703451143837907085690097)
                  ·
                    refine ⟨9527588357878430314267573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12703451143837907085690097 9527588357878430314267573)
                    ·
                      refine ⟨893211408551102841962585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9527588357878430314267573 893211408551102841962585)
                      ·
                        rfl

theorem cell23_1739523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_1739523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739523 prefixEnd_1739523 := by exact prefixLift 1739523
  have htrace : WordTrace (prefixWord ++ tailWord_1739523) baseStart_1739523 baseEnd_1739523 := by
    simpa [prefixWord, tailWord_1739523, baseEnd_1739523] using wordTrace_append hprefix tailTrace_1739523
  have hstable : (prefixWord ++ tailWord_1739523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739523).length < 2 ^ (prefixWord ++ tailWord_1739523).sum := by decide
  have hdescent : baseEnd_1739523 < baseStart_1739523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739528 : List Nat := [2, 1, 3, 2, 2, 3, 3, 2, 1, 2, 2]
def baseStart_1739528 : Nat := 118140960795 + 1739528 * 2 ^ 59
def prefixEnd_1739528 : Nat := 4983230072969 + 3 ^ 40 * 1739528 * 2
def baseEnd_1739528 : Nat := 893213975954375322400063

theorem tailTrace_1739528 : CollatzResearch.WordTrace tailWord_1739528 prefixEnd_1739528 893213975954375322400063 := by
  unfold tailWord_1739528
  simp only [CollatzResearch.WordTrace]
  refine ⟨31722899220997309287573619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42297198961329745716764825 31722899220997309287573619)
  ·
    refine ⟨47584348831495963931360429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31722899220997309287573619 47584348831495963931360429)
    ·
      refine ⟨17844130811810986474260161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47584348831495963931360429 17844130811810986474260161)
      ·
        refine ⟨13383098108858239855695121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17844130811810986474260161 13383098108858239855695121)
        ·
          refine ⟨10037323581643679891771341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13383098108858239855695121 10037323581643679891771341)
          ·
            refine ⟨3763996343116379959414253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10037323581643679891771341 3763996343116379959414253)
            ·
              refine ⟨1411498628668642484780345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3763996343116379959414253 1411498628668642484780345)
              ·
                refine ⟨1058623971501481863585259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411498628668642484780345 1058623971501481863585259)
                ·
                  refine ⟨1587935957252222795377889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058623971501481863585259 1587935957252222795377889)
                  ·
                    refine ⟨1190951967939167096533417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1587935957252222795377889 1190951967939167096533417)
                    ·
                      refine ⟨893213975954375322400063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190951967939167096533417 893213975954375322400063)
                      ·
                        rfl

theorem cell23_1739528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_1739528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739528 prefixEnd_1739528 := by exact prefixLift 1739528
  have htrace : WordTrace (prefixWord ++ tailWord_1739528) baseStart_1739528 baseEnd_1739528 := by
    simpa [prefixWord, tailWord_1739528, baseEnd_1739528] using wordTrace_append hprefix tailTrace_1739528
  have hstable : (prefixWord ++ tailWord_1739528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739528).length < 2 ^ (prefixWord ++ tailWord_1739528).sum := by decide
  have hdescent : baseEnd_1739528 < baseStart_1739528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739538 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1739538 : Nat := 118140960795 + 1739538 * 2 ^ 59
def prefixEnd_1739538 : Nat := 4983230072969 + 3 ^ 40 * 1739538 * 2
def baseEnd_1739538 : Nat := 297739703586973427758339

theorem tailTrace_1739538 : CollatzResearch.WordTrace tailWord_1739538 prefixEnd_1739538 297739703586973427758339 := by
  unfold tailWord_1739538
  simp only [CollatzResearch.WordTrace]
  refine ⟨15861540792989597570752817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42297442114638926855340845 15861540792989597570752817)
  ·
    refine ⟨11896155594742198178064613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15861540792989597570752817 11896155594742198178064613)
    ·
      refine ⟨2230529174014162158387115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11896155594742198178064613 2230529174014162158387115)
      ·
        refine ⟨3345793761021243237580673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230529174014162158387115 3345793761021243237580673)
        ·
          refine ⟨2509345320765932428185505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3345793761021243237580673 2509345320765932428185505)
          ·
            refine ⟨1882008990574449321139129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2509345320765932428185505 1882008990574449321139129)
            ·
              refine ⟨1411506742930836990854347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1882008990574449321139129 1411506742930836990854347)
              ·
                refine ⟨2117260114396255486281521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411506742930836990854347 2117260114396255486281521)
                ·
                  refine ⟨1587945085797191614711141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2117260114396255486281521 1587945085797191614711141)
                  ·
                    refine ⟨297739703586973427758339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1587945085797191614711141 297739703586973427758339)
                    ·
                      rfl

theorem cell23_1739538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1739538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739538 prefixEnd_1739538 := by exact prefixLift 1739538
  have htrace : WordTrace (prefixWord ++ tailWord_1739538) baseStart_1739538 baseEnd_1739538 := by
    simpa [prefixWord, tailWord_1739538, baseEnd_1739538] using wordTrace_append hprefix tailTrace_1739538
  have hstable : (prefixWord ++ tailWord_1739538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739538).length < 2 ^ (prefixWord ++ tailWord_1739538).sum := by decide
  have hdescent : baseEnd_1739538 < baseStart_1739538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739554 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_1739554 : Nat := 118140960795 + 1739554 * 2 ^ 59
def prefixEnd_1739554 : Nat := 4983230072969 + 3 ^ 40 * 1739554 * 2
def baseEnd_1739554 : Nat := 893227326451392220674943

theorem tailTrace_1739554 : CollatzResearch.WordTrace tailWord_1739554 prefixEnd_1739554 893227326451392220674943 := by
  unfold tailWord_1739554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15861686684975106253898429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42297831159933616677062477 15861686684975106253898429)
  ·
    refine ⟨5948132506865664845211911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15861686684975106253898429 5948132506865664845211911)
    ·
      refine ⟨8922198760298497267817867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5948132506865664845211911 8922198760298497267817867)
      ·
        refine ⟨13383298140447745901726801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8922198760298497267817867 13383298140447745901726801)
        ·
          refine ⟨10037473605335809426295101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13383298140447745901726801 10037473605335809426295101)
          ·
            refine ⟨3764052602000928534860663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10037473605335809426295101 3764052602000928534860663)
            ·
              refine ⟨5646078903001392802290995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764052602000928534860663 5646078903001392802290995)
              ·
                refine ⟨8469118354502089203436493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646078903001392802290995 8469118354502089203436493)
                ·
                  refine ⟨3175919382938283451288685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8469118354502089203436493 3175919382938283451288685)
                  ·
                    refine ⟨1190969768601856294233257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3175919382938283451288685 1190969768601856294233257)
                    ·
                      refine ⟨893227326451392220674943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190969768601856294233257 893227326451392220674943)
                      ·
                        rfl

theorem cell23_1739554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_1739554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739554 prefixEnd_1739554 := by exact prefixLift 1739554
  have htrace : WordTrace (prefixWord ++ tailWord_1739554) baseStart_1739554 baseEnd_1739554 := by
    simpa [prefixWord, tailWord_1739554, baseEnd_1739554] using wordTrace_append hprefix tailTrace_1739554
  have hstable : (prefixWord ++ tailWord_1739554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739554).length < 2 ^ (prefixWord ++ tailWord_1739554).sum := by decide
  have hdescent : baseEnd_1739554 < baseStart_1739554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739570 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1739570 : Nat := 118140960795 + 1739570 * 2 ^ 59
def prefixEnd_1739570 : Nat := 4983230072969 + 3 ^ 40 * 1739570 * 2
def baseEnd_1739570 : Nat := 893235542141864158074869

theorem tailTrace_1739570 : CollatzResearch.WordTrace tailWord_1739570 prefixEnd_1739570 893235542141864158074869 := by
  unfold tailWord_1739570
  simp only [CollatzResearch.WordTrace]
  refine ⟨15861832576960614937044041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42298220205228306498784109 15861832576960614937044041)
  ·
    refine ⟨11896374432720461202783031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15861832576960614937044041 11896374432720461202783031)
    ·
      refine ⟨17844561649080691804174547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11896374432720461202783031 17844561649080691804174547)
      ·
        refine ⟨26766842473621037706261821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17844561649080691804174547 26766842473621037706261821)
        ·
          refine ⟨10037565927607889139848183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26766842473621037706261821 10037565927607889139848183)
          ·
            refine ⟨15056348891411833709772275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10037565927607889139848183 15056348891411833709772275)
            ·
              refine ⟨22584523337117750564658413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15056348891411833709772275 22584523337117750564658413)
              ·
                refine ⟨8469196251419156461746905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22584523337117750564658413 8469196251419156461746905)
                ·
                  refine ⟨6351897188564367346310179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8469196251419156461746905 6351897188564367346310179)
                  ·
                    refine ⟨9527845782846551019465269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6351897188564367346310179 9527845782846551019465269)
                    ·
                      refine ⟨893235542141864158074869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9527845782846551019465269 893235542141864158074869)
                      ·
                        rfl

theorem cell23_1739570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1739570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739570 prefixEnd_1739570 := by exact prefixLift 1739570
  have htrace : WordTrace (prefixWord ++ tailWord_1739570) baseStart_1739570 baseEnd_1739570 := by
    simpa [prefixWord, tailWord_1739570, baseEnd_1739570] using wordTrace_append hprefix tailTrace_1739570
  have hstable : (prefixWord ++ tailWord_1739570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739570).length < 2 ^ (prefixWord ++ tailWord_1739570).sum := by decide
  have hdescent : baseEnd_1739570 < baseStart_1739570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739571 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 1, 3, 2]
def baseStart_1739571 : Nat := 118140960795 + 1739571 * 2 ^ 59
def prefixEnd_1739571 : Nat := 4983230072969 + 3 ^ 40 * 1739571 * 2
def baseEnd_1739571 : Nat := 893236055622518654162365

theorem tailTrace_1739571 : CollatzResearch.WordTrace tailWord_1739571 prefixEnd_1739571 893236055622518654162365 := by
  unfold tailWord_1739571
  simp only [CollatzResearch.WordTrace]
  refine ⟨63447366780838836918962567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42298244520559224612641711 63447366780838836918962567)
  ·
    refine ⟨95171050171258255378443851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63447366780838836918962567 95171050171258255378443851)
    ·
      refine ⟨142756575256887383067665777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95171050171258255378443851 142756575256887383067665777)
      ·
        refine ⟨107067431442665537300749333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142756575256887383067665777 107067431442665537300749333)
        ·
          refine ⟨5018785848874947060972625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107067431442665537300749333 5018785848874947060972625)
          ·
            refine ⟨3764089386656210295729469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5018785848874947060972625 3764089386656210295729469)
            ·
              refine ⟨1411533519996078860898551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3764089386656210295729469 1411533519996078860898551)
              ·
                refine ⟨2117300279994118291347827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411533519996078860898551 2117300279994118291347827)
                ·
                  refine ⟨3175950419991177437021741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117300279994118291347827 3175950419991177437021741)
                  ·
                    refine ⟨1190981407496691538883153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3175950419991177437021741 1190981407496691538883153)
                    ·
                      refine ⟨893236055622518654162365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1190981407496691538883153 893236055622518654162365)
                      ·
                        rfl

theorem cell23_1739571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 3, 2].length) (baseStart_1739571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739571 prefixEnd_1739571 := by exact prefixLift 1739571
  have htrace : WordTrace (prefixWord ++ tailWord_1739571) baseStart_1739571 baseEnd_1739571 := by
    simpa [prefixWord, tailWord_1739571, baseEnd_1739571] using wordTrace_append hprefix tailTrace_1739571
  have hstable : (prefixWord ++ tailWord_1739571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739571).length < 2 ^ (prefixWord ++ tailWord_1739571).sum := by decide
  have hdescent : baseEnd_1739571 < baseStart_1739571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739580 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1739580 : Nat := 118140960795 + 1739580 * 2 ^ 59
def prefixEnd_1739580 : Nat := 4983230072969 + 3 ^ 40 * 1739580 * 2
def baseEnd_1739580 : Nat := 893240676948409118949823

theorem tailTrace_1739580 : CollatzResearch.WordTrace tailWord_1739580 prefixEnd_1739580 893240676948409118949823 := by
  unfold tailWord_1739580
  simp only [CollatzResearch.WordTrace]
  refine ⟨31723847518903115728020097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42298463358537487637360129 31723847518903115728020097)
  ·
    refine ⟨23792885639177336796015073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31723847518903115728020097 23792885639177336796015073)
    ·
      refine ⟨17844664229383002597011305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23792885639177336796015073 17844664229383002597011305)
      ·
        refine ⟨13383498172037251947758479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17844664229383002597011305 13383498172037251947758479)
        ·
          refine ⟨20075247258055877921637719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13383498172037251947758479 20075247258055877921637719)
          ·
            refine ⟨30112870887083816882456579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20075247258055877921637719 30112870887083816882456579)
            ·
              refine ⟨45169306330625725323684869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30112870887083816882456579 45169306330625725323684869)
              ·
                refine ⟨8469244936992323498190913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45169306330625725323684869 8469244936992323498190913)
                ·
                  refine ⟨6351933702744242623643185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8469244936992323498190913 6351933702744242623643185)
                  ·
                    refine ⟨4763950277058181967732389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6351933702744242623643185 4763950277058181967732389)
                    ·
                      refine ⟨893240676948409118949823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4763950277058181967732389 893240676948409118949823)
                      ·
                        rfl

theorem cell23_1739580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1739580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739580 prefixEnd_1739580 := by exact prefixLift 1739580
  have htrace : WordTrace (prefixWord ++ tailWord_1739580) baseStart_1739580 baseEnd_1739580 := by
    simpa [prefixWord, tailWord_1739580, baseEnd_1739580] using wordTrace_append hprefix tailTrace_1739580
  have hstable : (prefixWord ++ tailWord_1739580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739580).length < 2 ^ (prefixWord ++ tailWord_1739580).sum := by decide
  have hdescent : baseEnd_1739580 < baseStart_1739580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739600 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 3]
def baseStart_1739600 : Nat := 118140960795 + 1739600 * 2 ^ 59
def prefixEnd_1739600 : Nat := 4983230072969 + 3 ^ 40 * 1739600 * 2
def baseEnd_1739600 : Nat := 893250946561499040699731

theorem tailTrace_1739600 : CollatzResearch.WordTrace tailWord_1739600 prefixEnd_1739600 893250946561499040699731 := by
  unfold tailWord_1739600
  simp only [CollatzResearch.WordTrace]
  refine ⟨31724212248866887435884127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42298949665155849914512169 31724212248866887435884127)
  ·
    refine ⟨47586318373300331153826191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31724212248866887435884127 47586318373300331153826191)
    ·
      refine ⟨71379477559950496730739287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47586318373300331153826191 71379477559950496730739287)
      ·
        refine ⟨107069216339925745096108931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71379477559950496730739287 107069216339925745096108931)
        ·
          refine ⟨160603824509888617644163397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107069216339925745096108931 160603824509888617644163397)
          ·
            refine ⟨30113217095604115808280637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160603824509888617644163397 30113217095604115808280637)
            ·
              refine ⟨11292456410851543428105239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30113217095604115808280637 11292456410851543428105239)
              ·
                refine ⟨16938684616277315142157859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11292456410851543428105239 16938684616277315142157859)
                ·
                  refine ⟨25408026924415972713236789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16938684616277315142157859 25408026924415972713236789)
                  ·
                    refine ⟨2382002524163997441865949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25408026924415972713236789 2382002524163997441865949)
                    ·
                      refine ⟨893250946561499040699731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2382002524163997441865949 893250946561499040699731)
                      ·
                        rfl

theorem cell23_1739600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 3].length) (baseStart_1739600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739600 prefixEnd_1739600 := by exact prefixLift 1739600
  have htrace : WordTrace (prefixWord ++ tailWord_1739600) baseStart_1739600 baseEnd_1739600 := by
    simpa [prefixWord, tailWord_1739600, baseEnd_1739600] using wordTrace_append hprefix tailTrace_1739600
  have hstable : (prefixWord ++ tailWord_1739600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739600).length < 2 ^ (prefixWord ++ tailWord_1739600).sum := by decide
  have hdescent : baseEnd_1739600 < baseStart_1739600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739624 : List Nat := [2, 1, 4, 2, 1, 3, 2, 3, 5]
def baseStart_1739624 : Nat := 118140960795 + 1739624 * 2 ^ 59
def prefixEnd_1739624 : Nat := 4983230072969 + 3 ^ 40 * 1739624 * 2
def baseEnd_1739624 : Nat := 99251474455245216311069

theorem tailTrace_1739624 : CollatzResearch.WordTrace tailWord_1739624 prefixEnd_1739624 99251474455245216311069 := by
  unfold tailWord_1739624
  simp only [CollatzResearch.WordTrace]
  refine ⟨31724649924823413485320963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42299533233097884647094617 31724649924823413485320963)
  ·
    refine ⟨47586974887235120227981445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31724649924823413485320963 47586974887235120227981445)
    ·
      refine ⟨8922557791356585042746521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47586974887235120227981445 8922557791356585042746521)
      ·
        refine ⟨6691918343517438782059891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8922557791356585042746521 6691918343517438782059891)
        ·
          refine ⟨10037877515276158173089837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6691918343517438782059891 10037877515276158173089837)
          ·
            refine ⟨3764204068228559314908689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10037877515276158173089837 3764204068228559314908689)
            ·
              refine ⟨2823153051171419486181517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764204068228559314908689 2823153051171419486181517)
              ·
                refine ⟨1058682394189282307318069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2823153051171419486181517 1058682394189282307318069)
                ·
                  refine ⟨99251474455245216311069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1058682394189282307318069 99251474455245216311069)
                  ·
                    rfl

theorem cell23_1739624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 5].length) (baseStart_1739624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739624 prefixEnd_1739624 := by exact prefixLift 1739624
  have htrace : WordTrace (prefixWord ++ tailWord_1739624) baseStart_1739624 baseEnd_1739624 := by
    simpa [prefixWord, tailWord_1739624, baseEnd_1739624] using wordTrace_append hprefix tailTrace_1739624
  have hstable : (prefixWord ++ tailWord_1739624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739624).length < 2 ^ (prefixWord ++ tailWord_1739624).sum := by decide
  have hdescent : baseEnd_1739624 < baseStart_1739624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739677 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_1739677 : Nat := 118140960795 + 1739677 * 2 ^ 59
def prefixEnd_1739677 : Nat := 4983230072969 + 3 ^ 40 * 1739677 * 2
def baseEnd_1739677 : Nat := 893290484571895239436877

theorem tailTrace_1739677 : CollatzResearch.WordTrace tailWord_1739677 prefixEnd_1739677 893290484571895239436877 := by
  unfold tailWord_1739677
  simp only [CollatzResearch.WordTrace]
  refine ⟨63451232918454817022321285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42300821945636544681547523 63451232918454817022321285)
  ·
    refine ⟨11897106172210278191685241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63451232918454817022321285 11897106172210278191685241)
    ·
      refine ⟨8922829629157708643763931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11897106172210278191685241 8922829629157708643763931)
      ·
        refine ⟨13384244443736562965645897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8922829629157708643763931 13384244443736562965645897)
        ·
          refine ⟨10038183332802422224234423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13384244443736562965645897 10038183332802422224234423)
          ·
            refine ⟨15057274999203633336351635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10038183332802422224234423 15057274999203633336351635)
            ·
              refine ⟨22585912498805450004527453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15057274999203633336351635 22585912498805450004527453)
              ·
                refine ⟨8469717187052043751697795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22585912498805450004527453 8469717187052043751697795)
                ·
                  refine ⟨12704575780578065627546693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8469717187052043751697795 12704575780578065627546693)
                  ·
                    refine ⟨2382107958858387305165005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12704575780578065627546693 2382107958858387305165005)
                    ·
                      refine ⟨893290484571895239436877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2382107958858387305165005 893290484571895239436877)
                      ·
                        rfl

theorem cell23_1739677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_1739677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739677 prefixEnd_1739677 := by exact prefixLift 1739677
  have htrace : WordTrace (prefixWord ++ tailWord_1739677) baseStart_1739677 baseEnd_1739677 := by
    simpa [prefixWord, tailWord_1739677, baseEnd_1739677] using wordTrace_append hprefix tailTrace_1739677
  have hstable : (prefixWord ++ tailWord_1739677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739677).length < 2 ^ (prefixWord ++ tailWord_1739677).sum := by decide
  have hdescent : baseEnd_1739677 < baseStart_1739677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739680 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 8]
def baseStart_1739680 : Nat := 118140960795 + 1739680 * 2 ^ 59
def prefixEnd_1739680 : Nat := 4983230072969 + 3 ^ 40 * 1739680 * 2
def baseEnd_1739680 : Nat := 99254669445984303077707

theorem tailTrace_1739680 : CollatzResearch.WordTrace tailWord_1739680 prefixEnd_1739680 99254669445984303077707 := by
  unfold tailWord_1739680
  simp only [CollatzResearch.WordTrace]
  refine ⟨31725671168721974267340247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42300894891629299023120329 31725671168721974267340247)
  ·
    refine ⟨47588506753082961401010371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31725671168721974267340247 47588506753082961401010371)
    ·
      refine ⟨71382760129624442101515557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47588506753082961401010371 71382760129624442101515557)
      ·
        refine ⟨13384267524304582894034167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71382760129624442101515557 13384267524304582894034167)
        ·
          refine ⟨20076401286456874341051251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13384267524304582894034167 20076401286456874341051251)
          ·
            refine ⟨30114601929685311511576877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20076401286456874341051251 30114601929685311511576877)
            ·
              refine ⟨11292975723631991816841329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30114601929685311511576877 11292975723631991816841329)
              ·
                refine ⟨8469731792723993862630997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11292975723631991816841329 8469731792723993862630997)
                ·
                  refine ⟨99254669445984303077707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8469731792723993862630997 99254669445984303077707)
                  ·
                    rfl

theorem cell23_1739680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 8].length) (baseStart_1739680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739680 prefixEnd_1739680 := by exact prefixLift 1739680
  have htrace : WordTrace (prefixWord ++ tailWord_1739680) baseStart_1739680 baseEnd_1739680 := by
    simpa [prefixWord, tailWord_1739680, baseEnd_1739680] using wordTrace_append hprefix tailTrace_1739680
  have hstable : (prefixWord ++ tailWord_1739680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739680).length < 2 ^ (prefixWord ++ tailWord_1739680).sum := by decide
  have hdescent : baseEnd_1739680 < baseStart_1739680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739724 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1739724 : Nat := 118140960795 + 1739724 * 2 ^ 59
def prefixEnd_1739724 : Nat := 4983230072969 + 3 ^ 40 * 1739724 * 2
def baseEnd_1739724 : Nat := 893314618162656555549161

theorem tailTrace_1739724 : CollatzResearch.WordTrace tailWord_1739724 prefixEnd_1739724 893314618162656555549161 := by
  unfold tailWord_1739724
  simp only [CollatzResearch.WordTrace]
  refine ⟨31726473574642272024641113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42301964766189696032854817 31726473574642272024641113)
  ·
    refine ⟨23794855180981704018480835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31726473574642272024641113 23794855180981704018480835)
    ·
      refine ⟨35692282771472556027721253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23794855180981704018480835 35692282771472556027721253)
      ·
        refine ⟨6692303019651104255197735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35692282771472556027721253 6692303019651104255197735)
        ·
          refine ⟨10038454529476656382796603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6692303019651104255197735 10038454529476656382796603)
          ·
            refine ⟨15057681794214984574194905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10038454529476656382796603 15057681794214984574194905)
            ·
              refine ⟨11293261345661238430646179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15057681794214984574194905 11293261345661238430646179)
              ·
                refine ⟨16939892018491857645969269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11293261345661238430646179 16939892018491857645969269)
                ·
                  refine ⟨1588114876733611654309619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16939892018491857645969269 1588114876733611654309619)
                  ·
                    refine ⟨2382172315100417481464429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1588114876733611654309619 2382172315100417481464429)
                    ·
                      refine ⟨893314618162656555549161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2382172315100417481464429 893314618162656555549161)
                      ·
                        rfl

theorem cell23_1739724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1739724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739724 prefixEnd_1739724 := by exact prefixLift 1739724
  have htrace : WordTrace (prefixWord ++ tailWord_1739724) baseStart_1739724 baseEnd_1739724 := by
    simpa [prefixWord, tailWord_1739724, baseEnd_1739724] using wordTrace_append hprefix tailTrace_1739724
  have hstable : (prefixWord ++ tailWord_1739724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739724).length < 2 ^ (prefixWord ++ tailWord_1739724).sum := by decide
  have hdescent : baseEnd_1739724 < baseStart_1739724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739725 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1739725 : Nat := 118140960795 + 1739725 * 2 ^ 59
def prefixEnd_1739725 : Nat := 4983230072969 + 3 ^ 40 * 1739725 * 2
def baseEnd_1739725 : Nat := 893315131643311051636657

theorem tailTrace_1739725 : CollatzResearch.WordTrace tailWord_1739725 prefixEnd_1739725 893315131643311051636657 := by
  unfold tailWord_1739725
  simp only [CollatzResearch.WordTrace]
  refine ⟨63452983622280921220068629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42301989081520614146712419 63452983622280921220068629)
  ·
    refine ⟨2974358607294418182190717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63452983622280921220068629 2974358607294418182190717)
    ·
      refine ⟨1115384477735406818321519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2974358607294418182190717 1115384477735406818321519)
      ·
        refine ⟨1673076716603110227482279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115384477735406818321519 1673076716603110227482279)
        ·
          refine ⟨2509615074904665341223419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673076716603110227482279 2509615074904665341223419)
          ·
            refine ⟨3764422612356998011835129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509615074904665341223419 3764422612356998011835129)
            ·
              refine ⟨2823316959267748508876347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764422612356998011835129 2823316959267748508876347)
              ·
                refine ⟨4234975438901622763314521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823316959267748508876347 4234975438901622763314521)
                ·
                  refine ⟨3176231579176217072485891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4234975438901622763314521 3176231579176217072485891)
                  ·
                    refine ⟨4764347368764325608728837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3176231579176217072485891 4764347368764325608728837)
                    ·
                      refine ⟨893315131643311051636657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4764347368764325608728837 893315131643311051636657)
                      ·
                        rfl

theorem cell23_1739725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1739725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739725 prefixEnd_1739725 := by exact prefixLift 1739725
  have htrace : WordTrace (prefixWord ++ tailWord_1739725) baseStart_1739725 baseEnd_1739725 := by
    simpa [prefixWord, tailWord_1739725, baseEnd_1739725] using wordTrace_append hprefix tailTrace_1739725
  have hstable : (prefixWord ++ tailWord_1739725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739725).length < 2 ^ (prefixWord ++ tailWord_1739725).sum := by decide
  have hdescent : baseEnd_1739725 < baseStart_1739725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739727 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 3, 5]
def baseStart_1739727 : Nat := 118140960795 + 1739727 * 2 ^ 59
def prefixEnd_1739727 : Nat := 4983230072969 + 3 ^ 40 * 1739727 * 2
def baseEnd_1739727 : Nat := 297772052868206681270549

theorem tailTrace_1739727 : CollatzResearch.WordTrace tailWord_1739727 prefixEnd_1739727 297772052868206681270549 := by
  unfold tailWord_1739727
  simp only [CollatzResearch.WordTrace]
  refine ⟨63453056568273675561641435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42302037712182450374427623 63453056568273675561641435)
  ·
    refine ⟨95179584852410513342462153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63453056568273675561641435 95179584852410513342462153)
    ·
      refine ⟨71384688639307885006846615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95179584852410513342462153 71384688639307885006846615)
      ·
        refine ⟨107077032958961827510269923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71384688639307885006846615 107077032958961827510269923)
        ·
          refine ⟨160615549438442741265404885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107077032958961827510269923 160615549438442741265404885)
          ·
            refine ⟨3764426939963501748407927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 160615549438442741265404885 3764426939963501748407927)
            ·
              refine ⟨5646640409945252622611891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764426939963501748407927 5646640409945252622611891)
              ·
                refine ⟨8469960614917878933917837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646640409945252622611891 8469960614917878933917837)
                ·
                  refine ⟨3176235230594204600219189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8469960614917878933917837 3176235230594204600219189)
                  ·
                    refine ⟨297772052868206681270549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3176235230594204600219189 297772052868206681270549)
                    ·
                      rfl

theorem cell23_1739727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_1739727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739727 prefixEnd_1739727 := by exact prefixLift 1739727
  have htrace : WordTrace (prefixWord ++ tailWord_1739727) baseStart_1739727 baseEnd_1739727 := by
    simpa [prefixWord, tailWord_1739727, baseEnd_1739727] using wordTrace_append hprefix tailTrace_1739727
  have hstable : (prefixWord ++ tailWord_1739727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739727).length < 2 ^ (prefixWord ++ tailWord_1739727).sum := by decide
  have hdescent : baseEnd_1739727 < baseStart_1739727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739751 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_1739751 : Nat := 118140960795 + 1739751 * 2 ^ 59
def prefixEnd_1739751 : Nat := 4983230072969 + 3 ^ 40 * 1739751 * 2
def baseEnd_1739751 : Nat := 893328482140327949911537

theorem tailTrace_1739751 : CollatzResearch.WordTrace tailWord_1739751 prefixEnd_1739751 893328482140327949911537 := by
  unfold tailWord_1739751
  simp only [CollatzResearch.WordTrace]
  refine ⟨63453931920186727660515107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42302621280124485107010071 63453931920186727660515107)
  ·
    refine ⟨95180897880280091490772661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63453931920186727660515107 95180897880280091490772661)
    ·
      refine ⟨8923209176276258577259937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95180897880280091490772661 8923209176276258577259937)
      ·
        refine ⟨6692406882207193932944953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8923209176276258577259937 6692406882207193932944953)
        ·
          refine ⟨5019305161655395449708715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6692406882207193932944953 5019305161655395449708715)
          ·
            refine ⟨7528957742483093174563073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019305161655395449708715 7528957742483093174563073)
            ·
              refine ⟨5646718306862319880922305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7528957742483093174563073 5646718306862319880922305)
              ·
                refine ⟨4235038730146739910691729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5646718306862319880922305 4235038730146739910691729)
                ·
                  refine ⟨3176279047610054933018797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235038730146739910691729 3176279047610054933018797)
                  ·
                    refine ⟨1191104642853770599882049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3176279047610054933018797 1191104642853770599882049)
                    ·
                      refine ⟨893328482140327949911537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191104642853770599882049 893328482140327949911537)
                      ·
                        rfl

theorem cell23_1739751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_1739751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739751 prefixEnd_1739751 := by exact prefixLift 1739751
  have htrace : WordTrace (prefixWord ++ tailWord_1739751) baseStart_1739751 baseEnd_1739751 := by
    simpa [prefixWord, tailWord_1739751, baseEnd_1739751] using wordTrace_append hprefix tailTrace_1739751
  have hstable : (prefixWord ++ tailWord_1739751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739751).length < 2 ^ (prefixWord ++ tailWord_1739751).sum := by decide
  have hdescent : baseEnd_1739751 < baseStart_1739751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739781 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 3, 2, 2]
def baseStart_1739781 : Nat := 118140960795 + 1739781 * 2 ^ 59
def prefixEnd_1739781 : Nat := 4983230072969 + 3 ^ 40 * 1739781 * 2
def baseEnd_1739781 : Nat := 893343886559962832536399

theorem tailTrace_1739781 : CollatzResearch.WordTrace tailWord_1739781 prefixEnd_1739781 893343886559962832536399 := by
  unfold tailWord_1739781
  simp only [CollatzResearch.WordTrace]
  refine ⟨63455026110078042784107197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42303350740052028522738131 63455026110078042784107197)
  ·
    refine ⟨23795634791279266044040199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63455026110078042784107197 23795634791279266044040199)
    ·
      refine ⟨35693452186918899066060299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23795634791279266044040199 35693452186918899066060299)
      ·
        refine ⟨53540178280378348599090449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35693452186918899066060299 53540178280378348599090449)
        ·
          refine ⟨40155133710283761449317837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53540178280378348599090449 40155133710283761449317837)
          ·
            refine ⟨15058175141356410543494189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40155133710283761449317837 15058175141356410543494189)
            ·
              refine ⟨5646815678008653953810321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15058175141356410543494189 5646815678008653953810321)
              ·
                refine ⟨4235111758506490465357741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5646815678008653953810321 4235111758506490465357741)
                ·
                  refine ⟨1588166909439933924509153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4235111758506490465357741 1588166909439933924509153)
                  ·
                    refine ⟨1191125182079950443381865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588166909439933924509153 1191125182079950443381865)
                    ·
                      refine ⟨893343886559962832536399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191125182079950443381865 893343886559962832536399)
                      ·
                        rfl

theorem cell23_1739781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_1739781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739781 prefixEnd_1739781 := by exact prefixLift 1739781
  have htrace : WordTrace (prefixWord ++ tailWord_1739781) baseStart_1739781 baseEnd_1739781 := by
    simpa [prefixWord, tailWord_1739781, baseEnd_1739781] using wordTrace_append hprefix tailTrace_1739781
  have hstable : (prefixWord ++ tailWord_1739781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739781).length < 2 ^ (prefixWord ++ tailWord_1739781).sum := by decide
  have hdescent : baseEnd_1739781 < baseStart_1739781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739784 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1739784 : Nat := 118140960795 + 1739784 * 2 ^ 59
def prefixEnd_1739784 : Nat := 4983230072969 + 3 ^ 40 * 1739784 * 2
def baseEnd_1739784 : Nat := 893345427001926320798885

theorem tailTrace_1739784 : CollatzResearch.WordTrace tailWord_1739784 prefixEnd_1739784 893345427001926320798885 := by
  unfold tailWord_1739784
  simp only [CollatzResearch.WordTrace]
  refine ⟨31727567764533587148233203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42303423686044782864310937 31727567764533587148233203)
  ·
    refine ⟨47591351646800380722349805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31727567764533587148233203 47591351646800380722349805)
    ·
      refine ⟨17846756867550142770881177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47591351646800380722349805 17846756867550142770881177)
      ·
        refine ⟨13385067650662607078160883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17846756867550142770881177 13385067650662607078160883)
        ·
          refine ⟨20077601475993910617241325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13385067650662607078160883 20077601475993910617241325)
          ·
            refine ⟨7529100553497716481465497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20077601475993910617241325 7529100553497716481465497)
            ·
              refine ⟨5646825415123287361099123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7529100553497716481465497 5646825415123287361099123)
              ·
                refine ⟨8470238122684931041648685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646825415123287361099123 8470238122684931041648685)
                ·
                  refine ⟨3176339296006849140618257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8470238122684931041648685 3176339296006849140618257)
                  ·
                    refine ⟨2382254472005136855463693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176339296006849140618257 2382254472005136855463693)
                    ·
                      refine ⟨893345427001926320798885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2382254472005136855463693 893345427001926320798885)
                      ·
                        rfl

theorem cell23_1739784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1739784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739784 prefixEnd_1739784 := by exact prefixLift 1739784
  have htrace : WordTrace (prefixWord ++ tailWord_1739784) baseStart_1739784 baseEnd_1739784 := by
    simpa [prefixWord, tailWord_1739784, baseEnd_1739784] using wordTrace_append hprefix tailTrace_1739784
  have hstable : (prefixWord ++ tailWord_1739784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739784).length < 2 ^ (prefixWord ++ tailWord_1739784).sum := by decide
  have hdescent : baseEnd_1739784 < baseStart_1739784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739801 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 1, 2, 3]
def baseStart_1739801 : Nat := 118140960795 + 1739801 * 2 ^ 59
def prefixEnd_1739801 : Nat := 4983230072969 + 3 ^ 40 * 1739801 * 2
def baseEnd_1739801 : Nat := 893354156173052754286307

theorem tailTrace_1739801 : CollatzResearch.WordTrace tailWord_1739801 prefixEnd_1739801 893354156173052754286307 := by
  unfold tailWord_1739801
  simp only [CollatzResearch.WordTrace]
  refine ⟨63455755570005586199835257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42303837046670390799890171 63455755570005586199835257)
  ·
    refine ⟨47591816677504189649876443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63455755570005586199835257 47591816677504189649876443)
    ·
      refine ⟨71387725016256284474814665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47591816677504189649876443 71387725016256284474814665)
      ·
        refine ⟨53540793762192213356110999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71387725016256284474814665 53540793762192213356110999)
        ·
          refine ⟨80311190643288320034166499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53540793762192213356110999 80311190643288320034166499)
          ·
            refine ⟨120466785964932480051249749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80311190643288320034166499 120466785964932480051249749)
            ·
              refine ⟨1411720148026552500600583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 120466785964932480051249749 1411720148026552500600583)
              ·
                refine ⟨2117580222039828750900875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411720148026552500600583 2117580222039828750900875)
                ·
                  refine ⟨3176370333059743126351313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117580222039828750900875 3176370333059743126351313)
                  ·
                    refine ⟨2382277749794807344763485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176370333059743126351313 2382277749794807344763485)
                    ·
                      refine ⟨893354156173052754286307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2382277749794807344763485 893354156173052754286307)
                      ·
                        rfl

theorem cell23_1739801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_1739801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739801 prefixEnd_1739801 := by exact prefixLift 1739801
  have htrace : WordTrace (prefixWord ++ tailWord_1739801) baseStart_1739801 baseEnd_1739801 := by
    simpa [prefixWord, tailWord_1739801, baseEnd_1739801] using wordTrace_append hprefix tailTrace_1739801
  have hstable : (prefixWord ++ tailWord_1739801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739801).length < 2 ^ (prefixWord ++ tailWord_1739801).sum := by decide
  have hdescent : baseEnd_1739801 < baseStart_1739801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739815 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1739815 : Nat := 118140960795 + 1739815 * 2 ^ 59
def prefixEnd_1739815 : Nat := 4983230072969 + 3 ^ 40 * 1739815 * 2
def baseEnd_1739815 : Nat := 893361344902215699511243

theorem tailTrace_1739815 : CollatzResearch.WordTrace tailWord_1739815 prefixEnd_1739815 893361344902215699511243 := by
  unfold tailWord_1739815
  simp only [CollatzResearch.WordTrace]
  refine ⟨63456266191954866590844899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42304177461303244393896599 63456266191954866590844899)
  ·
    refine ⟨95184399287932299886267349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63456266191954866590844899 95184399287932299886267349)
    ·
      refine ⟨2230884358310913278584391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 95184399287932299886267349 2230884358310913278584391)
      ·
        refine ⟨3346326537466369917876587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230884358310913278584391 3346326537466369917876587)
        ·
          refine ⟨5019489806199554876814881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346326537466369917876587 5019489806199554876814881)
          ·
            refine ⟨3764617354649666157611161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5019489806199554876814881 3764617354649666157611161)
            ·
              refine ⟨2823463015987249618208371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764617354649666157611161 2823463015987249618208371)
              ·
                refine ⟨4235194523980874427312557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823463015987249618208371 4235194523980874427312557)
                ·
                  refine ⟨1588197946492827910242209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4235194523980874427312557 1588197946492827910242209)
                  ·
                    refine ⟨1191148459869620932681657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588197946492827910242209 1191148459869620932681657)
                    ·
                      refine ⟨893361344902215699511243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191148459869620932681657 893361344902215699511243)
                      ·
                        rfl

theorem cell23_1739815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1739815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739815 prefixEnd_1739815 := by exact prefixLift 1739815
  have htrace : WordTrace (prefixWord ++ tailWord_1739815) baseStart_1739815 baseEnd_1739815 := by
    simpa [prefixWord, tailWord_1739815, baseEnd_1739815] using wordTrace_append hprefix tailTrace_1739815
  have hstable : (prefixWord ++ tailWord_1739815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739815).length < 2 ^ (prefixWord ++ tailWord_1739815).sum := by decide
  have hdescent : baseEnd_1739815 < baseStart_1739815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739828 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1739828 : Nat := 118140960795 + 1739828 * 2 ^ 59
def prefixEnd_1739828 : Nat := 4983230072969 + 3 ^ 40 * 1739828 * 2
def baseEnd_1739828 : Nat := 893368020150724148648683

theorem tailTrace_1739828 : CollatzResearch.WordTrace tailWord_1739828 prefixEnd_1739828 893368020150724148648683 := by
  unfold tailWord_1739828
  simp only [CollatzResearch.WordTrace]
  refine ⟨31728370170453884905534069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42304493560605179874045425 31728370170453884905534069)
  ·
    refine ⟨2974534703480051709893819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31728370170453884905534069 2974534703480051709893819)
    ·
      refine ⟨4461802055220077564840729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974534703480051709893819 4461802055220077564840729)
      ·
        refine ⟨3346351541415058173630547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4461802055220077564840729 3346351541415058173630547)
        ·
          refine ⟨5019527312122587260445821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346351541415058173630547 5019527312122587260445821)
          ·
            refine ⟨1882322742045970222667183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5019527312122587260445821 1882322742045970222667183)
            ·
              refine ⟨2823484113068955334000775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882322742045970222667183 2823484113068955334000775)
              ·
                refine ⟨4235226169603433001001163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823484113068955334000775 4235226169603433001001163)
                ·
                  refine ⟨6352839254405149501501745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235226169603433001001163 6352839254405149501501745)
                  ·
                    refine ⟨4764629440803862126126309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6352839254405149501501745 4764629440803862126126309)
                    ·
                      refine ⟨893368020150724148648683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4764629440803862126126309 893368020150724148648683)
                      ·
                        rfl

theorem cell23_1739828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1739828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739828 prefixEnd_1739828 := by exact prefixLift 1739828
  have htrace : WordTrace (prefixWord ++ tailWord_1739828) baseStart_1739828 baseEnd_1739828 := by
    simpa [prefixWord, tailWord_1739828, baseEnd_1739828] using wordTrace_append hprefix tailTrace_1739828
  have hstable : (prefixWord ++ tailWord_1739828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739828).length < 2 ^ (prefixWord ++ tailWord_1739828).sum := by decide
  have hdescent : baseEnd_1739828 < baseStart_1739828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739857 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_1739857 : Nat := 118140960795 + 1739857 * 2 ^ 59
def prefixEnd_1739857 : Nat := 4983230072969 + 3 ^ 40 * 1739857 * 2
def baseEnd_1739857 : Nat := 893382911089704535186049

theorem tailTrace_1739857 : CollatzResearch.WordTrace tailWord_1739857 prefixEnd_1739857 893382911089704535186049 := by
  unfold tailWord_1739857
  simp only [CollatzResearch.WordTrace]
  refine ⟨63457798057802707763873825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42305198705201805175915883 63457798057802707763873825)
  ·
    refine ⟨47593348543352030822905369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63457798057802707763873825 47593348543352030822905369)
    ·
      refine ⟨35695011407514023117179027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47593348543352030822905369 35695011407514023117179027)
      ·
        refine ⟨53542517111271034675768541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35695011407514023117179027 53542517111271034675768541)
        ·
          refine ⟨20078443916726638003413203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53542517111271034675768541 20078443916726638003413203)
          ·
            refine ⟨30117665875089957005119805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20078443916726638003413203 30117665875089957005119805)
            ·
              refine ⟨11294124703158733876919927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30117665875089957005119805 11294124703158733876919927)
              ·
                refine ⟨16941187054738100815379891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11294124703158733876919927 16941187054738100815379891)
                ·
                  refine ⟨25411780582107151223069837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16941187054738100815379891 25411780582107151223069837)
                  ·
                    refine ⟨9529417718290181708651189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25411780582107151223069837 9529417718290181708651189)
                    ·
                      refine ⟨893382911089704535186049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9529417718290181708651189 893382911089704535186049)
                      ·
                        rfl

theorem cell23_1739857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_1739857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739857 prefixEnd_1739857 := by exact prefixLift 1739857
  have htrace : WordTrace (prefixWord ++ tailWord_1739857) baseStart_1739857 baseEnd_1739857 := by
    simpa [prefixWord, tailWord_1739857, baseEnd_1739857] using wordTrace_append hprefix tailTrace_1739857
  have hstable : (prefixWord ++ tailWord_1739857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739857).length < 2 ^ (prefixWord ++ tailWord_1739857).sum := by decide
  have hdescent : baseEnd_1739857 < baseStart_1739857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739858 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_1739858 : Nat := 118140960795 + 1739858 * 2 ^ 59
def prefixEnd_1739858 : Nat := 4983230072969 + 3 ^ 40 * 1739858 * 2
def baseEnd_1739858 : Nat := 893383424570359031273545

theorem tailTrace_1739858 : CollatzResearch.WordTrace tailWord_1739858 prefixEnd_1739858 893383424570359031273545 := by
  unfold tailWord_1739858
  simp only [CollatzResearch.WordTrace]
  refine ⟨15864458632699771233665057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42305223020532723289773485 15864458632699771233665057)
  ·
    refine ⟨11898343974524828425248793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15864458632699771233665057 11898343974524828425248793)
    ·
      refine ⟨8923757980893621318936595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11898343974524828425248793 8923757980893621318936595)
      ·
        refine ⟨13385636971340431978404893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8923757980893621318936595 13385636971340431978404893)
        ·
          refine ⟨5019613864252661991901835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13385636971340431978404893 5019613864252661991901835)
          ·
            refine ⟨7529420796378992987852753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019613864252661991901835 7529420796378992987852753)
            ·
              refine ⟨5647065597284244740889565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7529420796378992987852753 5647065597284244740889565)
              ·
                refine ⟨2117649598981591777833587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5647065597284244740889565 2117649598981591777833587)
                ·
                  refine ⟨3176474398472387666750381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117649598981591777833587 3176474398472387666750381)
                  ·
                    refine ⟨1191177899427145375031393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3176474398472387666750381 1191177899427145375031393)
                    ·
                      refine ⟨893383424570359031273545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191177899427145375031393 893383424570359031273545)
                      ·
                        rfl

theorem cell23_1739858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_1739858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739858 prefixEnd_1739858 := by exact prefixLift 1739858
  have htrace : WordTrace (prefixWord ++ tailWord_1739858) baseStart_1739858 baseEnd_1739858 := by
    simpa [prefixWord, tailWord_1739858, baseEnd_1739858] using wordTrace_append hprefix tailTrace_1739858
  have hstable : (prefixWord ++ tailWord_1739858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739858).length < 2 ^ (prefixWord ++ tailWord_1739858).sum := by decide
  have hdescent : baseEnd_1739858 < baseStart_1739858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739871 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 4, 2, 2]
def baseStart_1739871 : Nat := 118140960795 + 1739871 * 2 ^ 59
def prefixEnd_1739871 : Nat := 4983230072969 + 3 ^ 40 * 1739871 * 2
def baseEnd_1739871 : Nat := 893390099818867480410985

theorem tailTrace_1739871 : CollatzResearch.WordTrace tailWord_1739871 prefixEnd_1739871 893390099818867480410985 := by
  unfold tailWord_1739871
  simp only [CollatzResearch.WordTrace]
  refine ⟨63458308679751988154883467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42305539119834658769922311 63458308679751988154883467)
  ·
    refine ⟨95187463019627982232325201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63458308679751988154883467 95187463019627982232325201)
    ·
      refine ⟨71390597264720986674243901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95187463019627982232325201 71390597264720986674243901)
      ·
        refine ⟨26771473974270370002841463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71390597264720986674243901 26771473974270370002841463)
        ·
          refine ⟨40157210961405555004262195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26771473974270370002841463 40157210961405555004262195)
          ·
            refine ⟨60235816442108332506393293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40157210961405555004262195 60235816442108332506393293)
            ·
              refine ⟨22588431165790624689897485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60235816442108332506393293 22588431165790624689897485)
              ·
                refine ⟨8470661687171484258711557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22588431165790624689897485 8470661687171484258711557)
                ·
                  refine ⟨1588249066344653298508417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8470661687171484258711557 1588249066344653298508417)
                  ·
                    refine ⟨1191186799758489973881313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588249066344653298508417 1191186799758489973881313)
                    ·
                      refine ⟨893390099818867480410985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191186799758489973881313 893390099818867480410985)
                      ·
                        rfl

theorem cell23_1739871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_1739871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739871 prefixEnd_1739871 := by exact prefixLift 1739871
  have htrace : WordTrace (prefixWord ++ tailWord_1739871) baseStart_1739871 baseEnd_1739871 := by
    simpa [prefixWord, tailWord_1739871, baseEnd_1739871] using wordTrace_append hprefix tailTrace_1739871
  have hstable : (prefixWord ++ tailWord_1739871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739871).length < 2 ^ (prefixWord ++ tailWord_1739871).sum := by decide
  have hdescent : baseEnd_1739871 < baseStart_1739871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739888 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 2, 2, 2]
def baseStart_1739888 : Nat := 118140960795 + 1739888 * 2 ^ 59
def prefixEnd_1739888 : Nat := 4983230072969 + 3 ^ 40 * 1739888 * 2
def baseEnd_1739888 : Nat := 893398828989993913898407

theorem tailTrace_1739888 : CollatzResearch.WordTrace tailWord_1739888 prefixEnd_1739888 893398828989993913898407 := by
  unfold tailWord_1739888
  simp only [CollatzResearch.WordTrace]
  refine ⟨31729464360345200029126159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42305952480460266705501545 31729464360345200029126159)
  ·
    refine ⟨47594196540517800043689239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31729464360345200029126159 47594196540517800043689239)
    ·
      refine ⟨71391294810776700065533859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47594196540517800043689239 71391294810776700065533859)
      ·
        refine ⟨107086942216165050098300789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71391294810776700065533859 107086942216165050098300789)
        ·
          refine ⟨10039400832765473446715699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107086942216165050098300789 10039400832765473446715699)
          ·
            refine ⟨15059101249148210170073549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10039400832765473446715699 15059101249148210170073549)
            ·
              refine ⟨5647162968430578813777581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15059101249148210170073549 5647162968430578813777581)
              ·
                refine ⟨2117686113161467055166593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5647162968430578813777581 2117686113161467055166593)
                ·
                  refine ⟨1588264584871100291374945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2117686113161467055166593 1588264584871100291374945)
                  ·
                    refine ⟨1191198438653325218531209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588264584871100291374945 1191198438653325218531209)
                    ·
                      refine ⟨893398828989993913898407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191198438653325218531209 893398828989993913898407)
                      ·
                        rfl

theorem cell23_1739888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2, 2, 2].length) (baseStart_1739888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739888 prefixEnd_1739888 := by exact prefixLift 1739888
  have htrace : WordTrace (prefixWord ++ tailWord_1739888) baseStart_1739888 baseEnd_1739888 := by
    simpa [prefixWord, tailWord_1739888, baseEnd_1739888] using wordTrace_append hprefix tailTrace_1739888
  have hstable : (prefixWord ++ tailWord_1739888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739888).length < 2 ^ (prefixWord ++ tailWord_1739888).sum := by decide
  have hdescent : baseEnd_1739888 < baseStart_1739888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739894 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_1739894 : Nat := 118140960795 + 1739894 * 2 ^ 59
def prefixEnd_1739894 : Nat := 4983230072969 + 3 ^ 40 * 1739894 * 2
def baseEnd_1739894 : Nat := 99266878874880098935931

theorem tailTrace_1739894 : CollatzResearch.WordTrace tailWord_1739894 prefixEnd_1739894 99266878874880098935931 := by
  unfold tailWord_1739894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966196722416791442685671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42306098372445775388647157 3966196722416791442685671)
  ·
    refine ⟨5949295083625187164028507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3966196722416791442685671 5949295083625187164028507)
    ·
      refine ⟨8923942625437780746042761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5949295083625187164028507 8923942625437780746042761)
      ·
        refine ⟨6692956969078335559532071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8923942625437780746042761 6692956969078335559532071)
        ·
          refine ⟨10039435453617503339298107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6692956969078335559532071 10039435453617503339298107)
          ·
            refine ⟨15059153180426255008947161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10039435453617503339298107 15059153180426255008947161)
            ·
              refine ⟨11294364885319691256710371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15059153180426255008947161 11294364885319691256710371)
              ·
                refine ⟨16941547327979536885065557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11294364885319691256710371 16941547327979536885065557)
                ·
                  refine ⟨99266878874880098935931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16941547327979536885065557 99266878874880098935931)
                  ·
                    rfl

theorem cell23_1739894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_1739894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739894 prefixEnd_1739894 := by exact prefixLift 1739894
  have htrace : WordTrace (prefixWord ++ tailWord_1739894) baseStart_1739894 baseEnd_1739894 := by
    simpa [prefixWord, tailWord_1739894, baseEnd_1739894] using wordTrace_append hprefix tailTrace_1739894
  have hstable : (prefixWord ++ tailWord_1739894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739894).length < 2 ^ (prefixWord ++ tailWord_1739894).sum := by decide
  have hdescent : baseEnd_1739894 < baseStart_1739894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739928 : List Nat := [2, 1, 2, 4, 2, 1, 4, 2, 5]
def baseStart_1739928 : Nat := 118140960795 + 1739928 * 2 ^ 59
def prefixEnd_1739928 : Nat := 4983230072969 + 3 ^ 40 * 1739928 * 2
def baseEnd_1739928 : Nat := 99268818690685973044247

theorem tailTrace_1739928 : CollatzResearch.WordTrace tailWord_1739928 prefixEnd_1739928 99268818690685973044247 := by
  unfold tailWord_1739928
  simp only [CollatzResearch.WordTrace]
  refine ⟨31730193820272743444854219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42306925093696991259805625 31730193820272743444854219)
  ·
    refine ⟨47595290730409115167281329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31730193820272743444854219 47595290730409115167281329)
    ·
      refine ⟨35696468047806836375460997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47595290730409115167281329 35696468047806836375460997)
      ·
        refine ⟨6693087758963781820398937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35696468047806836375460997 6693087758963781820398937)
        ·
          refine ⟨5019815819222836365299203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6693087758963781820398937 5019815819222836365299203)
          ·
            refine ⟨7529723728834254547948805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019815819222836365299203 7529723728834254547948805)
            ·
              refine ⟨1411823199156422727740401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7529723728834254547948805 1411823199156422727740401)
              ·
                refine ⟨1058867399367317045805301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411823199156422727740401 1058867399367317045805301)
                ·
                  refine ⟨99268818690685973044247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1058867399367317045805301 99268818690685973044247)
                  ·
                    rfl

theorem cell23_1739928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 5].length) (baseStart_1739928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739928 prefixEnd_1739928 := by exact prefixLift 1739928
  have htrace : WordTrace (prefixWord ++ tailWord_1739928) baseStart_1739928 baseEnd_1739928 := by
    simpa [prefixWord, tailWord_1739928, baseEnd_1739928] using wordTrace_append hprefix tailTrace_1739928
  have hstable : (prefixWord ++ tailWord_1739928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739928).length < 2 ^ (prefixWord ++ tailWord_1739928).sum := by decide
  have hdescent : baseEnd_1739928 < baseStart_1739928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739938 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1739938 : Nat := 118140960795 + 1739938 * 2 ^ 59
def prefixEnd_1739938 : Nat := 4983230072969 + 3 ^ 40 * 1739938 * 2
def baseEnd_1739938 : Nat := 893424503022718718273177

theorem tailTrace_1739938 : CollatzResearch.WordTrace tailWord_1739938 prefixEnd_1739938 893424503022718718273177 := by
  unfold tailWord_1739938
  simp only [CollatzResearch.WordTrace]
  refine ⟨15865188092627314649393117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42307168247006172398381645 15865188092627314649393117)
  ·
    refine ⟨5949445534735242993522419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15865188092627314649393117 5949445534735242993522419)
    ·
      refine ⟨8924168302102864490283629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5949445534735242993522419 8924168302102864490283629)
      ·
        refine ⟨3346563113288574183856361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8924168302102864490283629 3346563113288574183856361)
        ·
          refine ⟨2509922334966430637892271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3346563113288574183856361 2509922334966430637892271)
          ·
            refine ⟨3764883502449645956838407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509922334966430637892271 3764883502449645956838407)
            ·
              refine ⟨5647325253674468935257611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764883502449645956838407 5647325253674468935257611)
              ·
                refine ⟨8470987880511703402886417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5647325253674468935257611 8470987880511703402886417)
                ·
                  refine ⟨6353240910383777552164813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8470987880511703402886417 6353240910383777552164813)
                  ·
                    refine ⟨2382465341393916582061805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6353240910383777552164813 2382465341393916582061805)
                    ·
                      refine ⟨893424503022718718273177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2382465341393916582061805 893424503022718718273177)
                      ·
                        rfl

theorem cell23_1739938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1739938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739938 prefixEnd_1739938 := by exact prefixLift 1739938
  have htrace : WordTrace (prefixWord ++ tailWord_1739938) baseStart_1739938 baseEnd_1739938 := by
    simpa [prefixWord, tailWord_1739938, baseEnd_1739938] using wordTrace_append hprefix tailTrace_1739938
  have hstable : (prefixWord ++ tailWord_1739938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739938).length < 2 ^ (prefixWord ++ tailWord_1739938).sum := by decide
  have hdescent : baseEnd_1739938 < baseStart_1739938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739961 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 4]
def baseStart_1739961 : Nat := 118140960795 + 1739961 * 2 ^ 59
def prefixEnd_1739961 : Nat := 4983230072969 + 3 ^ 40 * 1739961 * 2
def baseEnd_1739961 : Nat := 893436313077772128285571

theorem tailTrace_1739961 : CollatzResearch.WordTrace tailWord_1739961 prefixEnd_1739961 893436313077772128285571 := by
  unfold tailWord_1739961
  simp only [CollatzResearch.WordTrace]
  refine ⟨63461591249425933525659737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42307727499617289017106491 63461591249425933525659737)
  ·
    refine ⟨47596193437069450144244803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63461591249425933525659737 47596193437069450144244803)
    ·
      refine ⟨71394290155604175216367205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47596193437069450144244803 71394290155604175216367205)
      ·
        refine ⟨13386429404175782853068851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71394290155604175216367205 13386429404175782853068851)
        ·
          refine ⟨20079644106263674279603277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13386429404175782853068851 20079644106263674279603277)
          ·
            refine ⟨7529866539848877854851229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20079644106263674279603277 7529866539848877854851229)
            ·
              refine ⟨2823699952443329195569211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7529866539848877854851229 2823699952443329195569211)
              ·
                refine ⟨4235549928664993793353817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823699952443329195569211 4235549928664993793353817)
                ·
                  refine ⟨3176662446498745345015363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235549928664993793353817 3176662446498745345015363)
                  ·
                    refine ⟨4764993669748118017523045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3176662446498745345015363 4764993669748118017523045)
                    ·
                      refine ⟨893436313077772128285571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4764993669748118017523045 893436313077772128285571)
                      ·
                        rfl

theorem cell23_1739961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_1739961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1739961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1739961 prefixEnd_1739961 := by exact prefixLift 1739961
  have htrace : WordTrace (prefixWord ++ tailWord_1739961) baseStart_1739961 baseEnd_1739961 := by
    simpa [prefixWord, tailWord_1739961, baseEnd_1739961] using wordTrace_append hprefix tailTrace_1739961
  have hstable : (prefixWord ++ tailWord_1739961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739961).length < 2 ^ (prefixWord ++ tailWord_1739961).sum := by decide
  have hdescent : baseEnd_1739961 < baseStart_1739961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740031 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 1, 5]
def baseStart_1740031 : Nat := 118140960795 + 1740031 * 2 ^ 59
def prefixEnd_1740031 : Nat := 4983230072969 + 3 ^ 40 * 1740031 * 2
def baseEnd_1740031 : Nat := 297824085574528951470083

theorem tailTrace_1740031 : CollatzResearch.WordTrace tailWord_1740031 prefixEnd_1740031 297824085574528951470083 := by
  unfold tailWord_1740031
  simp only [CollatzResearch.WordTrace]
  refine ⟨63464144359172335480707947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42309429572781556987138631 63464144359172335480707947)
  ·
    refine ⟨95196216538758503221061921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63464144359172335480707947 95196216538758503221061921)
    ·
      refine ⟨71397162404068877415796441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95196216538758503221061921 71397162404068877415796441)
      ·
        refine ⟨53547871803051658061847331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71397162404068877415796441 53547871803051658061847331)
        ·
          refine ⟨80321807704577487092770997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53547871803051658061847331 80321807704577487092770997)
          ·
            refine ⟨7530169472304139414947281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80321807704577487092770997 7530169472304139414947281)
            ·
              refine ⟨5647627104228104561210461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7530169472304139414947281 5647627104228104561210461)
              ·
                refine ⟨2117860164085539210453923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5647627104228104561210461 2117860164085539210453923)
                ·
                  refine ⟨3176790246128308815680885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117860164085539210453923 3176790246128308815680885)
                  ·
                    refine ⟨297824085574528951470083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3176790246128308815680885 297824085574528951470083)
                    ·
                      rfl

theorem cell23_1740031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 5].length) (baseStart_1740031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740031 prefixEnd_1740031 := by exact prefixLift 1740031
  have htrace : WordTrace (prefixWord ++ tailWord_1740031) baseStart_1740031 baseEnd_1740031 := by
    simpa [prefixWord, tailWord_1740031, baseEnd_1740031] using wordTrace_append hprefix tailTrace_1740031
  have hstable : (prefixWord ++ tailWord_1740031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740031).length < 2 ^ (prefixWord ++ tailWord_1740031).sum := by decide
  have hdescent : baseEnd_1740031 < baseStart_1740031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740081 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1740081 : Nat := 118140960795 + 1740081 * 2 ^ 59
def prefixEnd_1740081 : Nat := 4983230072969 + 3 ^ 40 * 1740081 * 2
def baseEnd_1740081 : Nat := 893497930756311658785019

theorem tailTrace_1740081 : CollatzResearch.WordTrace tailWord_1740081 prefixEnd_1740081 893497930756311658785019 := by
  unfold tailWord_1740081
  simp only [CollatzResearch.WordTrace]
  refine ⟨63465968008991194020028097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42310645339327462680018731 63465968008991194020028097)
  ·
    refine ⟨47599476006743395515021073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63465968008991194020028097 47599476006743395515021073)
    ·
      refine ⟨35699607005057546636265805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47599476006743395515021073 35699607005057546636265805)
      ·
        refine ⟨13387352626896579988599677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35699607005057546636265805 13387352626896579988599677)
        ·
          refine ⟨5020257235086217495724879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13387352626896579988599677 5020257235086217495724879)
          ·
            refine ⟨7530385852629326243587319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020257235086217495724879 7530385852629326243587319)
            ·
              refine ⟨11295578778943989365380979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7530385852629326243587319 11295578778943989365380979)
              ·
                refine ⟨16943368168415984048071469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11295578778943989365380979 16943368168415984048071469)
                ·
                  refine ⟨6353763063155994018026801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16943368168415984048071469 6353763063155994018026801)
                  ·
                    refine ⟨4765322297366995513520101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6353763063155994018026801 4765322297366995513520101)
                    ·
                      refine ⟨893497930756311658785019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4765322297366995513520101 893497930756311658785019)
                      ·
                        rfl

theorem cell23_1740081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1740081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740081 prefixEnd_1740081 := by exact prefixLift 1740081
  have htrace : WordTrace (prefixWord ++ tailWord_1740081) baseStart_1740081 baseEnd_1740081 := by
    simpa [prefixWord, tailWord_1740081, baseEnd_1740081] using wordTrace_append hprefix tailTrace_1740081
  have hstable : (prefixWord ++ tailWord_1740081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740081).length < 2 ^ (prefixWord ++ tailWord_1740081).sum := by decide
  have hdescent : baseEnd_1740081 < baseStart_1740081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740085 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_1740085 : Nat := 118140960795 + 1740085 * 2 ^ 59
def prefixEnd_1740085 : Nat := 4983230072969 + 3 ^ 40 * 1740085 * 2
def baseEnd_1740085 : Nat := 893499984678929643135001

theorem tailTrace_1740085 : CollatzResearch.WordTrace tailWord_1740085 prefixEnd_1740085 893499984678929643135001 := by
  unfold tailWord_1740085
  simp only [CollatzResearch.WordTrace]
  refine ⟨63466113900976702703173709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42310742600651135135449139 63466113900976702703173709)
  ·
    refine ⟨23799792712866263513690141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63466113900976702703173709 23799792712866263513690141)
    ·
      refine ⟨8924922267324848817633803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23799792712866263513690141 8924922267324848817633803)
      ·
        refine ⟨13387383400987273226450705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8924922267324848817633803 13387383400987273226450705)
        ·
          refine ⟨10040537550740454919838029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13387383400987273226450705 10040537550740454919838029)
          ·
            refine ⟨3765201581527670594939261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10040537550740454919838029 3765201581527670594939261)
            ·
              refine ⟨1411950593072876473102223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3765201581527670594939261 1411950593072876473102223)
              ·
                refine ⟨2117925889609314709653335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411950593072876473102223 2117925889609314709653335)
                ·
                  refine ⟨3176888834413972064480003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117925889609314709653335 3176888834413972064480003)
                  ·
                    refine ⟨4765333251620958096720005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3176888834413972064480003 4765333251620958096720005)
                    ·
                      refine ⟨893499984678929643135001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4765333251620958096720005 893499984678929643135001)
                      ·
                        rfl

theorem cell23_1740085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_1740085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740085 prefixEnd_1740085 := by exact prefixLift 1740085
  have htrace : WordTrace (prefixWord ++ tailWord_1740085) baseStart_1740085 baseEnd_1740085 := by
    simpa [prefixWord, tailWord_1740085, baseEnd_1740085] using wordTrace_append hprefix tailTrace_1740085
  have hstable : (prefixWord ++ tailWord_1740085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740085).length < 2 ^ (prefixWord ++ tailWord_1740085).sum := by decide
  have hdescent : baseEnd_1740085 < baseStart_1740085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740171 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 4]
def baseStart_1740171 : Nat := 118140960795 + 1740171 * 2 ^ 59
def prefixEnd_1740171 : Nat := 4983230072969 + 3 ^ 40 * 1740171 * 2
def baseEnd_1740171 : Nat := 893544144015216306659605

theorem tailTrace_1740171 : CollatzResearch.WordTrace tailWord_1740171 prefixEnd_1740171 893544144015216306659605 := by
  unfold tailWord_1740171
  simp only [CollatzResearch.WordTrace]
  refine ⟨63469250578665139390804367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42312833719110092927202911 63469250578665139390804367)
  ·
    refine ⟨95203875867997709086206551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63469250578665139390804367 95203875867997709086206551)
    ·
      refine ⟨142805813801996563629309827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95203875867997709086206551 142805813801996563629309827)
      ·
        refine ⟨214208720702994845443964741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142805813801996563629309827 214208720702994845443964741)
        ·
          refine ⟨40164135131811533520743389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214208720702994845443964741 40164135131811533520743389)
          ·
            refine ⟨15061550674429325070278771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40164135131811533520743389 15061550674429325070278771)
            ·
              refine ⟨22592326011643987605418157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15061550674429325070278771 22592326011643987605418157)
              ·
                refine ⟨8472122254366495352031809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22592326011643987605418157 8472122254366495352031809)
                ·
                  refine ⟨6354091690774871514023857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8472122254366495352031809 6354091690774871514023857)
                  ·
                    refine ⟨4765568768081153635517893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6354091690774871514023857 4765568768081153635517893)
                    ·
                      refine ⟨893544144015216306659605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4765568768081153635517893 893544144015216306659605)
                      ·
                        rfl

theorem cell23_1740171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 4].length) (baseStart_1740171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740171 prefixEnd_1740171 := by exact prefixLift 1740171
  have htrace : WordTrace (prefixWord ++ tailWord_1740171) baseStart_1740171 baseEnd_1740171 := by
    simpa [prefixWord, tailWord_1740171, baseEnd_1740171] using wordTrace_append hprefix tailTrace_1740171
  have hstable : (prefixWord ++ tailWord_1740171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740171).length < 2 ^ (prefixWord ++ tailWord_1740171).sum := by decide
  have hdescent : baseEnd_1740171 < baseStart_1740171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740181 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 7]
def baseStart_1740181 : Nat := 118140960795 + 1740181 * 2 ^ 59
def prefixEnd_1740181 : Nat := 4983230072969 + 3 ^ 40 * 1740181 * 2
def baseEnd_1740181 : Nat := 99283253202417918614951

theorem tailTrace_1740181 : CollatzResearch.WordTrace tailWord_1740181 prefixEnd_1740181 99283253202417918614951 := by
  unfold tailWord_1740181
  simp only [CollatzResearch.WordTrace]
  refine ⟨63469615308628911098668397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42313076872419274065778931 63469615308628911098668397)
  ·
    refine ⟨23801105740735841662000649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63469615308628911098668397 23801105740735841662000649)
    ·
      refine ⟨17850829305551881246500487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23801105740735841662000649 17850829305551881246500487)
      ·
        refine ⟨26776243958327821869750731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17850829305551881246500487 26776243958327821869750731)
        ·
          refine ⟨40164365937491732804626097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26776243958327821869750731 40164365937491732804626097)
          ·
            refine ⟨30123274453118799603469573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40164365937491732804626097 30123274453118799603469573)
            ·
              refine ⟨5648113959959774925650545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30123274453118799603469573 5648113959959774925650545)
              ·
                refine ⟨4236085469969831194237909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5648113959959774925650545 4236085469969831194237909)
                ·
                  refine ⟨99283253202417918614951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4236085469969831194237909 99283253202417918614951)
                  ·
                    rfl

theorem cell23_1740181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_1740181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740181 prefixEnd_1740181 := by exact prefixLift 1740181
  have htrace : WordTrace (prefixWord ++ tailWord_1740181) baseStart_1740181 baseEnd_1740181 := by
    simpa [prefixWord, tailWord_1740181, baseEnd_1740181] using wordTrace_append hprefix tailTrace_1740181
  have hstable : (prefixWord ++ tailWord_1740181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740181).length < 2 ^ (prefixWord ++ tailWord_1740181).sum := by decide
  have hdescent : baseEnd_1740181 < baseStart_1740181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740215 : List Nat := [1, 1, 3, 1, 3, 2, 5, 2, 5]
def baseStart_1740215 : Nat := 118140960795 + 1740215 * 2 ^ 59
def prefixEnd_1740215 : Nat := 4983230072969 + 3 ^ 40 * 1740215 * 2
def baseEnd_1740215 : Nat := 99285193018223792723267

theorem tailTrace_1740215 : CollatzResearch.WordTrace tailWord_1740215 prefixEnd_1740215 99285193018223792723267 := by
  unfold tailWord_1740215
  simp only [CollatzResearch.WordTrace]
  refine ⟨63470855390505734905406099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42313903593670489936937399 63470855390505734905406099)
  ·
    refine ⟨95206283085758602358109149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63470855390505734905406099 95206283085758602358109149)
    ·
      refine ⟨35702356157159475884290931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95206283085758602358109149 35702356157159475884290931)
      ·
        refine ⟨53553534235739213826436397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35702356157159475884290931 53553534235739213826436397)
        ·
          refine ⟨20082575338402205184913649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53553534235739213826436397 20082575338402205184913649)
          ·
            refine ⟨15061931503801653888685237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20082575338402205184913649 15061931503801653888685237)
            ·
              refine ⟨1412056078481405052064241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15061931503801653888685237 1412056078481405052064241)
              ·
                refine ⟨1059042058861053789048181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1412056078481405052064241 1059042058861053789048181)
                ·
                  refine ⟨99285193018223792723267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1059042058861053789048181 99285193018223792723267)
                  ·
                    rfl

theorem cell23_1740215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 5].length) (baseStart_1740215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740215 prefixEnd_1740215 := by exact prefixLift 1740215
  have htrace : WordTrace (prefixWord ++ tailWord_1740215) baseStart_1740215 baseEnd_1740215 := by
    simpa [prefixWord, tailWord_1740215, baseEnd_1740215] using wordTrace_append hprefix tailTrace_1740215
  have hstable : (prefixWord ++ tailWord_1740215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740215).length < 2 ^ (prefixWord ++ tailWord_1740215).sum := by decide
  have hdescent : baseEnd_1740215 < baseStart_1740215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740248 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_1740248 : Nat := 118140960795 + 1740248 * 2 ^ 59
def prefixEnd_1740248 : Nat := 4983230072969 + 3 ^ 40 * 1740248 * 2
def baseEnd_1740248 : Nat := 893583682025612505396751

theorem tailTrace_1740248 : CollatzResearch.WordTrace tailWord_1740248 prefixEnd_1740248 893583682025612505396751 := by
  unfold tailWord_1740248
  simp only [CollatzResearch.WordTrace]
  refine ⟨31736029499693090770678699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42314705999590787694238265 31736029499693090770678699)
  ·
    refine ⟨47604044249539636156018049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31736029499693090770678699 47604044249539636156018049)
    ·
      refine ⟨35703033187154727117013537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47604044249539636156018049 35703033187154727117013537)
      ·
        refine ⟨26777274890366045337760153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35703033187154727117013537 26777274890366045337760153)
        ·
          refine ⟨20082956167774534003320115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26777274890366045337760153 20082956167774534003320115)
          ·
            refine ⟨30124434251661801004980173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20082956167774534003320115 30124434251661801004980173)
            ·
              refine ⟨11296662844373175376867565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30124434251661801004980173 11296662844373175376867565)
              ·
                refine ⟨4236248566639940766325337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11296662844373175376867565 4236248566639940766325337)
                ·
                  refine ⟨3177186424979955574744003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236248566639940766325337 3177186424979955574744003)
                  ·
                    refine ⟨4765779637469933362116005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3177186424979955574744003 4765779637469933362116005)
                    ·
                      refine ⟨893583682025612505396751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4765779637469933362116005 893583682025612505396751)
                      ·
                        rfl

theorem cell23_1740248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_1740248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740248 prefixEnd_1740248 := by exact prefixLift 1740248
  have htrace : WordTrace (prefixWord ++ tailWord_1740248) baseStart_1740248 baseEnd_1740248 := by
    simpa [prefixWord, tailWord_1740248, baseEnd_1740248] using wordTrace_append hprefix tailTrace_1740248
  have hstable : (prefixWord ++ tailWord_1740248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740248).length < 2 ^ (prefixWord ++ tailWord_1740248).sum := by decide
  have hdescent : baseEnd_1740248 < baseStart_1740248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740268 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 3]
def baseStart_1740268 : Nat := 118140960795 + 1740268 * 2 ^ 59
def prefixEnd_1740268 : Nat := 4983230072969 + 3 ^ 40 * 1740268 * 2
def baseEnd_1740268 : Nat := 893593951638702427146659

theorem tailTrace_1740268 : CollatzResearch.WordTrace tailWord_1740268 prefixEnd_1740268 893593951638702427146659 := by
  unfold tailWord_1740268
  simp only [CollatzResearch.WordTrace]
  refine ⟨31736394229656862478542729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42315192306209149971390305 31736394229656862478542729)
  ·
    refine ⟨23802295672242646858907047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31736394229656862478542729 23802295672242646858907047)
    ·
      refine ⟨35703443508363970288360571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23802295672242646858907047 35703443508363970288360571)
      ·
        refine ⟨53555165262545955432540857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35703443508363970288360571 53555165262545955432540857)
        ·
          refine ⟨40166373946909466574405643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53555165262545955432540857 40166373946909466574405643)
          ·
            refine ⟨60249560920364199861608465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40166373946909466574405643 60249560920364199861608465)
            ·
              refine ⟨45187170690273149896206349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60249560920364199861608465 45187170690273149896206349)
              ·
                refine ⟨16945189008852431211077381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45187170690273149896206349 16945189008852431211077381)
                ·
                  refine ⟨3177222939159830852077009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16945189008852431211077381 3177222939159830852077009)
                  ·
                    refine ⟨2382917204369873139057757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3177222939159830852077009 2382917204369873139057757)
                    ·
                      refine ⟨893593951638702427146659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2382917204369873139057757 893593951638702427146659)
                      ·
                        rfl

theorem cell23_1740268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_1740268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740268 prefixEnd_1740268 := by exact prefixLift 1740268
  have htrace : WordTrace (prefixWord ++ tailWord_1740268) baseStart_1740268 baseEnd_1740268 := by
    simpa [prefixWord, tailWord_1740268, baseEnd_1740268] using wordTrace_append hprefix tailTrace_1740268
  have hstable : (prefixWord ++ tailWord_1740268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740268).length < 2 ^ (prefixWord ++ tailWord_1740268).sum := by decide
  have hdescent : baseEnd_1740268 < baseStart_1740268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740271 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 8]
def baseStart_1740271 : Nat := 118140960795 + 1740271 * 2 ^ 59
def prefixEnd_1740271 : Nat := 4983230072969 + 3 ^ 40 * 1740271 * 2
def baseEnd_1740271 : Nat := 99288388008962879489905

theorem tailTrace_1740271 : CollatzResearch.WordTrace tailWord_1740271 prefixEnd_1740271 99288388008962879489905 := by
  unfold tailWord_1740271
  simp only [CollatzResearch.WordTrace]
  refine ⟨63472897878302856469444667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42315265252201904312963111 63472897878302856469444667)
  ·
    refine ⟨95209346817454284704167001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63472897878302856469444667 95209346817454284704167001)
    ·
      refine ⟨71407010113090713528125251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95209346817454284704167001 71407010113090713528125251)
      ·
        refine ⟨107110515169636070292187877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71407010113090713528125251 107110515169636070292187877)
        ·
          refine ⟨20083221594306763179785227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107110515169636070292187877 20083221594306763179785227)
          ·
            refine ⟨30124832391460144769677841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20083221594306763179785227 30124832391460144769677841)
            ·
              refine ⟨22593624293595108577258381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30124832391460144769677841 22593624293595108577258381)
              ·
                refine ⟨8472609110098165716471893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22593624293595108577258381 8472609110098165716471893)
                ·
                  refine ⟨99288388008962879489905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8472609110098165716471893 99288388008962879489905)
                  ·
                    rfl

theorem cell23_1740271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 8].length) (baseStart_1740271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740271 prefixEnd_1740271 := by exact prefixLift 1740271
  have htrace : WordTrace (prefixWord ++ tailWord_1740271) baseStart_1740271 baseEnd_1740271 := by
    simpa [prefixWord, tailWord_1740271, baseEnd_1740271] using wordTrace_append hprefix tailTrace_1740271
  have hstable : (prefixWord ++ tailWord_1740271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740271).length < 2 ^ (prefixWord ++ tailWord_1740271).sum := by decide
  have hdescent : baseEnd_1740271 < baseStart_1740271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740291 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 6]
def baseStart_1740291 : Nat := 118140960795 + 1740291 * 2 ^ 59
def prefixEnd_1740291 : Nat := 4983230072969 + 3 ^ 40 * 1740291 * 2
def baseEnd_1740291 : Nat := 893605761693755837159053

theorem tailTrace_1740291 : CollatzResearch.WordTrace tailWord_1740291 prefixEnd_1740291 893605761693755837159053 := by
  unfold tailWord_1740291
  simp only [CollatzResearch.WordTrace]
  refine ⟨63473627338230399885172727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42315751558820266590115151 63473627338230399885172727)
  ·
    refine ⟨95210441007345599827759091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63473627338230399885172727 95210441007345599827759091)
    ·
      refine ⟨142815661511018399741638637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95210441007345599827759091 142815661511018399741638637)
      ·
        refine ⟨53555873066631899903114489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142815661511018399741638637 53555873066631899903114489)
        ·
          refine ⟨40166904799973924927335867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53555873066631899903114489 40166904799973924927335867)
          ·
            refine ⟨60250357199960887391003801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40166904799973924927335867 60250357199960887391003801)
            ·
              refine ⟨45187767899970665543252851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60250357199960887391003801 45187767899970665543252851)
              ·
                refine ⟨67781651849955998314879277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45187767899970665543252851 67781651849955998314879277)
                ·
                  refine ⟨25418119443733499368079729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67781651849955998314879277 25418119443733499368079729)
                  ·
                    refine ⟨19063589582800124526059797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25418119443733499368079729 19063589582800124526059797)
                    ·
                      refine ⟨893605761693755837159053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19063589582800124526059797 893605761693755837159053)
                      ·
                        rfl

theorem cell23_1740291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_1740291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740291 prefixEnd_1740291 := by exact prefixLift 1740291
  have htrace : WordTrace (prefixWord ++ tailWord_1740291) baseStart_1740291 baseEnd_1740291 := by
    simpa [prefixWord, tailWord_1740291, baseEnd_1740291] using wordTrace_append hprefix tailTrace_1740291
  have hstable : (prefixWord ++ tailWord_1740291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740291).length < 2 ^ (prefixWord ++ tailWord_1740291).sum := by decide
  have hdescent : baseEnd_1740291 < baseStart_1740291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740292 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1740292 : Nat := 118140960795 + 1740292 * 2 ^ 59
def prefixEnd_1740292 : Nat := 4983230072969 + 3 ^ 40 * 1740292 * 2
def baseEnd_1740292 : Nat := 297868758391470111082183

theorem tailTrace_1740292 : CollatzResearch.WordTrace tailWord_1740292 prefixEnd_1740292 297868758391470111082183 := by
  unfold tailWord_1740292
  simp only [CollatzResearch.WordTrace]
  refine ⟨31736831905613388527979565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42315775874151184703972753 31736831905613388527979565)
  ·
    refine ⟨11901311964605020697992337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31736831905613388527979565 11901311964605020697992337)
    ·
      refine ⟨8925983973453765523494253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11901311964605020697992337 8925983973453765523494253)
      ·
        refine ⟨3347243990045162071310345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8925983973453765523494253 3347243990045162071310345)
        ·
          refine ⟨2510432992533871553482759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3347243990045162071310345 2510432992533871553482759)
          ·
            refine ⟨3765649488800807330224139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510432992533871553482759 3765649488800807330224139)
            ·
              refine ⟨5648474233201210995336209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765649488800807330224139 5648474233201210995336209)
              ·
                refine ⟨4236355674900908246502157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5648474233201210995336209 4236355674900908246502157)
                ·
                  refine ⟨1588633378087840592438309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4236355674900908246502157 1588633378087840592438309)
                  ·
                    refine ⟨297868758391470111082183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1588633378087840592438309 297868758391470111082183)
                    ·
                      rfl

theorem cell23_1740292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1740292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740292 prefixEnd_1740292 := by exact prefixLift 1740292
  have htrace : WordTrace (prefixWord ++ tailWord_1740292) baseStart_1740292 baseEnd_1740292 := by
    simpa [prefixWord, tailWord_1740292, baseEnd_1740292] using wordTrace_append hprefix tailTrace_1740292
  have hstable : (prefixWord ++ tailWord_1740292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740292).length < 2 ^ (prefixWord ++ tailWord_1740292).sum := by decide
  have hdescent : baseEnd_1740292 < baseStart_1740292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740325 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 4, 3, 2]
def baseStart_1740325 : Nat := 118140960795 + 1740325 * 2 ^ 59
def prefixEnd_1740325 : Nat := 4983230072969 + 3 ^ 40 * 1740325 * 2
def baseEnd_1740325 : Nat := 893623220036008704133897

theorem tailTrace_1740325 : CollatzResearch.WordTrace tailWord_1740325 prefixEnd_1740325 893623220036008704133897 := by
  unfold tailWord_1740325
  simp only [CollatzResearch.WordTrace]
  refine ⟨63474867420107223691910429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42316578280071482461273619 63474867420107223691910429)
  ·
    refine ⟨23803075282540208884466411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63474867420107223691910429 23803075282540208884466411)
    ·
      refine ⟨35704612923810313326699617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23803075282540208884466411 35704612923810313326699617)
      ·
        refine ⟨26778459692857734995024713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35704612923810313326699617 26778459692857734995024713)
        ·
          refine ⟨20083844769643301246268535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26778459692857734995024713 20083844769643301246268535)
          ·
            refine ⟨30125767154464951869402803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20083844769643301246268535 30125767154464951869402803)
            ·
              refine ⟨45188650731697427804104205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30125767154464951869402803 45188650731697427804104205)
              ·
                refine ⟨16945744024386535426539077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45188650731697427804104205 16945744024386535426539077)
                ·
                  refine ⟨3177327004572475392476077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16945744024386535426539077 3177327004572475392476077)
                  ·
                    refine ⟨1191497626714678272178529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177327004572475392476077 1191497626714678272178529)
                    ·
                      refine ⟨893623220036008704133897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191497626714678272178529 893623220036008704133897)
                      ·
                        rfl

theorem cell23_1740325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_1740325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740325 prefixEnd_1740325 := by exact prefixLift 1740325
  have htrace : WordTrace (prefixWord ++ tailWord_1740325) baseStart_1740325 baseEnd_1740325 := by
    simpa [prefixWord, tailWord_1740325, baseEnd_1740325] using wordTrace_append hprefix tailTrace_1740325
  have hstable : (prefixWord ++ tailWord_1740325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740325).length < 2 ^ (prefixWord ++ tailWord_1740325).sum := by decide
  have hdescent : baseEnd_1740325 < baseStart_1740325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740331 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 2, 10]
def baseStart_1740331 : Nat := 118140960795 + 1740331 * 2 ^ 59
def prefixEnd_1740331 : Nat := 4983230072969 + 3 ^ 40 * 1740331 * 2
def baseEnd_1740331 : Nat := 297875433639978560219623

theorem tailTrace_1740331 : CollatzResearch.WordTrace tailWord_1740331 prefixEnd_1740331 297875433639978560219623 := by
  unfold tailWord_1740331
  simp only [CollatzResearch.WordTrace]
  refine ⟨63475086258085486716628847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42316724172056991144419231 63475086258085486716628847)
  ·
    refine ⟨95212629387128230074943271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63475086258085486716628847 95212629387128230074943271)
    ·
      refine ⟨142818944080692345112414907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95212629387128230074943271 142818944080692345112414907)
      ·
        refine ⟨214228416121038517668622361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142818944080692345112414907 214228416121038517668622361)
        ·
          refine ⟨160671312090778888251466771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214228416121038517668622361 160671312090778888251466771)
          ·
            refine ⟨241006968136168332377200157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160671312090778888251466771 241006968136168332377200157)
            ·
              refine ⟨90377613051063124641450059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241006968136168332377200157 90377613051063124641450059)
              ·
                refine ⟨135566419576594686962175089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90377613051063124641450059 135566419576594686962175089)
                ·
                  refine ⟨101674814682446015221631317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135566419576594686962175089 101674814682446015221631317)
                  ·
                    refine ⟨297875433639978560219623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 101674814682446015221631317 297875433639978560219623)
                    ·
                      rfl

theorem cell23_1740331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 10].length) (baseStart_1740331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740331 prefixEnd_1740331 := by exact prefixLift 1740331
  have htrace : WordTrace (prefixWord ++ tailWord_1740331) baseStart_1740331 baseEnd_1740331 := by
    simpa [prefixWord, tailWord_1740331, baseEnd_1740331] using wordTrace_append hprefix tailTrace_1740331
  have hstable : (prefixWord ++ tailWord_1740331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740331).length < 2 ^ (prefixWord ++ tailWord_1740331).sum := by decide
  have hdescent : baseEnd_1740331 < baseStart_1740331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740368 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_1740368 : Nat := 118140960795 + 1740368 * 2 ^ 59
def prefixEnd_1740368 : Nat := 4983230072969 + 3 ^ 40 * 1740368 * 2
def baseEnd_1740368 : Nat := 893645299704152035896199

theorem tailTrace_1740368 : CollatzResearch.WordTrace tailWord_1740368 prefixEnd_1740368 893645299704152035896199 := by
  unfold tailWord_1740368
  simp only [CollatzResearch.WordTrace]
  refine ⟨31738217879475721017862879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42317623839300961357150505 31738217879475721017862879)
  ·
    refine ⟨47607326819213581526794319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31738217879475721017862879 47607326819213581526794319)
    ·
      refine ⟨71410990228820372290191479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47607326819213581526794319 71410990228820372290191479)
      ·
        refine ⟨107116485343230558435287219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71410990228820372290191479 107116485343230558435287219)
        ·
          refine ⟨160674728014845837652930829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107116485343230558435287219 160674728014845837652930829)
          ·
            refine ⟨60253023005567189119849061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160674728014845837652930829 60253023005567189119849061)
            ·
              refine ⟨11297441813543847959971699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60253023005567189119849061 11297441813543847959971699)
              ·
                refine ⟨16946162720315771939957549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11297441813543847959971699 16946162720315771939957549)
                ·
                  refine ⟨6354811020118414477484081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16946162720315771939957549 6354811020118414477484081)
                  ·
                    refine ⟨4766108265088810858113061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6354811020118414477484081 4766108265088810858113061)
                    ·
                      refine ⟨893645299704152035896199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4766108265088810858113061 893645299704152035896199)
                      ·
                        rfl

theorem cell23_1740368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_1740368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740368 prefixEnd_1740368 := by exact prefixLift 1740368
  have htrace : WordTrace (prefixWord ++ tailWord_1740368) baseStart_1740368 baseEnd_1740368 := by
    simpa [prefixWord, tailWord_1740368, baseEnd_1740368] using wordTrace_append hprefix tailTrace_1740368
  have hstable : (prefixWord ++ tailWord_1740368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740368).length < 2 ^ (prefixWord ++ tailWord_1740368).sum := by decide
  have hdescent : baseEnd_1740368 < baseStart_1740368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740375 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 5]
def baseStart_1740375 : Nat := 118140960795 + 1740375 * 2 ^ 59
def prefixEnd_1740375 : Nat := 4983230072969 + 3 ^ 40 * 1740375 * 2
def baseEnd_1740375 : Nat := 893648894068733508508667

theorem tailTrace_1740375 : CollatzResearch.WordTrace tailWord_1740375 prefixEnd_1740375 893648894068733508508667 := by
  unfold tailWord_1740375
  simp only [CollatzResearch.WordTrace]
  refine ⟨63476691069926082231230579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42317794046617388154153719 63476691069926082231230579)
  ·
    refine ⟨95215036604889123346845869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63476691069926082231230579 95215036604889123346845869)
    ·
      refine ⟨35705638726833421255067201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95215036604889123346845869 35705638726833421255067201)
      ·
        refine ⟨26779229045125065941300401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35705638726833421255067201 26779229045125065941300401)
        ·
          refine ⟨20084421783843799455975301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26779229045125065941300401 20084421783843799455975301)
          ·
            refine ⟨3765829084470712397995369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20084421783843799455975301 3765829084470712397995369)
            ·
              refine ⟨2824371813353034298496527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765829084470712397995369 2824371813353034298496527)
              ·
                refine ⟨4236557720029551447744791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824371813353034298496527 4236557720029551447744791)
                ·
                  refine ⟨6354836580044327171617187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4236557720029551447744791 6354836580044327171617187)
                  ·
                    refine ⟨9532254870066490757425781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6354836580044327171617187 9532254870066490757425781)
                    ·
                      refine ⟨893648894068733508508667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9532254870066490757425781 893648894068733508508667)
                      ·
                        rfl

theorem cell23_1740375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_1740375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740375 prefixEnd_1740375 := by exact prefixLift 1740375
  have htrace : WordTrace (prefixWord ++ tailWord_1740375) baseStart_1740375 baseEnd_1740375 := by
    simpa [prefixWord, tailWord_1740375, baseEnd_1740375] using wordTrace_append hprefix tailTrace_1740375
  have hstable : (prefixWord ++ tailWord_1740375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740375).length < 2 ^ (prefixWord ++ tailWord_1740375).sum := by decide
  have hdescent : baseEnd_1740375 < baseStart_1740375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740389 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 3, 2, 2]
def baseStart_1740389 : Nat := 118140960795 + 1740389 * 2 ^ 59
def prefixEnd_1740389 : Nat := 4983230072969 + 3 ^ 40 * 1740389 * 2
def baseEnd_1740389 : Nat := 893656082797896453733603

theorem tailTrace_1740389 : CollatzResearch.WordTrace tailWord_1740389 prefixEnd_1740389 893656082797896453733603 := by
  unfold tailWord_1740389
  simp only [CollatzResearch.WordTrace]
  refine ⟨63477201691875362622240221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42318134461250241748160147 63477201691875362622240221)
  ·
    refine ⟨23803950634453260983340083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63477201691875362622240221 23803950634453260983340083)
    ·
      refine ⟨35705925951679891475010125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23803950634453260983340083 35705925951679891475010125)
      ·
        refine ⟨13389722231879959303128797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35705925951679891475010125 13389722231879959303128797)
        ·
          refine ⟨5021145836954984738673299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13389722231879959303128797 5021145836954984738673299)
          ·
            refine ⟨7531718755432477108009949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5021145836954984738673299 7531718755432477108009949)
            ·
              refine ⟨2824394533287178915503731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7531718755432477108009949 2824394533287178915503731)
              ·
                refine ⟨4236591799930768373255597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824394533287178915503731 4236591799930768373255597)
                ·
                  refine ⟨1588721924974038139970849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4236591799930768373255597 1588721924974038139970849)
                  ·
                    refine ⟨1191541443730528604978137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588721924974038139970849 1191541443730528604978137)
                    ·
                      refine ⟨893656082797896453733603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191541443730528604978137 893656082797896453733603)
                      ·
                        rfl

theorem cell23_1740389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_1740389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740389 prefixEnd_1740389 := by exact prefixLift 1740389
  have htrace : WordTrace (prefixWord ++ tailWord_1740389) baseStart_1740389 baseEnd_1740389 := by
    simpa [prefixWord, tailWord_1740389, baseEnd_1740389] using wordTrace_append hprefix tailTrace_1740389
  have hstable : (prefixWord ++ tailWord_1740389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740389).length < 2 ^ (prefixWord ++ tailWord_1740389).sum := by decide
  have hdescent : baseEnd_1740389 < baseStart_1740389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740432 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 1, 3, 2]
def baseStart_1740432 : Nat := 118140960795 + 1740432 * 2 ^ 59
def prefixEnd_1740432 : Nat := 4983230072969 + 3 ^ 40 * 1740432 * 2
def baseEnd_1740432 : Nat := 893678162466039785495905

theorem tailTrace_1740432 : CollatzResearch.WordTrace tailWord_1740432 prefixEnd_1740432 893678162466039785495905 := by
  unfold tailWord_1740432
  simp only [CollatzResearch.WordTrace]
  refine ⟨31739385015359790483027775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42319180020479720644037033 31739385015359790483027775)
  ·
    refine ⟨47609077523039685724541663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31739385015359790483027775 47609077523039685724541663)
    ·
      refine ⟨71413616284559528586812495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47609077523039685724541663 71413616284559528586812495)
      ·
        refine ⟨107120424426839292880218743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71413616284559528586812495 107120424426839292880218743)
        ·
          refine ⟨160680636640258939320328115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107120424426839292880218743 160680636640258939320328115)
          ·
            refine ⟨241020954960388408980492173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160680636640258939320328115 241020954960388408980492173)
            ·
              refine ⟨90382858110145653367684565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241020954960388408980492173 90382858110145653367684565)
              ·
                refine ⟨2118348236956538750805107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90382858110145653367684565 2118348236956538750805107)
                ·
                  refine ⟨3177522355434808126207661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118348236956538750805107 3177522355434808126207661)
                  ·
                    refine ⟨1191570883288053047327873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177522355434808126207661 1191570883288053047327873)
                    ·
                      refine ⟨893678162466039785495905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191570883288053047327873 893678162466039785495905)
                      ·
                        rfl

theorem cell23_1740432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 3, 2].length) (baseStart_1740432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740432 prefixEnd_1740432 := by exact prefixLift 1740432
  have htrace : WordTrace (prefixWord ++ tailWord_1740432) baseStart_1740432 baseEnd_1740432 := by
    simpa [prefixWord, tailWord_1740432, baseEnd_1740432] using wordTrace_append hprefix tailTrace_1740432
  have hstable : (prefixWord ++ tailWord_1740432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740432).length < 2 ^ (prefixWord ++ tailWord_1740432).sum := by decide
  have hdescent : baseEnd_1740432 < baseStart_1740432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740439 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 2, 1, 3]
def baseStart_1740439 : Nat := 118140960795 + 1740439 * 2 ^ 59
def prefixEnd_1740439 : Nat := 4983230072969 + 3 ^ 40 * 1740439 * 2
def baseEnd_1740439 : Nat := 893681756830621258108373

theorem tailTrace_1740439 : CollatzResearch.WordTrace tailWord_1740439 prefixEnd_1740439 893681756830621258108373 := by
  unfold tailWord_1740439
  simp only [CollatzResearch.WordTrace]
  refine ⟨63479025341694221161560371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42319350227796147441040247 63479025341694221161560371)
  ·
    refine ⟨95218538012541331742340557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63479025341694221161560371 95218538012541331742340557)
    ·
      refine ⟨35706951754702999403377709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95218538012541331742340557 35706951754702999403377709)
      ·
        refine ⟨13390106908013624776266641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35706951754702999403377709 13390106908013624776266641)
        ·
          refine ⟨10042580181010218582199981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13390106908013624776266641 10042580181010218582199981)
          ·
            refine ⟨3765967567878831968324993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10042580181010218582199981 3765967567878831968324993)
            ·
              refine ⟨2824475675909123976243745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765967567878831968324993 2824475675909123976243745)
              ·
                refine ⟨2118356756931842982182809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824475675909123976243745 2118356756931842982182809)
                ·
                  refine ⟨1588767567698882236637107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118356756931842982182809 1588767567698882236637107)
                  ·
                    refine ⟨2383151351548323354955661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1588767567698882236637107 2383151351548323354955661)
                    ·
                      refine ⟨893681756830621258108373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2383151351548323354955661 893681756830621258108373)
                      ·
                        rfl

theorem cell23_1740439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_1740439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740439 prefixEnd_1740439 := by exact prefixLift 1740439
  have htrace : WordTrace (prefixWord ++ tailWord_1740439) baseStart_1740439 baseEnd_1740439 := by
    simpa [prefixWord, tailWord_1740439, baseEnd_1740439] using wordTrace_append hprefix tailTrace_1740439
  have hstable : (prefixWord ++ tailWord_1740439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740439).length < 2 ^ (prefixWord ++ tailWord_1740439).sum := by decide
  have hdescent : baseEnd_1740439 < baseStart_1740439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740513 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 2, 2, 2]
def baseStart_1740513 : Nat := 118140960795 + 1740513 * 2 ^ 59
def prefixEnd_1740513 : Nat := 4983230072969 + 3 ^ 40 * 1740513 * 2
def baseEnd_1740513 : Nat := 893719754399053968583033

theorem tailTrace_1740513 : CollatzResearch.WordTrace tailWord_1740513 prefixEnd_1740513 893719754399053968583033 := by
  unfold tailWord_1740513
  simp only [CollatzResearch.WordTrace]
  refine ⟨63481724343426131799754193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42321149562284087866502795 63481724343426131799754193)
  ·
    refine ⟨47611293257569598849815645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63481724343426131799754193 47611293257569598849815645)
    ·
      refine ⟨17854234971588599568680867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47611293257569598849815645 17854234971588599568680867)
      ·
        refine ⟨26781352457382899353021301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17854234971588599568680867 26781352457382899353021301)
        ·
          refine ⟨2510751792879646814345747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26781352457382899353021301 2510751792879646814345747)
          ·
            refine ⟨3766127689319470221518621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510751792879646814345747 3766127689319470221518621)
            ·
              refine ⟨1412297883494801333069483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3766127689319470221518621 1412297883494801333069483)
              ·
                refine ⟨2118446825242201999604225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412297883494801333069483 2118446825242201999604225)
                ·
                  refine ⟨1588835118931651499703169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118446825242201999604225 1588835118931651499703169)
                  ·
                    refine ⟨1191626339198738624777377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588835118931651499703169 1191626339198738624777377)
                    ·
                      refine ⟨893719754399053968583033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191626339198738624777377 893719754399053968583033)
                      ·
                        rfl

theorem cell23_1740513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_1740513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740513 prefixEnd_1740513 := by exact prefixLift 1740513
  have htrace : WordTrace (prefixWord ++ tailWord_1740513) baseStart_1740513 baseEnd_1740513 := by
    simpa [prefixWord, tailWord_1740513, baseEnd_1740513] using wordTrace_append hprefix tailTrace_1740513
  have hstable : (prefixWord ++ tailWord_1740513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740513).length < 2 ^ (prefixWord ++ tailWord_1740513).sum := by decide
  have hdescent : baseEnd_1740513 < baseStart_1740513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740522 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_1740522 : Nat := 118140960795 + 1740522 * 2 ^ 59
def prefixEnd_1740522 : Nat := 4983230072969 + 3 ^ 40 * 1740522 * 2
def baseEnd_1740522 : Nat := 893724375724944433370491

theorem tailTrace_1740522 : CollatzResearch.WordTrace tailWord_1740522 prefixEnd_1740522 893724375724944433370491 := by
  unfold tailWord_1740522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15870513150098381584207955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42321368400262350891221213 15870513150098381584207955)
  ·
    refine ⟨23805769725147572376311933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15870513150098381584207955 23805769725147572376311933)
    ·
      refine ⟨8927163646930339641116975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23805769725147572376311933 8927163646930339641116975)
      ·
        refine ⟨13390745470395509461675463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8927163646930339641116975 13390745470395509461675463)
        ·
          refine ⟨20086118205593264192513195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13390745470395509461675463 20086118205593264192513195)
          ·
            refine ⟨30129177308389896288769793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20086118205593264192513195 30129177308389896288769793)
            ·
              refine ⟨22596882981292422216577345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30129177308389896288769793 22596882981292422216577345)
              ·
                refine ⟨16947662235969316662433009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22596882981292422216577345 16947662235969316662433009)
                ·
                  refine ⟨12710746676976987496824757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16947662235969316662433009 12710746676976987496824757)
                  ·
                    refine ⟨1191632500966592577827321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12710746676976987496824757 1191632500966592577827321)
                    ·
                      refine ⟨893724375724944433370491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191632500966592577827321 893724375724944433370491)
                      ·
                        rfl

theorem cell23_1740522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_1740522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740522 prefixEnd_1740522 := by exact prefixLift 1740522
  have htrace : WordTrace (prefixWord ++ tailWord_1740522) baseStart_1740522 baseEnd_1740522 := by
    simpa [prefixWord, tailWord_1740522, baseEnd_1740522] using wordTrace_append hprefix tailTrace_1740522
  have hstable : (prefixWord ++ tailWord_1740522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740522).length < 2 ^ (prefixWord ++ tailWord_1740522).sum := by decide
  have hdescent : baseEnd_1740522 < baseStart_1740522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740535 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_1740535 : Nat := 118140960795 + 1740535 * 2 ^ 59
def prefixEnd_1740535 : Nat := 4983230072969 + 3 ^ 40 * 1740535 * 2
def baseEnd_1740535 : Nat := 893731050973452882507931

theorem tailTrace_1740535 : CollatzResearch.WordTrace tailWord_1740535 prefixEnd_1740535 893731050973452882507931 := by
  unfold tailWord_1740535
  simp only [CollatzResearch.WordTrace]
  refine ⟨63482526749346429557055059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42321684499564286371370039 63482526749346429557055059)
  ·
    refine ⟨95223790124019644335582589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63482526749346429557055059 95223790124019644335582589)
    ·
      refine ⟨35708921296507366625843471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95223790124019644335582589 35708921296507366625843471)
      ·
        refine ⟨53563381944761049938765207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35708921296507366625843471 53563381944761049938765207)
        ·
          refine ⟨80345072917141574908147811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53563381944761049938765207 80345072917141574908147811)
          ·
            refine ⟨120517609375712362362221717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80345072917141574908147811 120517609375712362362221717)
            ·
              refine ⟨5649262939486516985729143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120517609375712362362221717 5649262939486516985729143)
              ·
                refine ⟨8473894409229775478593715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5649262939486516985729143 8473894409229775478593715)
                ·
                  refine ⟨12710841613844663217890573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8473894409229775478593715 12710841613844663217890573)
                  ·
                    refine ⟨4766565605191748706708965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12710841613844663217890573 4766565605191748706708965)
                    ·
                      refine ⟨893731050973452882507931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4766565605191748706708965 893731050973452882507931)
                      ·
                        rfl

theorem cell23_1740535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_1740535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740535 prefixEnd_1740535 := by exact prefixLift 1740535
  have htrace : WordTrace (prefixWord ++ tailWord_1740535) baseStart_1740535 baseEnd_1740535 := by
    simpa [prefixWord, tailWord_1740535, baseEnd_1740535] using wordTrace_append hprefix tailTrace_1740535
  have hstable : (prefixWord ++ tailWord_1740535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740535).length < 2 ^ (prefixWord ++ tailWord_1740535).sum := by decide
  have hdescent : baseEnd_1740535 < baseStart_1740535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740552 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1740552 : Nat := 118140960795 + 1740552 * 2 ^ 59
def prefixEnd_1740552 : Nat := 4983230072969 + 3 ^ 40 * 1740552 * 2
def baseEnd_1740552 : Nat := 893739780144579315995353

theorem tailTrace_1740552 : CollatzResearch.WordTrace tailWord_1740552 prefixEnd_1740552 893739780144579315995353 := by
  unfold tailWord_1740552
  simp only [CollatzResearch.WordTrace]
  refine ⟨31741573395142420730211955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42322097860189894306949273 31741573395142420730211955)
  ·
    refine ⟨47612360092713631095317933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31741573395142420730211955 47612360092713631095317933)
    ·
      refine ⟨17854635034767611660744225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47612360092713631095317933 17854635034767611660744225)
      ·
        refine ⟨13390976276075708745558169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17854635034767611660744225 13390976276075708745558169)
        ·
          refine ⟨10043232207056781559168627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13390976276075708745558169 10043232207056781559168627)
          ·
            refine ⟨15064848310585172338752941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10043232207056781559168627 15064848310585172338752941)
            ·
              refine ⟨5649318116469439627032353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15064848310585172338752941 5649318116469439627032353)
              ·
                refine ⟨4236988587352079720274265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5649318116469439627032353 4236988587352079720274265)
                ·
                  refine ⟨3177741440514059790205699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236988587352079720274265 3177741440514059790205699)
                  ·
                    refine ⟨4766612160771089685308549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3177741440514059790205699 4766612160771089685308549)
                    ·
                      refine ⟨893739780144579315995353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4766612160771089685308549 893739780144579315995353)
                      ·
                        rfl

theorem cell23_1740552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1740552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740552 prefixEnd_1740552 := by exact prefixLift 1740552
  have htrace : WordTrace (prefixWord ++ tailWord_1740552) baseStart_1740552 baseEnd_1740552 := by
    simpa [prefixWord, tailWord_1740552, baseEnd_1740552] using wordTrace_append hprefix tailTrace_1740552
  have hstable : (prefixWord ++ tailWord_1740552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740552).length < 2 ^ (prefixWord ++ tailWord_1740552).sum := by decide
  have hdescent : baseEnd_1740552 < baseStart_1740552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740564 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1740564 : Nat := 118140960795 + 1740564 * 2 ^ 59
def prefixEnd_1740564 : Nat := 4983230072969 + 3 ^ 40 * 1740564 * 2
def baseEnd_1740564 : Nat := 893745941912433269045299

theorem tailTrace_1740564 : CollatzResearch.WordTrace tailWord_1740564 prefixEnd_1740564 893745941912433269045299 := by
  unfold tailWord_1740564
  simp only [CollatzResearch.WordTrace]
  refine ⟨31741792233120683754930373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42322389644160911673240497 31741792233120683754930373)
  ·
    refine ⟨5951586043710128204049445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31741792233120683754930373 5951586043710128204049445)
    ·
      refine ⟨1115922383195649038259271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5951586043710128204049445 1115922383195649038259271)
      ·
        refine ⟨1673883574793473557388907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115922383195649038259271 1673883574793473557388907)
        ·
          refine ⟨2510825362190210336083361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673883574793473557388907 2510825362190210336083361)
          ·
            refine ⟨1883119021642657752062521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2510825362190210336083361 1883119021642657752062521)
            ·
              refine ⟨1412339266231993314046891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883119021642657752062521 1412339266231993314046891)
              ·
                refine ⟨2118508899347989971070337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412339266231993314046891 2118508899347989971070337)
                ·
                  refine ⟨1588881674510992478302753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118508899347989971070337 1588881674510992478302753)
                  ·
                    refine ⟨1191661255883244358727065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588881674510992478302753 1191661255883244358727065)
                    ·
                      refine ⟨893745941912433269045299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191661255883244358727065 893745941912433269045299)
                      ·
                        rfl

theorem cell23_1740564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1740564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740564 prefixEnd_1740564 := by exact prefixLift 1740564
  have htrace : WordTrace (prefixWord ++ tailWord_1740564) baseStart_1740564 baseEnd_1740564 := by
    simpa [prefixWord, tailWord_1740564, baseEnd_1740564] using wordTrace_append hprefix tailTrace_1740564
  have hstable : (prefixWord ++ tailWord_1740564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740564).length < 2 ^ (prefixWord ++ tailWord_1740564).sum := by decide
  have hdescent : baseEnd_1740564 < baseStart_1740564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740572 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_1740572 : Nat := 118140960795 + 1740572 * 2 ^ 59
def prefixEnd_1740572 : Nat := 4983230072969 + 3 ^ 40 * 1740572 * 2
def baseEnd_1740572 : Nat := 893750049757669237745261

theorem tailTrace_1740572 : CollatzResearch.WordTrace tailWord_1740572 prefixEnd_1740572 893750049757669237745261 := by
  unfold tailWord_1740572
  simp only [CollatzResearch.WordTrace]
  refine ⟨31741938125106192438075985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42322584166808256584101313 31741938125106192438075985)
  ·
    refine ⟨23806453593829644328556989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31741938125106192438075985 23806453593829644328556989)
    ·
      refine ⟨8927420097686116623208871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23806453593829644328556989 8927420097686116623208871)
      ·
        refine ⟨13391130146529174934813307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8927420097686116623208871 13391130146529174934813307)
        ·
          refine ⟨20086695219793762402219961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13391130146529174934813307 20086695219793762402219961)
          ·
            refine ⟨15065021414845321801664971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20086695219793762402219961 15065021414845321801664971)
            ·
              refine ⟨22597532122267982702497457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15065021414845321801664971 22597532122267982702497457)
              ·
                refine ⟨16948149091700987026873093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22597532122267982702497457 16948149091700987026873093)
                ·
                  refine ⟨3177777954693935067538705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16948149091700987026873093 3177777954693935067538705)
                  ·
                    refine ⟨2383333466020451300654029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3177777954693935067538705 2383333466020451300654029)
                    ·
                      refine ⟨893750049757669237745261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2383333466020451300654029 893750049757669237745261)
                      ·
                        rfl

theorem cell23_1740572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_1740572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740572 prefixEnd_1740572 := by exact prefixLift 1740572
  have htrace : WordTrace (prefixWord ++ tailWord_1740572) baseStart_1740572 baseEnd_1740572 := by
    simpa [prefixWord, tailWord_1740572, baseEnd_1740572] using wordTrace_append hprefix tailTrace_1740572
  have hstable : (prefixWord ++ tailWord_1740572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740572).length < 2 ^ (prefixWord ++ tailWord_1740572).sum := by decide
  have hdescent : baseEnd_1740572 < baseStart_1740572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740652 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_1740652 : Nat := 118140960795 + 1740652 * 2 ^ 59
def prefixEnd_1740652 : Nat := 4983230072969 + 3 ^ 40 * 1740652 * 2
def baseEnd_1740652 : Nat := 297930376070009641581631

theorem tailTrace_1740652 : CollatzResearch.WordTrace tailWord_1740652 prefixEnd_1740652 297930376070009641581631 := by
  unfold tailWord_1740652
  simp only [CollatzResearch.WordTrace]
  refine ⟨31743397044961279269532105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42324529393281705692709473 31743397044961279269532105)
  ·
    refine ⟨23807547783720959452149079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31743397044961279269532105 23807547783720959452149079)
    ·
      refine ⟨35711321675581439178223619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23807547783720959452149079 35711321675581439178223619)
      ·
        refine ⟨53566982513372158767335429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35711321675581439178223619 53566982513372158767335429)
        ·
          refine ⟨10043809221257279768875393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53566982513372158767335429 10043809221257279768875393)
          ·
            refine ⟨7532856915942959826656545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10043809221257279768875393 7532856915942959826656545)
            ·
              refine ⟨5649642686957219869992409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7532856915942959826656545 5649642686957219869992409)
              ·
                refine ⟨4237232015217914902494307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5649642686957219869992409 4237232015217914902494307)
                ·
                  refine ⟨6355848022826872353741461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237232015217914902494307 6355848022826872353741461)
                  ·
                    refine ⟨297930376070009641581631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6355848022826872353741461 297930376070009641581631)
                    ·
                      rfl

theorem cell23_1740652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_1740652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740652 prefixEnd_1740652 := by exact prefixLift 1740652
  have htrace : WordTrace (prefixWord ++ tailWord_1740652) baseStart_1740652 baseEnd_1740652 := by
    simpa [prefixWord, tailWord_1740652, baseEnd_1740652] using wordTrace_append hprefix tailTrace_1740652
  have hstable : (prefixWord ++ tailWord_1740652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740652).length < 2 ^ (prefixWord ++ tailWord_1740652).sum := by decide
  have hdescent : baseEnd_1740652 < baseStart_1740652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740655 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_1740655 : Nat := 118140960795 + 1740655 * 2 ^ 59
def prefixEnd_1740655 : Nat := 4983230072969 + 3 ^ 40 * 1740655 * 2
def baseEnd_1740655 : Nat := 893792668651992413007379

theorem tailTrace_1740655 : CollatzResearch.WordTrace tailWord_1740655 prefixEnd_1740655 893792668651992413007379 := by
  unfold tailWord_1740655
  simp only [CollatzResearch.WordTrace]
  refine ⟨63486903508911690051423419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42324602339274460034282279 63486903508911690051423419)
  ·
    refine ⟨95230355263367535077135129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63486903508911690051423419 95230355263367535077135129)
    ·
      refine ⟨71422766447525651307851347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95230355263367535077135129 71422766447525651307851347)
      ·
        refine ⟨107134149671288476961777021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71422766447525651307851347 107134149671288476961777021)
        ·
          refine ⟨40175306126733178860666383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107134149671288476961777021 40175306126733178860666383)
          ·
            refine ⟨60262959190099768290999575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40175306126733178860666383 60262959190099768290999575)
            ·
              refine ⟨90394438785149652436499363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60262959190099768290999575 90394438785149652436499363)
              ·
                refine ⟨135591658177724478654749045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90394438785149652436499363 135591658177724478654749045)
                ·
                  refine ⟨12711717954161669873882723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135591658177724478654749045 12711717954161669873882723)
                  ·
                    refine ⟨19067576931242504810824085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12711717954161669873882723 19067576931242504810824085)
                    ·
                      refine ⟨893792668651992413007379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19067576931242504810824085 893792668651992413007379)
                      ·
                        rfl

theorem cell23_1740655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_1740655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740655 prefixEnd_1740655 := by exact prefixLift 1740655
  have htrace : WordTrace (prefixWord ++ tailWord_1740655) baseStart_1740655 baseEnd_1740655 := by
    simpa [prefixWord, tailWord_1740655, baseEnd_1740655] using wordTrace_append hprefix tailTrace_1740655
  have hstable : (prefixWord ++ tailWord_1740655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740655).length < 2 ^ (prefixWord ++ tailWord_1740655).sum := by decide
  have hdescent : baseEnd_1740655 < baseStart_1740655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740659 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 7, 2, 2]
def baseStart_1740659 : Nat := 118140960795 + 1740659 * 2 ^ 59
def prefixEnd_1740659 : Nat := 4983230072969 + 3 ^ 40 * 1740659 * 2
def baseEnd_1740659 : Nat := 893794722574610397357361

theorem tailTrace_1740659 : CollatzResearch.WordTrace tailWord_1740659 prefixEnd_1740659 893794722574610397357361 := by
  unfold tailWord_1740659
  simp only [CollatzResearch.WordTrace]
  refine ⟨63487049400897198734569031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42324699600598132489712687 63487049400897198734569031)
  ·
    refine ⟨95230574101345798101853547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63487049400897198734569031 95230574101345798101853547)
    ·
      refine ⟨142845861152018697152780321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95230574101345798101853547 142845861152018697152780321)
      ·
        refine ⟨107134395864014022864585241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142845861152018697152780321 107134395864014022864585241)
        ·
          refine ⟨80350796898010517148438931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107134395864014022864585241 80350796898010517148438931)
          ·
            refine ⟨120526195347015775722658397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80350796898010517148438931 120526195347015775722658397)
            ·
              refine ⟨45197323255130915895996899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120526195347015775722658397 45197323255130915895996899)
              ·
                refine ⟨67795984882696373843995349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45197323255130915895996899 67795984882696373843995349)
                ·
                  refine ⟨1588968395688196261968641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 67795984882696373843995349 1588968395688196261968641)
                  ·
                    refine ⟨1191726296766147196476481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588968395688196261968641 1191726296766147196476481)
                    ·
                      refine ⟨893794722574610397357361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191726296766147196476481 893794722574610397357361)
                      ·
                        rfl

theorem cell23_1740659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 2, 2].length) (baseStart_1740659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740659 prefixEnd_1740659 := by exact prefixLift 1740659
  have htrace : WordTrace (prefixWord ++ tailWord_1740659) baseStart_1740659 baseEnd_1740659 := by
    simpa [prefixWord, tailWord_1740659, baseEnd_1740659] using wordTrace_append hprefix tailTrace_1740659
  have hstable : (prefixWord ++ tailWord_1740659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740659).length < 2 ^ (prefixWord ++ tailWord_1740659).sum := by decide
  have hdescent : baseEnd_1740659 < baseStart_1740659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740665 : List Nat := [1, 2, 1, 3, 2, 2, 12]
def baseStart_1740665 : Nat := 118140960795 + 1740665 * 2 ^ 59
def prefixEnd_1740665 : Nat := 4983230072969 + 3 ^ 40 * 1740665 * 2
def baseEnd_1740665 : Nat := 11034540783438733010893

theorem tailTrace_1740665 : CollatzResearch.WordTrace tailWord_1740665 prefixEnd_1740665 11034540783438733010893 := by
  unfold tailWord_1740665
  simp only [CollatzResearch.WordTrace]
  refine ⟨63487268238875461759287449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42324845492583641172858299 63487268238875461759287449)
  ·
    refine ⟨47615451179156596319465587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63487268238875461759287449 47615451179156596319465587)
    ·
      refine ⟨71423176768734894479198381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47615451179156596319465587 71423176768734894479198381)
      ·
        refine ⟨26783691288275585429699393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71423176768734894479198381 26783691288275585429699393)
        ·
          refine ⟨20087768466206689072274545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26783691288275585429699393 20087768466206689072274545)
          ·
            refine ⟨15065826349655016804205909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20087768466206689072274545 15065826349655016804205909)
            ·
              refine ⟨11034540783438733010893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 15065826349655016804205909 11034540783438733010893)
              ·
                rfl

theorem cell23_1740665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 12].length) (baseStart_1740665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740665 prefixEnd_1740665 := by exact prefixLift 1740665
  have htrace : WordTrace (prefixWord ++ tailWord_1740665) baseStart_1740665 baseEnd_1740665 := by
    simpa [prefixWord, tailWord_1740665, baseEnd_1740665] using wordTrace_append hprefix tailTrace_1740665
  have hstable : (prefixWord ++ tailWord_1740665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740665).length < 2 ^ (prefixWord ++ tailWord_1740665).sum := by decide
  have hdescent : baseEnd_1740665 < baseStart_1740665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740670 : List Nat := [4, 2, 3, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1740670 : Nat := 118140960795 + 1740670 * 2 ^ 59
def prefixEnd_1740670 : Nat := 4983230072969 + 3 ^ 40 * 1740670 * 2
def baseEnd_1740670 : Nat := 893800370861809854319811

theorem tailTrace_1740670 : CollatzResearch.WordTrace tailWord_1740670 prefixEnd_1740670 893800370861809854319811 := by
  unfold tailWord_1740670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935931325482168451652433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42324967069238231742146309 7935931325482168451652433)
  ·
    refine ⟨5951948494111626338739325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7935931325482168451652433 5951948494111626338739325)
    ·
      refine ⟨2231980685291859877027247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5951948494111626338739325 2231980685291859877027247)
      ·
        refine ⟨3347971027937789815540871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2231980685291859877027247 3347971027937789815540871)
        ·
          refine ⟨5021956541906684723311307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3347971027937789815540871 5021956541906684723311307)
          ·
            refine ⟨7532934812860027084966961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5021956541906684723311307 7532934812860027084966961)
            ·
              refine ⟨5649701109645020313725221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7532934812860027084966961 5649701109645020313725221)
              ·
                refine ⟨1059318958058441308823479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5649701109645020313725221 1059318958058441308823479)
                ·
                  refine ⟨1588978437087661963235219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1059318958058441308823479 1588978437087661963235219)
                  ·
                    refine ⟨2383467655631492944852829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1588978437087661963235219 2383467655631492944852829)
                    ·
                      refine ⟨893800370861809854319811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2383467655631492944852829 893800370861809854319811)
                      ·
                        rfl

theorem cell23_1740670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1740670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740670 prefixEnd_1740670 := by exact prefixLift 1740670
  have htrace : WordTrace (prefixWord ++ tailWord_1740670) baseStart_1740670 baseEnd_1740670 := by
    simpa [prefixWord, tailWord_1740670, baseEnd_1740670] using wordTrace_append hprefix tailTrace_1740670
  have hstable : (prefixWord ++ tailWord_1740670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740670).length < 2 ^ (prefixWord ++ tailWord_1740670).sum := by decide
  have hdescent : baseEnd_1740670 < baseStart_1740670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740676 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_1740676 : Nat := 118140960795 + 1740676 * 2 ^ 59
def prefixEnd_1740676 : Nat := 4983230072969 + 3 ^ 40 * 1740676 * 2
def baseEnd_1740676 : Nat := 893803451745736830844783

theorem tailTrace_1740676 : CollatzResearch.WordTrace tailWord_1740676 prefixEnd_1740676 893803451745736830844783 := by
  unfold tailWord_1740676
  simp only [CollatzResearch.WordTrace]
  refine ⟨31743834720917805318968941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42325112961223740425291921 31743834720917805318968941)
  ·
    refine ⟨11903938020344176994613353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31743834720917805318968941 11903938020344176994613353)
    ·
      refine ⟨8927953515258132745960015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11903938020344176994613353 8927953515258132745960015)
      ·
        refine ⟨13391930272887199118940023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8927953515258132745960015 13391930272887199118940023)
        ·
          refine ⟨20087895409330798678410035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13391930272887199118940023 20087895409330798678410035)
          ·
            refine ⟨30131843113996198017615053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20087895409330798678410035 30131843113996198017615053)
            ·
              refine ⟨11299441167748574256605645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30131843113996198017615053 11299441167748574256605645)
              ·
                refine ⟨4237290437905715346227117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11299441167748574256605645 4237290437905715346227117)
                ·
                  refine ⟨1588983914214643254835169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4237290437905715346227117 1588983914214643254835169)
                  ·
                    refine ⟨1191737935660982441126377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1588983914214643254835169 1191737935660982441126377)
                    ·
                      refine ⟨893803451745736830844783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191737935660982441126377 893803451745736830844783)
                      ·
                        rfl

theorem cell23_1740676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_1740676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740676 prefixEnd_1740676 := by exact prefixLift 1740676
  have htrace : WordTrace (prefixWord ++ tailWord_1740676) baseStart_1740676 baseEnd_1740676 := by
    simpa [prefixWord, tailWord_1740676, baseEnd_1740676] using wordTrace_append hprefix tailTrace_1740676
  have hstable : (prefixWord ++ tailWord_1740676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740676).length < 2 ^ (prefixWord ++ tailWord_1740676).sum := by decide
  have hdescent : baseEnd_1740676 < baseStart_1740676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740679 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_1740679 : Nat := 118140960795 + 1740679 * 2 ^ 59
def prefixEnd_1740679 : Nat := 4983230072969 + 3 ^ 40 * 1740679 * 2
def baseEnd_1740679 : Nat := 893804992187700319107269

theorem tailTrace_1740679 : CollatzResearch.WordTrace tailWord_1740679 prefixEnd_1740679 893804992187700319107269 := by
  unfold tailWord_1740679
  simp only [CollatzResearch.WordTrace]
  refine ⟨63487778860824742150297091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42325185907216494766864727 63487778860824742150297091)
  ·
    refine ⟨95231668291237113225445637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63487778860824742150297091 95231668291237113225445637)
    ·
      refine ⟨17855937804606958729771057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95231668291237113225445637 17855937804606958729771057)
      ·
        refine ⟨13391953353455219047328293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17855937804606958729771057 13391953353455219047328293)
        ·
          refine ⟨2510991253772853571374055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13391953353455219047328293 2510991253772853571374055)
          ·
            refine ⟨3766486880659280357061083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510991253772853571374055 3766486880659280357061083)
            ·
              refine ⟨5649730320988920535591625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766486880659280357061083 5649730320988920535591625)
              ·
                refine ⟨4237297740741690401693719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5649730320988920535591625 4237297740741690401693719)
                ·
                  refine ⟨6355946611112535602540579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237297740741690401693719 6355946611112535602540579)
                  ·
                    refine ⟨9533919916668803403810869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6355946611112535602540579 9533919916668803403810869)
                    ·
                      refine ⟨893804992187700319107269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9533919916668803403810869 893804992187700319107269)
                      ·
                        rfl

theorem cell23_1740679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_1740679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740679 prefixEnd_1740679 := by exact prefixLift 1740679
  have htrace : WordTrace (prefixWord ++ tailWord_1740679) baseStart_1740679 baseEnd_1740679 := by
    simpa [prefixWord, tailWord_1740679, baseEnd_1740679] using wordTrace_append hprefix tailTrace_1740679
  have hstable : (prefixWord ++ tailWord_1740679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740679).length < 2 ^ (prefixWord ++ tailWord_1740679).sum := by decide
  have hdescent : baseEnd_1740679 < baseStart_1740679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740752 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_1740752 : Nat := 118140960795 + 1740752 * 2 ^ 59
def prefixEnd_1740752 : Nat := 4983230072969 + 3 ^ 40 * 1740752 * 2
def baseEnd_1740752 : Nat := 893842476275478533494433

theorem tailTrace_1740752 : CollatzResearch.WordTrace tailWord_1740752 prefixEnd_1740752 893842476275478533494433 := by
  unfold tailWord_1740752
  simp only [CollatzResearch.WordTrace]
  refine ⟨31745220694780137808852255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42326960926373517078469673 31745220694780137808852255)
  ·
    refine ⟨47617831042170206713278383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31745220694780137808852255 47617831042170206713278383)
    ·
      refine ⟨71426746563255310069917575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47617831042170206713278383 71426746563255310069917575)
      ·
        refine ⟨107140119844882965104876363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71426746563255310069917575 107140119844882965104876363)
        ·
          refine ⟨160710179767324447657314545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107140119844882965104876363 160710179767324447657314545)
          ·
            refine ⟨120532634825493335742985909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160710179767324447657314545 120532634825493335742985909)
            ·
              refine ⟨11299934514890000225904929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120532634825493335742985909 11299934514890000225904929)
              ·
                refine ⟨8474950886167500169428697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11299934514890000225904929 8474950886167500169428697)
                ·
                  refine ⟨6356213164625625127071523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8474950886167500169428697 6356213164625625127071523)
                  ·
                    refine ⟨9534319746938437690607285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6356213164625625127071523 9534319746938437690607285)
                    ·
                      refine ⟨893842476275478533494433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9534319746938437690607285 893842476275478533494433)
                      ·
                        rfl

theorem cell23_1740752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_1740752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740752 prefixEnd_1740752 := by exact prefixLift 1740752
  have htrace : WordTrace (prefixWord ++ tailWord_1740752) baseStart_1740752 baseEnd_1740752 := by
    simpa [prefixWord, tailWord_1740752, baseEnd_1740752] using wordTrace_append hprefix tailTrace_1740752
  have hstable : (prefixWord ++ tailWord_1740752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740752).length < 2 ^ (prefixWord ++ tailWord_1740752).sum := by decide
  have hdescent : baseEnd_1740752 < baseStart_1740752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740783 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 2, 2, 2]
def baseStart_1740783 : Nat := 118140960795 + 1740783 * 2 ^ 59
def prefixEnd_1740783 : Nat := 4983230072969 + 3 ^ 40 * 1740783 * 2
def baseEnd_1740783 : Nat := 893858394175767912206791

theorem tailTrace_1740783 : CollatzResearch.WordTrace tailWord_1740783 prefixEnd_1740783 893858394175767912206791 := by
  unfold tailWord_1740783
  simp only [CollatzResearch.WordTrace]
  refine ⟨63491572052447967912083003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42327714701631978608055335 63491572052447967912083003)
  ·
    refine ⟨95237358078671951868124505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63491572052447967912083003 95237358078671951868124505)
    ·
      refine ⟨71428018559003963901093379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95237358078671951868124505 71428018559003963901093379)
      ·
        refine ⟨107142027838505945851640069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71428018559003963901093379 107142027838505945851640069)
        ·
          refine ⟨20089130219719864847182513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107142027838505945851640069 20089130219719864847182513)
          ·
            refine ⟨15066847664789898635386885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20089130219719864847182513 15066847664789898635386885)
            ·
              refine ⟨2825033937148105994135041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15066847664789898635386885 2825033937148105994135041)
              ·
                refine ⟨2118775452861079495601281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2825033937148105994135041 2118775452861079495601281)
                ·
                  refine ⟨1589081589645809621700961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118775452861079495601281 1589081589645809621700961)
                  ·
                    refine ⟨1191811192234357216275721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1589081589645809621700961 1191811192234357216275721)
                    ·
                      refine ⟨893858394175767912206791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191811192234357216275721 893858394175767912206791)
                      ·
                        rfl

theorem cell23_1740783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 2, 2].length) (baseStart_1740783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740783 prefixEnd_1740783 := by exact prefixLift 1740783
  have htrace : WordTrace (prefixWord ++ tailWord_1740783) baseStart_1740783 baseEnd_1740783 := by
    simpa [prefixWord, tailWord_1740783, baseEnd_1740783] using wordTrace_append hprefix tailTrace_1740783
  have hstable : (prefixWord ++ tailWord_1740783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740783).length < 2 ^ (prefixWord ++ tailWord_1740783).sum := by decide
  have hdescent : baseEnd_1740783 < baseStart_1740783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740819 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 2, 5]
def baseStart_1740819 : Nat := 118140960795 + 1740819 * 2 ^ 59
def prefixEnd_1740819 : Nat := 4983230072969 + 3 ^ 40 * 1740819 * 2
def baseEnd_1740819 : Nat := 297958959826443257118875

theorem tailTrace_1740819 : CollatzResearch.WordTrace tailWord_1740819 prefixEnd_1740819 297958959826443257118875 := by
  unfold tailWord_1740819
  simp only [CollatzResearch.WordTrace]
  refine ⟨63492885080317546060393511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42328590053545030706929007 63492885080317546060393511)
  ·
    refine ⟨95239327620476319090590267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63492885080317546060393511 95239327620476319090590267)
    ·
      refine ⟨142858991430714478635885401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95239327620476319090590267 142858991430714478635885401)
      ·
        refine ⟨107144243573035858976914051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142858991430714478635885401 107144243573035858976914051)
        ·
          refine ⟨160716365359553788465371077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107144243573035858976914051 160716365359553788465371077)
          ·
            refine ⟨30134318504916335337257077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160716365359553788465371077 30134318504916335337257077)
            ·
              refine ⟨2825092359835906437867851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30134318504916335337257077 2825092359835906437867851)
              ·
                refine ⟨4237638539753859656801777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825092359835906437867851 4237638539753859656801777)
                ·
                  refine ⟨3178228904815394742601333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4237638539753859656801777 3178228904815394742601333)
                  ·
                    refine ⟨297958959826443257118875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3178228904815394742601333 297958959826443257118875)
                    ·
                      rfl

theorem cell23_1740819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 5].length) (baseStart_1740819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740819 prefixEnd_1740819 := by exact prefixLift 1740819
  have htrace : WordTrace (prefixWord ++ tailWord_1740819) baseStart_1740819 baseEnd_1740819 := by
    simpa [prefixWord, tailWord_1740819, baseEnd_1740819] using wordTrace_append hprefix tailTrace_1740819
  have hstable : (prefixWord ++ tailWord_1740819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740819).length < 2 ^ (prefixWord ++ tailWord_1740819).sum := by decide
  have hdescent : baseEnd_1740819 < baseStart_1740819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740823 : List Nat := [1, 1, 3, 5, 2, 1, 2, 3, 5]
def baseStart_1740823 : Nat := 118140960795 + 1740823 * 2 ^ 59
def prefixEnd_1740823 : Nat := 4983230072969 + 3 ^ 40 * 1740823 * 2
def baseEnd_1740823 : Nat := 99319881489105306189623

theorem tailTrace_1740823 : CollatzResearch.WordTrace tailWord_1740823 prefixEnd_1740823 99319881489105306189623 := by
  unfold tailWord_1740823
  simp only [CollatzResearch.WordTrace]
  refine ⟨63493030972303054743539123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42328687314868703162359415 63493030972303054743539123)
  ·
    refine ⟨95239546458454582115308685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63493030972303054743539123 95239546458454582115308685)
    ·
      refine ⟨35714829921920468293240757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95239546458454582115308685 35714829921920468293240757)
      ·
        refine ⟨3348265305180043902491321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35714829921920468293240757 3348265305180043902491321)
        ·
          refine ⟨2511198978885032926868491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3348265305180043902491321 2511198978885032926868491)
          ·
            refine ⟨3766798468327549390302737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511198978885032926868491 3766798468327549390302737)
            ·
              refine ⟨2825098851245662042727053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3766798468327549390302737 2825098851245662042727053)
              ·
                refine ⟨1059412069217123266022645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2825098851245662042727053 1059412069217123266022645)
                ·
                  refine ⟨99319881489105306189623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1059412069217123266022645 99319881489105306189623)
                  ·
                    rfl

theorem cell23_1740823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 5].length) (baseStart_1740823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740823 prefixEnd_1740823 := by exact prefixLift 1740823
  have htrace : WordTrace (prefixWord ++ tailWord_1740823) baseStart_1740823 baseEnd_1740823 := by
    simpa [prefixWord, tailWord_1740823, baseEnd_1740823] using wordTrace_append hprefix tailTrace_1740823
  have hstable : (prefixWord ++ tailWord_1740823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740823).length < 2 ^ (prefixWord ++ tailWord_1740823).sum := by decide
  have hdescent : baseEnd_1740823 < baseStart_1740823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740859 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 3]
def baseStart_1740859 : Nat := 118140960795 + 1740859 * 2 ^ 59
def prefixEnd_1740859 : Nat := 4983230072969 + 3 ^ 40 * 1740859 * 2
def baseEnd_1740859 : Nat := 893897418705509614856441

theorem tailTrace_1740859 : CollatzResearch.WordTrace tailWord_1740859 prefixEnd_1740859 893897418705509614856441 := by
  unfold tailWord_1740859
  simp only [CollatzResearch.WordTrace]
  refine ⟨63494344000172632891849631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42329562666781755261233087 63494344000172632891849631)
  ·
    refine ⟨95241516000258949337774447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63494344000172632891849631 95241516000258949337774447)
    ·
      refine ⟨142862274000388424006661671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95241516000258949337774447 142862274000388424006661671)
      ·
        refine ⟨214293411000582636009992507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142862274000388424006661671 214293411000582636009992507)
        ·
          refine ⟨321440116500873954014988761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214293411000582636009992507 321440116500873954014988761)
          ·
            refine ⟨241080087375655465511241571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321440116500873954014988761 241080087375655465511241571)
            ·
              refine ⟨361620131063483198266862357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241080087375655465511241571 361620131063483198266862357)
              ·
                refine ⟨16950943643600774918759173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 361620131063483198266862357 16950943643600774918759173)
                ·
                  refine ⟨3178301933175145297267345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16950943643600774918759173 3178301933175145297267345)
                  ·
                    refine ⟨2383726449881358972950509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3178301933175145297267345 2383726449881358972950509)
                    ·
                      refine ⟨893897418705509614856441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2383726449881358972950509 893897418705509614856441)
                      ·
                        rfl

theorem cell23_1740859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 3].length) (baseStart_1740859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740859 prefixEnd_1740859 := by exact prefixLift 1740859
  have htrace : WordTrace (prefixWord ++ tailWord_1740859) baseStart_1740859 baseEnd_1740859 := by
    simpa [prefixWord, tailWord_1740859, baseEnd_1740859] using wordTrace_append hprefix tailTrace_1740859
  have hstable : (prefixWord ++ tailWord_1740859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740859).length < 2 ^ (prefixWord ++ tailWord_1740859).sum := by decide
  have hdescent : baseEnd_1740859 < baseStart_1740859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740893 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1740893 : Nat := 118140960795 + 1740893 * 2 ^ 59
def prefixEnd_1740893 : Nat := 4983230072969 + 3 ^ 40 * 1740893 * 2
def baseEnd_1740893 : Nat := 893914877047762481831285

theorem tailTrace_1740893 : CollatzResearch.WordTrace tailWord_1740893 prefixEnd_1740893 893914877047762481831285 := by
  unfold tailWord_1740893
  simp only [CollatzResearch.WordTrace]
  refine ⟨63495584082049456698587333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42330389388032971132391555 63495584082049456698587333)
  ·
    refine ⟨11905422015384273130985125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63495584082049456698587333 11905422015384273130985125)
    ·
      refine ⟨2232266627884551212059711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11905422015384273130985125 2232266627884551212059711)
      ·
        refine ⟨3348399941826826818089567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2232266627884551212059711 3348399941826826818089567)
        ·
          refine ⟨5022599912740240227134351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348399941826826818089567 5022599912740240227134351)
          ·
            refine ⟨7533899869110360340701527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022599912740240227134351 7533899869110360340701527)
            ·
              refine ⟨11300849803665540511052291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533899869110360340701527 11300849803665540511052291)
              ·
                refine ⟨16951274705498310766578437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11300849803665540511052291 16951274705498310766578437)
                ·
                  refine ⟨3178364007280933268733457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16951274705498310766578437 3178364007280933268733457)
                  ·
                    refine ⟨2383773005460699951550093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3178364007280933268733457 2383773005460699951550093)
                    ·
                      refine ⟨893914877047762481831285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2383773005460699951550093 893914877047762481831285)
                      ·
                        rfl

theorem cell23_1740893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1740893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740893 prefixEnd_1740893 := by exact prefixLift 1740893
  have htrace : WordTrace (prefixWord ++ tailWord_1740893) baseStart_1740893 baseEnd_1740893 := by
    simpa [prefixWord, tailWord_1740893, baseEnd_1740893] using wordTrace_append hprefix tailTrace_1740893
  have hstable : (prefixWord ++ tailWord_1740893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740893).length < 2 ^ (prefixWord ++ tailWord_1740893).sum := by decide
  have hdescent : baseEnd_1740893 < baseStart_1740893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740933 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 2, 3, 2]
def baseStart_1740933 : Nat := 118140960795 + 1740933 * 2 ^ 59
def prefixEnd_1740933 : Nat := 4983230072969 + 3 ^ 40 * 1740933 * 2
def baseEnd_1740933 : Nat := 893935416273942325331101

theorem tailTrace_1740933 : CollatzResearch.WordTrace tailWord_1740933 prefixEnd_1740933 893935416273942325331101 := by
  unfold tailWord_1740933
  simp only [CollatzResearch.WordTrace]
  refine ⟨63497043001904543530043453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42331362001269695686695635 63497043001904543530043453)
  ·
    refine ⟨23811391125714203823766295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63497043001904543530043453 23811391125714203823766295)
    ·
      refine ⟨35717086688571305735649443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23811391125714203823766295 35717086688571305735649443)
      ·
        refine ⟨53575630032856958603474165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35717086688571305735649443 53575630032856958603474165)
        ·
          refine ⟨5022715315580339869075703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53575630032856958603474165 5022715315580339869075703)
          ·
            refine ⟨7534072973370509803613555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022715315580339869075703 7534072973370509803613555)
            ·
              refine ⟨11301109460055764705420333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7534072973370509803613555 11301109460055764705420333)
              ·
                refine ⟨4237916047520911764532625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11301109460055764705420333 4237916047520911764532625)
                ·
                  refine ⟨3178437035640683823399469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4237916047520911764532625 3178437035640683823399469)
                  ·
                    refine ⟨1191913888365256433774801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3178437035640683823399469 1191913888365256433774801)
                    ·
                      refine ⟨893935416273942325331101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191913888365256433774801 893935416273942325331101)
                      ·
                        rfl

theorem cell23_1740933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_1740933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740933 prefixEnd_1740933 := by exact prefixLift 1740933
  have htrace : WordTrace (prefixWord ++ tailWord_1740933) baseStart_1740933 baseEnd_1740933 := by
    simpa [prefixWord, tailWord_1740933, baseEnd_1740933] using wordTrace_append hprefix tailTrace_1740933
  have hstable : (prefixWord ++ tailWord_1740933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740933).length < 2 ^ (prefixWord ++ tailWord_1740933).sum := by decide
  have hdescent : baseEnd_1740933 < baseStart_1740933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740957 : List Nat := [1, 4, 2, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_1740957 : Nat := 118140960795 + 1740957 * 2 ^ 59
def prefixEnd_1740957 : Nat := 4983230072969 + 3 ^ 40 * 1740957 * 2
def baseEnd_1740957 : Nat := 893947739809650231430991

theorem tailTrace_1740957 : CollatzResearch.WordTrace tailWord_1740957 prefixEnd_1740957 893947739809650231430991 := by
  unfold tailWord_1740957
  simp only [CollatzResearch.WordTrace]
  refine ⟨63497918353817595628917125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42331945569211730419278083 63497918353817595628917125)
  ·
    refine ⟨11905859691340799180421961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63497918353817595628917125 11905859691340799180421961)
    ·
      refine ⟨8929394768505599385316471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11905859691340799180421961 8929394768505599385316471)
      ·
        refine ⟨13394092152758399077974707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8929394768505599385316471 13394092152758399077974707)
        ·
          refine ⟨20091138229137598616962061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13394092152758399077974707 20091138229137598616962061)
          ·
            refine ⟨7534176835926599481360773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20091138229137598616962061 7534176835926599481360773)
            ·
              refine ⟨1412658156736237402755145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7534176835926599481360773 1412658156736237402755145)
              ·
                refine ⟨1059493617552178052066359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1412658156736237402755145 1059493617552178052066359)
                ·
                  refine ⟨1589240426328267078099539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1059493617552178052066359 1589240426328267078099539)
                  ·
                    refine ⟨2383860639492400617149309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1589240426328267078099539 2383860639492400617149309)
                    ·
                      refine ⟨893947739809650231430991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2383860639492400617149309 893947739809650231430991)
                      ·
                        rfl

theorem cell23_1740957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_1740957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740957 prefixEnd_1740957 := by exact prefixLift 1740957
  have htrace : WordTrace (prefixWord ++ tailWord_1740957) baseStart_1740957 baseEnd_1740957 := by
    simpa [prefixWord, tailWord_1740957, baseEnd_1740957] using wordTrace_append hprefix tailTrace_1740957
  have hstable : (prefixWord ++ tailWord_1740957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740957).length < 2 ^ (prefixWord ++ tailWord_1740957).sum := by decide
  have hdescent : baseEnd_1740957 < baseStart_1740957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740973 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1740973 : Nat := 118140960795 + 1740973 * 2 ^ 59
def prefixEnd_1740973 : Nat := 4983230072969 + 3 ^ 40 * 1740973 * 2
def baseEnd_1740973 : Nat := 297985318500040722943639

theorem tailTrace_1740973 : CollatzResearch.WordTrace tailWord_1740973 prefixEnd_1740973 297985318500040722943639 := by
  unfold tailWord_1740973
  simp only [CollatzResearch.WordTrace]
  refine ⟨63498501921759630361499573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42332334614506420240999715 63498501921759630361499573)
  ·
    refine ⟨5952984555164965346390585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63498501921759630361499573 5952984555164965346390585)
    ·
      refine ⟨4464738416373724009792939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5952984555164965346390585 4464738416373724009792939)
      ·
        refine ⟨6697107624560586014689409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4464738416373724009792939 6697107624560586014689409)
        ·
          refine ⟨5022830718420439511017057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6697107624560586014689409 5022830718420439511017057)
          ·
            refine ⟨3767123038815329633262793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5022830718420439511017057 3767123038815329633262793)
            ·
              refine ⟨2825342279111497224947095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3767123038815329633262793 2825342279111497224947095)
              ·
                refine ⟨4238013418667245837420643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825342279111497224947095 4238013418667245837420643)
                ·
                  refine ⟨6357020128000868756130965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238013418667245837420643 6357020128000868756130965)
                  ·
                    refine ⟨297985318500040722943639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6357020128000868756130965 297985318500040722943639)
                    ·
                      rfl

theorem cell23_1740973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1740973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740973 prefixEnd_1740973 := by exact prefixLift 1740973
  have htrace : WordTrace (prefixWord ++ tailWord_1740973) baseStart_1740973 baseEnd_1740973 := by
    simpa [prefixWord, tailWord_1740973, baseEnd_1740973] using wordTrace_append hprefix tailTrace_1740973
  have hstable : (prefixWord ++ tailWord_1740973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740973).length < 2 ^ (prefixWord ++ tailWord_1740973).sum := by decide
  have hdescent : baseEnd_1740973 < baseStart_1740973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740994 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1740994 : Nat := 118140960795 + 1740994 * 2 ^ 59
def prefixEnd_1740994 : Nat := 4983230072969 + 3 ^ 40 * 1740994 * 2
def baseEnd_1740994 : Nat := 297988912864622195556107

theorem tailTrace_1740994 : CollatzResearch.WordTrace tailWord_1740994 prefixEnd_1740994 297988912864622195556107 := by
  unfold tailWord_1740994
  simp only [CollatzResearch.WordTrace]
  refine ⟨15874816963670887737003509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42332845236455700632009357 15874816963670887737003509)
  ·
    refine ⟨1488264090344145725344079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15874816963670887737003509 1488264090344145725344079)
    ·
      refine ⟨2232396135516218588016119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488264090344145725344079 2232396135516218588016119)
      ·
        refine ⟨3348594203274327882024179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2232396135516218588016119 3348594203274327882024179)
        ·
          refine ⟨5022891304911491823036269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348594203274327882024179 5022891304911491823036269)
          ·
            refine ⟨1883584239341809433638601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5022891304911491823036269 1883584239341809433638601)
            ·
              refine ⟨1412688179506357075228951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883584239341809433638601 1412688179506357075228951)
              ·
                refine ⟨2119032269259535612843427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412688179506357075228951 2119032269259535612843427)
                ·
                  refine ⟨3178548403889303419265141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119032269259535612843427 3178548403889303419265141)
                  ·
                    refine ⟨297988912864622195556107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3178548403889303419265141 297988912864622195556107)
                    ·
                      rfl

theorem cell23_1740994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1740994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1740994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1740994 prefixEnd_1740994 := by exact prefixLift 1740994
  have htrace : WordTrace (prefixWord ++ tailWord_1740994) baseStart_1740994 baseEnd_1740994 := by
    simpa [prefixWord, tailWord_1740994, baseEnd_1740994] using wordTrace_append hprefix tailTrace_1740994
  have hstable : (prefixWord ++ tailWord_1740994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740994).length < 2 ^ (prefixWord ++ tailWord_1740994).sum := by decide
  have hdescent : baseEnd_1740994 < baseStart_1740994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741014 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1741014 : Nat := 118140960795 + 1741014 * 2 ^ 59
def prefixEnd_1741014 : Nat := 4983230072969 + 3 ^ 40 * 1741014 * 2
def baseEnd_1741014 : Nat := 893977008206956508418229

theorem tailTrace_1741014 : CollatzResearch.WordTrace tailWord_1741014 prefixEnd_1741014 893977008206956508418229 := by
  unfold tailWord_1741014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968749832163193397733881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42333331543074062909161397 3968749832163193397733881)
  ·
    refine ⟨2976562374122395048300411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3968749832163193397733881 2976562374122395048300411)
    ·
      refine ⟨4464843561183592572450617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2976562374122395048300411 4464843561183592572450617)
      ·
        refine ⟨3348632670887694429337963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4464843561183592572450617 3348632670887694429337963)
        ·
          refine ⟨5022949006331541644006945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348632670887694429337963 5022949006331541644006945)
          ·
            refine ⟨3767211754748656233005209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5022949006331541644006945 3767211754748656233005209)
            ·
              refine ⟨2825408816061492174753907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3767211754748656233005209 2825408816061492174753907)
              ·
                refine ⟨4238113224092238262130861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825408816061492174753907 4238113224092238262130861)
                ·
                  refine ⟨1589292459034589348299073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4238113224092238262130861 1589292459034589348299073)
                  ·
                    refine ⟨1191969344275942011224305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1589292459034589348299073 1191969344275942011224305)
                    ·
                      refine ⟨893977008206956508418229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191969344275942011224305 893977008206956508418229)
                      ·
                        rfl

theorem cell23_1741014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1741014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741014 prefixEnd_1741014 := by exact prefixLift 1741014
  have htrace : WordTrace (prefixWord ++ tailWord_1741014) baseStart_1741014 baseEnd_1741014 := by
    simpa [prefixWord, tailWord_1741014, baseEnd_1741014] using wordTrace_append hprefix tailTrace_1741014
  have hstable : (prefixWord ++ tailWord_1741014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741014).length < 2 ^ (prefixWord ++ tailWord_1741014).sum := by decide
  have hdescent : baseEnd_1741014 < baseStart_1741014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741027 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1741027 : Nat := 118140960795 + 1741027 * 2 ^ 59
def prefixEnd_1741027 : Nat := 4983230072969 + 3 ^ 40 * 1741027 * 2
def baseEnd_1741027 : Nat := 893983683455464957555669

theorem tailTrace_1741027 : CollatzResearch.WordTrace tailWord_1741027 prefixEnd_1741027 893983683455464957555669 := by
  unfold tailWord_1741027
  simp only [CollatzResearch.WordTrace]
  refine ⟨63500471463563997583965335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42333647642375998389310223 63500471463563997583965335)
  ·
    refine ⟨95250707195345996375948003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63500471463563997583965335 95250707195345996375948003)
    ·
      refine ⟨142876060793018994563922005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95250707195345996375948003 142876060793018994563922005)
      ·
        refine ⟨1674328837418191342545961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 142876060793018994563922005 1674328837418191342545961)
        ·
          refine ⟨1255746628063643506909471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1674328837418191342545961 1255746628063643506909471)
          ·
            refine ⟨1883619942095465260364207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255746628063643506909471 1883619942095465260364207)
            ·
              refine ⟨2825429913143197890546311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883619942095465260364207 2825429913143197890546311)
              ·
                refine ⟨4238144869714796835819467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825429913143197890546311 4238144869714796835819467)
                ·
                  refine ⟨6357217304572195253729201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238144869714796835819467 6357217304572195253729201)
                  ·
                    refine ⟨4767912978429146440296901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6357217304572195253729201 4767912978429146440296901)
                    ·
                      refine ⟨893983683455464957555669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4767912978429146440296901 893983683455464957555669)
                      ·
                        rfl

theorem cell23_1741027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1741027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741027 prefixEnd_1741027 := by exact prefixLift 1741027
  have htrace : WordTrace (prefixWord ++ tailWord_1741027) baseStart_1741027 baseEnd_1741027 := by
    simpa [prefixWord, tailWord_1741027, baseEnd_1741027] using wordTrace_append hprefix tailTrace_1741027
  have hstable : (prefixWord ++ tailWord_1741027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741027).length < 2 ^ (prefixWord ++ tailWord_1741027).sum := by decide
  have hdescent : baseEnd_1741027 < baseStart_1741027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741046 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_1741046 : Nat := 118140960795 + 1741046 * 2 ^ 59
def prefixEnd_1741046 : Nat := 4983230072969 + 3 ^ 40 * 1741046 * 2
def baseEnd_1741046 : Nat := 297997813195966794406027

theorem tailTrace_1741046 : CollatzResearch.WordTrace tailWord_1741046 prefixEnd_1741046 297997813195966794406027 := by
  unfold tailWord_1741046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968822778155947739306687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42334109633663442552604661 3968822778155947739306687)
  ·
    refine ⟨5953234167233921608960031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3968822778155947739306687 5953234167233921608960031)
    ·
      refine ⟨8929851250850882413440047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5953234167233921608960031 8929851250850882413440047)
      ·
        refine ⟨13394776876276323620160071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8929851250850882413440047 13394776876276323620160071)
        ·
          refine ⟨20092165314414485430240107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13394776876276323620160071 20092165314414485430240107)
          ·
            refine ⟨30138247971621728145360161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20092165314414485430240107 30138247971621728145360161)
            ·
              refine ⟨22603685978716296109020121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30138247971621728145360161 22603685978716296109020121)
              ·
                refine ⟨16952764484037222081765091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22603685978716296109020121 16952764484037222081765091)
                ·
                  refine ⟨25429146726055833122647637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16952764484037222081765091 25429146726055833122647637)
                  ·
                    refine ⟨297997813195966794406027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25429146726055833122647637 297997813195966794406027)
                    ·
                      rfl

theorem cell23_1741046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_1741046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741046 prefixEnd_1741046 := by exact prefixLift 1741046
  have htrace : WordTrace (prefixWord ++ tailWord_1741046) baseStart_1741046 baseEnd_1741046 := by
    simpa [prefixWord, tailWord_1741046, baseEnd_1741046] using wordTrace_append hprefix tailTrace_1741046
  have hstable : (prefixWord ++ tailWord_1741046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741046).length < 2 ^ (prefixWord ++ tailWord_1741046).sum := by decide
  have hdescent : baseEnd_1741046 < baseStart_1741046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741053 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 1, 4, 2]
def baseStart_1741053 : Nat := 118140960795 + 1741053 * 2 ^ 59
def prefixEnd_1741053 : Nat := 4983230072969 + 3 ^ 40 * 1741053 * 2
def baseEnd_1741053 : Nat := 893997033952481855830549

theorem tailTrace_1741053 : CollatzResearch.WordTrace tailWord_1741053 prefixEnd_1741053 893997033952481855830549 := by
  unfold tailWord_1741053
  simp only [CollatzResearch.WordTrace]
  refine ⟨63501419761469804024411813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42334279840979869349607875 63501419761469804024411813)
  ·
    refine ⟨11906516205275588254577215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63501419761469804024411813 11906516205275588254577215)
    ·
      refine ⟨17859774307913382381865823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11906516205275588254577215 17859774307913382381865823)
      ·
        refine ⟨26789661461870073572798735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17859774307913382381865823 26789661461870073572798735)
        ·
          refine ⟨40184492192805110359198103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26789661461870073572798735 40184492192805110359198103)
          ·
            refine ⟨60276738289207665538797155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40184492192805110359198103 60276738289207665538797155)
            ·
              refine ⟨90415107433811498308195733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60276738289207665538797155 90415107433811498308195733)
              ·
                refine ⟨4238208160959913983196675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90415107433811498308195733 4238208160959913983196675)
                ·
                  refine ⟨6357312241439870974795013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238208160959913983196675 6357312241439870974795013)
                  ·
                    refine ⟨1191996045269975807774065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6357312241439870974795013 1191996045269975807774065)
                    ·
                      refine ⟨893997033952481855830549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1191996045269975807774065 893997033952481855830549)
                      ·
                        rfl

theorem cell23_1741053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_1741053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741053 prefixEnd_1741053 := by exact prefixLift 1741053
  have htrace : WordTrace (prefixWord ++ tailWord_1741053) baseStart_1741053 baseEnd_1741053 := by
    simpa [prefixWord, tailWord_1741053, baseEnd_1741053] using wordTrace_append hprefix tailTrace_1741053
  have hstable : (prefixWord ++ tailWord_1741053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741053).length < 2 ^ (prefixWord ++ tailWord_1741053).sum := by decide
  have hdescent : baseEnd_1741053 < baseStart_1741053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741066 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1741066 : Nat := 118140960795 + 1741066 * 2 ^ 59
def prefixEnd_1741066 : Nat := 4983230072969 + 3 ^ 40 * 1741066 * 2
def baseEnd_1741066 : Nat := 894003709200990304967989

theorem tailTrace_1741066 : CollatzResearch.WordTrace tailWord_1741066 prefixEnd_1741066 894003709200990304967989 := by
  unfold tailWord_1741066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15875473477605676811158763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42334595940281804829756701 15875473477605676811158763)
  ·
    refine ⟨23813210216408515216738145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15875473477605676811158763 23813210216408515216738145)
    ·
      refine ⟨17859907662306386412553609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23813210216408515216738145 17859907662306386412553609)
      ·
        refine ⟨13394930746729789809415207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17859907662306386412553609 13394930746729789809415207)
        ·
          refine ⟨20092396120094684714122811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13394930746729789809415207 20092396120094684714122811)
          ·
            refine ⟨30138594180142027071184217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20092396120094684714122811 30138594180142027071184217)
            ·
              refine ⟨22603945635106520303388163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30138594180142027071184217 22603945635106520303388163)
              ·
                refine ⟨33905918452659780455082245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22603945635106520303388163 33905918452659780455082245)
                ·
                  refine ⟨6357359709873708835327921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33905918452659780455082245 6357359709873708835327921)
                  ·
                    refine ⟨4768019782405281626495941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6357359709873708835327921 4768019782405281626495941)
                    ·
                      refine ⟨894003709200990304967989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4768019782405281626495941 894003709200990304967989)
                      ·
                        rfl

theorem cell23_1741066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1741066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741066 prefixEnd_1741066 := by exact prefixLift 1741066
  have htrace : WordTrace (prefixWord ++ tailWord_1741066) baseStart_1741066 baseEnd_1741066 := by
    simpa [prefixWord, tailWord_1741066, baseEnd_1741066] using wordTrace_append hprefix tailTrace_1741066
  have hstable : (prefixWord ++ tailWord_1741066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741066).length < 2 ^ (prefixWord ++ tailWord_1741066).sum := by decide
  have hdescent : baseEnd_1741066 < baseStart_1741066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741070 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2]
def baseStart_1741070 : Nat := 118140960795 + 1741070 * 2 ^ 59
def prefixEnd_1741070 : Nat := 4983230072969 + 3 ^ 40 * 1741070 * 2
def baseEnd_1741070 : Nat := 894005763123608289317971

theorem tailTrace_1741070 : CollatzResearch.WordTrace tailWord_1741070 prefixEnd_1741070 894005763123608289317971 := by
  unfold tailWord_1741070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937754975301026990972583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42334693201605477285187109 7937754975301026990972583)
  ·
    refine ⟨11906632462951540486458875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7937754975301026990972583 11906632462951540486458875)
    ·
      refine ⟨17859948694427310729688313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11906632462951540486458875 17859948694427310729688313)
      ·
        refine ⟨13394961520820483047266235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17859948694427310729688313 13394961520820483047266235)
        ·
          refine ⟨20092442281230724570899353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13394961520820483047266235 20092442281230724570899353)
          ·
            refine ⟨15069331710923043428174515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20092442281230724570899353 15069331710923043428174515)
            ·
              refine ⟨22603997566384565142261773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15069331710923043428174515 22603997566384565142261773)
              ·
                refine ⟨8476499087394211928348165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22603997566384565142261773 8476499087394211928348165)
                ·
                  refine ⟨1589343578886414736565281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8476499087394211928348165 1589343578886414736565281)
                  ·
                    refine ⟨1192007684164811052423961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1589343578886414736565281 1192007684164811052423961)
                    ·
                      refine ⟨894005763123608289317971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192007684164811052423961 894005763123608289317971)
                      ·
                        rfl

theorem cell23_1741070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_1741070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741070 prefixEnd_1741070 := by exact prefixLift 1741070
  have htrace : WordTrace (prefixWord ++ tailWord_1741070) baseStart_1741070 baseEnd_1741070 := by
    simpa [prefixWord, tailWord_1741070, baseEnd_1741070] using wordTrace_append hprefix tailTrace_1741070
  have hstable : (prefixWord ++ tailWord_1741070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741070).length < 2 ^ (prefixWord ++ tailWord_1741070).sum := by decide
  have hdescent : baseEnd_1741070 < baseStart_1741070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741087 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 2, 2, 2]
def baseStart_1741087 : Nat := 118140960795 + 1741087 * 2 ^ 59
def prefixEnd_1741087 : Nat := 4983230072969 + 3 ^ 40 * 1741087 * 2
def baseEnd_1741087 : Nat := 894014492294734722805393

theorem tailTrace_1741087 : CollatzResearch.WordTrace tailWord_1741087 prefixEnd_1741087 894014492294734722805393 := by
  unfold tailWord_1741087
  simp only [CollatzResearch.WordTrace]
  refine ⟨63502659843346627831149515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42335106562231085220766343 63502659843346627831149515)
  ·
    refine ⟨95253989765019941746724273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63502659843346627831149515 95253989765019941746724273)
    ·
      refine ⟨71440492323764956310043205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95253989765019941746724273 71440492323764956310043205)
      ·
        refine ⟨13395092310705929308133101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71440492323764956310043205 13395092310705929308133101)
        ·
          refine ⟨5023159616514723490549913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13395092310705929308133101 5023159616514723490549913)
          ·
            refine ⟨3767369712386042617912435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5023159616514723490549913 3767369712386042617912435)
            ·
              refine ⟨5651054568579063926868653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3767369712386042617912435 5651054568579063926868653)
              ·
                refine ⟨2119145463217148972575745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5651054568579063926868653 2119145463217148972575745)
                ·
                  refine ⟨1589359097412861729431809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2119145463217148972575745 1589359097412861729431809)
                  ·
                    refine ⟨1192019323059646297073857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1589359097412861729431809 1192019323059646297073857)
                    ·
                      refine ⟨894014492294734722805393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192019323059646297073857 894014492294734722805393)
                      ·
                        rfl

theorem cell23_1741087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_1741087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741087 prefixEnd_1741087 := by exact prefixLift 1741087
  have htrace : WordTrace (prefixWord ++ tailWord_1741087) baseStart_1741087 baseEnd_1741087 := by
    simpa [prefixWord, tailWord_1741087, baseEnd_1741087] using wordTrace_append hprefix tailTrace_1741087
  have hstable : (prefixWord ++ tailWord_1741087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741087).length < 2 ^ (prefixWord ++ tailWord_1741087).sum := by decide
  have hdescent : baseEnd_1741087 < baseStart_1741087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741116 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1741116 : Nat := 118140960795 + 1741116 * 2 ^ 59
def prefixEnd_1741116 : Nat := 4983230072969 + 3 ^ 40 * 1741116 * 2
def baseEnd_1741116 : Nat := 894029383233715109342759

theorem tailTrace_1741116 : CollatzResearch.WordTrace tailWord_1741116 prefixEnd_1741116 894029383233715109342759 := by
  unfold tailWord_1741116
  simp only [CollatzResearch.WordTrace]
  refine ⟨31751858780120782891977601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42335811706827710522636801 31751858780120782891977601)
  ·
    refine ⟨23813894085090587168983201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31751858780120782891977601 23813894085090587168983201)
    ·
      refine ⟨17860420563817940376737401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23813894085090587168983201 17860420563817940376737401)
      ·
        refine ⟨13395315422863455282553051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17860420563817940376737401 13395315422863455282553051)
        ·
          refine ⟨20092973134295182923829577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13395315422863455282553051 20092973134295182923829577)
          ·
            refine ⟨15069729850721387192872183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20092973134295182923829577 15069729850721387192872183)
            ·
              refine ⟨22604594776082080789308275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15069729850721387192872183 22604594776082080789308275)
              ·
                refine ⟨33906892164123121183962413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22604594776082080789308275 33906892164123121183962413)
                ·
                  refine ⟨12715084561546170443985905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33906892164123121183962413 12715084561546170443985905)
                  ·
                    refine ⟨9536313421159627832989429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12715084561546170443985905 9536313421159627832989429)
                    ·
                      refine ⟨894029383233715109342759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9536313421159627832989429 894029383233715109342759)
                      ·
                        rfl

theorem cell23_1741116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1741116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741116 prefixEnd_1741116 := by exact prefixLift 1741116
  have htrace : WordTrace (prefixWord ++ tailWord_1741116) baseStart_1741116 baseEnd_1741116 := by
    simpa [prefixWord, tailWord_1741116, baseEnd_1741116] using wordTrace_append hprefix tailTrace_1741116
  have hstable : (prefixWord ++ tailWord_1741116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741116).length < 2 ^ (prefixWord ++ tailWord_1741116).sum := by decide
  have hdescent : baseEnd_1741116 < baseStart_1741116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741160 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1741160 : Nat := 118140960795 + 1741160 * 2 ^ 59
def prefixEnd_1741160 : Nat := 4983230072969 + 3 ^ 40 * 1741160 * 2
def baseEnd_1741160 : Nat := 894051976382512937192557

theorem tailTrace_1741160 : CollatzResearch.WordTrace tailWord_1741160 prefixEnd_1741160 894051976382512937192557 := by
  unfold tailWord_1741160
  simp only [CollatzResearch.WordTrace]
  refine ⟨31752661186041080649278467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42336881581388107532371289 31752661186041080649278467)
  ·
    refine ⟨47628991779061620973917701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31752661186041080649278467 47628991779061620973917701)
    ·
      refine ⟨8930435958574053932609569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47628991779061620973917701 8930435958574053932609569)
      ·
        refine ⟨6697826968930540449457177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8930435958574053932609569 6697826968930540449457177)
        ·
          refine ⟨5023370226697905337092883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6697826968930540449457177 5023370226697905337092883)
          ·
            refine ⟨7535055340046858005639325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5023370226697905337092883 7535055340046858005639325)
            ·
              refine ⟨2825645752517571752114747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7535055340046858005639325 2825645752517571752114747)
              ·
                refine ⟨4238468628776357628172121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825645752517571752114747 4238468628776357628172121)
                ·
                  refine ⟨3178851471582268221129091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4238468628776357628172121 3178851471582268221129091)
                  ·
                    refine ⟨4768277207373402331693637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3178851471582268221129091 4768277207373402331693637)
                    ·
                      refine ⟨894051976382512937192557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4768277207373402331693637 894051976382512937192557)
                      ·
                        rfl

theorem cell23_1741160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1741160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741160 prefixEnd_1741160 := by exact prefixLift 1741160
  have htrace : WordTrace (prefixWord ++ tailWord_1741160) baseStart_1741160 baseEnd_1741160 := by
    simpa [prefixWord, tailWord_1741160, baseEnd_1741160] using wordTrace_append hprefix tailTrace_1741160
  have hstable : (prefixWord ++ tailWord_1741160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741160).length < 2 ^ (prefixWord ++ tailWord_1741160).sum := by decide
  have hdescent : baseEnd_1741160 < baseStart_1741160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741173 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1741173 : Nat := 118140960795 + 1741173 * 2 ^ 59
def prefixEnd_1741173 : Nat := 4983230072969 + 3 ^ 40 * 1741173 * 2
def baseEnd_1741173 : Nat := 894058651631021386329997

theorem tailTrace_1741173 : CollatzResearch.WordTrace tailWord_1741173 prefixEnd_1741173 894058651631021386329997 := by
  unfold tailWord_1741173
  simp only [CollatzResearch.WordTrace]
  refine ⟨63505796521035064518780173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42337197680690043012520115 63505796521035064518780173)
  ·
    refine ⟨23814673695388149194542565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63505796521035064518780173 23814673695388149194542565)
    ·
      refine ⟨4465251317885277973976731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23814673695388149194542565 4465251317885277973976731)
      ·
        refine ⟨6697876976827916960965097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465251317885277973976731 6697876976827916960965097)
        ·
          refine ⟨5023407732620937720723823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6697876976827916960965097 5023407732620937720723823)
          ·
            refine ⟨7535111598931406581085735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5023407732620937720723823 7535111598931406581085735)
            ·
              refine ⟨11302667398397109871628603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7535111598931406581085735 11302667398397109871628603)
              ·
                refine ⟨16954001097595664807442905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11302667398397109871628603 16954001097595664807442905)
                ·
                  refine ⟨12715500823196748605582179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16954001097595664807442905 12715500823196748605582179)
                  ·
                    refine ⟨19073251234795122908373269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12715500823196748605582179 19073251234795122908373269)
                    ·
                      refine ⟨894058651631021386329997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19073251234795122908373269 894058651631021386329997)
                      ·
                        rfl

theorem cell23_1741173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1741173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741173 prefixEnd_1741173 := by exact prefixLift 1741173
  have htrace : WordTrace (prefixWord ++ tailWord_1741173) baseStart_1741173 baseEnd_1741173 := by
    simpa [prefixWord, tailWord_1741173, baseEnd_1741173] using wordTrace_append hprefix tailTrace_1741173
  have hstable : (prefixWord ++ tailWord_1741173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741173).length < 2 ^ (prefixWord ++ tailWord_1741173).sum := by decide
  have hdescent : baseEnd_1741173 < baseStart_1741173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741220 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 1, 5, 2]
def baseStart_1741220 : Nat := 118140960795 + 1741220 * 2 ^ 59
def prefixEnd_1741220 : Nat := 4983230072969 + 3 ^ 40 * 1741220 * 2
def baseEnd_1741220 : Nat := 894082785221782702442281

theorem tailTrace_1741220 : CollatzResearch.WordTrace tailWord_1741220 prefixEnd_1741220 894082785221782702442281 := by
  unfold tailWord_1741220
  simp only [CollatzResearch.WordTrace]
  refine ⟨31753755375932395772870557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42338340501243194363827409 31753755375932395772870557)
  ·
    refine ⟨11907658265974648414826459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31753755375932395772870557 11907658265974648414826459)
    ·
      refine ⟨17861487398961972622239689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11907658265974648414826459 17861487398961972622239689)
      ·
        refine ⟨13396115549221479466679767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17861487398961972622239689 13396115549221479466679767)
        ·
          refine ⟨20094173323832219200019651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13396115549221479466679767 20094173323832219200019651)
          ·
            refine ⟨30141259985748328800029477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20094173323832219200019651 30141259985748328800029477)
            ·
              refine ⟨5651486247327811650005527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30141259985748328800029477 5651486247327811650005527)
              ·
                refine ⟨8477229370991717475008291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5651486247327811650005527 8477229370991717475008291)
                ·
                  refine ⟨12715844056487576212512437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8477229370991717475008291 12715844056487576212512437)
                  ·
                    refine ⟨1192110380295710269923041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12715844056487576212512437 1192110380295710269923041)
                    ·
                      refine ⟨894082785221782702442281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192110380295710269923041 894082785221782702442281)
                      ·
                        rfl

theorem cell23_1741220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_1741220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741220 prefixEnd_1741220 := by exact prefixLift 1741220
  have htrace : WordTrace (prefixWord ++ tailWord_1741220) baseStart_1741220 baseEnd_1741220 := by
    simpa [prefixWord, tailWord_1741220, baseEnd_1741220] using wordTrace_append hprefix tailTrace_1741220
  have hstable : (prefixWord ++ tailWord_1741220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741220).length < 2 ^ (prefixWord ++ tailWord_1741220).sum := by decide
  have hdescent : baseEnd_1741220 < baseStart_1741220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741244 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1741244 : Nat := 118140960795 + 1741244 * 2 ^ 59
def prefixEnd_1741244 : Nat := 4983230072969 + 3 ^ 40 * 1741244 * 2
def baseEnd_1741244 : Nat := 894095108757490608542171

theorem tailTrace_1741244 : CollatzResearch.WordTrace tailWord_1741244 prefixEnd_1741244 894095108757490608542171 := by
  unfold tailWord_1741244
  simp only [CollatzResearch.WordTrace]
  refine ⟨31754193051888921822307393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42338924069185229096409857 31754193051888921822307393)
  ·
    refine ⟨23815644788916691366730545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31754193051888921822307393 23815644788916691366730545)
    ·
      refine ⟨17861733591687518525047909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23815644788916691366730545 17861733591687518525047909)
      ·
        refine ⟨3349075048441409723446483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17861733591687518525047909 3349075048441409723446483)
        ·
          refine ⟨5023612572662114585169725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3349075048441409723446483 5023612572662114585169725)
          ·
            refine ⟨1883854714748292969438647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5023612572662114585169725 1883854714748292969438647)
            ·
              refine ⟨2825782072122439454157971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883854714748292969438647 2825782072122439454157971)
              ·
                refine ⟨4238673108183659181236957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825782072122439454157971 4238673108183659181236957)
                ·
                  refine ⟨1589502415568872192963859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4238673108183659181236957 1589502415568872192963859)
                  ·
                    refine ⟨2384253623353308289445789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1589502415568872192963859 2384253623353308289445789)
                    ·
                      refine ⟨894095108757490608542171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2384253623353308289445789 894095108757490608542171)
                      ·
                        rfl

theorem cell23_1741244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1741244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741244 prefixEnd_1741244 := by exact prefixLift 1741244
  have htrace : WordTrace (prefixWord ++ tailWord_1741244) baseStart_1741244 baseEnd_1741244 := by
    simpa [prefixWord, tailWord_1741244, baseEnd_1741244] using wordTrace_append hprefix tailTrace_1741244
  have hstable : (prefixWord ++ tailWord_1741244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741244).length < 2 ^ (prefixWord ++ tailWord_1741244).sum := by decide
  have hdescent : baseEnd_1741244 < baseStart_1741244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741263 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 4]
def baseStart_1741263 : Nat := 118140960795 + 1741263 * 2 ^ 59
def prefixEnd_1741263 : Nat := 4983230072969 + 3 ^ 40 * 1741263 * 2
def baseEnd_1741263 : Nat := 894104864889926034204583

theorem tailTrace_1741263 : CollatzResearch.WordTrace tailWord_1741263 prefixEnd_1741263 894104864889926034204583 := by
  unfold tailWord_1741263
  simp only [CollatzResearch.WordTrace]
  refine ⟨63509079090709009889556443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42339386060472673259704295 63509079090709009889556443)
  ·
    refine ⟨95263618636063514834334665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63509079090709009889556443 95263618636063514834334665)
    ·
      refine ⟨71447713977047636125750999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95263618636063514834334665 71447713977047636125750999)
      ·
        refine ⟨107171570965571454188626499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71447713977047636125750999 107171570965571454188626499)
        ·
          refine ⟨160757356448357181282939749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107171570965571454188626499 160757356448357181282939749)
          ·
            refine ⟨30142004334066971490551203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160757356448357181282939749 30142004334066971490551203)
            ·
              refine ⟨45213006501100457235826805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30142004334066971490551203 45213006501100457235826805)
              ·
                refine ⟨4238719359478167865858763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45213006501100457235826805 4238719359478167865858763)
                ·
                  refine ⟨6358079039217251798788145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238719359478167865858763 6358079039217251798788145)
                  ·
                    refine ⟨4768559279412938849091109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6358079039217251798788145 4768559279412938849091109)
                    ·
                      refine ⟨894104864889926034204583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4768559279412938849091109 894104864889926034204583)
                      ·
                        rfl

theorem cell23_1741263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_1741263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741263 prefixEnd_1741263 := by exact prefixLift 1741263
  have htrace : WordTrace (prefixWord ++ tailWord_1741263) baseStart_1741263 baseEnd_1741263 := by
    simpa [prefixWord, tailWord_1741263, baseEnd_1741263] using wordTrace_append hprefix tailTrace_1741263
  have hstable : (prefixWord ++ tailWord_1741263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741263).length < 2 ^ (prefixWord ++ tailWord_1741263).sum := by decide
  have hdescent : baseEnd_1741263 < baseStart_1741263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741314 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1741314 : Nat := 118140960795 + 1741314 * 2 ^ 59
def prefixEnd_1741314 : Nat := 4983230072969 + 3 ^ 40 * 1741314 * 2
def baseEnd_1741314 : Nat := 894131052403305334666849

theorem tailTrace_1741314 : CollatzResearch.WordTrace tailWord_1741314 prefixEnd_1741314 894131052403305334666849 := by
  unfold tailWord_1741314
  simp only [CollatzResearch.WordTrace]
  refine ⟨15877734803381061399915749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42340626142349497066441997 15877734803381061399915749)
  ·
    refine ⟨2977075275633949012484203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15877734803381061399915749 2977075275633949012484203)
    ·
      refine ⟨4465612913450923518726305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2977075275633949012484203 4465612913450923518726305)
      ·
        refine ⟨3349209685088192639044729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4465612913450923518726305 3349209685088192639044729)
        ·
          refine ⟨2511907263816144479283547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3349209685088192639044729 2511907263816144479283547)
          ·
            refine ⟨3767860895724216718925321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511907263816144479283547 3767860895724216718925321)
            ·
              refine ⟨2825895671793162539193991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3767860895724216718925321 2825895671793162539193991)
              ·
                refine ⟨4238843507689743808790987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825895671793162539193991 4238843507689743808790987)
                ·
                  refine ⟨6358265261534615713186481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238843507689743808790987 6358265261534615713186481)
                  ·
                    refine ⟨4768698946150961784889861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6358265261534615713186481 4768698946150961784889861)
                    ·
                      refine ⟨894131052403305334666849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4768698946150961784889861 894131052403305334666849)
                      ·
                        rfl

theorem cell23_1741314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1741314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741314 prefixEnd_1741314 := by exact prefixLift 1741314
  have htrace : WordTrace (prefixWord ++ tailWord_1741314) baseStart_1741314 baseEnd_1741314 := by
    simpa [prefixWord, tailWord_1741314, baseEnd_1741314] using wordTrace_append hprefix tailTrace_1741314
  have hstable : (prefixWord ++ tailWord_1741314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741314).length < 2 ^ (prefixWord ++ tailWord_1741314).sum := by decide
  have hdescent : baseEnd_1741314 < baseStart_1741314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741317 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 2, 1, 3]
def baseStart_1741317 : Nat := 118140960795 + 1741317 * 2 ^ 59
def prefixEnd_1741317 : Nat := 4983230072969 + 3 ^ 40 * 1741317 * 2
def baseEnd_1741317 : Nat := 894132592845268822929335

theorem tailTrace_1741317 : CollatzResearch.WordTrace tailWord_1741317 prefixEnd_1741317 894132592845268822929335 := by
  unfold tailWord_1741317
  simp only [CollatzResearch.WordTrace]
  refine ⟨63511048632513377112022205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42340699088342251408014803 63511048632513377112022205)
  ·
    refine ⟨23816643237192516417008327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63511048632513377112022205 23816643237192516417008327)
    ·
      refine ⟨35724964855788774625512491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23816643237192516417008327 35724964855788774625512491)
      ·
        refine ⟨53587447283683161938268737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35724964855788774625512491 53587447283683161938268737)
        ·
          refine ⟨40190585462762371453701553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53587447283683161938268737 40190585462762371453701553)
          ·
            refine ⟨30142939097071778590276165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40190585462762371453701553 30142939097071778590276165)
            ·
              refine ⟨5651801080700958485676781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30142939097071778590276165 5651801080700958485676781)
              ·
                refine ⟨2119425405262859432128793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5651801080700958485676781 2119425405262859432128793)
                ·
                  refine ⟨1589569053947144574096595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2119425405262859432128793 1589569053947144574096595)
                  ·
                    refine ⟨2384353580920716861144893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1589569053947144574096595 2384353580920716861144893)
                    ·
                      refine ⟨894132592845268822929335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2384353580920716861144893 894132592845268822929335)
                      ·
                        rfl

theorem cell23_1741317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_1741317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741317 prefixEnd_1741317 := by exact prefixLift 1741317
  have htrace : WordTrace (prefixWord ++ tailWord_1741317) baseStart_1741317 baseEnd_1741317 := by
    simpa [prefixWord, tailWord_1741317, baseEnd_1741317] using wordTrace_append hprefix tailTrace_1741317
  have hstable : (prefixWord ++ tailWord_1741317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741317).length < 2 ^ (prefixWord ++ tailWord_1741317).sum := by decide
  have hdescent : baseEnd_1741317 < baseStart_1741317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741318 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_1741318 : Nat := 118140960795 + 1741318 * 2 ^ 59
def prefixEnd_1741318 : Nat := 4983230072969 + 3 ^ 40 * 1741318 * 2
def baseEnd_1741318 : Nat := 894133106325923319016831

theorem tailTrace_1741318 : CollatzResearch.WordTrace tailWord_1741318 prefixEnd_1741318 894133106325923319016831 := by
  unfold tailWord_1741318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984721409547179821337769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42340723403673169521872405 1984721409547179821337769)
  ·
    refine ⟨1488541057160384866003327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1984721409547179821337769 1488541057160384866003327)
    ·
      refine ⟨2232811585740577299004991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488541057160384866003327 2232811585740577299004991)
      ·
        refine ⟨3349217378610865948507487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2232811585740577299004991 3349217378610865948507487)
        ·
          refine ⟨5023826067916298922761231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3349217378610865948507487 5023826067916298922761231)
          ·
            refine ⟨7535739101874448384141847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5023826067916298922761231 7535739101874448384141847)
            ·
              refine ⟨11303608652811672576212771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7535739101874448384141847 11303608652811672576212771)
              ·
                refine ⟨16955412979217508864319157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11303608652811672576212771 16955412979217508864319157)
                ·
                  refine ⟨1589569966801641456029921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16955412979217508864319157 1589569966801641456029921)
                  ·
                    refine ⟨1192177475101231092022441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1589569966801641456029921 1192177475101231092022441)
                    ·
                      refine ⟨894133106325923319016831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192177475101231092022441 894133106325923319016831)
                      ·
                        rfl

theorem cell23_1741318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_1741318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741318 prefixEnd_1741318 := by exact prefixLift 1741318
  have htrace : WordTrace (prefixWord ++ tailWord_1741318) baseStart_1741318 baseEnd_1741318 := by
    simpa [prefixWord, tailWord_1741318, baseEnd_1741318] using wordTrace_append hprefix tailTrace_1741318
  have hstable : (prefixWord ++ tailWord_1741318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741318).length < 2 ^ (prefixWord ++ tailWord_1741318).sum := by decide
  have hdescent : baseEnd_1741318 < baseStart_1741318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741333 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_1741333 : Nat := 118140960795 + 1741333 * 2 ^ 59
def prefixEnd_1741333 : Nat := 4983230072969 + 3 ^ 40 * 1741333 * 2
def baseEnd_1741333 : Nat := 298046936178580253443087

theorem tailTrace_1741333 : CollatzResearch.WordTrace tailWord_1741333 prefixEnd_1741333 298046936178580253443087 := by
  unfold tailWord_1741333
  simp only [CollatzResearch.WordTrace]
  refine ⟨63511632200455411844604653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42341088133636941229736435 63511632200455411844604653)
  ·
    refine ⟨23816862075170779441726745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63511632200455411844604653 23816862075170779441726745)
    ·
      refine ⟨17862646556378084581295059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23816862075170779441726745 17862646556378084581295059)
      ·
        refine ⟨26793969834567126871942589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17862646556378084581295059 26793969834567126871942589)
        ·
          refine ⟨10047738687962672576978471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26793969834567126871942589 10047738687962672576978471)
          ·
            refine ⟨15071608031944008865467707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10047738687962672576978471 15071608031944008865467707)
            ·
              refine ⟨22607412047916013298201561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15071608031944008865467707 22607412047916013298201561)
              ·
                refine ⟨16955559035937009973651171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22607412047916013298201561 16955559035937009973651171)
                ·
                  refine ⟨25433338553905514960476757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16955559035937009973651171 25433338553905514960476757)
                  ·
                    refine ⟨298046936178580253443087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25433338553905514960476757 298046936178580253443087)
                    ·
                      rfl

theorem cell23_1741333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_1741333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741333 prefixEnd_1741333 := by exact prefixLift 1741333
  have htrace : WordTrace (prefixWord ++ tailWord_1741333) baseStart_1741333 baseEnd_1741333 := by
    simpa [prefixWord, tailWord_1741333, baseEnd_1741333] using wordTrace_append hprefix tailTrace_1741333
  have hstable : (prefixWord ++ tailWord_1741333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741333).length < 2 ^ (prefixWord ++ tailWord_1741333).sum := by decide
  have hdescent : baseEnd_1741333 < baseStart_1741333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741343 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1741343 : Nat := 118140960795 + 1741343 * 2 ^ 59
def prefixEnd_1741343 : Nat := 4983230072969 + 3 ^ 40 * 1741343 * 2
def baseEnd_1741343 : Nat := 894145943342285721204215

theorem tailTrace_1741343 : CollatzResearch.WordTrace tailWord_1741343 prefixEnd_1741343 894145943342285721204215 := by
  unfold tailWord_1741343
  simp only [CollatzResearch.WordTrace]
  refine ⟨63511996930419183552468683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42341331286946122368312455 63511996930419183552468683)
  ·
    refine ⟨95267995395628775328703025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63511996930419183552468683 95267995395628775328703025)
    ·
      refine ⟨71450996546721581496527269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95267995395628775328703025 71450996546721581496527269)
      ·
        refine ⟨13397061852510296530598863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71450996546721581496527269 13397061852510296530598863)
        ·
          refine ⟨20095592778765444795898295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13397061852510296530598863 20095592778765444795898295)
          ·
            refine ⟨30143389168148167193847443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20095592778765444795898295 30143389168148167193847443)
            ·
              refine ⟨45215083752222250790771165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30143389168148167193847443 45215083752222250790771165)
              ·
                refine ⟨16955656407083344046539187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45215083752222250790771165 16955656407083344046539187)
                ·
                  refine ⟨25433484610625016069808781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16955656407083344046539187 25433484610625016069808781)
                  ·
                    refine ⟨9537556728984381026178293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25433484610625016069808781 9537556728984381026178293)
                    ·
                      refine ⟨894145943342285721204215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9537556728984381026178293 894145943342285721204215)
                      ·
                        rfl

theorem cell23_1741343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1741343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741343 prefixEnd_1741343 := by exact prefixLift 1741343
  have htrace : WordTrace (prefixWord ++ tailWord_1741343) baseStart_1741343 baseEnd_1741343 := by
    simpa [prefixWord, tailWord_1741343, baseEnd_1741343] using wordTrace_append hprefix tailTrace_1741343
  have hstable : (prefixWord ++ tailWord_1741343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741343).length < 2 ^ (prefixWord ++ tailWord_1741343).sum := by decide
  have hdescent : baseEnd_1741343 < baseStart_1741343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741351 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1741351 : Nat := 118140960795 + 1741351 * 2 ^ 59
def prefixEnd_1741351 : Nat := 4983230072969 + 3 ^ 40 * 1741351 * 2
def baseEnd_1741351 : Nat := 894150051187521689904179

theorem tailTrace_1741351 : CollatzResearch.WordTrace tailWord_1741351 prefixEnd_1741351 894150051187521689904179 := by
  unfold tailWord_1741351
  simp only [CollatzResearch.WordTrace]
  refine ⟨63512288714390200918759907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42341525809593467279173271 63512288714390200918759907)
  ·
    refine ⟨95268433071585301378139861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63512288714390200918759907 95268433071585301378139861)
    ·
      refine ⟨2232853900115280501050153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 95268433071585301378139861 2232853900115280501050153)
      ·
        refine ⟨1674640425086460375787615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2232853900115280501050153 1674640425086460375787615)
        ·
          refine ⟨2511960637629690563681423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674640425086460375787615 2511960637629690563681423)
          ·
            refine ⟨3767940956444535845522135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511960637629690563681423 3767940956444535845522135)
            ·
              refine ⟨5651911434666803768283203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3767940956444535845522135 5651911434666803768283203)
              ·
                refine ⟨8477867152000205652424805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5651911434666803768283203 8477867152000205652424805)
                ·
                  refine ⟨1589600091000038559829651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8477867152000205652424805 1589600091000038559829651)
                  ·
                    refine ⟨2384400136500057839744477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1589600091000038559829651 2384400136500057839744477)
                    ·
                      refine ⟨894150051187521689904179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2384400136500057839744477 894150051187521689904179)
                      ·
                        rfl

theorem cell23_1741351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1741351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741351 prefixEnd_1741351 := by exact prefixLift 1741351
  have htrace : WordTrace (prefixWord ++ tailWord_1741351) baseStart_1741351 baseEnd_1741351 := by
    simpa [prefixWord, tailWord_1741351, baseEnd_1741351] using wordTrace_append hprefix tailTrace_1741351
  have hstable : (prefixWord ++ tailWord_1741351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741351).length < 2 ^ (prefixWord ++ tailWord_1741351).sum := by decide
  have hdescent : baseEnd_1741351 < baseStart_1741351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741370 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_1741370 : Nat := 118140960795 + 1741370 * 2 ^ 59
def prefixEnd_1741370 : Nat := 4983230072969 + 3 ^ 40 * 1741370 * 2
def baseEnd_1741370 : Nat := 894159807319957115566591

theorem tailTrace_1741370 : CollatzResearch.WordTrace tailWord_1741370 prefixEnd_1741370 894159807319957115566591 := by
  unfold tailWord_1741370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15878245425330341790925391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42341987800880911442467709 15878245425330341790925391)
  ·
    refine ⟨23817368137995512686388087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15878245425330341790925391 23817368137995512686388087)
    ·
      refine ⟨35726052206993269029582131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23817368137995512686388087 35726052206993269029582131)
      ·
        refine ⟨53589078310489903544373197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35726052206993269029582131 53589078310489903544373197)
        ·
          refine ⟨20095904366433713829139949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53589078310489903544373197 20095904366433713829139949)
          ·
            refine ⟨7535964137412642685927481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20095904366433713829139949 7535964137412642685927481)
            ·
              refine ⟨5651973103059482014445611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7535964137412642685927481 5651973103059482014445611)
              ·
                refine ⟨8477959654589223021668417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5651973103059482014445611 8477959654589223021668417)
                ·
                  refine ⟨6358469740941917266251313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8477959654589223021668417 6358469740941917266251313)
                  ·
                    refine ⟨4768852305706437949688485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6358469740941917266251313 4768852305706437949688485)
                    ·
                      refine ⟨894159807319957115566591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4768852305706437949688485 894159807319957115566591)
                      ·
                        rfl

theorem cell23_1741370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_1741370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741370 prefixEnd_1741370 := by exact prefixLift 1741370
  have htrace : WordTrace (prefixWord ++ tailWord_1741370) baseStart_1741370 baseEnd_1741370 := by
    simpa [prefixWord, tailWord_1741370, baseEnd_1741370] using wordTrace_append hprefix tailTrace_1741370
  have hstable : (prefixWord ++ tailWord_1741370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741370).length < 2 ^ (prefixWord ++ tailWord_1741370).sum := by decide
  have hdescent : baseEnd_1741370 < baseStart_1741370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741390 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_1741390 : Nat := 118140960795 + 1741390 * 2 ^ 59
def prefixEnd_1741390 : Nat := 4983230072969 + 3 ^ 40 * 1741390 * 2
def baseEnd_1741390 : Nat := 894170076933047037316499

theorem tailTrace_1741390 : CollatzResearch.WordTrace tailWord_1741390 prefixEnd_1741390 894170076933047037316499 := by
  unfold tailWord_1741390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7939213895156113822428703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42342474107499273719619749 7939213895156113822428703)
  ·
    refine ⟨11908820842734170733643055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7939213895156113822428703 11908820842734170733643055)
    ·
      refine ⟨17863231264101256100464583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11908820842734170733643055 17863231264101256100464583)
      ·
        refine ⟨26794846896151884150696875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17863231264101256100464583 26794846896151884150696875)
        ·
          refine ⟨40192270344227826226045313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26794846896151884150696875 40192270344227826226045313)
          ·
            refine ⟨30144202758170869669533985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40192270344227826226045313 30144202758170869669533985)
            ·
              refine ⟨22608152068628152252150489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30144202758170869669533985 22608152068628152252150489)
              ·
                refine ⟨16956114051471114189112867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22608152068628152252150489 16956114051471114189112867)
                ·
                  refine ⟨25434171077206671283669301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16956114051471114189112867 25434171077206671283669301)
                  ·
                    refine ⟨2384453538488125432843997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25434171077206671283669301 2384453538488125432843997)
                    ·
                      refine ⟨894170076933047037316499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2384453538488125432843997 894170076933047037316499)
                      ·
                        rfl

theorem cell23_1741390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_1741390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741390 prefixEnd_1741390 := by exact prefixLift 1741390
  have htrace : WordTrace (prefixWord ++ tailWord_1741390) baseStart_1741390 baseEnd_1741390 := by
    simpa [prefixWord, tailWord_1741390, baseEnd_1741390] using wordTrace_append hprefix tailTrace_1741390
  have hstable : (prefixWord ++ tailWord_1741390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741390).length < 2 ^ (prefixWord ++ tailWord_1741390).sum := by decide
  have hdescent : baseEnd_1741390 < baseStart_1741390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741397 : List Nat := [1, 3, 2, 2, 1, 1, 5, 3, 5]
def baseStart_1741397 : Nat := 118140960795 + 1741397 * 2 ^ 59
def prefixEnd_1741397 : Nat := 4983230072969 + 3 ^ 40 * 1741397 * 2
def baseEnd_1741397 : Nat := 99352630144180945547663

theorem tailTrace_1741397 : CollatzResearch.WordTrace tailWord_1741397 prefixEnd_1741397 99352630144180945547663 := by
  unfold tailWord_1741397
  simp only [CollatzResearch.WordTrace]
  refine ⟨63513966472223550774934445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42342644314815700516622963 63513966472223550774934445)
  ·
    refine ⟨23817737427083831540600417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63513966472223550774934445 23817737427083831540600417)
    ·
      refine ⟨17863303070312873655450313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23817737427083831540600417 17863303070312873655450313)
      ·
        refine ⟨13397477302734655241587735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17863303070312873655450313 13397477302734655241587735)
        ·
          refine ⟨20096215954101982862381603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13397477302734655241587735 20096215954101982862381603)
          ·
            refine ⟨30144323931152974293572405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20096215954101982862381603 30144323931152974293572405)
            ·
              refine ⟨2826030368545591340022413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30144323931152974293572405 2826030368545591340022413)
              ·
                refine ⟨1059761388204596752508405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2826030368545591340022413 1059761388204596752508405)
                ·
                  refine ⟨99352630144180945547663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1059761388204596752508405 99352630144180945547663)
                  ·
                    rfl

theorem cell23_1741397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_1741397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741397 prefixEnd_1741397 := by exact prefixLift 1741397
  have htrace : WordTrace (prefixWord ++ tailWord_1741397) baseStart_1741397 baseEnd_1741397 := by
    simpa [prefixWord, tailWord_1741397, baseEnd_1741397] using wordTrace_append hprefix tailTrace_1741397
  have hstable : (prefixWord ++ tailWord_1741397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741397).length < 2 ^ (prefixWord ++ tailWord_1741397).sum := by decide
  have hdescent : baseEnd_1741397 < baseStart_1741397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741447 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_1741447 : Nat := 118140960795 + 1741447 * 2 ^ 59
def prefixEnd_1741447 : Nat := 4983230072969 + 3 ^ 40 * 1741447 * 2
def baseEnd_1741447 : Nat := 894199345330353314303737

theorem tailTrace_1741447 : CollatzResearch.WordTrace tailWord_1741447 prefixEnd_1741447 894199345330353314303737 := by
  unfold tailWord_1741447
  simp only [CollatzResearch.WordTrace]
  refine ⟨63515790122042409314254595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42343860081361606209503063 63515790122042409314254595)
  ·
    refine ⟨95273685183063613971381893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63515790122042409314254595 95273685183063613971381893)
    ·
      refine ⟨17863815971824427619634105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95273685183063613971381893 17863815971824427619634105)
      ·
        refine ⟨13397861978868320714725579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17863815971824427619634105 13397861978868320714725579)
        ·
          refine ⟨20096792968302481072088369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13397861978868320714725579 20096792968302481072088369)
          ·
            refine ⟨15072594726226860804066277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20096792968302481072088369 15072594726226860804066277)
            ·
              refine ⟨2826111511167536400762427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15072594726226860804066277 2826111511167536400762427)
              ·
                refine ⟨4239167266751304601143641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826111511167536400762427 4239167266751304601143641)
                ·
                  refine ⟨3179375450063478450857731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4239167266751304601143641 3179375450063478450857731)
                  ·
                    refine ⟨4769063175095217676286597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3179375450063478450857731 4769063175095217676286597)
                    ·
                      refine ⟨894199345330353314303737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4769063175095217676286597 894199345330353314303737)
                      ·
                        rfl

theorem cell23_1741447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_1741447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741447 prefixEnd_1741447 := by exact prefixLift 1741447
  have htrace : WordTrace (prefixWord ++ tailWord_1741447) baseStart_1741447 baseEnd_1741447 := by
    simpa [prefixWord, tailWord_1741447, baseEnd_1741447] using wordTrace_append hprefix tailTrace_1741447
  have hstable : (prefixWord ++ tailWord_1741447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741447).length < 2 ^ (prefixWord ++ tailWord_1741447).sum := by decide
  have hdescent : baseEnd_1741447 < baseStart_1741447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741554 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1741554 : Nat := 118140960795 + 1741554 * 2 ^ 59
def prefixEnd_1741554 : Nat := 4983230072969 + 3 ^ 40 * 1741554 * 2
def baseEnd_1741554 : Nat := 894254287760384395665745

theorem tailTrace_1741554 : CollatzResearch.WordTrace tailWord_1741554 prefixEnd_1741554 894254287760384395665745 := by
  unfold tailWord_1741554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15879923183163691647099929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42346461821769844392266477 15879923183163691647099929)
  ·
    refine ⟨11909942387372768735324947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15879923183163691647099929 11909942387372768735324947)
    ·
      refine ⟨17864913581059153102987421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11909942387372768735324947 17864913581059153102987421)
      ·
        refine ⟨6699342592897182413620283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17864913581059153102987421 6699342592897182413620283)
        ·
          refine ⟨10049013889345773620430425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6699342592897182413620283 10049013889345773620430425)
          ·
            refine ⟨7536760417009330215322819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10049013889345773620430425 7536760417009330215322819)
            ·
              refine ⟨11305140625513995322984229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7536760417009330215322819 11305140625513995322984229)
              ·
                refine ⟨2119713867283874123059543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11305140625513995322984229 2119713867283874123059543)
                ·
                  refine ⟨3179570800925811184589315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119713867283874123059543 3179570800925811184589315)
                  ·
                    refine ⟨4769356201388716776883973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3179570800925811184589315 4769356201388716776883973)
                    ·
                      refine ⟨894254287760384395665745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4769356201388716776883973 894254287760384395665745)
                      ·
                        rfl

theorem cell23_1741554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1741554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741554 prefixEnd_1741554 := by exact prefixLift 1741554
  have htrace : WordTrace (prefixWord ++ tailWord_1741554) baseStart_1741554 baseEnd_1741554 := by
    simpa [prefixWord, tailWord_1741554, baseEnd_1741554] using wordTrace_append hprefix tailTrace_1741554
  have hstable : (prefixWord ++ tailWord_1741554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741554).length < 2 ^ (prefixWord ++ tailWord_1741554).sum := by decide
  have hdescent : baseEnd_1741554 < baseStart_1741554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741560 : List Nat := [2, 1, 2, 1, 1, 2, 5, 9]
def baseStart_1741560 : Nat := 118140960795 + 1741560 * 2 ^ 59
def prefixEnd_1741560 : Nat := 4983230072969 + 3 ^ 40 * 1741560 * 2
def baseEnd_1741560 : Nat := 33120643283122643414471

theorem tailTrace_1741560 : CollatzResearch.WordTrace tailWord_1741560 prefixEnd_1741560 33120643283122643414471 := by
  unfold tailWord_1741560
  simp only [CollatzResearch.WordTrace]
  refine ⟨31759955785316514806559067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42346607713755353075412089 31759955785316514806559067)
  ·
    refine ⟨47639933677974772209838601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31759955785316514806559067 47639933677974772209838601)
    ·
      refine ⟨35729950258481079157378951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47639933677974772209838601 35729950258481079157378951)
      ·
        refine ⟨53594925387721618736068427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35729950258481079157378951 53594925387721618736068427)
        ·
          refine ⟨80392388081582428104102641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53594925387721618736068427 80392388081582428104102641)
          ·
            refine ⟨60294291061186821078076981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80392388081582428104102641 60294291061186821078076981)
            ·
              refine ⟨5652589786986264476069717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60294291061186821078076981 5652589786986264476069717)
              ·
                refine ⟨33120643283122643414471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5652589786986264476069717 33120643283122643414471)
                ·
                  rfl

theorem cell23_1741560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 9].length) (baseStart_1741560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741560 prefixEnd_1741560 := by exact prefixLift 1741560
  have htrace : WordTrace (prefixWord ++ tailWord_1741560) baseStart_1741560 baseEnd_1741560 := by
    simpa [prefixWord, tailWord_1741560, baseEnd_1741560] using wordTrace_append hprefix tailTrace_1741560
  have hstable : (prefixWord ++ tailWord_1741560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741560).length < 2 ^ (prefixWord ++ tailWord_1741560).sum := by decide
  have hdescent : baseEnd_1741560 < baseStart_1741560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741657 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_1741657 : Nat := 118140960795 + 1741657 * 2 ^ 59
def prefixEnd_1741657 : Nat := 4983230072969 + 3 ^ 40 * 1741657 * 2
def baseEnd_1741657 : Nat := 894307176267797492677771

theorem tailTrace_1741657 : CollatzResearch.WordTrace tailWord_1741657 prefixEnd_1741657 894307176267797492677771 := by
  unfold tailWord_1741657
  simp only [CollatzResearch.WordTrace]
  refine ⟨63523449451281615179399225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42348966300854410119599483 63523449451281615179399225)
  ·
    refine ⟨47642587088461211384549419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63523449451281615179399225 47642587088461211384549419)
    ·
      refine ⟨71463880632691817076824129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47642587088461211384549419 71463880632691817076824129)
      ·
        refine ⟨53597910474518862807618097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71463880632691817076824129 53597910474518862807618097)
        ·
          refine ⟨40198432855889147105713573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53597910474518862807618097 40198432855889147105713573)
          ·
            refine ⟨7537206160479215082321295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40198432855889147105713573 7537206160479215082321295)
            ·
              refine ⟨11305809240718822623481943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537206160479215082321295 11305809240718822623481943)
              ·
                refine ⟨16958713861078233935222915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11305809240718822623481943 16958713861078233935222915)
                ·
                  refine ⟨25438070791617350902834373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16958713861078233935222915 25438070791617350902834373)
                  ·
                    refine ⟨4769638273428253294281445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25438070791617350902834373 4769638273428253294281445)
                    ·
                      refine ⟨894307176267797492677771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4769638273428253294281445 894307176267797492677771)
                      ·
                        rfl

theorem cell23_1741657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_1741657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741657 prefixEnd_1741657 := by exact prefixLift 1741657
  have htrace : WordTrace (prefixWord ++ tailWord_1741657) baseStart_1741657 baseEnd_1741657 := by
    simpa [prefixWord, tailWord_1741657, baseEnd_1741657] using wordTrace_append hprefix tailTrace_1741657
  have hstable : (prefixWord ++ tailWord_1741657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741657).length < 2 ^ (prefixWord ++ tailWord_1741657).sum := by decide
  have hdescent : baseEnd_1741657 < baseStart_1741657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741667 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 9]
def baseStart_1741667 : Nat := 118140960795 + 1741667 * 2 ^ 59
def prefixEnd_1741667 : Nat := 4983230072969 + 3 ^ 40 * 1741667 * 2
def baseEnd_1741667 : Nat := 99368034563815828172525

theorem tailTrace_1741667 : CollatzResearch.WordTrace tailWord_1741667 prefixEnd_1741667 99368034563815828172525 := by
  unfold tailWord_1741667
  simp only [CollatzResearch.WordTrace]
  refine ⟨63523814181245386887263255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42349209454163591258175503 63523814181245386887263255)
  ·
    refine ⟨95285721271868080330894883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63523814181245386887263255 95285721271868080330894883)
    ·
      refine ⟨142928581907802120496342325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95285721271868080330894883 142928581907802120496342325)
      ·
        refine ⟨13399554553856448796532093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142928581907802120496342325 13399554553856448796532093)
        ·
          refine ⟨5024832957696168298699535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13399554553856448796532093 5024832957696168298699535)
          ·
            refine ⟨7537249436544252448049303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024832957696168298699535 7537249436544252448049303)
            ·
              refine ⟨11305874154816378672073955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537249436544252448049303 11305874154816378672073955)
              ·
                refine ⟨16958811232224568008110933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11305874154816378672073955 16958811232224568008110933)
                ·
                  refine ⟨99368034563815828172525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16958811232224568008110933 99368034563815828172525)
                  ·
                    rfl

theorem cell23_1741667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 9].length) (baseStart_1741667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741667 prefixEnd_1741667 := by exact prefixLift 1741667
  have htrace : WordTrace (prefixWord ++ tailWord_1741667) baseStart_1741667 baseEnd_1741667 := by
    simpa [prefixWord, tailWord_1741667, baseEnd_1741667] using wordTrace_append hprefix tailTrace_1741667
  have hstable : (prefixWord ++ tailWord_1741667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741667).length < 2 ^ (prefixWord ++ tailWord_1741667).sum := by decide
  have hdescent : baseEnd_1741667 < baseStart_1741667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741677 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1741677 : Nat := 118140960795 + 1741677 * 2 ^ 59
def prefixEnd_1741677 : Nat := 4983230072969 + 3 ^ 40 * 1741677 * 2
def baseEnd_1741677 : Nat := 894317445880887414427679

theorem tailTrace_1741677 : CollatzResearch.WordTrace tailWord_1741677 prefixEnd_1741677 894317445880887414427679 := by
  unfold tailWord_1741677
  simp only [CollatzResearch.WordTrace]
  refine ⟨63524178911209158595127285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42349452607472772396751523 63524178911209158595127285)
  ·
    refine ⟨5955391772925858618293183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63524178911209158595127285 5955391772925858618293183)
    ·
      refine ⟨8933087659388787927439775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5955391772925858618293183 8933087659388787927439775)
      ·
        refine ⟨13399631489083181891159663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8933087659388787927439775 13399631489083181891159663)
        ·
          refine ⟨20099447233624772836739495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13399631489083181891159663 20099447233624772836739495)
          ·
            refine ⟨30149170850437159255109243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20099447233624772836739495 30149170850437159255109243)
            ·
              refine ⟨45223756275655738882663865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30149170850437159255109243 45223756275655738882663865)
              ·
                refine ⟨33917817206741804161997899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45223756275655738882663865 33917817206741804161997899)
                ·
                  refine ⟨50876725810112706242996849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33917817206741804161997899 50876725810112706242996849)
                  ·
                    refine ⟨38157544357584529682247637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50876725810112706242996849 38157544357584529682247637)
                    ·
                      refine ⟨894317445880887414427679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38157544357584529682247637 894317445880887414427679)
                      ·
                        rfl

theorem cell23_1741677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1741677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741677 prefixEnd_1741677 := by exact prefixLift 1741677
  have htrace : WordTrace (prefixWord ++ tailWord_1741677) baseStart_1741677 baseEnd_1741677 := by
    simpa [prefixWord, tailWord_1741677, baseEnd_1741677] using wordTrace_append hprefix tailTrace_1741677
  have hstable : (prefixWord ++ tailWord_1741677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741677).length < 2 ^ (prefixWord ++ tailWord_1741677).sum := by decide
  have hdescent : baseEnd_1741677 < baseStart_1741677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741707 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 5]
def baseStart_1741707 : Nat := 118140960795 + 1741707 * 2 ^ 59
def prefixEnd_1741707 : Nat := 4983230072969 + 3 ^ 40 * 1741707 * 2
def baseEnd_1741707 : Nat := 894332850300522297052541

theorem tailTrace_1741707 : CollatzResearch.WordTrace tailWord_1741707 prefixEnd_1741707 894332850300522297052541 := by
  unfold tailWord_1741707
  simp only [CollatzResearch.WordTrace]
  refine ⟨63525273101100473718719375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42350182067400315812479583 63525273101100473718719375)
  ·
    refine ⟨95287909651650710578079063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63525273101100473718719375 95287909651650710578079063)
    ·
      refine ⟨142931864477476065867118595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95287909651650710578079063 142931864477476065867118595)
      ·
        refine ⟨214397796716214098800677893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142931864477476065867118595 214397796716214098800677893)
        ·
          refine ⟨40199586884290143525127105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214397796716214098800677893 40199586884290143525127105)
          ·
            refine ⟨30149690163217607643845329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40199586884290143525127105 30149690163217607643845329)
            ·
              refine ⟨22612267622413205732883997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30149690163217607643845329 22612267622413205732883997)
              ·
                refine ⟨8479600358404952149831499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22612267622413205732883997 8479600358404952149831499)
                ·
                  refine ⟨12719400537607428224747249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8479600358404952149831499 12719400537607428224747249)
                  ·
                    refine ⟨9539550403205571168560437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12719400537607428224747249 9539550403205571168560437)
                    ·
                      refine ⟨894332850300522297052541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9539550403205571168560437 894332850300522297052541)
                      ·
                        rfl

theorem cell23_1741707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 5].length) (baseStart_1741707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741707 prefixEnd_1741707 := by exact prefixLift 1741707
  have htrace : WordTrace (prefixWord ++ tailWord_1741707) baseStart_1741707 baseEnd_1741707 := by
    simpa [prefixWord, tailWord_1741707, baseEnd_1741707] using wordTrace_append hprefix tailTrace_1741707
  have hstable : (prefixWord ++ tailWord_1741707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741707).length < 2 ^ (prefixWord ++ tailWord_1741707).sum := by decide
  have hdescent : baseEnd_1741707 < baseStart_1741707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741718 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1741718 : Nat := 118140960795 + 1741718 * 2 ^ 59
def prefixEnd_1741718 : Nat := 4983230072969 + 3 ^ 40 * 1741718 * 2
def baseEnd_1741718 : Nat := 99370944287524639334999

theorem tailTrace_1741718 : CollatzResearch.WordTrace tailWord_1741718 prefixEnd_1741718 99370944287524639334999 := by
  unfold tailWord_1741718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970354644003788912335613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42350449536040415064913205 3970354644003788912335613)
  ·
    refine ⟨1488882991501420842125855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3970354644003788912335613 1488882991501420842125855)
    ·
      refine ⟨2233324487252131263188783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488882991501420842125855 2233324487252131263188783)
      ·
        refine ⟨3349986730878196894783175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233324487252131263188783 3349986730878196894783175)
        ·
          refine ⟨5024980096317295342174763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3349986730878196894783175 5024980096317295342174763)
          ·
            refine ⟨7537470144475943013262145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024980096317295342174763 7537470144475943013262145)
            ·
              refine ⟨5653102608356957259946609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7537470144475943013262145 5653102608356957259946609)
              ·
                refine ⟨4239826956267717944959957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5653102608356957259946609 4239826956267717944959957)
                ·
                  refine ⟨99370944287524639334999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4239826956267717944959957 99370944287524639334999)
                  ·
                    rfl

theorem cell23_1741718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1741718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741718 prefixEnd_1741718 := by exact prefixLift 1741718
  have htrace : WordTrace (prefixWord ++ tailWord_1741718) baseStart_1741718 baseEnd_1741718 := by
    simpa [prefixWord, tailWord_1741718, baseEnd_1741718] using wordTrace_append hprefix tailTrace_1741718
  have hstable : (prefixWord ++ tailWord_1741718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741718).length < 2 ^ (prefixWord ++ tailWord_1741718).sum := by decide
  have hdescent : baseEnd_1741718 < baseStart_1741718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741735 : List Nat := [1, 1, 6, 1, 4, 1, 1, 3, 5]
def baseStart_1741735 : Nat := 118140960795 + 1741735 * 2 ^ 59
def prefixEnd_1741735 : Nat := 4983230072969 + 3 ^ 40 * 1741735 * 2
def baseEnd_1741735 : Nat := 99371914195427576389157

theorem tailTrace_1741735 : CollatzResearch.WordTrace tailWord_1741735 prefixEnd_1741735 99371914195427576389157 := by
  unfold tailWord_1741735
  simp only [CollatzResearch.WordTrace]
  refine ⟨63526294344999034500738659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42350862896666023000492439 63526294344999034500738659)
  ·
    refine ⟨95289441517498551751107989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63526294344999034500738659 95289441517498551751107989)
    ·
      refine ⟨4466692571132744613333187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95289441517498551751107989 4466692571132744613333187)
      ·
        refine ⟨6700038856699116919999781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4466692571132744613333187 6700038856699116919999781)
        ·
          refine ⟨1256257285631084422499959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6700038856699116919999781 1256257285631084422499959)
          ·
            refine ⟨1884385928446626633749939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256257285631084422499959 1884385928446626633749939)
            ·
              refine ⟨2826578892669939950624909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884385928446626633749939 2826578892669939950624909)
              ·
                refine ⟨1059967084751227481484341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2826578892669939950624909 1059967084751227481484341)
                ·
                  refine ⟨99371914195427576389157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1059967084751227481484341 99371914195427576389157)
                  ·
                    rfl

theorem cell23_1741735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 5].length) (baseStart_1741735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741735 prefixEnd_1741735 := by exact prefixLift 1741735
  have htrace : WordTrace (prefixWord ++ tailWord_1741735) baseStart_1741735 baseEnd_1741735 := by
    simpa [prefixWord, tailWord_1741735, baseEnd_1741735] using wordTrace_append hprefix tailTrace_1741735
  have hstable : (prefixWord ++ tailWord_1741735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741735).length < 2 ^ (prefixWord ++ tailWord_1741735).sum := by decide
  have hdescent : baseEnd_1741735 < baseStart_1741735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741747 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 6]
def baseStart_1741747 : Nat := 118140960795 + 1741747 * 2 ^ 59
def prefixEnd_1741747 : Nat := 4983230072969 + 3 ^ 40 * 1741747 * 2
def baseEnd_1741747 : Nat := 894353389526702140552357

theorem tailTrace_1741747 : CollatzResearch.WordTrace tailWord_1741747 prefixEnd_1741747 894353389526702140552357 := by
  unfold tailWord_1741747
  simp only [CollatzResearch.WordTrace]
  refine ⟨63526732020955560550175495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42351154680637040366783663 63526732020955560550175495)
  ·
    refine ⟨95290098031433340825263243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63526732020955560550175495 95290098031433340825263243)
    ·
      refine ⟨142935147047150011237894865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95290098031433340825263243 142935147047150011237894865)
      ·
        refine ⟨107201360285362508428421149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142935147047150011237894865 107201360285362508428421149)
        ·
          refine ⟨40200510107010940660657931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107201360285362508428421149 40200510107010940660657931)
          ·
            refine ⟨60300765160516410990986897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40200510107010940660657931 60300765160516410990986897)
            ·
              refine ⟨45225573870387308243240173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60300765160516410990986897 45225573870387308243240173)
              ·
                refine ⟨16959590201395240591215065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45225573870387308243240173 16959590201395240591215065)
                ·
                  refine ⟨12719692651046430443411299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16959590201395240591215065 12719692651046430443411299)
                  ·
                    refine ⟨19079538976569645665116949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12719692651046430443411299 19079538976569645665116949)
                    ·
                      refine ⟨894353389526702140552357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19079538976569645665116949 894353389526702140552357)
                      ·
                        rfl

theorem cell23_1741747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_1741747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741747 prefixEnd_1741747 := by exact prefixLift 1741747
  have htrace : WordTrace (prefixWord ++ tailWord_1741747) baseStart_1741747 baseEnd_1741747 := by
    simpa [prefixWord, tailWord_1741747, baseEnd_1741747] using wordTrace_append hprefix tailTrace_1741747
  have hstable : (prefixWord ++ tailWord_1741747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741747).length < 2 ^ (prefixWord ++ tailWord_1741747).sum := by decide
  have hdescent : baseEnd_1741747 < baseStart_1741747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741748 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1741748 : Nat := 118140960795 + 1741748 * 2 ^ 59
def prefixEnd_1741748 : Nat := 4983230072969 + 3 ^ 40 * 1741748 * 2
def baseEnd_1741748 : Nat := 298117967669118878879951

theorem tailTrace_1741748 : CollatzResearch.WordTrace tailWord_1741748 prefixEnd_1741748 298117967669118878879951 := by
  unfold tailWord_1741748
  simp only [CollatzResearch.WordTrace]
  refine ⟨31763384246975968860480949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42351178995967958480641265 31763384246975968860480949)
  ·
    refine ⟨2977817273153997080670089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31763384246975968860480949 2977817273153997080670089)
    ·
      refine ⟨2233362954865497810502567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2977817273153997080670089 2233362954865497810502567)
      ·
        refine ⟨3350044432298246715753851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233362954865497810502567 3350044432298246715753851)
        ·
          refine ⟨5025066648447370073630777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3350044432298246715753851 5025066648447370073630777)
          ·
            refine ⟨3768799986335527555223083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5025066648447370073630777 3768799986335527555223083)
            ·
              refine ⟨5653199979503291332834625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3768799986335527555223083 5653199979503291332834625)
              ·
                refine ⟨4239899984627468499625969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5653199979503291332834625 4239899984627468499625969)
                ·
                  refine ⟨3179924988470601374719477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4239899984627468499625969 3179924988470601374719477)
                  ·
                    refine ⟨298117967669118878879951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3179924988470601374719477 298117967669118878879951)
                    ·
                      rfl

theorem cell23_1741748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1741748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741748 prefixEnd_1741748 := by exact prefixLift 1741748
  have htrace : WordTrace (prefixWord ++ tailWord_1741748) baseStart_1741748 baseEnd_1741748 := by
    simpa [prefixWord, tailWord_1741748, baseEnd_1741748] using wordTrace_append hprefix tailTrace_1741748
  have hstable : (prefixWord ++ tailWord_1741748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741748).length < 2 ^ (prefixWord ++ tailWord_1741748).sum := by decide
  have hdescent : baseEnd_1741748 < baseStart_1741748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741845 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 2, 3, 2]
def baseStart_1741845 : Nat := 118140960795 + 1741845 * 2 ^ 59
def prefixEnd_1741845 : Nat := 4983230072969 + 3 ^ 40 * 1741845 * 2
def baseEnd_1741845 : Nat := 894403710630842757126907

theorem tailTrace_1741845 : CollatzResearch.WordTrace tailWord_1741845 prefixEnd_1741845 894403710630842757126907 := by
  unfold tailWord_1741845
  simp only [CollatzResearch.WordTrace]
  refine ⟨63530306374600523287242989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42353537583067015524828659 63530306374600523287242989)
  ·
    refine ⟨23823864890475196232716121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63530306374600523287242989 23823864890475196232716121)
    ·
      refine ⟨17867898667856397174537091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23823864890475196232716121 17867898667856397174537091)
      ·
        refine ⟨26801848001784595761805637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17867898667856397174537091 26801848001784595761805637)
        ·
          refine ⟨5025346500334611705338557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26801848001784595761805637 5025346500334611705338557)
          ·
            refine ⟨1884504937625479389501959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5025346500334611705338557 1884504937625479389501959)
            ·
              refine ⟨2826757406438219084252939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884504937625479389501959 2826757406438219084252939)
              ·
                refine ⟨4240136109657328626379409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826757406438219084252939 4240136109657328626379409)
                ·
                  refine ⟨3180102082242996469784557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4240136109657328626379409 3180102082242996469784557)
                  ·
                    refine ⟨1192538280841123676169209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180102082242996469784557 1192538280841123676169209)
                    ·
                      refine ⟨894403710630842757126907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192538280841123676169209 894403710630842757126907)
                      ·
                        rfl

theorem cell23_1741845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_1741845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741845 prefixEnd_1741845 := by exact prefixLift 1741845
  have htrace : WordTrace (prefixWord ++ tailWord_1741845) baseStart_1741845 baseEnd_1741845 := by
    simpa [prefixWord, tailWord_1741845, baseEnd_1741845] using wordTrace_append hprefix tailTrace_1741845
  have hstable : (prefixWord ++ tailWord_1741845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741845).length < 2 ^ (prefixWord ++ tailWord_1741845).sum := by decide
  have hdescent : baseEnd_1741845 < baseStart_1741845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741852 : List Nat := [2, 2, 3, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_1741852 : Nat := 118140960795 + 1741852 * 2 ^ 59
def prefixEnd_1741852 : Nat := 4983230072969 + 3 ^ 40 * 1741852 * 2
def baseEnd_1741852 : Nat := 894407304995424229739375

theorem tailTrace_1741852 : CollatzResearch.WordTrace tailWord_1741852 prefixEnd_1741852 894407304995424229739375 := by
  unfold tailWord_1741852
  simp only [CollatzResearch.WordTrace]
  refine ⟨31765280842787581741373905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42353707790383442321831873 31765280842787581741373905)
  ·
    refine ⟨23823960632090686306030429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31765280842787581741373905 23823960632090686306030429)
    ·
      refine ⟨8933985237034007364761411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23823960632090686306030429 8933985237034007364761411)
      ·
        refine ⟨13400977855551011047142117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8933985237034007364761411 13400977855551011047142117)
        ·
          refine ⟨2512683347915814571339147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13400977855551011047142117 2512683347915814571339147)
          ·
            refine ⟨3769025021873721857008721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512683347915814571339147 3769025021873721857008721)
            ·
              refine ⟨2826768766405291392756541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769025021873721857008721 2826768766405291392756541)
              ·
                refine ⟨1060038287401984272283703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2826768766405291392756541 1060038287401984272283703)
                ·
                  refine ⟨1590057431102976408425555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060038287401984272283703 1590057431102976408425555)
                  ·
                    refine ⟨2385086146654464612638333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1590057431102976408425555 2385086146654464612638333)
                    ·
                      refine ⟨894407304995424229739375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2385086146654464612638333 894407304995424229739375)
                      ·
                        rfl

theorem cell23_1741852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_1741852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741852 prefixEnd_1741852 := by exact prefixLift 1741852
  have htrace : WordTrace (prefixWord ++ tailWord_1741852) baseStart_1741852 baseEnd_1741852 := by
    simpa [prefixWord, tailWord_1741852, baseEnd_1741852] using wordTrace_append hprefix tailTrace_1741852
  have hstable : (prefixWord ++ tailWord_1741852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741852).length < 2 ^ (prefixWord ++ tailWord_1741852).sum := by decide
  have hdescent : baseEnd_1741852 < baseStart_1741852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741858 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_1741858 : Nat := 118140960795 + 1741858 * 2 ^ 59
def prefixEnd_1741858 : Nat := 4983230072969 + 3 ^ 40 * 1741858 * 2
def baseEnd_1741858 : Nat := 894410385879351206264347

theorem tailTrace_1741858 : CollatzResearch.WordTrace tailWord_1741858 prefixEnd_1741858 894410385879351206264347 := by
  unfold tailWord_1741858
  simp only [CollatzResearch.WordTrace]
  refine ⟨15882695130888356626866557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42353853682368951004977485 15882695130888356626866557)
  ·
    refine ⟨5956010674083133735074959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15882695130888356626866557 5956010674083133735074959)
    ·
      refine ⟨8934016011124700602612439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5956010674083133735074959 8934016011124700602612439)
      ·
        refine ⟨13401024016687050903918659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8934016011124700602612439 13401024016687050903918659)
        ·
          refine ⟨20101536025030576355877989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13401024016687050903918659 20101536025030576355877989)
          ·
            refine ⟨3769038004693233066727123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20101536025030576355877989 3769038004693233066727123)
            ·
              refine ⟨5653557007039849600090685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769038004693233066727123 5653557007039849600090685)
              ·
                refine ⟨2120083877639943600034007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5653557007039849600090685 2120083877639943600034007)
                ·
                  refine ⟨3180125816459915400051011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120083877639943600034007 3180125816459915400051011)
                  ·
                    refine ⟨4770188724689873100076517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3180125816459915400051011 4770188724689873100076517)
                    ·
                      refine ⟨894410385879351206264347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4770188724689873100076517 894410385879351206264347)
                      ·
                        rfl

theorem cell23_1741858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_1741858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741858 prefixEnd_1741858 := by exact prefixLift 1741858
  have htrace : WordTrace (prefixWord ++ tailWord_1741858) baseStart_1741858 baseEnd_1741858 := by
    simpa [prefixWord, tailWord_1741858, baseEnd_1741858] using wordTrace_append hprefix tailTrace_1741858
  have hstable : (prefixWord ++ tailWord_1741858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741858).length < 2 ^ (prefixWord ++ tailWord_1741858).sum := by decide
  have hdescent : baseEnd_1741858 < baseStart_1741858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741878 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1741878 : Nat := 118140960795 + 1741878 * 2 ^ 59
def prefixEnd_1741878 : Nat := 4983230072969 + 3 ^ 40 * 1741878 * 2
def baseEnd_1741878 : Nat := 894420655492441128014255

theorem tailTrace_1741878 : CollatzResearch.WordTrace tailWord_1741878 prefixEnd_1741878 894420655492441128014255 := by
  unfold tailWord_1741878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970719373967560620199643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42354339988987313282129525 3970719373967560620199643)
  ·
    refine ⟨5956079060951340930299465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3970719373967560620199643 5956079060951340930299465)
    ·
      refine ⟨4467059295713505697724599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5956079060951340930299465 4467059295713505697724599)
      ·
        refine ⟨6700588943570258546586899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467059295713505697724599 6700588943570258546586899)
        ·
          refine ⟨10050883415355387819880349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6700588943570258546586899 10050883415355387819880349)
          ·
            refine ⟨3769081280758270432455131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10050883415355387819880349 3769081280758270432455131)
            ·
              refine ⟨5653621921137405648682697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769081280758270432455131 5653621921137405648682697)
              ·
                refine ⟨4240216440853054236512023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5653621921137405648682697 4240216440853054236512023)
                ·
                  refine ⟨6360324661279581354768035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240216440853054236512023 6360324661279581354768035)
                  ·
                    refine ⟨9540486991919372032152053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6360324661279581354768035 9540486991919372032152053)
                    ·
                      refine ⟨894420655492441128014255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9540486991919372032152053 894420655492441128014255)
                      ·
                        rfl

theorem cell23_1741878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1741878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741878 prefixEnd_1741878 := by exact prefixLift 1741878
  have htrace : WordTrace (prefixWord ++ tailWord_1741878) baseStart_1741878 baseEnd_1741878 := by
    simpa [prefixWord, tailWord_1741878, baseEnd_1741878] using wordTrace_append hprefix tailTrace_1741878
  have hstable : (prefixWord ++ tailWord_1741878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741878).length < 2 ^ (prefixWord ++ tailWord_1741878).sum := by decide
  have hdescent : baseEnd_1741878 < baseStart_1741878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741885 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_1741885 : Nat := 118140960795 + 1741885 * 2 ^ 59
def prefixEnd_1741885 : Nat := 4983230072969 + 3 ^ 40 * 1741885 * 2
def baseEnd_1741885 : Nat := 298141416619007533542241

theorem tailTrace_1741885 : CollatzResearch.WordTrace tailWord_1741885 prefixEnd_1741885 298141416619007533542241 := by
  unfold tailWord_1741885
  simp only [CollatzResearch.WordTrace]
  refine ⟨63531765294455610118699109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42354510196303740079132739 63531765294455610118699109)
  ·
    refine ⟨11912205992710426897256083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63531765294455610118699109 11912205992710426897256083)
    ·
      refine ⟨17868308989065640345884125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11912205992710426897256083 17868308989065640345884125)
      ·
        refine ⟨6700615870899615129706547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17868308989065640345884125 6700615870899615129706547)
        ·
          refine ⟨10050923806349422694559821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6700615870899615129706547 10050923806349422694559821)
          ·
            refine ⟨3769096427381033510459933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10050923806349422694559821 3769096427381033510459933)
            ·
              refine ⟨1413411160267887566422475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3769096427381033510459933 1413411160267887566422475)
              ·
                refine ⟨2120116740401831349633713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413411160267887566422475 2120116740401831349633713)
                ·
                  refine ⟨1590087555301373512225285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2120116740401831349633713 1590087555301373512225285)
                  ·
                    refine ⟨298141416619007533542241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1590087555301373512225285 298141416619007533542241)
                    ·
                      rfl

theorem cell23_1741885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_1741885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741885 prefixEnd_1741885 := by exact prefixLift 1741885
  have htrace : WordTrace (prefixWord ++ tailWord_1741885) baseStart_1741885 baseEnd_1741885 := by
    simpa [prefixWord, tailWord_1741885, baseEnd_1741885] using wordTrace_append hprefix tailTrace_1741885
  have hstable : (prefixWord ++ tailWord_1741885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741885).length < 2 ^ (prefixWord ++ tailWord_1741885).sum := by decide
  have hdescent : baseEnd_1741885 < baseStart_1741885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741908 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_1741908 : Nat := 118140960795 + 1741908 * 2 ^ 59
def prefixEnd_1741908 : Nat := 4983230072969 + 3 ^ 40 * 1741908 * 2
def baseEnd_1741908 : Nat := 894436059912076010639117

theorem tailTrace_1741908 : CollatzResearch.WordTrace tailWord_1741908 prefixEnd_1741908 894436059912076010639117 := by
  unfold tailWord_1741908
  simp only [CollatzResearch.WordTrace]
  refine ⟨31766302086686142523393189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42355069448914856697857585 31766302086686142523393189)
  ·
    refine ⟨5956181641253651723136223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31766302086686142523393189 5956181641253651723136223)
    ·
      refine ⟨8934272461880477584704335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5956181641253651723136223 8934272461880477584704335)
      ·
        refine ⟨13401408692820716377056503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8934272461880477584704335 13401408692820716377056503)
        ·
          refine ⟨20102113039231074565584755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13401408692820716377056503 20102113039231074565584755)
          ·
            refine ⟨30153169558846611848377133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20102113039231074565584755 30153169558846611848377133)
            ·
              refine ⟨11307438584567479443141425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30153169558846611848377133 11307438584567479443141425)
              ·
                refine ⟨8480578938425609582356069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11307438584567479443141425 8480578938425609582356069)
                ·
                  refine ⟨1590108550954801796691763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8480578938425609582356069 1590108550954801796691763)
                  ·
                    refine ⟨2385162826432202695037645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1590108550954801796691763 2385162826432202695037645)
                    ·
                      refine ⟨894436059912076010639117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2385162826432202695037645 894436059912076010639117)
                      ·
                        rfl

theorem cell23_1741908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_1741908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741908 prefixEnd_1741908 := by exact prefixLift 1741908
  have htrace : WordTrace (prefixWord ++ tailWord_1741908) baseStart_1741908 baseEnd_1741908 := by
    simpa [prefixWord, tailWord_1741908, baseEnd_1741908] using wordTrace_append hprefix tailTrace_1741908
  have hstable : (prefixWord ++ tailWord_1741908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741908).length < 2 ^ (prefixWord ++ tailWord_1741908).sum := by decide
  have hdescent : baseEnd_1741908 < baseStart_1741908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741948 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 1, 4, 2]
def baseStart_1741948 : Nat := 118140960795 + 1741948 * 2 ^ 59
def prefixEnd_1741948 : Nat := 4983230072969 + 3 ^ 40 * 1741948 * 2
def baseEnd_1741948 : Nat := 894456599138255854138933

theorem tailTrace_1741948 : CollatzResearch.WordTrace tailWord_1741948 prefixEnd_1741948 894456599138255854138933 := by
  unfold tailWord_1741948
  simp only [CollatzResearch.WordTrace]
  refine ⟨31767031546613685939121249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42356042062151581252161665 31767031546613685939121249)
  ·
    refine ⟨23825273659960264454340937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31767031546613685939121249 23825273659960264454340937)
    ·
      refine ⟨17868955244970198340755703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23825273659960264454340937 17868955244970198340755703)
      ·
        refine ⟨26803432867455297511133555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17868955244970198340755703 26803432867455297511133555)
        ·
          refine ⟨40205149301182946266700333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26803432867455297511133555 40205149301182946266700333)
          ·
            refine ⟨15076930987943604850012625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40205149301182946266700333 15076930987943604850012625)
            ·
              refine ⟨11307698240957703637509469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15076930987943604850012625 11307698240957703637509469)
              ·
                refine ⟨4240386840359138864066051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11307698240957703637509469 4240386840359138864066051)
                ·
                  refine ⟨6360580260538708296099077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240386840359138864066051 6360580260538708296099077)
                  ·
                    refine ⟨1192608798851007805518577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6360580260538708296099077 1192608798851007805518577)
                    ·
                      refine ⟨894456599138255854138933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192608798851007805518577 894456599138255854138933)
                      ·
                        rfl

theorem cell23_1741948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_1741948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1741948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1741948 prefixEnd_1741948 := by exact prefixLift 1741948
  have htrace : WordTrace (prefixWord ++ tailWord_1741948) baseStart_1741948 baseEnd_1741948 := by
    simpa [prefixWord, tailWord_1741948, baseEnd_1741948] using wordTrace_append hprefix tailTrace_1741948
  have hstable : (prefixWord ++ tailWord_1741948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741948).length < 2 ^ (prefixWord ++ tailWord_1741948).sum := by decide
  have hdescent : baseEnd_1741948 < baseStart_1741948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742048 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 3, 4]
def baseStart_1742048 : Nat := 118140960795 + 1742048 * 2 ^ 59
def prefixEnd_1742048 : Nat := 4983230072969 + 3 ^ 40 * 1742048 * 2
def baseEnd_1742048 : Nat := 298169315734568487629491

theorem tailTrace_1742048 : CollatzResearch.WordTrace tailWord_1742048 prefixEnd_1742048 298169315734568487629491 := by
  unfold tailWord_1742048
  simp only [CollatzResearch.WordTrace]
  refine ⟨31768855196432544478441399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42358473595243392637921865 31768855196432544478441399)
  ·
    refine ⟨47653282794648816717662099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31768855196432544478441399 47653282794648816717662099)
    ·
      refine ⟨71479924191973225076493149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47653282794648816717662099 71479924191973225076493149)
      ·
        refine ⟨26804971571989959403684931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71479924191973225076493149 26804971571989959403684931)
        ·
          refine ⟨40207457357984939105527397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26804971571989959403684931 40207457357984939105527397)
          ·
            refine ⟨7538898254622176082286387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40207457357984939105527397 7538898254622176082286387)
            ·
              refine ⟨11308347381933264123429581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538898254622176082286387 11308347381933264123429581)
              ·
                refine ⟨4240630268224974046286093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11308347381933264123429581 4240630268224974046286093)
                ·
                  refine ⟨1590236350584365267357285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4240630268224974046286093 1590236350584365267357285)
                  ·
                    refine ⟨298169315734568487629491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1590236350584365267357285 298169315734568487629491)
                    ·
                      rfl

theorem cell23_1742048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3, 4].length) (baseStart_1742048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742048 prefixEnd_1742048 := by exact prefixLift 1742048
  have htrace : WordTrace (prefixWord ++ tailWord_1742048) baseStart_1742048 baseEnd_1742048 := by
    simpa [prefixWord, tailWord_1742048, baseEnd_1742048] using wordTrace_append hprefix tailTrace_1742048
  have hstable : (prefixWord ++ tailWord_1742048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742048).length < 2 ^ (prefixWord ++ tailWord_1742048).sum := by decide
  have hdescent : baseEnd_1742048 < baseStart_1742048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742058 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_1742058 : Nat := 118140960795 + 1742058 * 2 ^ 59
def prefixEnd_1742058 : Nat := 4983230072969 + 3 ^ 40 * 1742058 * 2
def baseEnd_1742058 : Nat := 894513082010250423763427

theorem tailTrace_1742058 : CollatzResearch.WordTrace tailWord_1742058 prefixEnd_1742058 894513082010250423763427 := by
  unfold tailWord_1742058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15884518780707215166186707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42358716748552573776497885 15884518780707215166186707)
  ·
    refine ⟨23826778171060822749280061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15884518780707215166186707 23826778171060822749280061)
    ·
      refine ⟨8935041814147808530980023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23826778171060822749280061 8935041814147808530980023)
      ·
        refine ⟨13402562721221712796470035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8935041814147808530980023 13402562721221712796470035)
        ·
          refine ⟨20103844081832569194705053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13402562721221712796470035 20103844081832569194705053)
          ·
            refine ⟨7538941530687213448014395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20103844081832569194705053 7538941530687213448014395)
            ·
              refine ⟨11308412296030820172021593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538941530687213448014395 11308412296030820172021593)
              ·
                refine ⟨8481309222023115129016195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11308412296030820172021593 8481309222023115129016195)
                ·
                  refine ⟨12721963833034672693524293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8481309222023115129016195 12721963833034672693524293)
                  ·
                    refine ⟨2385368218694001130035805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12721963833034672693524293 2385368218694001130035805)
                    ·
                      refine ⟨894513082010250423763427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2385368218694001130035805 894513082010250423763427)
                      ·
                        rfl

theorem cell23_1742058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_1742058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742058 prefixEnd_1742058 := by exact prefixLift 1742058
  have htrace : WordTrace (prefixWord ++ tailWord_1742058) baseStart_1742058 baseEnd_1742058 := by
    simpa [prefixWord, tailWord_1742058, baseEnd_1742058] using wordTrace_append hprefix tailTrace_1742058
  have hstable : (prefixWord ++ tailWord_1742058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742058).length < 2 ^ (prefixWord ++ tailWord_1742058).sum := by decide
  have hdescent : baseEnd_1742058 < baseStart_1742058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742078 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_1742078 : Nat := 118140960795 + 1742078 * 2 ^ 59
def prefixEnd_1742078 : Nat := 4983230072969 + 3 ^ 40 * 1742078 * 2
def baseEnd_1742078 : Nat := 99391483513704482834815

theorem tailTrace_1742078 : CollatzResearch.WordTrace tailWord_1742078 prefixEnd_1742078 99391483513704482834815 := by
  unfold tailWord_1742078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942350572844550510059361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42359203055170936053649925 7942350572844550510059361)
  ·
    refine ⟨5956762929633412882544521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7942350572844550510059361 5956762929633412882544521)
    ·
      refine ⟨4467572197225059661908391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5956762929633412882544521 4467572197225059661908391)
      ·
        refine ⟨6701358295837589492862587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467572197225059661908391 6701358295837589492862587)
        ·
          refine ⟨10052037443756384239293881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701358295837589492862587 10052037443756384239293881)
          ·
            refine ⟨7539028082817288179470411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10052037443756384239293881 7539028082817288179470411)
            ·
              refine ⟨11308542124225932269205617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7539028082817288179470411 11308542124225932269205617)
              ·
                refine ⟨8481406593169449201904213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11308542124225932269205617 8481406593169449201904213)
                ·
                  refine ⟨99391483513704482834815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8481406593169449201904213 99391483513704482834815)
                  ·
                    rfl

theorem cell23_1742078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_1742078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742078 prefixEnd_1742078 := by exact prefixLift 1742078
  have htrace : WordTrace (prefixWord ++ tailWord_1742078) baseStart_1742078 baseEnd_1742078 := by
    simpa [prefixWord, tailWord_1742078, baseEnd_1742078] using wordTrace_append hprefix tailTrace_1742078
  have hstable : (prefixWord ++ tailWord_1742078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742078).length < 2 ^ (prefixWord ++ tailWord_1742078).sum := by decide
  have hdescent : baseEnd_1742078 < baseStart_1742078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742101 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_1742101 : Nat := 118140960795 + 1742101 * 2 ^ 59
def prefixEnd_1742101 : Nat := 4983230072969 + 3 ^ 40 * 1742101 * 2
def baseEnd_1742101 : Nat := 894535161678393755525729

theorem tailTrace_1742101 : CollatzResearch.WordTrace tailWord_1742101 prefixEnd_1742101 894535161678393755525729 := by
  unfold tailWord_1742101
  simp only [CollatzResearch.WordTrace]
  refine ⟨63539643461673079008562157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42359762307782052672374771 63539643461673079008562157)
  ·
    refine ⟨23827366298127404628210809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63539643461673079008562157 23827366298127404628210809)
    ·
      refine ⟨17870524723595553471158107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23827366298127404628210809 17870524723595553471158107)
      ·
        refine ⟨26805787085393330206737161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17870524723595553471158107 26805787085393330206737161)
        ·
          refine ⟨20104340314044997655052871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26805787085393330206737161 20104340314044997655052871)
          ·
            refine ⟨30156510471067496482579307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20104340314044997655052871 30156510471067496482579307)
            ·
              refine ⟨45234765706601244723868961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30156510471067496482579307 45234765706601244723868961)
              ·
                refine ⟨33926074279950933542901721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45234765706601244723868961 33926074279950933542901721)
                ·
                  refine ⟨25444555709963200157176291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33926074279950933542901721 25444555709963200157176291)
                  ·
                    refine ⟨38166833564944800235764437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25444555709963200157176291 38166833564944800235764437)
                    ·
                      refine ⟨894535161678393755525729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38166833564944800235764437 894535161678393755525729)
                      ·
                        rfl

theorem cell23_1742101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_1742101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742101 prefixEnd_1742101 := by exact prefixLift 1742101
  have htrace : WordTrace (prefixWord ++ tailWord_1742101) baseStart_1742101 baseEnd_1742101 := by
    simpa [prefixWord, tailWord_1742101, baseEnd_1742101] using wordTrace_append hprefix tailTrace_1742101
  have hstable : (prefixWord ++ tailWord_1742101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742101).length < 2 ^ (prefixWord ++ tailWord_1742101).sum := by decide
  have hdescent : baseEnd_1742101 < baseStart_1742101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742112 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 6]
def baseStart_1742112 : Nat := 118140960795 + 1742112 * 2 ^ 59
def prefixEnd_1742112 : Nat := 4983230072969 + 3 ^ 40 * 1742112 * 2
def baseEnd_1742112 : Nat := 99393423329510356943131

theorem tailTrace_1742112 : CollatzResearch.WordTrace tailWord_1742112 prefixEnd_1742112 99393423329510356943131 := by
  unfold tailWord_1742112
  simp only [CollatzResearch.WordTrace]
  refine ⟨31770022332316613943606295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42360029776422151924808393 31770022332316613943606295)
  ·
    refine ⟨47655033498474920915409443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31770022332316613943606295 47655033498474920915409443)
    ·
      refine ⟨71482550247712381373114165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47655033498474920915409443 71482550247712381373114165)
      ·
        refine ⟨6701489085723035753729453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71482550247712381373114165 6701489085723035753729453)
        ·
          refine ⟨2513058407146138407648545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6701489085723035753729453 2513058407146138407648545)
          ·
            refine ⟨1884793805359603805736409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513058407146138407648545 1884793805359603805736409)
            ·
              refine ⟨1413595354019702854302307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884793805359603805736409 1413595354019702854302307)
              ·
                refine ⟨2120393031029554281453461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413595354019702854302307 2120393031029554281453461)
                ·
                  refine ⟨99393423329510356943131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2120393031029554281453461 99393423329510356943131)
                  ·
                    rfl

theorem cell23_1742112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 6].length) (baseStart_1742112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742112 prefixEnd_1742112 := by exact prefixLift 1742112
  have htrace : WordTrace (prefixWord ++ tailWord_1742112) baseStart_1742112 baseEnd_1742112 := by
    simpa [prefixWord, tailWord_1742112, baseEnd_1742112] using wordTrace_append hprefix tailTrace_1742112
  have hstable : (prefixWord ++ tailWord_1742112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742112).length < 2 ^ (prefixWord ++ tailWord_1742112).sum := by decide
  have hdescent : baseEnd_1742112 < baseStart_1742112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742128 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 4]
def baseStart_1742128 : Nat := 118140960795 + 1742128 * 2 ^ 59
def prefixEnd_1742128 : Nat := 4983230072969 + 3 ^ 40 * 1742128 * 2
def baseEnd_1742128 : Nat := 894549025656065149888105

theorem tailTrace_1742128 : CollatzResearch.WordTrace tailWord_1742128 prefixEnd_1742128 894549025656065149888105 := by
  unfold tailWord_1742128
  simp only [CollatzResearch.WordTrace]
  refine ⟨31770314116287631309897519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42360418821716841746530025 31770314116287631309897519)
  ·
    refine ⟨47655471174431446964846279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31770314116287631309897519 47655471174431446964846279)
    ·
      refine ⟨71483206761647170447269419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47655471174431446964846279 71483206761647170447269419)
      ·
        refine ⟨107224810142470755670904129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71483206761647170447269419 107224810142470755670904129)
        ·
          refine ⟨80418607606853066753178097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107224810142470755670904129 80418607606853066753178097)
          ·
            refine ⟨60313955705139800064883573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80418607606853066753178097 60313955705139800064883573)
            ·
              refine ⟨5654433347356856256082835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60313955705139800064883573 5654433347356856256082835)
              ·
                refine ⟨8481650021035284384124253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5654433347356856256082835 8481650021035284384124253)
                ·
                  refine ⟨3180618757888231644046595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8481650021035284384124253 3180618757888231644046595)
                  ·
                    refine ⟨4770928136832347466069893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3180618757888231644046595 4770928136832347466069893)
                    ·
                      refine ⟨894549025656065149888105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4770928136832347466069893 894549025656065149888105)
                      ·
                        rfl

theorem cell23_1742128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_1742128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742128 prefixEnd_1742128 := by exact prefixLift 1742128
  have htrace : WordTrace (prefixWord ++ tailWord_1742128) baseStart_1742128 baseEnd_1742128 := by
    simpa [prefixWord, tailWord_1742128, baseEnd_1742128] using wordTrace_append hprefix tailTrace_1742128
  have hstable : (prefixWord ++ tailWord_1742128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742128).length < 2 ^ (prefixWord ++ tailWord_1742128).sum := by decide
  have hdescent : baseEnd_1742128 < baseStart_1742128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742138 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_1742138 : Nat := 118140960795 + 1742138 * 2 ^ 59
def prefixEnd_1742138 : Nat := 4983230072969 + 3 ^ 40 * 1742138 * 2
def baseEnd_1742138 : Nat := 298184720154203370254353

theorem tailTrace_1742138 : CollatzResearch.WordTrace tailWord_1742138 prefixEnd_1742138 298184720154203370254353 := by
  unfold tailWord_1742138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15885248240634758581914767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42360661975026022885106045 15885248240634758581914767)
  ·
    refine ⟨23827872360952137872872151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15885248240634758581914767 23827872360952137872872151)
    ·
      refine ⟨35741808541428206809308227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23827872360952137872872151 35741808541428206809308227)
      ·
        refine ⟨53612712812142310213962341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35741808541428206809308227 53612712812142310213962341)
        ·
          refine ⟨10052383652276683165117939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53612712812142310213962341 10052383652276683165117939)
          ·
            refine ⟨15078575478415024747676909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10052383652276683165117939 15078575478415024747676909)
            ·
              refine ⟨5654465804405634280378841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15078575478415024747676909 5654465804405634280378841)
              ·
                refine ⟨4240849353304225710284131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5654465804405634280378841 4240849353304225710284131)
                ·
                  refine ⟨6361274029956338565426197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240849353304225710284131 6361274029956338565426197)
                  ·
                    refine ⟨298184720154203370254353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6361274029956338565426197 298184720154203370254353)
                    ·
                      rfl

theorem cell23_1742138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_1742138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742138 prefixEnd_1742138 := by exact prefixLift 1742138
  have htrace : WordTrace (prefixWord ++ tailWord_1742138) baseStart_1742138 baseEnd_1742138 := by
    simpa [prefixWord, tailWord_1742138, baseEnd_1742138] using wordTrace_append hprefix tailTrace_1742138
  have hstable : (prefixWord ++ tailWord_1742138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742138).length < 2 ^ (prefixWord ++ tailWord_1742138).sum := by decide
  have hdescent : baseEnd_1742138 < baseStart_1742138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742142 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1742142 : Nat := 118140960795 + 1742142 * 2 ^ 59
def prefixEnd_1742142 : Nat := 4983230072969 + 3 ^ 40 * 1742142 * 2
def baseEnd_1742142 : Nat := 298185404795076031704347

theorem tailTrace_1742142 : CollatzResearch.WordTrace tailWord_1742142 prefixEnd_1742142 298185404795076031704347 := by
  unfold tailWord_1742142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942642356815567876350585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42360759236349695340536453 7942642356815567876350585)
  ·
    refine ⟨5956981767611675907262939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7942642356815567876350585 5956981767611675907262939)
    ·
      refine ⟨8935472651417513860894409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5956981767611675907262939 8935472651417513860894409)
      ·
        refine ⟨6701604488563135395670807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8935472651417513860894409 6701604488563135395670807)
        ·
          refine ⟨10052406732844703093506211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701604488563135395670807 10052406732844703093506211)
          ·
            refine ⟨15078610099267054640259317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10052406732844703093506211 15078610099267054640259317)
            ·
              refine ⟨1413619696806286372524311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15078610099267054640259317 1413619696806286372524311)
              ·
                refine ⟨2120429545209429558786467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413619696806286372524311 2120429545209429558786467)
                ·
                  refine ⟨3180644317814144338179701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120429545209429558786467 3180644317814144338179701)
                  ·
                    refine ⟨298185404795076031704347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3180644317814144338179701 298185404795076031704347)
                    ·
                      rfl

theorem cell23_1742142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1742142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742142 prefixEnd_1742142 := by exact prefixLift 1742142
  have htrace : WordTrace (prefixWord ++ tailWord_1742142) baseStart_1742142 baseEnd_1742142 := by
    simpa [prefixWord, tailWord_1742142, baseEnd_1742142] using wordTrace_append hprefix tailTrace_1742142
  have hstable : (prefixWord ++ tailWord_1742142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742142).length < 2 ^ (prefixWord ++ tailWord_1742142).sum := by decide
  have hdescent : baseEnd_1742142 < baseStart_1742142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742150 : List Nat := [6, 1, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1742150 : Nat := 118140960795 + 1742150 * 2 ^ 59
def prefixEnd_1742150 : Nat := 4983230072969 + 3 ^ 40 * 1742150 * 2
def baseEnd_1742150 : Nat := 298186774076821354604335

theorem tailTrace_1742150 : CollatzResearch.WordTrace tailWord_1742150 prefixEnd_1742150 298186774076821354604335 := by
  unfold tailWord_1742150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985669707452986261784247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42360953758997040251397269 1985669707452986261784247)
  ·
    refine ⟨2978504561179479392676371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1985669707452986261784247 2978504561179479392676371)
    ·
      refine ⟨4467756841769219089014557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978504561179479392676371 4467756841769219089014557)
      ·
        refine ⟨1675408815663457158380459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4467756841769219089014557 1675408815663457158380459)
        ·
          refine ⟨2513113223495185737570689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675408815663457158380459 2513113223495185737570689)
          ·
            refine ⟨1884834917621389303178017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513113223495185737570689 1884834917621389303178017)
            ·
              refine ⟨1413626188216041977383513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884834917621389303178017 1413626188216041977383513)
              ·
                refine ⟨1060219641162031483037635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413626188216041977383513 1060219641162031483037635)
                ·
                  refine ⟨1590329461743047224556453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060219641162031483037635 1590329461743047224556453)
                  ·
                    refine ⟨298186774076821354604335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1590329461743047224556453 298186774076821354604335)
                    ·
                      rfl

theorem cell23_1742150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1742150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742150 prefixEnd_1742150 := by exact prefixLift 1742150
  have htrace : WordTrace (prefixWord ++ tailWord_1742150) baseStart_1742150 baseEnd_1742150 := by
    simpa [prefixWord, tailWord_1742150, baseEnd_1742150] using wordTrace_append hprefix tailTrace_1742150
  have hstable : (prefixWord ++ tailWord_1742150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742150).length < 2 ^ (prefixWord ++ tailWord_1742150).sum := by decide
  have hdescent : baseEnd_1742150 < baseStart_1742150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742151 : List Nat := [1, 1, 4, 1, 2, 14]
def baseStart_1742151 : Nat := 118140960795 + 1742151 * 2 ^ 59
def prefixEnd_1742151 : Nat := 4983230072969 + 3 ^ 40 * 1742151 * 2
def baseEnd_1742151 : Nat := 3681320311568389135393

theorem tailTrace_1742151 : CollatzResearch.WordTrace tailWord_1742151 prefixEnd_1742151 3681320311568389135393 := by
  unfold tailWord_1742151
  simp only [CollatzResearch.WordTrace]
  refine ⟨63541467111491937547882307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42360978074327958365254871 63541467111491937547882307)
  ·
    refine ⟨95312200667237906321823461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63541467111491937547882307 95312200667237906321823461)
    ·
      refine ⟨17871037625107107435341899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95312200667237906321823461 17871037625107107435341899)
      ·
        refine ⟨26806556437660661153012849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17871037625107107435341899 26806556437660661153012849)
        ·
          refine ⟨20104917328245495864759637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26806556437660661153012849 20104917328245495864759637)
          ·
            refine ⟨3681320311568389135393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 20104917328245495864759637 3681320311568389135393)
            ·
              rfl

theorem cell23_1742151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 14].length) (baseStart_1742151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742151 prefixEnd_1742151 := by exact prefixLift 1742151
  have htrace : WordTrace (prefixWord ++ tailWord_1742151) baseStart_1742151 baseEnd_1742151 := by
    simpa [prefixWord, tailWord_1742151, baseEnd_1742151] using wordTrace_append hprefix tailTrace_1742151
  have hstable : (prefixWord ++ tailWord_1742151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742151).length < 2 ^ (prefixWord ++ tailWord_1742151).sum := by decide
  have hdescent : baseEnd_1742151 < baseStart_1742151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742156 : List Nat := [2, 2, 1, 3, 2, 4, 2, 2, 1, 1, 3]
def baseStart_1742156 : Nat := 118140960795 + 1742156 * 2 ^ 59
def prefixEnd_1742156 : Nat := 4983230072969 + 3 ^ 40 * 1742156 * 2
def baseEnd_1742156 : Nat := 894563403114391040337977

theorem tailTrace_1742156 : CollatzResearch.WordTrace tailWord_1742156 prefixEnd_1742156 894563403114391040337977 := by
  unfold tailWord_1742156
  simp only [CollatzResearch.WordTrace]
  refine ⟨31770824738236911700907161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42361099650982548934542881 31770824738236911700907161)
  ·
    refine ⟨23828118553677683775680371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31770824738236911700907161 23828118553677683775680371)
    ·
      refine ⟨35742177830516525663520557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23828118553677683775680371 35742177830516525663520557)
      ·
        refine ⟨13403316686443697123820209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35742177830516525663520557 13403316686443697123820209)
        ·
          refine ⟨10052487514832772842865157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13403316686443697123820209 10052487514832772842865157)
          ·
            refine ⟨1884841409031144908037217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10052487514832772842865157 1884841409031144908037217)
            ·
              refine ⟨1413631056773358681027913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884841409031144908037217 1413631056773358681027913)
              ·
                refine ⟨1060223292580019010770935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413631056773358681027913 1060223292580019010770935)
                ·
                  refine ⟨1590334938870028516156403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060223292580019010770935 1590334938870028516156403)
                  ·
                    refine ⟨2385502408305042774234605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1590334938870028516156403 2385502408305042774234605)
                    ·
                      refine ⟨894563403114391040337977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2385502408305042774234605 894563403114391040337977)
                      ·
                        rfl

theorem cell23_1742156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_1742156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742156 prefixEnd_1742156 := by exact prefixLift 1742156
  have htrace : WordTrace (prefixWord ++ tailWord_1742156) baseStart_1742156 baseEnd_1742156 := by
    simpa [prefixWord, tailWord_1742156, baseEnd_1742156] using wordTrace_append hprefix tailTrace_1742156
  have hstable : (prefixWord ++ tailWord_1742156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742156).length < 2 ^ (prefixWord ++ tailWord_1742156).sum := by decide
  have hdescent : baseEnd_1742156 < baseStart_1742156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742158 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_1742158 : Nat := 118140960795 + 1742158 * 2 ^ 59
def prefixEnd_1742158 : Nat := 4983230072969 + 3 ^ 40 * 1742158 * 2
def baseEnd_1742158 : Nat := 894564430075700032512967

theorem tailTrace_1742158 : CollatzResearch.WordTrace tailWord_1742158 prefixEnd_1742158 894564430075700032512967 := by
  unfold tailWord_1742158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942715302808322217923391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42361148281644385162258085 7942715302808322217923391)
  ·
    refine ⟨11914072954212483326885087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7942715302808322217923391 11914072954212483326885087)
    ·
      refine ⟨17871109431318724990327631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11914072954212483326885087 17871109431318724990327631)
      ·
        refine ⟨26806664146978087485491447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17871109431318724990327631 26806664146978087485491447)
        ·
          refine ⟨40209996220467131228237171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26806664146978087485491447 40209996220467131228237171)
          ·
            refine ⟨60314994330700696842355757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40209996220467131228237171 60314994330700696842355757)
            ·
              refine ⟨22618122874012761315883409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60314994330700696842355757 22618122874012761315883409)
              ·
                refine ⟨16963592155509570986912557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22618122874012761315883409 16963592155509570986912557)
                ·
                  refine ⟨6361347058316089120092209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16963592155509570986912557 6361347058316089120092209)
                  ·
                    refine ⟨4771010293737066840069157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6361347058316089120092209 4771010293737066840069157)
                    ·
                      refine ⟨894564430075700032512967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4771010293737066840069157 894564430075700032512967)
                      ·
                        rfl

theorem cell23_1742158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_1742158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742158 prefixEnd_1742158 := by exact prefixLift 1742158
  have htrace : WordTrace (prefixWord ++ tailWord_1742158) baseStart_1742158 baseEnd_1742158 := by
    simpa [prefixWord, tailWord_1742158, baseEnd_1742158] using wordTrace_append hprefix tailTrace_1742158
  have hstable : (prefixWord ++ tailWord_1742158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742158).length < 2 ^ (prefixWord ++ tailWord_1742158).sum := by decide
  have hdescent : baseEnd_1742158 < baseStart_1742158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742162 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_1742162 : Nat := 118140960795 + 1742162 * 2 ^ 59
def prefixEnd_1742162 : Nat := 4983230072969 + 3 ^ 40 * 1742162 * 2
def baseEnd_1742162 : Nat := 894566483998318016862949

theorem tailTrace_1742162 : CollatzResearch.WordTrace tailWord_1742162 prefixEnd_1742162 894566483998318016862949 := by
  unfold tailWord_1742162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15885467078613021606633185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42361245542968057617688493 15885467078613021606633185)
  ·
    refine ⟨11914100308959766204974889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15885467078613021606633185 11914100308959766204974889)
    ·
      refine ⟨8935575231719824653731167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11914100308959766204974889 8935575231719824653731167)
      ·
        refine ⟨13403362847579736980596751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8935575231719824653731167 13403362847579736980596751)
        ·
          refine ⟨20105044271369605470895127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13403362847579736980596751 20105044271369605470895127)
          ·
            refine ⟨30157566407054408206342691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20105044271369605470895127 30157566407054408206342691)
            ·
              refine ⟨45236349610581612309514037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30157566407054408206342691 45236349610581612309514037)
              ·
                refine ⟨4240907775992026154016941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45236349610581612309514037 4240907775992026154016941)
                ·
                  refine ⟨1590340415997009807756353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4240907775992026154016941 1590340415997009807756353)
                  ·
                    refine ⟨1192755311997757355817265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590340415997009807756353 1192755311997757355817265)
                    ·
                      refine ⟨894566483998318016862949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192755311997757355817265 894566483998318016862949)
                      ·
                        rfl

theorem cell23_1742162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_1742162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742162 prefixEnd_1742162 := by exact prefixLift 1742162
  have htrace : WordTrace (prefixWord ++ tailWord_1742162) baseStart_1742162 baseEnd_1742162 := by
    simpa [prefixWord, tailWord_1742162, baseEnd_1742162] using wordTrace_append hprefix tailTrace_1742162
  have hstable : (prefixWord ++ tailWord_1742162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742162).length < 2 ^ (prefixWord ++ tailWord_1742162).sum := by decide
  have hdescent : baseEnd_1742162 < baseStart_1742162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742165 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_1742165 : Nat := 118140960795 + 1742165 * 2 ^ 59
def prefixEnd_1742165 : Nat := 4983230072969 + 3 ^ 40 * 1742165 * 2
def baseEnd_1742165 : Nat := 894568024440281505125435

theorem tailTrace_1742165 : CollatzResearch.WordTrace tailWord_1742165 prefixEnd_1742165 894568024440281505125435 := by
  unfold tailWord_1742165
  simp only [CollatzResearch.WordTrace]
  refine ⟨63541977733441217938891949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42361318488960811959261299 63541977733441217938891949)
  ·
    refine ⟨23828241650040456727084481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63541977733441217938891949 23828241650040456727084481)
    ·
      refine ⟨17871181237530342545313361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23828241650040456727084481 17871181237530342545313361)
      ·
        refine ⟨13403385928147756908985021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17871181237530342545313361 13403385928147756908985021)
        ·
          refine ⟨5026269723055408840869383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13403385928147756908985021 5026269723055408840869383)
          ·
            refine ⟨7539404584583113261304075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5026269723055408840869383 7539404584583113261304075)
            ·
              refine ⟨11309106876874669891956113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7539404584583113261304075 11309106876874669891956113)
              ·
                refine ⟨8481830157656002418967085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11309106876874669891956113 8481830157656002418967085)
                ·
                  refine ⟨3180686309121000907112657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8481830157656002418967085 3180686309121000907112657)
                  ·
                    refine ⟨2385514731840750680334493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3180686309121000907112657 2385514731840750680334493)
                    ·
                      refine ⟨894568024440281505125435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2385514731840750680334493 894568024440281505125435)
                      ·
                        rfl

theorem cell23_1742165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_1742165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742165 prefixEnd_1742165 := by exact prefixLift 1742165
  have htrace : WordTrace (prefixWord ++ tailWord_1742165) baseStart_1742165 baseEnd_1742165 := by
    simpa [prefixWord, tailWord_1742165, baseEnd_1742165] using wordTrace_append hprefix tailTrace_1742165
  have hstable : (prefixWord ++ tailWord_1742165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742165).length < 2 ^ (prefixWord ++ tailWord_1742165).sum := by decide
  have hdescent : baseEnd_1742165 < baseStart_1742165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742212 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_1742212 : Nat := 118140960795 + 1742212 * 2 ^ 59
def prefixEnd_1742212 : Nat := 4983230072969 + 3 ^ 40 * 1742212 * 2
def baseEnd_1742212 : Nat := 894592158031042821237719

theorem tailTrace_1742212 : CollatzResearch.WordTrace tailWord_1742212 prefixEnd_1742212 894592158031042821237719 := by
  unfold tailWord_1742212
  simp only [CollatzResearch.WordTrace]
  refine ⟨31771845982135472482926445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42362461309513963310568593 31771845982135472482926445)
  ·
    refine ⟨11914442243300802181097417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31771845982135472482926445 11914442243300802181097417)
    ·
      refine ⟨8935831682475601635823063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11914442243300802181097417 8935831682475601635823063)
      ·
        refine ⟨13403747523713402453734595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8935831682475601635823063 13403747523713402453734595)
        ·
          refine ⟨20105621285570103680601893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13403747523713402453734595 20105621285570103680601893)
          ·
            refine ⟨3769803991044394440112855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20105621285570103680601893 3769803991044394440112855)
            ·
              refine ⟨5654705986566591660169283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769803991044394440112855 5654705986566591660169283)
              ·
                refine ⟨8482058979849887490253925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5654705986566591660169283 8482058979849887490253925)
                ·
                  refine ⟨1590386058721853904422611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8482058979849887490253925 1590386058721853904422611)
                  ·
                    refine ⟨2385579088082780856633917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1590386058721853904422611 2385579088082780856633917)
                    ·
                      refine ⟨894592158031042821237719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2385579088082780856633917 894592158031042821237719)
                      ·
                        rfl

theorem cell23_1742212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_1742212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742212 prefixEnd_1742212 := by exact prefixLift 1742212
  have htrace : WordTrace (prefixWord ++ tailWord_1742212) baseStart_1742212 baseEnd_1742212 := by
    simpa [prefixWord, tailWord_1742212, baseEnd_1742212] using wordTrace_append hprefix tailTrace_1742212
  have hstable : (prefixWord ++ tailWord_1742212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742212).length < 2 ^ (prefixWord ++ tailWord_1742212).sum := by decide
  have hdescent : baseEnd_1742212 < baseStart_1742212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742226 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1742226 : Nat := 118140960795 + 1742226 * 2 ^ 59
def prefixEnd_1742226 : Nat := 4983230072969 + 3 ^ 40 * 1742226 * 2
def baseEnd_1742226 : Nat := 894599346760205766462655

theorem tailTrace_1742226 : CollatzResearch.WordTrace tailWord_1742226 prefixEnd_1742226 894599346760205766462655 := by
  unfold tailWord_1742226
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886050646555056339215633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42362801724146816904575021 15886050646555056339215633)
  ·
    refine ⟨11914537984916292254411725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15886050646555056339215633 11914537984916292254411725)
    ·
      refine ⟨4467951744343609595404397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11914537984916292254411725 4467951744343609595404397)
      ·
        refine ⟨1675481904128853598276649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4467951744343609595404397 1675481904128853598276649)
        ·
          refine ⟨1256611428096640198707487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1675481904128853598276649 1256611428096640198707487)
          ·
            refine ⟨1884917142144960298061231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256611428096640198707487 1884917142144960298061231)
            ·
              refine ⟨2827375713217440447091847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884917142144960298061231 2827375713217440447091847)
              ·
                refine ⟨4241063569826160670637771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827375713217440447091847 4241063569826160670637771)
                ·
                  refine ⟨6361595354739241005956657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241063569826160670637771 6361595354739241005956657)
                  ·
                    refine ⟨4771196516054430754467493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6361595354739241005956657 4771196516054430754467493)
                    ·
                      refine ⟨894599346760205766462655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4771196516054430754467493 894599346760205766462655)
                      ·
                        rfl

theorem cell23_1742226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1742226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742226 prefixEnd_1742226 := by exact prefixLift 1742226
  have htrace : WordTrace (prefixWord ++ tailWord_1742226) baseStart_1742226 baseEnd_1742226 := by
    simpa [prefixWord, tailWord_1742226, baseEnd_1742226] using wordTrace_append hprefix tailTrace_1742226
  have hstable : (prefixWord ++ tailWord_1742226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742226).length < 2 ^ (prefixWord ++ tailWord_1742226).sum := by decide
  have hdescent : baseEnd_1742226 < baseStart_1742226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742239 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 1, 3, 2]
def baseStart_1742239 : Nat := 118140960795 + 1742239 * 2 ^ 59
def prefixEnd_1742239 : Nat := 4983230072969 + 3 ^ 40 * 1742239 * 2
def baseEnd_1742239 : Nat := 894606022008714215600095

theorem tailTrace_1742239 : CollatzResearch.WordTrace tailWord_1742239 prefixEnd_1742239 894606022008714215600095 := by
  unfold tailWord_1742239
  simp only [CollatzResearch.WordTrace]
  refine ⟨63544676735173128577085771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42363117823448752384723847 63544676735173128577085771)
  ·
    refine ⟨95317015102759692865628657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63544676735173128577085771 95317015102759692865628657)
    ·
      refine ⟨71487761327069769649221493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95317015102759692865628657 71487761327069769649221493)
      ·
        refine ⟨6701977624412790904614515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71487761327069769649221493 6701977624412790904614515)
        ·
          refine ⟨10052966436619186356921773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701977624412790904614515 10052966436619186356921773)
          ·
            refine ⟨3769862413732194883845665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10052966436619186356921773 3769862413732194883845665)
            ·
              refine ⟨2827396810299146162884249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769862413732194883845665 2827396810299146162884249)
              ·
                refine ⟨2120547607724359622163187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2827396810299146162884249 2120547607724359622163187)
                ·
                  refine ⟨3180821411586539433244781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120547607724359622163187 3180821411586539433244781)
                  ·
                    refine ⟨1192808029344952287466793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180821411586539433244781 1192808029344952287466793)
                    ·
                      refine ⟨894606022008714215600095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192808029344952287466793 894606022008714215600095)
                      ·
                        rfl

theorem cell23_1742239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_1742239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742239 prefixEnd_1742239 := by exact prefixLift 1742239
  have htrace : WordTrace (prefixWord ++ tailWord_1742239) baseStart_1742239 baseEnd_1742239 := by
    simpa [prefixWord, tailWord_1742239, baseEnd_1742239] using wordTrace_append hprefix tailTrace_1742239
  have hstable : (prefixWord ++ tailWord_1742239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742239).length < 2 ^ (prefixWord ++ tailWord_1742239).sum := by decide
  have hdescent : baseEnd_1742239 < baseStart_1742239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742252 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 4, 2, 2]
def baseStart_1742252 : Nat := 118140960795 + 1742252 * 2 ^ 59
def prefixEnd_1742252 : Nat := 4983230072969 + 3 ^ 40 * 1742252 * 2
def baseEnd_1742252 : Nat := 894612697257222664737535

theorem tailTrace_1742252 : CollatzResearch.WordTrace tailWord_1742252 prefixEnd_1742252 894612697257222664737535 := by
  unfold tailWord_1742252
  simp only [CollatzResearch.WordTrace]
  refine ⟨31772575442063015898654505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42363433922750687864872673 31772575442063015898654505)
  ·
    refine ⟨23829431581547261923990879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31772575442063015898654505 23829431581547261923990879)
    ·
      refine ⟨35744147372320892885986319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23829431581547261923990879 35744147372320892885986319)
      ·
        refine ⟨53616221058481339328979479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35744147372320892885986319 53616221058481339328979479)
        ·
          refine ⟨80424331587722008993469219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53616221058481339328979479 80424331587722008993469219)
          ·
            refine ⟨120636497381583013490203829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80424331587722008993469219 120636497381583013490203829)
            ·
              refine ⟨11309671629523407514706609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120636497381583013490203829 11309671629523407514706609)
              ·
                refine ⟨8482253722142555636029957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11309671629523407514706609 8482253722142555636029957)
                ·
                  refine ⟨1590422572901729181755617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8482253722142555636029957 1590422572901729181755617)
                  ·
                    refine ⟨1192816929676296886316713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590422572901729181755617 1192816929676296886316713)
                    ·
                      refine ⟨894612697257222664737535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192816929676296886316713 894612697257222664737535)
                      ·
                        rfl

theorem cell23_1742252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_1742252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742252 prefixEnd_1742252 := by exact prefixLift 1742252
  have htrace : WordTrace (prefixWord ++ tailWord_1742252) baseStart_1742252 baseEnd_1742252 := by
    simpa [prefixWord, tailWord_1742252, baseEnd_1742252] using wordTrace_append hprefix tailTrace_1742252
  have hstable : (prefixWord ++ tailWord_1742252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742252).length < 2 ^ (prefixWord ++ tailWord_1742252).sum := by decide
  have hdescent : baseEnd_1742252 < baseStart_1742252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742269 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 2, 2, 2]
def baseStart_1742269 : Nat := 118140960795 + 1742269 * 2 ^ 59
def prefixEnd_1742269 : Nat := 4983230072969 + 3 ^ 40 * 1742269 * 2
def baseEnd_1742269 : Nat := 894621426428349098224957

theorem tailTrace_1742269 : CollatzResearch.WordTrace tailWord_1742269 prefixEnd_1742269 894621426428349098224957 := by
  unfold tailWord_1742269
  simp only [CollatzResearch.WordTrace]
  refine ⟨63545770925064443700677861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42363847283376295800451907 63545770925064443700677861)
  ·
    refine ⟨11914832048449583193877099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63545770925064443700677861 11914832048449583193877099)
    ·
      refine ⟨17872248072674374790815649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11914832048449583193877099 17872248072674374790815649)
      ·
        refine ⟨13404186054505781093111737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17872248072674374790815649 13404186054505781093111737)
        ·
          refine ⟨10053139540879335819833803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13404186054505781093111737 10053139540879335819833803)
          ·
            refine ⟨15079709311319003729750705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10053139540879335819833803 15079709311319003729750705)
            ·
              refine ⟨11309781983489252797313029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15079709311319003729750705 11309781983489252797313029)
              ·
                refine ⟨2120584121904234899496193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11309781983489252797313029 2120584121904234899496193)
                ·
                  refine ⟨1590438091428176174622145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2120584121904234899496193 1590438091428176174622145)
                  ·
                    refine ⟨1192828568571132130966609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590438091428176174622145 1192828568571132130966609)
                    ·
                      refine ⟨894621426428349098224957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192828568571132130966609 894621426428349098224957)
                      ·
                        rfl

theorem cell23_1742269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_1742269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742269 prefixEnd_1742269 := by exact prefixLift 1742269
  have htrace : WordTrace (prefixWord ++ tailWord_1742269) baseStart_1742269 baseEnd_1742269 := by
    simpa [prefixWord, tailWord_1742269, baseEnd_1742269] using wordTrace_append hprefix tailTrace_1742269
  have hstable : (prefixWord ++ tailWord_1742269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742269).length < 2 ^ (prefixWord ++ tailWord_1742269).sum := by decide
  have hdescent : baseEnd_1742269 < baseStart_1742269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742275 : List Nat := [1, 1, 1, 3, 1, 1, 4, 6, 5]
def baseStart_1742275 : Nat := 118140960795 + 1742275 * 2 ^ 59
def prefixEnd_1742275 : Nat := 4983230072969 + 3 ^ 40 * 1742275 * 2
def baseEnd_1742275 : Nat := 99402723034697341638881

theorem tailTrace_1742275 : CollatzResearch.WordTrace tailWord_1742275 prefixEnd_1742275 99402723034697341638881 := by
  unfold tailWord_1742275
  simp only [CollatzResearch.WordTrace]
  refine ⟨63545989763042706725396279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42363993175361804483597519 63545989763042706725396279)
  ·
    refine ⟨95318984644564060088094419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63545989763042706725396279 95318984644564060088094419)
    ·
      refine ⟨142978476966846090132141629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95318984644564060088094419 142978476966846090132141629)
      ·
        refine ⟨53616928862567283799553111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142978476966846090132141629 53616928862567283799553111)
        ·
          refine ⟨80425393293850925699329667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53616928862567283799553111 80425393293850925699329667)
          ·
            refine ⟨120638089940776388548994501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80425393293850925699329667 120638089940776388548994501)
            ·
              refine ⟨22619641863895572852936469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120638089940776388548994501 22619641863895572852936469)
              ·
                refine ⟨1060295712370104977481397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22619641863895572852936469 1060295712370104977481397)
                ·
                  refine ⟨99402723034697341638881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1060295712370104977481397 99402723034697341638881)
                  ·
                    rfl

theorem cell23_1742275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 5].length) (baseStart_1742275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742275 prefixEnd_1742275 := by exact prefixLift 1742275
  have htrace : WordTrace (prefixWord ++ tailWord_1742275) baseStart_1742275 baseEnd_1742275 := by
    simpa [prefixWord, tailWord_1742275, baseEnd_1742275] using wordTrace_append hprefix tailTrace_1742275
  have hstable : (prefixWord ++ tailWord_1742275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742275).length < 2 ^ (prefixWord ++ tailWord_1742275).sum := by decide
  have hdescent : baseEnd_1742275 < baseStart_1742275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742286 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2]
def baseStart_1742286 : Nat := 118140960795 + 1742286 * 2 ^ 59
def prefixEnd_1742286 : Nat := 4983230072969 + 3 ^ 40 * 1742286 * 2
def baseEnd_1742286 : Nat := 894630155599475531712379

theorem tailTrace_1742286 : CollatzResearch.WordTrace tailWord_1742286 prefixEnd_1742286 894630155599475531712379 := by
  unfold tailWord_1742286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7943298870750356950505839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42364260644001903736031141 7943298870750356950505839)
  ·
    refine ⟨11914948306125535425758759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7943298870750356950505839 11914948306125535425758759)
    ·
      refine ⟨17872422459188303138638139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11914948306125535425758759 17872422459188303138638139)
      ·
        refine ⟨26808633688782454707957209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17872422459188303138638139 26808633688782454707957209)
        ·
          refine ⟨20106475266586841030967907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26808633688782454707957209 20106475266586841030967907)
          ·
            refine ⟨30159712899880261546451861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20106475266586841030967907 30159712899880261546451861)
            ·
              refine ⟨1413736542181887259989931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30159712899880261546451861 1413736542181887259989931)
              ·
                refine ⟨2120604813272830889984897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413736542181887259989931 2120604813272830889984897)
                ·
                  refine ⟨1590453609954623167488673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2120604813272830889984897 1590453609954623167488673)
                  ·
                    refine ⟨1192840207465967375616505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590453609954623167488673 1192840207465967375616505)
                    ·
                      refine ⟨894630155599475531712379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192840207465967375616505 894630155599475531712379)
                      ·
                        rfl

theorem cell23_1742286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_1742286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742286 prefixEnd_1742286 := by exact prefixLift 1742286
  have htrace : WordTrace (prefixWord ++ tailWord_1742286) baseStart_1742286 baseEnd_1742286 := by
    simpa [prefixWord, tailWord_1742286, baseEnd_1742286] using wordTrace_append hprefix tailTrace_1742286
  have hstable : (prefixWord ++ tailWord_1742286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742286).length < 2 ^ (prefixWord ++ tailWord_1742286).sum := by decide
  have hdescent : baseEnd_1742286 < baseStart_1742286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742305 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 2, 5]
def baseStart_1742305 : Nat := 118140960795 + 1742305 * 2 ^ 59
def prefixEnd_1742305 : Nat := 4983230072969 + 3 ^ 40 * 1742305 * 2
def baseEnd_1742305 : Nat := 298213303910636985791597

theorem tailTrace_1742305 : CollatzResearch.WordTrace tailWord_1742305 prefixEnd_1742305 298213303910636985791597 := by
  unfold tailWord_1742305
  simp only [CollatzResearch.WordTrace]
  refine ⟨63547083952934021848988369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42364722635289347899325579 63547083952934021848988369)
  ·
    refine ⟨47660312964700516386741277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63547083952934021848988369 47660312964700516386741277)
    ·
      refine ⟨17872617361762693645027979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47660312964700516386741277 17872617361762693645027979)
      ·
        refine ⟨26808926042644040467541969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17872617361762693645027979 26808926042644040467541969)
        ·
          refine ⟨20106694531983030350656477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26808926042644040467541969 20106694531983030350656477)
          ·
            refine ⟨7540010449493636381496179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20106694531983030350656477 7540010449493636381496179)
            ·
              refine ⟨11310015674240454572244269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540010449493636381496179 11310015674240454572244269)
              ·
                refine ⟨4241255877840170464591601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11310015674240454572244269 4241255877840170464591601)
                ·
                  refine ⟨3180941908380127848443701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4241255877840170464591601 3180941908380127848443701)
                  ·
                    refine ⟨298213303910636985791597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3180941908380127848443701 298213303910636985791597)
                    ·
                      rfl

theorem cell23_1742305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_1742305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742305 prefixEnd_1742305 := by exact prefixLift 1742305
  have htrace : WordTrace (prefixWord ++ tailWord_1742305) baseStart_1742305 baseEnd_1742305 := by
    simpa [prefixWord, tailWord_1742305, baseEnd_1742305] using wordTrace_append hprefix tailTrace_1742305
  have hstable : (prefixWord ++ tailWord_1742305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742305).length < 2 ^ (prefixWord ++ tailWord_1742305).sum := by decide
  have hdescent : baseEnd_1742305 < baseStart_1742305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742322 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_1742322 : Nat := 118140960795 + 1742322 * 2 ^ 59
def prefixEnd_1742322 : Nat := 4983230072969 + 3 ^ 40 * 1742322 * 2
def baseEnd_1742322 : Nat := 298216213634345796954071

theorem tailTrace_1742322 : CollatzResearch.WordTrace tailWord_1742322 prefixEnd_1742322 298216213634345796954071 := by
  unfold tailWord_1742322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886925998468108438089305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42365135995914955834904813 15886925998468108438089305)
  ·
    refine ⟨11915194498851081328566979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15886925998468108438089305 11915194498851081328566979)
    ·
      refine ⟨17872791748276621992850469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11915194498851081328566979 17872791748276621992850469)
      ·
        refine ⟨3351148452801866623659463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17872791748276621992850469 3351148452801866623659463)
        ·
          refine ⟨5026722679202799935489195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3351148452801866623659463 5026722679202799935489195)
          ·
            refine ⟨7540084018804199903233793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5026722679202799935489195 7540084018804199903233793)
            ·
              refine ⟨5655063014103149927425345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7540084018804199903233793 5655063014103149927425345)
              ·
                refine ⟨4241297260577362445569009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5655063014103149927425345 4241297260577362445569009)
                ·
                  refine ⟨3180972945433021834176757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4241297260577362445569009 3180972945433021834176757)
                  ·
                    refine ⟨298216213634345796954071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3180972945433021834176757 298216213634345796954071)
                    ·
                      rfl

theorem cell23_1742322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_1742322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742322 prefixEnd_1742322 := by exact prefixLift 1742322
  have htrace : WordTrace (prefixWord ++ tailWord_1742322) baseStart_1742322 baseEnd_1742322 := by
    simpa [prefixWord, tailWord_1742322, baseEnd_1742322] using wordTrace_append hprefix tailTrace_1742322
  have hstable : (prefixWord ++ tailWord_1742322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742322).length < 2 ^ (prefixWord ++ tailWord_1742322).sum := by decide
  have hdescent : baseEnd_1742322 < baseStart_1742322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742326 : List Nat := [5, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_1742326 : Nat := 118140960795 + 1742326 * 2 ^ 59
def prefixEnd_1742326 : Nat := 4983230072969 + 3 ^ 40 * 1742326 * 2
def baseEnd_1742326 : Nat := 99405632758406152801355

theorem tailTrace_1742326 : CollatzResearch.WordTrace tailWord_1742326 prefixEnd_1742326 99405632758406152801355 := by
  unfold tailWord_1742326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3971740617866121402218927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42365233257238628290335221 3971740617866121402218927)
  ·
    refine ⟨5957610926799182103328391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3971740617866121402218927 5957610926799182103328391)
    ·
      refine ⟨8936416390198773154992587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5957610926799182103328391 8936416390198773154992587)
      ·
        refine ⟨13404624585298159732488881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8936416390198773154992587 13404624585298159732488881)
        ·
          refine ⟨10053468438973619799366661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13404624585298159732488881 10053468438973619799366661)
          ·
            refine ⟨1885025332307553712381249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10053468438973619799366661 1885025332307553712381249)
            ·
              refine ⟨1413768999230665284285937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885025332307553712381249 1413768999230665284285937)
              ·
                refine ⟨1060326749422998963214453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413768999230665284285937 1060326749422998963214453)
                ·
                  refine ⟨99405632758406152801355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1060326749422998963214453 99405632758406152801355)
                  ·
                    rfl

theorem cell23_1742326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_1742326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742326 prefixEnd_1742326 := by exact prefixLift 1742326
  have htrace : WordTrace (prefixWord ++ tailWord_1742326) baseStart_1742326 baseEnd_1742326 := by
    simpa [prefixWord, tailWord_1742326, baseEnd_1742326] using wordTrace_append hprefix tailTrace_1742326
  have hstable : (prefixWord ++ tailWord_1742326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742326).length < 2 ^ (prefixWord ++ tailWord_1742326).sum := by decide
  have hdescent : baseEnd_1742326 < baseStart_1742326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742345 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 1, 4, 3]
def baseStart_1742345 : Nat := 118140960795 + 1742345 * 2 ^ 59
def prefixEnd_1742345 : Nat := 4983230072969 + 3 ^ 40 * 1742345 * 2
def baseEnd_1742345 : Nat := 894660450958090800874607

theorem tailTrace_1742345 : CollatzResearch.WordTrace tailWord_1742345 prefixEnd_1742345 894660450958090800874607 := by
  unfold tailWord_1742345
  simp only [CollatzResearch.WordTrace]
  refine ⟨63548542872789108680444489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42365695248526072453629659 63548542872789108680444489)
  ·
    refine ⟨47661407154591831510333367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63548542872789108680444489 47661407154591831510333367)
    ·
      refine ⟨71492110731887747265500051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47661407154591831510333367 71492110731887747265500051)
      ·
        refine ⟨107238166097831620898250077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71492110731887747265500051 107238166097831620898250077)
        ·
          refine ⟨40214312286686857836843779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107238166097831620898250077 40214312286686857836843779)
          ·
            refine ⟨60321468430030286755265669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40214312286686857836843779 60321468430030286755265669)
            ·
              refine ⟨11310275330630678766612313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60321468430030286755265669 11310275330630678766612313)
              ·
                refine ⟨8482706497973009074959235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11310275330630678766612313 8482706497973009074959235)
                ·
                  refine ⟨12724059746959513612438853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8482706497973009074959235 12724059746959513612438853)
                  ·
                    refine ⟨2385761202554908802332285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12724059746959513612438853 2385761202554908802332285)
                    ·
                      refine ⟨894660450958090800874607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2385761202554908802332285 894660450958090800874607)
                      ·
                        rfl

theorem cell23_1742345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4, 3].length) (baseStart_1742345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742345 prefixEnd_1742345 := by exact prefixLift 1742345
  have htrace : WordTrace (prefixWord ++ tailWord_1742345) baseStart_1742345 baseEnd_1742345 := by
    simpa [prefixWord, tailWord_1742345, baseEnd_1742345] using wordTrace_append hprefix tailTrace_1742345
  have hstable : (prefixWord ++ tailWord_1742345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742345).length < 2 ^ (prefixWord ++ tailWord_1742345).sum := by decide
  have hdescent : baseEnd_1742345 < baseStart_1742345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742356 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1742356 : Nat := 118140960795 + 1742356 * 2 ^ 59
def prefixEnd_1742356 : Nat := 4983230072969 + 3 ^ 40 * 1742356 * 2
def baseEnd_1742356 : Nat := 298222033081763419279019

theorem tailTrace_1742356 : CollatzResearch.WordTrace tailWord_1742356 prefixEnd_1742356 298222033081763419279019 := by
  unfold tailWord_1742356
  simp only [CollatzResearch.WordTrace]
  refine ⟨31774472037874628779547461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42365962717166171706063281 31774472037874628779547461)
  ·
    refine ⟨5957713507101492896165149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31774472037874628779547461 5957713507101492896165149)
    ·
      refine ⟨2234142565163059836061931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5957713507101492896165149 2234142565163059836061931)
      ·
        refine ⟨3351213847744589754092897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234142565163059836061931 3351213847744589754092897)
        ·
          refine ⟨2513410385808442315569673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3351213847744589754092897 2513410385808442315569673)
          ·
            refine ⟨1885057789356331736677255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513410385808442315569673 1885057789356331736677255)
            ·
              refine ⟨2827586684034497605015883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885057789356331736677255 2827586684034497605015883)
              ·
                refine ⟨4241380026051746407523825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827586684034497605015883 4241380026051746407523825)
                ·
                  refine ⟨3181035019538809805642869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4241380026051746407523825 3181035019538809805642869)
                  ·
                    refine ⟨298222033081763419279019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3181035019538809805642869 298222033081763419279019)
                    ·
                      rfl

theorem cell23_1742356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1742356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742356 prefixEnd_1742356 := by exact prefixLift 1742356
  have htrace : WordTrace (prefixWord ++ tailWord_1742356) baseStart_1742356 baseEnd_1742356 := by
    simpa [prefixWord, tailWord_1742356, baseEnd_1742356] using wordTrace_append hprefix tailTrace_1742356
  have hstable : (prefixWord ++ tailWord_1742356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742356).length < 2 ^ (prefixWord ++ tailWord_1742356).sum := by decide
  have hdescent : baseEnd_1742356 < baseStart_1742356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742365 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 8]
def baseStart_1742365 : Nat := 118140960795 + 1742365 * 2 ^ 59
def prefixEnd_1742365 : Nat := 4983230072969 + 3 ^ 40 * 1742365 * 2
def baseEnd_1742365 : Nat := 99407857841242302513835

theorem tailTrace_1742365 : CollatzResearch.WordTrace tailWord_1742365 prefixEnd_1742365 99407857841242302513835 := by
  unfold tailWord_1742365
  simp only [CollatzResearch.WordTrace]
  refine ⟨63549272332716652096172549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42366181555144434730781699 63549272332716652096172549)
  ·
    refine ⟨11915488562384372268032353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63549272332716652096172549 11915488562384372268032353)
    ·
      refine ⟨8936616421788279201024265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11915488562384372268032353 8936616421788279201024265)
      ·
        refine ⟨6702462316341209400768199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8936616421788279201024265 6702462316341209400768199)
        ·
          refine ⟨10053693474511814101152299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6702462316341209400768199 10053693474511814101152299)
          ·
            refine ⟨15080540211767721151728449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10053693474511814101152299 15080540211767721151728449)
            ·
              refine ⟨11310405158825790863796337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15080540211767721151728449 11310405158825790863796337)
              ·
                refine ⟨8482803869119343147847253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11310405158825790863796337 8482803869119343147847253)
                ·
                  refine ⟨99407857841242302513835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8482803869119343147847253 99407857841242302513835)
                  ·
                    rfl

theorem cell23_1742365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_1742365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742365 prefixEnd_1742365 := by exact prefixLift 1742365
  have htrace : WordTrace (prefixWord ++ tailWord_1742365) baseStart_1742365 baseEnd_1742365 := by
    simpa [prefixWord, tailWord_1742365, baseEnd_1742365] using wordTrace_append hprefix tailTrace_1742365
  have hstable : (prefixWord ++ tailWord_1742365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742365).length < 2 ^ (prefixWord ++ tailWord_1742365).sum := by decide
  have hdescent : baseEnd_1742365 < baseStart_1742365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742369 : List Nat := [1, 2, 3, 2, 2, 2, 1, 5, 1, 4]
def baseStart_1742369 : Nat := 118140960795 + 1742369 * 2 ^ 59
def prefixEnd_1742369 : Nat := 4983230072969 + 3 ^ 40 * 1742369 * 2
def baseEnd_1742369 : Nat := 298224258164599568991499

theorem tailTrace_1742369 : CollatzResearch.WordTrace tailWord_1742369 prefixEnd_1742369 298224258164599568991499 := by
  unfold tailWord_1742369
  simp only [CollatzResearch.WordTrace]
  refine ⟨63549418224702160779318161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42366278816468107186212107 63549418224702160779318161)
  ·
    refine ⟨47662063668526620584488621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63549418224702160779318161 47662063668526620584488621)
    ·
      refine ⟨17873273875697482719183233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47662063668526620584488621 17873273875697482719183233)
      ·
        refine ⟨13404955406773112039387425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17873273875697482719183233 13404955406773112039387425)
        ·
          refine ⟨10053716555079834029540569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13404955406773112039387425 10053716555079834029540569)
          ·
            refine ⟨7540287416309875522155427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10053716555079834029540569 7540287416309875522155427)
            ·
              refine ⟨11310431124464813283233141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540287416309875522155427 11310431124464813283233141)
              ·
                refine ⟨1060352917918576245303107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11310431124464813283233141 1060352917918576245303107)
                ·
                  refine ⟨1590529376877864367954661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060352917918576245303107 1590529376877864367954661)
                  ·
                    refine ⟨298224258164599568991499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1590529376877864367954661 298224258164599568991499)
                    ·
                      rfl

theorem cell23_1742369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_1742369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742369 prefixEnd_1742369 := by exact prefixLift 1742369
  have htrace : WordTrace (prefixWord ++ tailWord_1742369) baseStart_1742369 baseEnd_1742369 := by
    simpa [prefixWord, tailWord_1742369, baseEnd_1742369] using wordTrace_append hprefix tailTrace_1742369
  have hstable : (prefixWord ++ tailWord_1742369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742369).length < 2 ^ (prefixWord ++ tailWord_1742369).sum := by decide
  have hdescent : baseEnd_1742369 < baseStart_1742369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742382 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_1742382 : Nat := 118140960795 + 1742382 * 2 ^ 59
def prefixEnd_1742382 : Nat := 4983230072969 + 3 ^ 40 * 1742382 * 2
def baseEnd_1742382 : Nat := 99408827749145239567993

theorem tailTrace_1742382 : CollatzResearch.WordTrace tailWord_1742382 prefixEnd_1742382 99408827749145239567993 := by
  unfold tailWord_1742382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7943736546706882999942675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42366594915770042666360933 7943736546706882999942675)
  ·
    refine ⟨11915604820060324499914013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7943736546706882999942675 11915604820060324499914013)
    ·
      refine ⟨4468351807522621687467755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11915604820060324499914013 4468351807522621687467755)
      ·
        refine ⟨6702527711283932531201633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4468351807522621687467755 6702527711283932531201633)
        ·
          refine ⟨5026895783462949398401225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6702527711283932531201633 5026895783462949398401225)
          ·
            refine ⟨3770171837597212048800919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5026895783462949398401225 3770171837597212048800919)
            ·
              refine ⟨5655257756395818073201379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770171837597212048800919 5655257756395818073201379)
              ·
                refine ⟨8482886634593727109802069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655257756395818073201379 8482886634593727109802069)
                ·
                  refine ⟨99408827749145239567993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8482886634593727109802069 99408827749145239567993)
                  ·
                    rfl

theorem cell23_1742382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_1742382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742382 prefixEnd_1742382 := by exact prefixLift 1742382
  have htrace : WordTrace (prefixWord ++ tailWord_1742382) baseStart_1742382 baseEnd_1742382 := by
    simpa [prefixWord, tailWord_1742382, baseEnd_1742382] using wordTrace_append hprefix tailTrace_1742382
  have hstable : (prefixWord ++ tailWord_1742382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742382).length < 2 ^ (prefixWord ++ tailWord_1742382).sum := by decide
  have hdescent : baseEnd_1742382 < baseStart_1742382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742412 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_1742412 : Nat := 118140960795 + 1742412 * 2 ^ 59
def prefixEnd_1742412 : Nat := 4983230072969 + 3 ^ 40 * 1742412 * 2
def baseEnd_1742412 : Nat := 298231618053980679578933

theorem tailTrace_1742412 : CollatzResearch.WordTrace tailWord_1742412 prefixEnd_1742412 298231618053980679578933 := by
  unfold tailWord_1742412
  simp only [CollatzResearch.WordTrace]
  refine ⟨31775493281773189561566745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42367324375697586082088993 31775493281773189561566745)
  ·
    refine ⟨23831619961329892171175059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31775493281773189561566745 23831619961329892171175059)
    ·
      refine ⟨35747429941994838256762589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23831619961329892171175059 35747429941994838256762589)
      ·
        refine ⟨13405286228248064346285971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35747429941994838256762589 13405286228248064346285971)
        ·
          refine ⟨20107929342372096519428957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13405286228248064346285971 20107929342372096519428957)
          ·
            refine ⟨7540473503389536194785859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20107929342372096519428957 7540473503389536194785859)
            ·
              refine ⟨11310710255084304292178789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540473503389536194785859 11310710255084304292178789)
              ·
                refine ⟨2120758172828307054783523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11310710255084304292178789 2120758172828307054783523)
                ·
                  refine ⟨3181137259242460582175285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120758172828307054783523 3181137259242460582175285)
                  ·
                    refine ⟨298231618053980679578933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3181137259242460582175285 298231618053980679578933)
                    ·
                      rfl

theorem cell23_1742412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_1742412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742412 prefixEnd_1742412 := by exact prefixLift 1742412
  have htrace : WordTrace (prefixWord ++ tailWord_1742412) baseStart_1742412 baseEnd_1742412 := by
    simpa [prefixWord, tailWord_1742412, baseEnd_1742412] using wordTrace_append hprefix tailTrace_1742412
  have hstable : (prefixWord ++ tailWord_1742412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742412).length < 2 ^ (prefixWord ++ tailWord_1742412).sum := by decide
  have hdescent : baseEnd_1742412 < baseStart_1742412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742425 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 1, 6]
def baseStart_1742425 : Nat := 118140960795 + 1742425 * 2 ^ 59
def prefixEnd_1742425 : Nat := 4983230072969 + 3 ^ 40 * 1742425 * 2
def baseEnd_1742425 : Nat := 298233843136816829291413

theorem tailTrace_1742425 : CollatzResearch.WordTrace tailWord_1742425 prefixEnd_1742425 298233843136816829291413 := by
  unfold tailWord_1742425
  simp only [CollatzResearch.WordTrace]
  refine ⟨63551460712499282343356729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42367640474999521562237819 63551460712499282343356729)
  ·
    refine ⟨47663595534374461757517547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63551460712499282343356729 47663595534374461757517547)
    ·
      refine ⟨71495393301561692636276321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47663595534374461757517547 71495393301561692636276321)
      ·
        refine ⟨53621544976171269477207241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71495393301561692636276321 53621544976171269477207241)
        ·
          refine ⟨40216158732128452107905431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53621544976171269477207241 40216158732128452107905431)
          ·
            refine ⟨60324238098192678161858147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40216158732128452107905431 60324238098192678161858147)
            ·
              refine ⟨90486357147289017242787221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60324238098192678161858147 90486357147289017242787221)
              ·
                refine ⟨4241547991279172683255651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90486357147289017242787221 4241547991279172683255651)
                ·
                  refine ⟨6362321986918759024883477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241547991279172683255651 6362321986918759024883477)
                  ·
                    refine ⟨298233843136816829291413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6362321986918759024883477 298233843136816829291413)
                    ·
                      rfl

theorem cell23_1742425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_1742425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742425 prefixEnd_1742425 := by exact prefixLift 1742425
  have htrace : WordTrace (prefixWord ++ tailWord_1742425) baseStart_1742425 baseEnd_1742425 := by
    simpa [prefixWord, tailWord_1742425, baseEnd_1742425] using wordTrace_append hprefix tailTrace_1742425
  have hstable : (prefixWord ++ tailWord_1742425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742425).length < 2 ^ (prefixWord ++ tailWord_1742425).sum := by decide
  have hdescent : baseEnd_1742425 < baseStart_1742425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742485 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_1742485 : Nat := 118140960795 + 1742485 * 2 ^ 59
def prefixEnd_1742485 : Nat := 4983230072969 + 3 ^ 40 * 1742485 * 2
def baseEnd_1742485 : Nat := 298244112749906751041321

theorem tailTrace_1742485 : CollatzResearch.WordTrace tailWord_1742485 prefixEnd_1742485 298244112749906751041321 := by
  unfold tailWord_1742485
  simp only [CollatzResearch.WordTrace]
  refine ⟨63553649092281912590540909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42369099394854608393693939 63553649092281912590540909)
  ·
    refine ⟨23832618409605717221452841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63553649092281912590540909 23832618409605717221452841)
    ·
      refine ⟨17874463807204287916089631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23832618409605717221452841 17874463807204287916089631)
      ·
        refine ⟨26811695710806431874134447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17874463807204287916089631 26811695710806431874134447)
        ·
          refine ⟨40217543566209647811201671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26811695710806431874134447 40217543566209647811201671)
          ·
            refine ⟨60326315349314471716802507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40217543566209647811201671 60326315349314471716802507)
            ·
              refine ⟨90489473023971707575203761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60326315349314471716802507 90489473023971707575203761)
              ·
                refine ⟨67867104767978780681402821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90489473023971707575203761 67867104767978780681402821)
                ·
                  refine ⟨12725082143996021377763029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67867104767978780681402821 12725082143996021377763029)
                  ·
                    refine ⟨298244112749906751041321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12725082143996021377763029 298244112749906751041321)
                    ·
                      rfl

theorem cell23_1742485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_1742485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742485 prefixEnd_1742485 := by exact prefixLift 1742485
  have htrace : WordTrace (prefixWord ++ tailWord_1742485) baseStart_1742485 baseEnd_1742485 := by
    simpa [prefixWord, tailWord_1742485, baseEnd_1742485] using wordTrace_append hprefix tailTrace_1742485
  have hstable : (prefixWord ++ tailWord_1742485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742485).length < 2 ^ (prefixWord ++ tailWord_1742485).sum := by decide
  have hdescent : baseEnd_1742485 < baseStart_1742485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742500 : List Nat := [2, 3, 1, 2, 2, 2, 4, 2, 1, 2, 2]
def baseStart_1742500 : Nat := 118140960795 + 1742500 * 2 ^ 59
def prefixEnd_1742500 : Nat := 4983230072969 + 3 ^ 40 * 1742500 * 2
def baseEnd_1742500 : Nat := 894740040459537694436395

theorem tailTrace_1742500 : CollatzResearch.WordTrace tailWord_1742500 prefixEnd_1742500 894740040459537694436395 := by
  unfold tailWord_1742500
  simp only [CollatzResearch.WordTrace]
  refine ⟨31777098093613785076168477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42369464124818380101557969 31777098093613785076168477)
  ·
    refine ⟨11916411785105169403563179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31777098093613785076168477 11916411785105169403563179)
    ·
      refine ⟨17874617677657754105344769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11916411785105169403563179 17874617677657754105344769)
      ·
        refine ⟨13405963258243315579008577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17874617677657754105344769 13405963258243315579008577)
        ·
          refine ⟨10054472443682486684256433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13405963258243315579008577 10054472443682486684256433)
          ·
            refine ⟨7540854332761865013192325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10054472443682486684256433 7540854332761865013192325)
            ·
              refine ⟨1413910187392849689973561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7540854332761865013192325 1413910187392849689973561)
              ·
                refine ⟨1060432640544637267480171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413910187392849689973561 1060432640544637267480171)
                ·
                  refine ⟨1590648960816955901220257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060432640544637267480171 1590648960816955901220257)
                  ·
                    refine ⟨1192986720612716925915193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590648960816955901220257 1192986720612716925915193)
                    ·
                      refine ⟨894740040459537694436395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1192986720612716925915193 894740040459537694436395)
                      ·
                        rfl

theorem cell23_1742500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_1742500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742500 prefixEnd_1742500 := by exact prefixLift 1742500
  have htrace : WordTrace (prefixWord ++ tailWord_1742500) baseStart_1742500 baseEnd_1742500 := by
    simpa [prefixWord, tailWord_1742500, baseEnd_1742500] using wordTrace_append hprefix tailTrace_1742500
  have hstable : (prefixWord ++ tailWord_1742500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742500).length < 2 ^ (prefixWord ++ tailWord_1742500).sum := by decide
  have hdescent : baseEnd_1742500 < baseStart_1742500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742526 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_1742526 : Nat := 118140960795 + 1742526 * 2 ^ 59
def prefixEnd_1742526 : Nat := 4983230072969 + 3 ^ 40 * 1742526 * 2
def baseEnd_1742526 : Nat := 894753390956554592711275

theorem tailTrace_1742526 : CollatzResearch.WordTrace tailWord_1742526 prefixEnd_1742526 894753390956554592711275 := by
  unfold tailWord_1742526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7944393060641672074097929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42370096323422251061855621 7944393060641672074097929)
  ·
    refine ⟨5958294795481254055573447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7944393060641672074097929 5958294795481254055573447)
    ·
      refine ⟨8937442193221881083360171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5958294795481254055573447 8937442193221881083360171)
      ·
        refine ⟨13406163289832821625040257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8937442193221881083360171 13406163289832821625040257)
        ·
          refine ⟨10054622467374616218780193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13406163289832821625040257 10054622467374616218780193)
          ·
            refine ⟨7540966850530962164085145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10054622467374616218780193 7540966850530962164085145)
            ·
              refine ⟨5655725137898221623063859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7540966850530962164085145 5655725137898221623063859)
              ·
                refine ⟨8483587706847332434595789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655725137898221623063859 8483587706847332434595789)
                ·
                  refine ⟨3181345390067749662973421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8483587706847332434595789 3181345390067749662973421)
                  ·
                    refine ⟨1193004521275406123615033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181345390067749662973421 1193004521275406123615033)
                    ·
                      refine ⟨894753390956554592711275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193004521275406123615033 894753390956554592711275)
                      ·
                        rfl

theorem cell23_1742526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_1742526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742526 prefixEnd_1742526 := by exact prefixLift 1742526
  have htrace : WordTrace (prefixWord ++ tailWord_1742526) baseStart_1742526 baseEnd_1742526 := by
    simpa [prefixWord, tailWord_1742526, baseEnd_1742526] using wordTrace_append hprefix tailTrace_1742526
  have hstable : (prefixWord ++ tailWord_1742526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742526).length < 2 ^ (prefixWord ++ tailWord_1742526).sum := by decide
  have hdescent : baseEnd_1742526 < baseStart_1742526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742532 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1742532 : Nat := 118140960795 + 1742532 * 2 ^ 59
def prefixEnd_1742532 : Nat := 4983230072969 + 3 ^ 40 * 1742532 * 2
def baseEnd_1742532 : Nat := 298252157280160523078749

theorem tailTrace_1742532 : CollatzResearch.WordTrace tailWord_1742532 prefixEnd_1742532 298252157280160523078749 := by
  unfold tailWord_1742532
  simp only [CollatzResearch.WordTrace]
  refine ⟨31777681661555819808750925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42370242215407759745001233 31777681661555819808750925)
  ·
    refine ⟨11916630623083432428281597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31777681661555819808750925 11916630623083432428281597)
    ·
      refine ⟨4468736483656287160605599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11916630623083432428281597 4468736483656287160605599)
      ·
        refine ⟨6703104725484430740908399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4468736483656287160605599 6703104725484430740908399)
        ·
          refine ⟨10054657088226646111362599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703104725484430740908399 10054657088226646111362599)
          ·
            refine ⟨15081985632339969167043899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10054657088226646111362599 15081985632339969167043899)
            ·
              refine ⟨22622978448509953750565849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15081985632339969167043899 22622978448509953750565849)
              ·
                refine ⟨16967233836382465312924387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22622978448509953750565849 16967233836382465312924387)
                ·
                  refine ⟨25450850754573697969386581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16967233836382465312924387 25450850754573697969386581)
                  ·
                    refine ⟨298252157280160523078749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25450850754573697969386581 298252157280160523078749)
                    ·
                      rfl

theorem cell23_1742532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1742532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742532 prefixEnd_1742532 := by exact prefixLift 1742532
  have htrace : WordTrace (prefixWord ++ tailWord_1742532) baseStart_1742532 baseEnd_1742532 := by
    simpa [prefixWord, tailWord_1742532, baseEnd_1742532] using wordTrace_append hprefix tailTrace_1742532
  have hstable : (prefixWord ++ tailWord_1742532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742532).length < 2 ^ (prefixWord ++ tailWord_1742532).sum := by decide
  have hdescent : baseEnd_1742532 < baseStart_1742532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742534 : List Nat := [6, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_1742534 : Nat := 118140960795 + 1742534 * 2 ^ 59
def prefixEnd_1742534 : Nat := 4983230072969 + 3 ^ 40 * 1742534 * 2
def baseEnd_1742534 : Nat := 894757498801790561411239

theorem tailTrace_1742534 : CollatzResearch.WordTrace tailWord_1742534 prefixEnd_1742534 894757498801790561411239 := by
  unfold tailWord_1742534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1986107383409512311221083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42370290846069595972716437 1986107383409512311221083)
  ·
    refine ⟨2979161075114268466831625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1986107383409512311221083 2979161075114268466831625)
    ·
      refine ⟨2234370806335701350123719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2979161075114268466831625 2234370806335701350123719)
      ·
        refine ⟨3351556209503552025185579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234370806335701350123719 3351556209503552025185579)
        ·
          refine ⟨5027334314255328037778369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3351556209503552025185579 5027334314255328037778369)
          ·
            refine ⟨3770500735691496028333777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5027334314255328037778369 3770500735691496028333777)
            ·
              refine ⟨2827875551768622021250333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3770500735691496028333777 2827875551768622021250333)
              ·
                refine ⟨1060453331913233257968875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2827875551768622021250333 1060453331913233257968875)
                ·
                  refine ⟨1590679997869849886953313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060453331913233257968875 1590679997869849886953313)
                  ·
                    refine ⟨1193009998402387415214985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590679997869849886953313 1193009998402387415214985)
                    ·
                      refine ⟨894757498801790561411239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193009998402387415214985 894757498801790561411239)
                      ·
                        rfl

theorem cell23_1742534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_1742534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742534 prefixEnd_1742534 := by exact prefixLift 1742534
  have htrace : WordTrace (prefixWord ++ tailWord_1742534) baseStart_1742534 baseEnd_1742534 := by
    simpa [prefixWord, tailWord_1742534, baseEnd_1742534] using wordTrace_append hprefix tailTrace_1742534
  have hstable : (prefixWord ++ tailWord_1742534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742534).length < 2 ^ (prefixWord ++ tailWord_1742534).sum := by decide
  have hdescent : baseEnd_1742534 < baseStart_1742534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742542 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1742542 : Nat := 118140960795 + 1742542 * 2 ^ 59
def prefixEnd_1742542 : Nat := 4983230072969 + 3 ^ 40 * 1742542 * 2
def baseEnd_1742542 : Nat := 894761606647026530111201

theorem tailTrace_1742542 : CollatzResearch.WordTrace tailWord_1742542 prefixEnd_1742542 894761606647026530111201 := by
  unfold tailWord_1742542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7944466006634426415670735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42370485368716940883577253 7944466006634426415670735)
  ·
    refine ⟨11916699009951639623506103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7944466006634426415670735 11916699009951639623506103)
    ·
      refine ⟨17875048514927459435259155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11916699009951639623506103 17875048514927459435259155)
      ·
        refine ⟨26812572772391189152888733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17875048514927459435259155 26812572772391189152888733)
        ·
          refine ⟨10054714789646695932333275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26812572772391189152888733 10054714789646695932333275)
          ·
            refine ⟨15082072184470043898499913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10054714789646695932333275 15082072184470043898499913)
            ·
              refine ⟨11311554138352532923874935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15082072184470043898499913 11311554138352532923874935)
              ·
                refine ⟨16967331207528799385812403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11311554138352532923874935 16967331207528799385812403)
                ·
                  refine ⟨25450996811293199078718605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16967331207528799385812403 25450996811293199078718605)
                  ·
                    refine ⟨9544123804234949654519477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25450996811293199078718605 9544123804234949654519477)
                    ·
                      refine ⟨894761606647026530111201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9544123804234949654519477 894761606647026530111201)
                      ·
                        rfl

theorem cell23_1742542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1742542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742542 prefixEnd_1742542 := by exact prefixLift 1742542
  have htrace : WordTrace (prefixWord ++ tailWord_1742542) baseStart_1742542 baseEnd_1742542 := by
    simpa [prefixWord, tailWord_1742542, baseEnd_1742542] using wordTrace_append hprefix tailTrace_1742542
  have hstable : (prefixWord ++ tailWord_1742542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742542).length < 2 ^ (prefixWord ++ tailWord_1742542).sum := by decide
  have hdescent : baseEnd_1742542 < baseStart_1742542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742550 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1742550 : Nat := 118140960795 + 1742550 * 2 ^ 59
def prefixEnd_1742550 : Nat := 4983230072969 + 3 ^ 40 * 1742550 * 2
def baseEnd_1742550 : Nat := 894765714492262498811165

theorem tailTrace_1742550 : CollatzResearch.WordTrace tailWord_1742550 prefixEnd_1742550 894765714492262498811165 := by
  unfold tailWord_1742550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972251239815401793228569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42370679891364285794438069 3972251239815401793228569)
  ·
    refine ⟨2979188429861551344921427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3972251239815401793228569 2979188429861551344921427)
    ·
      refine ⟨4468782644792327017382141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2979188429861551344921427 4468782644792327017382141)
      ·
        refine ⟨1675793491797122631518303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4468782644792327017382141 1675793491797122631518303)
        ·
          refine ⟨2513690237695683947277455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675793491797122631518303 2513690237695683947277455)
          ·
            refine ⟨3770535356543525920916183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513690237695683947277455 3770535356543525920916183)
            ·
              refine ⟨5655803034815288881374275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770535356543525920916183 5655803034815288881374275)
              ·
                refine ⟨8483704552222933322061413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655803034815288881374275 8483704552222933322061413)
                ·
                  refine ⟨1590694603541799997886515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8483704552222933322061413 1590694603541799997886515)
                  ·
                    refine ⟨2386041905312699996829773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1590694603541799997886515 2386041905312699996829773)
                    ·
                      refine ⟨894765714492262498811165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2386041905312699996829773 894765714492262498811165)
                      ·
                        rfl

theorem cell23_1742550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1742550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742550 prefixEnd_1742550 := by exact prefixLift 1742550
  have htrace : WordTrace (prefixWord ++ tailWord_1742550) baseStart_1742550 baseEnd_1742550 := by
    simpa [prefixWord, tailWord_1742550, baseEnd_1742550] using wordTrace_append hprefix tailTrace_1742550
  have hstable : (prefixWord ++ tailWord_1742550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742550).length < 2 ^ (prefixWord ++ tailWord_1742550).sum := by decide
  have hdescent : baseEnd_1742550 < baseStart_1742550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742552 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1742552 : Nat := 118140960795 + 1742552 * 2 ^ 59
def prefixEnd_1742552 : Nat := 4983230072969 + 3 ^ 40 * 1742552 * 2
def baseEnd_1742552 : Nat := 894766741453571490986155

theorem tailTrace_1742552 : CollatzResearch.WordTrace tailWord_1742552 prefixEnd_1742552 894766741453571490986155 := by
  unfold tailWord_1742552
  simp only [CollatzResearch.WordTrace]
  refine ⟨31778046391519591516614955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42370728522026122022153273 31778046391519591516614955)
  ·
    refine ⟨47667069587279387274922433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31778046391519591516614955 47667069587279387274922433)
    ·
      refine ⟨35750302190459540456191825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47667069587279387274922433 35750302190459540456191825)
      ·
        refine ⟨26812726642844655342143869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35750302190459540456191825 26812726642844655342143869)
        ·
          refine ⟨10054772491066745753303951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26812726642844655342143869 10054772491066745753303951)
          ·
            refine ⟨15082158736600118629955927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10054772491066745753303951 15082158736600118629955927)
            ·
              refine ⟨22623238104900177944933891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15082158736600118629955927 22623238104900177944933891)
              ·
                refine ⟨33934857157350266917400837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22623238104900177944933891 33934857157350266917400837)
                ·
                  refine ⟨6362785717003175047012657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33934857157350266917400837 6362785717003175047012657)
                  ·
                    refine ⟨4772089287752381285259493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6362785717003175047012657 4772089287752381285259493)
                    ·
                      refine ⟨894766741453571490986155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4772089287752381285259493 894766741453571490986155)
                      ·
                        rfl

theorem cell23_1742552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1742552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742552 prefixEnd_1742552 := by exact prefixLift 1742552
  have htrace : WordTrace (prefixWord ++ tailWord_1742552) baseStart_1742552 baseEnd_1742552 := by
    simpa [prefixWord, tailWord_1742552, baseEnd_1742552] using wordTrace_append hprefix tailTrace_1742552
  have hstable : (prefixWord ++ tailWord_1742552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742552).length < 2 ^ (prefixWord ++ tailWord_1742552).sum := by decide
  have hdescent : baseEnd_1742552 < baseStart_1742552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742573 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_1742573 : Nat := 118140960795 + 1742573 * 2 ^ 59
def prefixEnd_1742573 : Nat := 4983230072969 + 3 ^ 40 * 1742573 * 2
def baseEnd_1742573 : Nat := 894777524547315908823559

theorem tailTrace_1742573 : CollatzResearch.WordTrace tailWord_1742573 prefixEnd_1742573 894777524547315908823559 := by
  unfold tailWord_1742573
  simp only [CollatzResearch.WordTrace]
  refine ⟨63556858715963103619744373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42371239143975402413162915 63556858715963103619744373)
  ·
    refine ⟨5958455504621540964351035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63556858715963103619744373 5958455504621540964351035)
    ·
      refine ⟨8937683256932311446526553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5958455504621540964351035 8937683256932311446526553)
      ·
        refine ⟨6703262442699233584894915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8937683256932311446526553 6703262442699233584894915)
        ·
          refine ⟨10054893664048850377342373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703262442699233584894915 10054893664048850377342373)
          ·
            refine ⟨1885292562009159445751695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10054893664048850377342373 1885292562009159445751695)
            ·
              refine ⟨2827938843013739168627543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885292562009159445751695 2827938843013739168627543)
              ·
                refine ⟨4241908264520608752941315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827938843013739168627543 4241908264520608752941315)
                ·
                  refine ⟨6362862396780913129411973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4241908264520608752941315 6362862396780913129411973)
                  ·
                    refine ⟨1193036699396421211764745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6362862396780913129411973 1193036699396421211764745)
                    ·
                      refine ⟨894777524547315908823559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193036699396421211764745 894777524547315908823559)
                      ·
                        rfl

theorem cell23_1742573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_1742573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742573 prefixEnd_1742573 := by exact prefixLift 1742573
  have htrace : WordTrace (prefixWord ++ tailWord_1742573) baseStart_1742573 baseEnd_1742573 := by
    simpa [prefixWord, tailWord_1742573, baseEnd_1742573] using wordTrace_append hprefix tailTrace_1742573
  have hstable : (prefixWord ++ tailWord_1742573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742573).length < 2 ^ (prefixWord ++ tailWord_1742573).sum := by decide
  have hdescent : baseEnd_1742573 < baseStart_1742573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742596 : List Nat := [2, 3, 2, 2, 1, 2, 3, 3, 5]
def baseStart_1742596 : Nat := 118140960795 + 1742596 * 2 ^ 59
def prefixEnd_1742596 : Nat := 4983230072969 + 3 ^ 40 * 1742596 * 2
def baseEnd_1742596 : Nat := 99421037178041035426217

theorem tailTrace_1742596 : CollatzResearch.WordTrace tailWord_1742596 prefixEnd_1742596 99421037178041035426217 := by
  unfold tailWord_1742596
  simp only [CollatzResearch.WordTrace]
  refine ⟨31778848797439889273915821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42371798396586519031887761 31778848797439889273915821)
  ·
    refine ⟨11917068299039958477718433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31778848797439889273915821 11917068299039958477718433)
    ·
      refine ⟨8937801224279968858288825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11917068299039958477718433 8937801224279968858288825)
      ·
        refine ⟨6703350918209976643716619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8937801224279968858288825 6703350918209976643716619)
        ·
          refine ⟨10055026377314964965574929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703350918209976643716619 10055026377314964965574929)
          ·
            refine ⟨7541269782986223724181197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10055026377314964965574929 7541269782986223724181197)
            ·
              refine ⟨2827976168619833896567949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7541269782986223724181197 2827976168619833896567949)
              ·
                refine ⟨1060491063232437711212981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2827976168619833896567949 1060491063232437711212981)
                ·
                  refine ⟨99421037178041035426217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1060491063232437711212981 99421037178041035426217)
                  ·
                    rfl

theorem cell23_1742596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_1742596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742596 prefixEnd_1742596 := by exact prefixLift 1742596
  have htrace : WordTrace (prefixWord ++ tailWord_1742596) baseStart_1742596 baseEnd_1742596 := by
    simpa [prefixWord, tailWord_1742596, baseEnd_1742596] using wordTrace_append hprefix tailTrace_1742596
  have hstable : (prefixWord ++ tailWord_1742596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742596).length < 2 ^ (prefixWord ++ tailWord_1742596).sum := by decide
  have hdescent : baseEnd_1742596 < baseStart_1742596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742652 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 10]
def baseStart_1742652 : Nat := 118140960795 + 1742652 * 2 ^ 59
def prefixEnd_1742652 : Nat := 4983230072969 + 3 ^ 40 * 1742652 * 2
def baseEnd_1742652 : Nat := 99424232168780122192855

theorem tailTrace_1742652 : CollatzResearch.WordTrace tailWord_1742652 prefixEnd_1742652 99424232168780122192855 := by
  unfold tailWord_1742652
  simp only [CollatzResearch.WordTrace]
  refine ⟨31779870041338450055935105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42373160055117933407913473 31779870041338450055935105)
  ·
    refine ⟨23834902531003837541951329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31779870041338450055935105 23834902531003837541951329)
    ·
      refine ⟨17876176898252878156463497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23834902531003837541951329 17876176898252878156463497)
      ·
        refine ⟨13407132673689658617347623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17876176898252878156463497 13407132673689658617347623)
        ·
          refine ⟨20110699010534487926021435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13407132673689658617347623 20110699010534487926021435)
          ·
            refine ⟨30166048515801731889032153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20110699010534487926021435 30166048515801731889032153)
            ·
              refine ⟨22624536386851298916774115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30166048515801731889032153 22624536386851298916774115)
              ·
                refine ⟨33936804580276948375161173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22624536386851298916774115 33936804580276948375161173)
                ·
                  refine ⟨99424232168780122192855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 33936804580276948375161173 99424232168780122192855)
                  ·
                    rfl

theorem cell23_1742652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_1742652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742652 prefixEnd_1742652 := by exact prefixLift 1742652
  have htrace : WordTrace (prefixWord ++ tailWord_1742652) baseStart_1742652 baseEnd_1742652 := by
    simpa [prefixWord, tailWord_1742652, baseEnd_1742652] using wordTrace_append hprefix tailTrace_1742652
  have hstable : (prefixWord ++ tailWord_1742652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742652).length < 2 ^ (prefixWord ++ tailWord_1742652).sum := by decide
  have hdescent : baseEnd_1742652 < baseStart_1742652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742672 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_1742672 : Nat := 118140960795 + 1742672 * 2 ^ 59
def prefixEnd_1742672 : Nat := 4983230072969 + 3 ^ 40 * 1742672 * 2
def baseEnd_1742672 : Nat := 894828359132111021485603

theorem tailTrace_1742672 : CollatzResearch.WordTrace tailWord_1742672 prefixEnd_1742672 894828359132111021485603 := by
  unfold tailWord_1742672
  simp only [CollatzResearch.WordTrace]
  refine ⟨31780234771302221763799135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42373646361736295685065513 31780234771302221763799135)
  ·
    refine ⟨47670352156953332645698703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31780234771302221763799135 47670352156953332645698703)
    ·
      refine ⟨71505528235429998968548055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47670352156953332645698703 71505528235429998968548055)
      ·
        refine ⟨107258292353144998452822083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71505528235429998968548055 107258292353144998452822083)
        ·
          refine ⟨160887438529717497679233125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107258292353144998452822083 160887438529717497679233125)
          ·
            refine ⟨30166394724322030814856211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160887438529717497679233125 30166394724322030814856211)
            ·
              refine ⟨45249592086483046222284317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30166394724322030814856211 45249592086483046222284317)
              ·
                refine ⟨16968597032431142333356619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45249592086483046222284317 16968597032431142333356619)
                ·
                  refine ⟨25452895548646713500034929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16968597032431142333356619 25452895548646713500034929)
                  ·
                    refine ⟨19089671661485035125026197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25452895548646713500034929 19089671661485035125026197)
                    ·
                      refine ⟨894828359132111021485603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19089671661485035125026197 894828359132111021485603)
                      ·
                        rfl

theorem cell23_1742672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_1742672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742672 prefixEnd_1742672 := by exact prefixLift 1742672
  have htrace : WordTrace (prefixWord ++ tailWord_1742672) baseStart_1742672 baseEnd_1742672 := by
    simpa [prefixWord, tailWord_1742672, baseEnd_1742672] using wordTrace_append hprefix tailTrace_1742672
  have hstable : (prefixWord ++ tailWord_1742672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742672).length < 2 ^ (prefixWord ++ tailWord_1742672).sum := by decide
  have hdescent : baseEnd_1742672 < baseStart_1742672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742673 : List Nat := [1, 2, 2, 1, 5, 2, 1, 4, 1, 4]
def baseStart_1742673 : Nat := 118140960795 + 1742673 * 2 ^ 59
def prefixEnd_1742673 : Nat := 4983230072969 + 3 ^ 40 * 1742673 * 2
def baseEnd_1742673 : Nat := 298276290870921839191033

theorem tailTrace_1742673 : CollatzResearch.WordTrace tailWord_1742673 prefixEnd_1742673 298276290870921839191033 := by
  unfold tailWord_1742673
  simp only [CollatzResearch.WordTrace]
  refine ⟨63560506015600820698384673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42373670677067213798923115 63560506015600820698384673)
  ·
    refine ⟨47670379511700615523788505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63560506015600820698384673 47670379511700615523788505)
    ·
      refine ⟨35752784633775461642841379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47670379511700615523788505 35752784633775461642841379)
      ·
        refine ⟨53629176950663192464262069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35752784633775461642841379 53629176950663192464262069)
        ·
          refine ⟨5027735339124674293524569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53629176950663192464262069 5027735339124674293524569)
          ·
            refine ⟨3770801504343505720143427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5027735339124674293524569 3770801504343505720143427)
            ·
              refine ⟨5656202256515258580215141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770801504343505720143427 5656202256515258580215141)
              ·
                refine ⟨1060537923096610983790339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5656202256515258580215141 1060537923096610983790339)
                ·
                  refine ⟨1590806884644916475685509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060537923096610983790339 1590806884644916475685509)
                  ·
                    refine ⟨298276290870921839191033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1590806884644916475685509 298276290870921839191033)
                    ·
                      rfl

theorem cell23_1742673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_1742673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742673 prefixEnd_1742673 := by exact prefixLift 1742673
  have htrace : WordTrace (prefixWord ++ tailWord_1742673) baseStart_1742673 baseEnd_1742673 := by
    simpa [prefixWord, tailWord_1742673, baseEnd_1742673] using wordTrace_append hprefix tailTrace_1742673
  have hstable : (prefixWord ++ tailWord_1742673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742673).length < 2 ^ (prefixWord ++ tailWord_1742673).sum := by decide
  have hdescent : baseEnd_1742673 < baseStart_1742673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742699 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 1, 5]
def baseStart_1742699 : Nat := 118140960795 + 1742699 * 2 ^ 59
def prefixEnd_1742699 : Nat := 4983230072969 + 3 ^ 40 * 1742699 * 2
def baseEnd_1742699 : Nat := 298280741036594138615993

theorem tailTrace_1742699 : CollatzResearch.WordTrace tailWord_1742699 prefixEnd_1742699 298280741036594138615993 := by
  unfold tailWord_1742699
  simp only [CollatzResearch.WordTrace]
  refine ⟨63561454313506627138831151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42374302875671084759220767 63561454313506627138831151)
  ·
    refine ⟨95342181470259940708246727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63561454313506627138831151 95342181470259940708246727)
    ·
      refine ⟨143013272205389911062370091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95342181470259940708246727 143013272205389911062370091)
      ·
        refine ⟨214519908308084866593555137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143013272205389911062370091 214519908308084866593555137)
        ·
          refine ⟨160889931231063649945166353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214519908308084866593555137 160889931231063649945166353)
          ·
            refine ⟨120667448423297737458874765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160889931231063649945166353 120667448423297737458874765)
            ·
              refine ⟨45250293158736651547078037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120667448423297737458874765 45250293158736651547078037)
              ·
                refine ⟨2121107491815780541269283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45250293158736651547078037 2121107491815780541269283)
                ·
                  refine ⟨3181661237723670811903925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121107491815780541269283 3181661237723670811903925)
                  ·
                    refine ⟨298280741036594138615993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3181661237723670811903925 298280741036594138615993)
                    ·
                      rfl

theorem cell23_1742699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 5].length) (baseStart_1742699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742699 prefixEnd_1742699 := by exact prefixLift 1742699
  have htrace : WordTrace (prefixWord ++ tailWord_1742699) baseStart_1742699 baseEnd_1742699 := by
    simpa [prefixWord, tailWord_1742699, baseEnd_1742699] using wordTrace_append hprefix tailTrace_1742699
  have hstable : (prefixWord ++ tailWord_1742699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742699).length < 2 ^ (prefixWord ++ tailWord_1742699).sum := by decide
  have hdescent : baseEnd_1742699 < baseStart_1742699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742712 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 2, 10]
def baseStart_1742712 : Nat := 118140960795 + 1742712 * 2 ^ 59
def prefixEnd_1742712 : Nat := 4983230072969 + 3 ^ 40 * 1742712 * 2
def baseEnd_1742712 : Nat := 298282966119430288328473

theorem tailTrace_1742712 : CollatzResearch.WordTrace tailWord_1742712 prefixEnd_1742712 298282966119430288328473 := by
  unfold tailWord_1742712
  simp only [CollatzResearch.WordTrace]
  refine ⟨31780964231229765179527195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42374618974973020239369593 31780964231229765179527195)
  ·
    refine ⟨47671446346844647769290793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31780964231229765179527195 47671446346844647769290793)
    ·
      refine ⟨35753584760133485826968095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47671446346844647769290793 35753584760133485826968095)
      ·
        refine ⟨53630377140200228740452143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35753584760133485826968095 53630377140200228740452143)
        ·
          refine ⟨80445565710300343110678215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53630377140200228740452143 80445565710300343110678215)
          ·
            refine ⟨120668348565450514666017323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80445565710300343110678215 120668348565450514666017323)
            ·
              refine ⟨181002522848175771999025985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120668348565450514666017323 181002522848175771999025985)
              ·
                refine ⟨135751892136131828999269489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181002522848175771999025985 135751892136131828999269489)
                ·
                  refine ⟨101813919102098871749452117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135751892136131828999269489 101813919102098871749452117)
                  ·
                    refine ⟨298282966119430288328473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 101813919102098871749452117 298282966119430288328473)
                    ·
                      rfl

theorem cell23_1742712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_1742712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742712 prefixEnd_1742712 := by exact prefixLift 1742712
  have htrace : WordTrace (prefixWord ++ tailWord_1742712) baseStart_1742712 baseEnd_1742712 := by
    simpa [prefixWord, tailWord_1742712, baseEnd_1742712] using wordTrace_append hprefix tailTrace_1742712
  have hstable : (prefixWord ++ tailWord_1742712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742712).length < 2 ^ (prefixWord ++ tailWord_1742712).sum := by decide
  have hdescent : baseEnd_1742712 < baseStart_1742712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742730 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1742730 : Nat := 118140960795 + 1742730 * 2 ^ 59
def prefixEnd_1742730 : Nat := 4983230072969 + 3 ^ 40 * 1742730 * 2
def baseEnd_1742730 : Nat := 894858141010071794560337

theorem tailTrace_1742730 : CollatzResearch.WordTrace tailWord_1742730 prefixEnd_1742730 894858141010071794560337 := by
  unfold tailWord_1742730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15890646244098579858302411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42375056650929546288806429 15890646244098579858302411)
  ·
    refine ⟨23835969366147869787453617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15890646244098579858302411 23835969366147869787453617)
    ·
      refine ⟨17876977024610902340590213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23835969366147869787453617 17876977024610902340590213)
      ·
        refine ⟨3351933192114544188860665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17876977024610902340590213 3351933192114544188860665)
        ·
          refine ⟨2513949894085908141645499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3351933192114544188860665 2513949894085908141645499)
          ·
            refine ⟨3770924841128862212468249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513949894085908141645499 3770924841128862212468249)
            ·
              refine ⟨2828193630846646659351187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3770924841128862212468249 2828193630846646659351187)
              ·
                refine ⟨4242290446269969989026781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828193630846646659351187 4242290446269969989026781)
                ·
                  refine ⟨1590858917351238745885043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4242290446269969989026781 1590858917351238745885043)
                  ·
                    refine ⟨2386288376026858118827565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1590858917351238745885043 2386288376026858118827565)
                    ·
                      refine ⟨894858141010071794560337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2386288376026858118827565 894858141010071794560337)
                      ·
                        rfl

theorem cell23_1742730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1742730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742730 prefixEnd_1742730 := by exact prefixLift 1742730
  have htrace : WordTrace (prefixWord ++ tailWord_1742730) baseStart_1742730 baseEnd_1742730 := by
    simpa [prefixWord, tailWord_1742730, baseEnd_1742730] using wordTrace_append hprefix tailTrace_1742730
  have hstable : (prefixWord ++ tailWord_1742730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742730).length < 2 ^ (prefixWord ++ tailWord_1742730).sum := by decide
  have hdescent : baseEnd_1742730 < baseStart_1742730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742746 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_1742746 : Nat := 118140960795 + 1742746 * 2 ^ 59
def prefixEnd_1742746 : Nat := 4983230072969 + 3 ^ 40 * 1742746 * 2
def baseEnd_1742746 : Nat := 298288785566847910653421

theorem tailTrace_1742746 : CollatzResearch.WordTrace tailWord_1742746 prefixEnd_1742746 298288785566847910653421 := by
  unfold tailWord_1742746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15890792136084088541448023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42375445696224236110528061 15890792136084088541448023)
  ·
    refine ⟨23836188204126132812172035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15890792136084088541448023 23836188204126132812172035)
    ·
      refine ⟨35754282306189199218258053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23836188204126132812172035 35754282306189199218258053)
      ·
        refine ⟨6703927932410474853423385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35754282306189199218258053 6703927932410474853423385)
        ·
          refine ⟨5027945949307856140067539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6703927932410474853423385 5027945949307856140067539)
          ·
            refine ⟨7541918923961784210101309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5027945949307856140067539 7541918923961784210101309)
            ·
              refine ⟨2828219596485669078787991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7541918923961784210101309 2828219596485669078787991)
              ·
                refine ⟨4242329394728503618181987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828219596485669078787991 4242329394728503618181987)
                ·
                  refine ⟨6363494092092755427272981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4242329394728503618181987 6363494092092755427272981)
                  ·
                    refine ⟨298288785566847910653421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6363494092092755427272981 298288785566847910653421)
                    ·
                      rfl

theorem cell23_1742746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_1742746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742746 prefixEnd_1742746 := by exact prefixLift 1742746
  have htrace : WordTrace (prefixWord ++ tailWord_1742746) baseStart_1742746 baseEnd_1742746 := by
    simpa [prefixWord, tailWord_1742746, baseEnd_1742746] using wordTrace_append hprefix tailTrace_1742746
  have hstable : (prefixWord ++ tailWord_1742746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742746).length < 2 ^ (prefixWord ++ tailWord_1742746).sum := by decide
  have hdescent : baseEnd_1742746 < baseStart_1742746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742773 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_1742773 : Nat := 118140960795 + 1742773 * 2 ^ 59
def prefixEnd_1742773 : Nat := 4983230072969 + 3 ^ 40 * 1742773 * 2
def baseEnd_1742773 : Nat := 894880220678215126322639

theorem tailTrace_1742773 : CollatzResearch.WordTrace tailWord_1742773 prefixEnd_1742773 894880220678215126322639 := by
  unfold tailWord_1742773
  simp only [CollatzResearch.WordTrace]
  refine ⟨63564153315238537777024973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42376102210159025184683315 63564153315238537777024973)
  ·
    refine ⟨23836557493214451666384365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63564153315238537777024973 23836557493214451666384365)
    ·
      refine ⟨8938709059955419374894137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23836557493214451666384365 8938709059955419374894137)
      ·
        refine ⟨6704031794966564531170603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8938709059955419374894137 6704031794966564531170603)
        ·
          refine ⟨10056047692449846796755905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6704031794966564531170603 10056047692449846796755905)
          ·
            refine ⟨7542035769337385097566929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10056047692449846796755905 7542035769337385097566929)
            ·
              refine ⟨5656526827003038823175197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7542035769337385097566929 5656526827003038823175197)
              ·
                refine ⟨2121197560126139558690699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5656526827003038823175197 2121197560126139558690699)
                ·
                  refine ⟨3181796340189209338036049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121197560126139558690699 3181796340189209338036049)
                  ·
                    refine ⟨2386347255141907003527037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3181796340189209338036049 2386347255141907003527037)
                    ·
                      refine ⟨894880220678215126322639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2386347255141907003527037 894880220678215126322639)
                      ·
                        rfl

theorem cell23_1742773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_1742773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742773 prefixEnd_1742773 := by exact prefixLift 1742773
  have htrace : WordTrace (prefixWord ++ tailWord_1742773) baseStart_1742773 baseEnd_1742773 := by
    simpa [prefixWord, tailWord_1742773, baseEnd_1742773] using wordTrace_append hprefix tailTrace_1742773
  have hstable : (prefixWord ++ tailWord_1742773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742773).length < 2 ^ (prefixWord ++ tailWord_1742773).sum := by decide
  have hdescent : baseEnd_1742773 < baseStart_1742773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742838 : List Nat := [5, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_1742838 : Nat := 118140960795 + 1742838 * 2 ^ 59
def prefixEnd_1742838 : Nat := 4983230072969 + 3 ^ 40 * 1742838 * 2
def baseEnd_1742838 : Nat := 894913596920757372009841

theorem tailTrace_1742838 : CollatzResearch.WordTrace tailWord_1742838 prefixEnd_1742838 894913596920757372009841 := by
  unfold tailWord_1742838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972907753750190867383823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42377682706668702585427445 3972907753750190867383823)
  ·
    refine ⟨5959361630625286301075735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3972907753750190867383823 5959361630625286301075735)
    ·
      refine ⟨8939042445937929451613603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5959361630625286301075735 8939042445937929451613603)
      ·
        refine ⟨13408563668906894177420405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8939042445937929451613603 13408563668906894177420405)
        ·
          refine ⟨1257052843960021329133163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13408563668906894177420405 1257052843960021329133163)
          ·
            refine ⟨1885579265940031993699745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257052843960021329133163 1885579265940031993699745)
            ·
              refine ⟨1414184449455023995274809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885579265940031993699745 1414184449455023995274809)
              ·
                refine ⟨1060638337091267996456107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1414184449455023995274809 1060638337091267996456107)
                ·
                  refine ⟨1590957505636901994684161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060638337091267996456107 1590957505636901994684161)
                  ·
                    refine ⟨1193218129227676496013121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590957505636901994684161 1193218129227676496013121)
                    ·
                      refine ⟨894913596920757372009841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193218129227676496013121 894913596920757372009841)
                      ·
                        rfl

theorem cell23_1742838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_1742838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742838 prefixEnd_1742838 := by exact prefixLift 1742838
  have htrace : WordTrace (prefixWord ++ tailWord_1742838) baseStart_1742838 baseEnd_1742838 := by
    simpa [prefixWord, tailWord_1742838, baseEnd_1742838] using wordTrace_append hprefix tailTrace_1742838
  have hstable : (prefixWord ++ tailWord_1742838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742838).length < 2 ^ (prefixWord ++ tailWord_1742838).sum := by decide
  have hdescent : baseEnd_1742838 < baseStart_1742838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742839 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_1742839 : Nat := 118140960795 + 1742839 * 2 ^ 59
def prefixEnd_1742839 : Nat := 4983230072969 + 3 ^ 40 * 1742839 * 2
def baseEnd_1742839 : Nat := 894914110401411868097335

theorem tailTrace_1742839 : CollatzResearch.WordTrace tailWord_1742839 prefixEnd_1742839 894914110401411868097335 := by
  unfold tailWord_1742839
  simp only [CollatzResearch.WordTrace]
  refine ⟨63566560532999431048927571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42377707021999620699285047 63566560532999431048927571)
  ·
    refine ⟨95349840799499146573391357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63566560532999431048927571 95349840799499146573391357)
    ·
      refine ⟨35756190299812179965021759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95349840799499146573391357 35756190299812179965021759)
      ·
        refine ⟨53634285449718269947532639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35756190299812179965021759 53634285449718269947532639)
        ·
          refine ⟨80451428174577404921298959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53634285449718269947532639 80451428174577404921298959)
          ·
            refine ⟨120677142261866107381948439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80451428174577404921298959 120677142261866107381948439)
            ·
              refine ⟨181015713392799161072922659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120677142261866107381948439 181015713392799161072922659)
              ·
                refine ⟨271523570089198741609383989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181015713392799161072922659 271523570089198741609383989)
                ·
                  refine ⟨25455334695862382025879749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 271523570089198741609383989 25455334695862382025879749)
                  ·
                    refine ⟨4772875255474196629852453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25455334695862382025879749 4772875255474196629852453)
                    ·
                      refine ⟨894914110401411868097335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4772875255474196629852453 894914110401411868097335)
                      ·
                        rfl

theorem cell23_1742839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_1742839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742839 prefixEnd_1742839 := by exact prefixLift 1742839
  have htrace : WordTrace (prefixWord ++ tailWord_1742839) baseStart_1742839 baseEnd_1742839 := by
    simpa [prefixWord, tailWord_1742839, baseEnd_1742839] using wordTrace_append hprefix tailTrace_1742839
  have hstable : (prefixWord ++ tailWord_1742839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742839).length < 2 ^ (prefixWord ++ tailWord_1742839).sum := by decide
  have hdescent : baseEnd_1742839 < baseStart_1742839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742843 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 4, 2, 2]
def baseStart_1742843 : Nat := 118140960795 + 1742843 * 2 ^ 59
def prefixEnd_1742843 : Nat := 4983230072969 + 3 ^ 40 * 1742843 * 2
def baseEnd_1742843 : Nat := 894916164324029852447317

theorem tailTrace_1742843 : CollatzResearch.WordTrace tailWord_1742843 prefixEnd_1742843 894916164324029852447317 := by
  unfold tailWord_1742843
  simp only [CollatzResearch.WordTrace]
  refine ⟨63566706424984939732073183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42377804283323293154715455 63566706424984939732073183)
  ·
    refine ⟨95350059637477409598109775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63566706424984939732073183 95350059637477409598109775)
    ·
      refine ⟨143025089456216114397164663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95350059637477409598109775 143025089456216114397164663)
      ·
        refine ⟨214537634184324171595746995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143025089456216114397164663 214537634184324171595746995)
        ·
          refine ⟨321806451276486257393620493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214537634184324171595746995 321806451276486257393620493)
          ·
            refine ⟨120677419228682346522607685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321806451276486257393620493 120677419228682346522607685)
            ·
              refine ⟨22627016105377939972988941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120677419228682346522607685 22627016105377939972988941)
              ·
                refine ⟨8485131039516727489870853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22627016105377939972988941 8485131039516727489870853)
                ·
                  refine ⟨1590962069909386404350785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8485131039516727489870853 1590962069909386404350785)
                  ·
                    refine ⟨1193221552432039803263089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590962069909386404350785 1193221552432039803263089)
                    ·
                      refine ⟨894916164324029852447317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193221552432039803263089 894916164324029852447317)
                      ·
                        rfl

theorem cell23_1742843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 2, 2].length) (baseStart_1742843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742843 prefixEnd_1742843 := by exact prefixLift 1742843
  have htrace : WordTrace (prefixWord ++ tailWord_1742843) baseStart_1742843 baseEnd_1742843 := by
    simpa [prefixWord, tailWord_1742843, baseEnd_1742843] using wordTrace_append hprefix tailTrace_1742843
  have hstable : (prefixWord ++ tailWord_1742843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742843).length < 2 ^ (prefixWord ++ tailWord_1742843).sum := by decide
  have hdescent : baseEnd_1742843 < baseStart_1742843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742856 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1742856 : Nat := 118140960795 + 1742856 * 2 ^ 59
def prefixEnd_1742856 : Nat := 4983230072969 + 3 ^ 40 * 1742856 * 2
def baseEnd_1742856 : Nat := 894922839572538301584757

theorem tailTrace_1742856 : CollatzResearch.WordTrace tailWord_1742856 prefixEnd_1742856 894922839572538301584757 := by
  unfold tailWord_1742856
  simp only [CollatzResearch.WordTrace]
  refine ⟨31783590286968921476148211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42378120382625228634864281 31783590286968921476148211)
  ·
    refine ⟨47675385430453382214222317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31783590286968921476148211 47675385430453382214222317)
    ·
      refine ⟨17878269536420018330333369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47675385430453382214222317 17878269536420018330333369)
      ·
        refine ⟨13408702152315013747750027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17878269536420018330333369 13408702152315013747750027)
        ·
          refine ⟨20113053228472520621625041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13408702152315013747750027 20113053228472520621625041)
          ·
            refine ⟨15084789921354390466218781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20113053228472520621625041 15084789921354390466218781)
            ·
              refine ⟨5656796220507896424832043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15084789921354390466218781 5656796220507896424832043)
              ·
                refine ⟨8485194330761844637248065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5656796220507896424832043 8485194330761844637248065)
                ·
                  refine ⟨6363895748071383477936049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8485194330761844637248065 6363895748071383477936049)
                  ·
                    refine ⟨4772921811053537608452037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6363895748071383477936049 4772921811053537608452037)
                    ·
                      refine ⟨894922839572538301584757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4772921811053537608452037 894922839572538301584757)
                      ·
                        rfl

theorem cell23_1742856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1742856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742856 prefixEnd_1742856 := by exact prefixLift 1742856
  have htrace : WordTrace (prefixWord ++ tailWord_1742856) baseStart_1742856 baseEnd_1742856 := by
    simpa [prefixWord, tailWord_1742856, baseEnd_1742856] using wordTrace_append hprefix tailTrace_1742856
  have hstable : (prefixWord ++ tailWord_1742856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742856).length < 2 ^ (prefixWord ++ tailWord_1742856).sum := by decide
  have hdescent : baseEnd_1742856 < baseStart_1742856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742860 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 2, 2, 2]
def baseStart_1742860 : Nat := 118140960795 + 1742860 * 2 ^ 59
def prefixEnd_1742860 : Nat := 4983230072969 + 3 ^ 40 * 1742860 * 2
def baseEnd_1742860 : Nat := 894924893495156285934739

theorem tailTrace_1742860 : CollatzResearch.WordTrace tailWord_1742860 prefixEnd_1742860 894924893495156285934739 := by
  unfold tailWord_1742860
  simp only [CollatzResearch.WordTrace]
  refine ⟨31783663232961675817721017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42378217643948901090294689 31783663232961675817721017)
  ·
    refine ⟨23837747424721256863290763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31783663232961675817721017 23837747424721256863290763)
    ·
      refine ⟨35756621137081885294936145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23837747424721256863290763 35756621137081885294936145)
      ·
        refine ⟨26817465852811413971202109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35756621137081885294936145 26817465852811413971202109)
        ·
          refine ⟨10056549694804280239200791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26817465852811413971202109 10056549694804280239200791)
          ·
            refine ⟨15084824542206420358801187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10056549694804280239200791 15084824542206420358801187)
            ·
              refine ⟨22627236813309630538201781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15084824542206420358801187 22627236813309630538201781)
              ·
                refine ⟨2121303451247777862956417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22627236813309630538201781 2121303451247777862956417)
                ·
                  refine ⟨1590977588435833397217313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2121303451247777862956417 1590977588435833397217313)
                  ·
                    refine ⟨1193233191326875047912985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1590977588435833397217313 1193233191326875047912985)
                    ·
                      refine ⟨894924893495156285934739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193233191326875047912985 894924893495156285934739)
                      ·
                        rfl

theorem cell23_1742860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_1742860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742860 prefixEnd_1742860 := by exact prefixLift 1742860
  have htrace : WordTrace (prefixWord ++ tailWord_1742860) baseStart_1742860 baseEnd_1742860 := by
    simpa [prefixWord, tailWord_1742860, baseEnd_1742860] using wordTrace_append hprefix tailTrace_1742860
  have hstable : (prefixWord ++ tailWord_1742860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742860).length < 2 ^ (prefixWord ++ tailWord_1742860).sum := by decide
  have hdescent : baseEnd_1742860 < baseStart_1742860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742883 : List Nat := [1, 1, 1, 4, 3, 1, 4, 3, 5]
def baseStart_1742883 : Nat := 118140960795 + 1742883 * 2 ^ 59
def prefixEnd_1742883 : Nat := 4983230072969 + 3 ^ 40 * 1742883 * 2
def baseEnd_1742883 : Nat := 99437411505578855105237

theorem tailTrace_1742883 : CollatzResearch.WordTrace tailWord_1742883 prefixEnd_1742883 99437411505578855105237 := by
  unfold tailWord_1742883
  simp only [CollatzResearch.WordTrace]
  refine ⟨63568165344840026563529303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42378776896560017709019535 63568165344840026563529303)
  ·
    refine ⟨95352248017260039845293955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63568165344840026563529303 95352248017260039845293955)
    ·
      refine ⟨143028372025890059767940933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95352248017260039845293955 143028372025890059767940933)
      ·
        refine ⟨26817819754854386206488925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143028372025890059767940933 26817819754854386206488925)
        ·
          refine ⟨10056682408070394827433347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26817819754854386206488925 10056682408070394827433347)
          ·
            refine ⟨15085023612105592241150021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10056682408070394827433347 15085023612105592241150021)
            ·
              refine ⟨2828441927269798545215629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15085023612105592241150021 2828441927269798545215629)
              ·
                refine ⟨1060665722726174454455861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2828441927269798545215629 1060665722726174454455861)
                ·
                  refine ⟨99437411505578855105237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1060665722726174454455861 99437411505578855105237)
                  ·
                    rfl

theorem cell23_1742883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 5].length) (baseStart_1742883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742883 prefixEnd_1742883 := by exact prefixLift 1742883
  have htrace : WordTrace (prefixWord ++ tailWord_1742883) baseStart_1742883 baseEnd_1742883 := by
    simpa [prefixWord, tailWord_1742883, baseEnd_1742883] using wordTrace_append hprefix tailTrace_1742883
  have hstable : (prefixWord ++ tailWord_1742883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742883).length < 2 ^ (prefixWord ++ tailWord_1742883).sum := by decide
  have hdescent : baseEnd_1742883 < baseStart_1742883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742894 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_1742894 : Nat := 118140960795 + 1742894 * 2 ^ 59
def prefixEnd_1742894 : Nat := 4983230072969 + 3 ^ 40 * 1742894 * 2
def baseEnd_1742894 : Nat := 894942351837409152909583

theorem tailTrace_1742894 : CollatzResearch.WordTrace tailWord_1742894 prefixEnd_1742894 894942351837409152909583 := by
  unfold tailWord_1742894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7946070818475021930272467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42379044365200116961453157 7946070818475021930272467)
  ·
    refine ⟨11919106227712532895408701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7946070818475021930272467 11919106227712532895408701)
    ·
      refine ⟨4469664835392199835778263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11919106227712532895408701 4469664835392199835778263)
      ·
        refine ⟨6704497253088299753667395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469664835392199835778263 6704497253088299753667395)
        ·
          refine ⟨10056745879632449630501093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6704497253088299753667395 10056745879632449630501093)
          ·
            refine ⟨1885639852431084305718955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10056745879632449630501093 1885639852431084305718955)
            ·
              refine ⟨2828459778646626458578433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885639852431084305718955 2828459778646626458578433)
              ·
                refine ⟨2121344833984969843933825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2828459778646626458578433 2121344833984969843933825)
                ·
                  refine ⟨1591008625488727382950369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2121344833984969843933825 1591008625488727382950369)
                  ·
                    refine ⟨1193256469116545537212777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1591008625488727382950369 1193256469116545537212777)
                    ·
                      refine ⟨894942351837409152909583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193256469116545537212777 894942351837409152909583)
                      ·
                        rfl

theorem cell23_1742894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_1742894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742894 prefixEnd_1742894 := by exact prefixLift 1742894
  have htrace : WordTrace (prefixWord ++ tailWord_1742894) baseStart_1742894 baseEnd_1742894 := by
    simpa [prefixWord, tailWord_1742894, baseEnd_1742894] using wordTrace_append hprefix tailTrace_1742894
  have hstable : (prefixWord ++ tailWord_1742894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742894).length < 2 ^ (prefixWord ++ tailWord_1742894).sum := by decide
  have hdescent : baseEnd_1742894 < baseStart_1742894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742900 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 7]
def baseStart_1742900 : Nat := 118140960795 + 1742900 * 2 ^ 59
def prefixEnd_1742900 : Nat := 4983230072969 + 3 ^ 40 * 1742900 * 2
def baseEnd_1742900 : Nat := 99438381413481792159395

theorem tailTrace_1742900 : CollatzResearch.WordTrace tailWord_1742900 prefixEnd_1742900 99438381413481792159395 := by
  unfold tailWord_1742900
  simp only [CollatzResearch.WordTrace]
  refine ⟨31784392692889219233449077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42379190257185625644598769 31784392692889219233449077)
  ·
    refine ⟨2979786814958364303135851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31784392692889219233449077 2979786814958364303135851)
    ·
      refine ⟨4469680222437546454703777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2979786814958364303135851 4469680222437546454703777)
      ·
        refine ⟨3352260166828159841027833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4469680222437546454703777 3352260166828159841027833)
        ·
          refine ⟨2514195125121119880770875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3352260166828159841027833 2514195125121119880770875)
          ·
            refine ⟨3771292687681679821156313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514195125121119880770875 3771292687681679821156313)
            ·
              refine ⟨2828469515761259865867235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3771292687681679821156313 2828469515761259865867235)
              ·
                refine ⟨4242704273641889798800853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828469515761259865867235 4242704273641889798800853)
                ·
                  refine ⟨99438381413481792159395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4242704273641889798800853 99438381413481792159395)
                  ·
                    rfl

theorem cell23_1742900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_1742900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742900 prefixEnd_1742900 := by exact prefixLift 1742900
  have htrace : WordTrace (prefixWord ++ tailWord_1742900) baseStart_1742900 baseEnd_1742900 := by
    simpa [prefixWord, tailWord_1742900, baseEnd_1742900] using wordTrace_append hprefix tailTrace_1742900
  have hstable : (prefixWord ++ tailWord_1742900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742900).length < 2 ^ (prefixWord ++ tailWord_1742900).sum := by decide
  have hdescent : baseEnd_1742900 < baseStart_1742900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742934 : List Nat := [5, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1742934 : Nat := 118140960795 + 1742934 * 2 ^ 59
def prefixEnd_1742934 : Nat := 4983230072969 + 3 ^ 40 * 1742934 * 2
def baseEnd_1742934 : Nat := 99440321229287666267711

theorem tailTrace_1742934 : CollatzResearch.WordTrace tailWord_1742934 prefixEnd_1742934 99440321229287666267711 := by
  unfold tailWord_1742934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973126591728453892102241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42380016978436841515757237 3973126591728453892102241)
  ·
    refine ⟨2979844943796340419076681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3973126591728453892102241 2979844943796340419076681)
    ·
      refine ⟨2234883707847255314307511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2979844943796340419076681 2234883707847255314307511)
      ·
        refine ⟨3352325561770882971461267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234883707847255314307511 3352325561770882971461267)
        ·
          refine ⟨5028488342656324457191901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352325561770882971461267 5028488342656324457191901)
          ·
            refine ⟨1885683128496121671446963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5028488342656324457191901 1885683128496121671446963)
            ·
              refine ⟨2828524692744182507170445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885683128496121671446963 2828524692744182507170445)
              ·
                refine ⟨1060696759779068440188917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2828524692744182507170445 1060696759779068440188917)
                ·
                  refine ⟨99440321229287666267711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1060696759779068440188917 99440321229287666267711)
                  ·
                    rfl

theorem cell23_1742934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1742934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742934 prefixEnd_1742934 := by exact prefixLift 1742934
  have htrace : WordTrace (prefixWord ++ tailWord_1742934) baseStart_1742934 baseEnd_1742934 := by
    simpa [prefixWord, tailWord_1742934, baseEnd_1742934] using wordTrace_append hprefix tailTrace_1742934
  have hstable : (prefixWord ++ tailWord_1742934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742934).length < 2 ^ (prefixWord ++ tailWord_1742934).sum := by decide
  have hdescent : baseEnd_1742934 < baseStart_1742934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742953 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 2, 2, 3]
def baseStart_1742953 : Nat := 118140960795 + 1742953 * 2 ^ 59
def prefixEnd_1742953 : Nat := 4983230072969 + 3 ^ 40 * 1742953 * 2
def baseEnd_1742953 : Nat := 894972647196024422071811

theorem tailTrace_1742953 : CollatzResearch.WordTrace tailWord_1742953 prefixEnd_1742953 894972647196024422071811 := by
  unfold tailWord_1742953
  simp only [CollatzResearch.WordTrace]
  refine ⟨63570718454586428518577513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42380478969724285679051675 63570718454586428518577513)
  ·
    refine ⟨47678038840939821388933135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63570718454586428518577513 47678038840939821388933135)
    ·
      refine ⟨71517058261409732083399703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47678038840939821388933135 71517058261409732083399703)
      ·
        refine ⟨107275587392114598125099555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71517058261409732083399703 107275587392114598125099555)
        ·
          refine ⟨160913381088171897187649333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107275587392114598125099555 160913381088171897187649333)
          ·
            refine ⟨15085629477016115361342125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160913381088171897187649333 15085629477016115361342125)
            ·
              refine ⟨5657111053881043260503297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15085629477016115361342125 5657111053881043260503297)
              ·
                refine ⟨4242833290410782445377473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5657111053881043260503297 4242833290410782445377473)
                ·
                  refine ⟨3182124967808086834033105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4242833290410782445377473 3182124967808086834033105)
                  ·
                    refine ⟨2386593725856065125524829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3182124967808086834033105 2386593725856065125524829)
                    ·
                      refine ⟨894972647196024422071811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2386593725856065125524829 894972647196024422071811)
                      ·
                        rfl

theorem cell23_1742953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2, 3].length) (baseStart_1742953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742953 prefixEnd_1742953 := by exact prefixLift 1742953
  have htrace : WordTrace (prefixWord ++ tailWord_1742953) baseStart_1742953 baseEnd_1742953 := by
    simpa [prefixWord, tailWord_1742953, baseEnd_1742953] using wordTrace_append hprefix tailTrace_1742953
  have hstable : (prefixWord ++ tailWord_1742953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742953).length < 2 ^ (prefixWord ++ tailWord_1742953).sum := by decide
  have hdescent : baseEnd_1742953 < baseStart_1742953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742956 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 8]
def baseStart_1742956 : Nat := 118140960795 + 1742956 * 2 ^ 59
def prefixEnd_1742956 : Nat := 4983230072969 + 3 ^ 40 * 1742956 * 2
def baseEnd_1742956 : Nat := 99441576404220878926033

theorem tailTrace_1742956 : CollatzResearch.WordTrace tailWord_1742956 prefixEnd_1742956 99441576404220878926033 := by
  unfold tailWord_1742956
  simp only [CollatzResearch.WordTrace]
  refine ⟨31785413936787780015468361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42380551915717040020624481 31785413936787780015468361)
  ·
    refine ⟨23839060452590835011601271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31785413936787780015468361 23839060452590835011601271)
    ·
      refine ⟨35758590678886252517401907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23839060452590835011601271 35758590678886252517401907)
      ·
        refine ⟨53637886018329378776102861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35758590678886252517401907 53637886018329378776102861)
        ·
          refine ⟨20114207256873517041038573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53637886018329378776102861 20114207256873517041038573)
          ·
            refine ⟨7542827721327568890389465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20114207256873517041038573 7542827721327568890389465)
            ·
              refine ⟨5657120790995676667792099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7542827721327568890389465 5657120790995676667792099)
              ·
                refine ⟨8485681186493515001688149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657120790995676667792099 8485681186493515001688149)
                ·
                  refine ⟨99441576404220878926033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8485681186493515001688149 99441576404220878926033)
                  ·
                    rfl

theorem cell23_1742956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_1742956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742956 prefixEnd_1742956 := by exact prefixLift 1742956
  have htrace : WordTrace (prefixWord ++ tailWord_1742956) baseStart_1742956 baseEnd_1742956 := by
    simpa [prefixWord, tailWord_1742956, baseEnd_1742956] using wordTrace_append hprefix tailTrace_1742956
  have hstable : (prefixWord ++ tailWord_1742956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742956).length < 2 ^ (prefixWord ++ tailWord_1742956).sum := by decide
  have hdescent : baseEnd_1742956 < baseStart_1742956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742960 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 3, 4]
def baseStart_1742960 : Nat := 118140960795 + 1742960 * 2 ^ 59
def prefixEnd_1742960 : Nat := 4983230072969 + 3 ^ 40 * 1742960 * 2
def baseEnd_1742960 : Nat := 298325413853535298228093

theorem tailTrace_1742960 : CollatzResearch.WordTrace tailWord_1742960 prefixEnd_1742960 298325413853535298228093 := by
  unfold tailWord_1742960
  simp only [CollatzResearch.WordTrace]
  refine ⟨31785486882780534357041167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42380649177040712476054889 31785486882780534357041167)
  ·
    refine ⟨47678230324170801535561751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31785486882780534357041167 47678230324170801535561751)
    ·
      refine ⟨71517345486256202303342627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47678230324170801535561751 71517345486256202303342627)
      ·
        refine ⟨107276018229384303455013941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71517345486256202303342627 107276018229384303455013941)
        ·
          refine ⟨10057126709004778448907557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107276018229384303455013941 10057126709004778448907557)
          ·
            refine ⟨1885711257938395959170167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10057126709004778448907557 1885711257938395959170167)
            ·
              refine ⟨2828566886907593938755251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885711257938395959170167 2828566886907593938755251)
              ·
                refine ⟨4242850330361390908132877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828566886907593938755251 4242850330361390908132877)
                ·
                  refine ⟨1591068873885521590549829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4242850330361390908132877 1591068873885521590549829)
                  ·
                    refine ⟨298325413853535298228093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1591068873885521590549829 298325413853535298228093)
                    ·
                      rfl

theorem cell23_1742960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3, 4].length) (baseStart_1742960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742960 prefixEnd_1742960 := by exact prefixLift 1742960
  have htrace : WordTrace (prefixWord ++ tailWord_1742960) baseStart_1742960 baseEnd_1742960 := by
    simpa [prefixWord, tailWord_1742960, baseEnd_1742960] using wordTrace_append hprefix tailTrace_1742960
  have hstable : (prefixWord ++ tailWord_1742960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742960).length < 2 ^ (prefixWord ++ tailWord_1742960).sum := by decide
  have hdescent : baseEnd_1742960 < baseStart_1742960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742973 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 6]
def baseStart_1742973 : Nat := 118140960795 + 1742973 * 2 ^ 59
def prefixEnd_1742973 : Nat := 4983230072969 + 3 ^ 40 * 1742973 * 2
def baseEnd_1742973 : Nat := 99442546312123815980191

theorem tailTrace_1742973 : CollatzResearch.WordTrace tailWord_1742973 prefixEnd_1742973 99442546312123815980191 := by
  unfold tailWord_1742973
  simp only [CollatzResearch.WordTrace]
  refine ⟨63571447914513971934305573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42380965276342647956203715 63571447914513971934305573)
  ·
    refine ⟨11919646483971369737682295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63571447914513971934305573 11919646483971369737682295)
    ·
      refine ⟨17879469725957054606523443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11919646483971369737682295 17879469725957054606523443)
      ·
        refine ⟨26819204588935581909785165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17879469725957054606523443 26819204588935581909785165)
        ·
          refine ⟨10057201720850843216169437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26819204588935581909785165 10057201720850843216169437)
          ·
            refine ⟨3771450645319066206063539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10057201720850843216169437 3771450645319066206063539)
            ·
              refine ⟨5657175967978599309095309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3771450645319066206063539 5657175967978599309095309)
              ·
                refine ⟨2121440987991974740910741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5657175967978599309095309 2121440987991974740910741)
                ·
                  refine ⟨99442546312123815980191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2121440987991974740910741 99442546312123815980191)
                  ·
                    rfl

theorem cell23_1742973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_1742973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1742973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1742973 prefixEnd_1742973 := by exact prefixLift 1742973
  have htrace : WordTrace (prefixWord ++ tailWord_1742973) baseStart_1742973 baseEnd_1742973 := by
    simpa [prefixWord, tailWord_1742973, baseEnd_1742973] using wordTrace_append hprefix tailTrace_1742973
  have hstable : (prefixWord ++ tailWord_1742973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742973).length < 2 ^ (prefixWord ++ tailWord_1742973).sum := by decide
  have hdescent : baseEnd_1742973 < baseStart_1742973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743023 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 2, 6, 2]
def baseStart_1743023 : Nat := 118140960795 + 1743023 * 2 ^ 59
def prefixEnd_1743023 : Nat := 4983230072969 + 3 ^ 40 * 1743023 * 2
def baseEnd_1743023 : Nat := 895008590841839148196489

theorem tailTrace_1743023 : CollatzResearch.WordTrace tailWord_1743023 prefixEnd_1743023 895008590841839148196489 := by
  unfold tailWord_1743023
  simp only [CollatzResearch.WordTrace]
  refine ⟨63573271564332830473625723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42382181042888553649083815 63573271564332830473625723)
  ·
    refine ⟨95359907346499245710438585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63573271564332830473625723 95359907346499245710438585)
    ·
      refine ⟨71519930509874434282828939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95359907346499245710438585 71519930509874434282828939)
      ·
        refine ⟨107279895764811651424243409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71519930509874434282828939 107279895764811651424243409)
        ·
          refine ⟨80459921823608738568182557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107279895764811651424243409 80459921823608738568182557)
          ·
            refine ⟨30172470683853276963068459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80459921823608738568182557 30172470683853276963068459)
            ·
              refine ⟨45258706025779915444602689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30172470683853276963068459 45258706025779915444602689)
              ·
                refine ⟨33944029519334936583452017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45258706025779915444602689 33944029519334936583452017)
                ·
                  refine ⟨25458022139501202437589013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33944029519334936583452017 25458022139501202437589013)
                  ·
                    refine ⟨1193344787789118864261985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25458022139501202437589013 1193344787789118864261985)
                    ·
                      refine ⟨895008590841839148196489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193344787789118864261985 895008590841839148196489)
                      ·
                        rfl

theorem cell23_1743023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 6, 2].length) (baseStart_1743023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743023 prefixEnd_1743023 := by exact prefixLift 1743023
  have htrace : WordTrace (prefixWord ++ tailWord_1743023) baseStart_1743023 baseEnd_1743023 := by
    simpa [prefixWord, tailWord_1743023, baseEnd_1743023] using wordTrace_append hprefix tailTrace_1743023
  have hstable : (prefixWord ++ tailWord_1743023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743023).length < 2 ^ (prefixWord ++ tailWord_1743023).sum := by decide
  have hdescent : baseEnd_1743023 < baseStart_1743023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743033 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 1, 6]
def baseStart_1743033 : Nat := 118140960795 + 1743033 * 2 ^ 59
def prefixEnd_1743033 : Nat := 4983230072969 + 3 ^ 40 * 1743033 * 2
def baseEnd_1743033 : Nat := 298337908549461369690481

theorem tailTrace_1743033 : CollatzResearch.WordTrace tailWord_1743033 prefixEnd_1743033 298337908549461369690481 := by
  unfold tailWord_1743033
  simp only [CollatzResearch.WordTrace]
  refine ⟨63573636294296602181489753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42382424196197734787659835 63573636294296602181489753)
  ·
    refine ⟨47680227220722451636117315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63573636294296602181489753 47680227220722451636117315)
    ·
      refine ⟨71520340831083677454175973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47680227220722451636117315 71520340831083677454175973)
      ·
        refine ⟨13410063905828189522657995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71520340831083677454175973 13410063905828189522657995)
        ·
          refine ⟨20115095858742284283986993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13410063905828189522657995 20115095858742284283986993)
          ·
            refine ⟨15086321894056713212990245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20115095858742284283986993 15086321894056713212990245)
            ·
              refine ⟨2828685355135633727435671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15086321894056713212990245 2828685355135633727435671)
              ·
                refine ⟨4243028032703450591153507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828685355135633727435671 4243028032703450591153507)
                ·
                  refine ⟨6364542049055175886730261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243028032703450591153507 6364542049055175886730261)
                  ·
                    refine ⟨298337908549461369690481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6364542049055175886730261 298337908549461369690481)
                    ·
                      rfl

theorem cell23_1743033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 6].length) (baseStart_1743033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743033 prefixEnd_1743033 := by exact prefixLift 1743033
  have htrace : WordTrace (prefixWord ++ tailWord_1743033) baseStart_1743033 baseEnd_1743033 := by
    simpa [prefixWord, tailWord_1743033, baseEnd_1743033] using wordTrace_append hprefix tailTrace_1743033
  have hstable : (prefixWord ++ tailWord_1743033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743033).length < 2 ^ (prefixWord ++ tailWord_1743033).sum := by decide
  have hdescent : baseEnd_1743033 < baseStart_1743033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743044 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_1743044 : Nat := 118140960795 + 1743044 * 2 ^ 59
def prefixEnd_1743044 : Nat := 4983230072969 + 3 ^ 40 * 1743044 * 2
def baseEnd_1743044 : Nat := 895019373935583566033893

theorem tailTrace_1743044 : CollatzResearch.WordTrace tailWord_1743044 prefixEnd_1743044 895019373935583566033893 := by
  unfold tailWord_1743044
  simp only [CollatzResearch.WordTrace]
  refine ⟨31787018748628375530070093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42382691664837834040093457 31787018748628375530070093)
  ·
    refine ⟨11920132030735640823776285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31787018748628375530070093 11920132030735640823776285)
    ·
      refine ⟨4470049511525865308916107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11920132030735640823776285 4470049511525865308916107)
      ·
        refine ⟨6705074267288797963374161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4470049511525865308916107 6705074267288797963374161)
        ·
          refine ⟨5028805700466598472530621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6705074267288797963374161 5028805700466598472530621)
          ·
            refine ⟨1885802137674974427198983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5028805700466598472530621 1885802137674974427198983)
            ·
              refine ⟨2828703206512461640798475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885802137674974427198983 2828703206512461640798475)
              ·
                refine ⟨4243054809768692461197713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828703206512461640798475 4243054809768692461197713)
                ·
                  refine ⟨3182291107326519345898285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4243054809768692461197713 3182291107326519345898285)
                  ·
                    refine ⟨1193359165247444754711857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3182291107326519345898285 1193359165247444754711857)
                    ·
                      refine ⟨895019373935583566033893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193359165247444754711857 895019373935583566033893)
                      ·
                        rfl

theorem cell23_1743044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_1743044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743044 prefixEnd_1743044 := by exact prefixLift 1743044
  have htrace : WordTrace (prefixWord ++ tailWord_1743044) baseStart_1743044 baseEnd_1743044 := by
    simpa [prefixWord, tailWord_1743044, baseEnd_1743044] using wordTrace_append hprefix tailTrace_1743044
  have hstable : (prefixWord ++ tailWord_1743044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743044).length < 2 ^ (prefixWord ++ tailWord_1743044).sum := by decide
  have hdescent : baseEnd_1743044 < baseStart_1743044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743108 : List Nat := [2, 3, 2, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_1743108 : Nat := 118140960795 + 1743108 * 2 ^ 59
def prefixEnd_1743108 : Nat := 4983230072969 + 3 ^ 40 * 1743108 * 2
def baseEnd_1743108 : Nat := 895052236697471315633599

theorem tailTrace_1743108 : CollatzResearch.WordTrace tailWord_1743108 prefixEnd_1743108 895052236697471315633599 := by
  unfold tailWord_1743108
  simp only [CollatzResearch.WordTrace]
  refine ⟨31788185884512444995234989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42384247846016593326979985 31788185884512444995234989)
  ·
    refine ⟨11920569706692166873213121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31788185884512444995234989 11920569706692166873213121)
    ·
      refine ⟨8940427280019125154909841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11920569706692166873213121 8940427280019125154909841)
      ·
        refine ⟨6705320460014343866182381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8940427280019125154909841 6705320460014343866182381)
        ·
          refine ⟨2514495172505378949818393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6705320460014343866182381 2514495172505378949818393)
          ·
            refine ⟨1885871379379034212363795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2514495172505378949818393 1885871379379034212363795)
            ·
              refine ⟨2828807069068551318545693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885871379379034212363795 2828807069068551318545693)
              ·
                refine ⟨1060802650900706744454635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2828807069068551318545693 1060802650900706744454635)
                ·
                  refine ⟨1591203976351060116681953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060802650900706744454635 1591203976351060116681953)
                  ·
                    refine ⟨1193402982263295087511465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1591203976351060116681953 1193402982263295087511465)
                    ·
                      refine ⟨895052236697471315633599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193402982263295087511465 895052236697471315633599)
                      ·
                        rfl

theorem cell23_1743108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_1743108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743108 prefixEnd_1743108 := by exact prefixLift 1743108
  have htrace : WordTrace (prefixWord ++ tailWord_1743108) baseStart_1743108 baseEnd_1743108 := by
    simpa [prefixWord, tailWord_1743108, baseEnd_1743108] using wordTrace_append hprefix tailTrace_1743108
  have hstable : (prefixWord ++ tailWord_1743108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743108).length < 2 ^ (prefixWord ++ tailWord_1743108).sum := by decide
  have hdescent : baseEnd_1743108 < baseStart_1743108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743141 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 2, 1, 3]
def baseStart_1743141 : Nat := 118140960795 + 1743141 * 2 ^ 59
def prefixEnd_1743141 : Nat := 4983230072969 + 3 ^ 40 * 1743141 * 2
def baseEnd_1743141 : Nat := 895069181559069686520947

theorem tailTrace_1743141 : CollatzResearch.WordTrace tailWord_1743141 prefixEnd_1743141 895069181559069686520947 := by
  unfold tailWord_1743141
  simp only [CollatzResearch.WordTrace]
  refine ⟨63577575377905336626421277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42385050251936891084280851 63577575377905336626421277)
  ·
    refine ⟨23841590766714501234907979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63577575377905336626421277 23841590766714501234907979)
    ·
      refine ⟨35762386150071751852361969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23841590766714501234907979 35762386150071751852361969)
      ·
        refine ⟨26821789612553813889271477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35762386150071751852361969 26821789612553813889271477)
        ·
          refine ⟨2514542776176920052119201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26821789612553813889271477 2514542776176920052119201)
          ·
            refine ⟨1885907082132690039089401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2514542776176920052119201 1885907082132690039089401)
            ·
              refine ⟨1414430311599517529317051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885907082132690039089401 1414430311599517529317051)
              ·
                refine ⟨2121645467399276293975577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414430311599517529317051 2121645467399276293975577)
                ·
                  refine ⟨1591234100549457220481683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2121645467399276293975577 1591234100549457220481683)
                  ·
                    refine ⟨2386851150824185830722525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1591234100549457220481683 2386851150824185830722525)
                    ·
                      refine ⟨895069181559069686520947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2386851150824185830722525 895069181559069686520947)
                      ·
                        rfl

theorem cell23_1743141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_1743141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743141 prefixEnd_1743141 := by exact prefixLift 1743141
  have htrace : WordTrace (prefixWord ++ tailWord_1743141) baseStart_1743141 baseEnd_1743141 := by
    simpa [prefixWord, tailWord_1743141, baseEnd_1743141] using wordTrace_append hprefix tailTrace_1743141
  have hstable : (prefixWord ++ tailWord_1743141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743141).length < 2 ^ (prefixWord ++ tailWord_1743141).sum := by decide
  have hdescent : baseEnd_1743141 < baseStart_1743141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743180 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1743180 : Nat := 118140960795 + 1743180 * 2 ^ 59
def prefixEnd_1743180 : Nat := 4983230072969 + 3 ^ 40 * 1743180 * 2
def baseEnd_1743180 : Nat := 895089207304595033933267

theorem tailTrace_1743180 : CollatzResearch.WordTrace tailWord_1743180 prefixEnd_1743180 895089207304595033933267 := by
  unfold tailWord_1743180
  simp only [CollatzResearch.WordTrace]
  refine ⟨31789498912382023143545497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42385998549842697524727329 31789498912382023143545497)
  ·
    refine ⟨23842124184286517357659123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31789498912382023143545497 23842124184286517357659123)
    ·
      refine ⟨35763186276429776036488685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23842124184286517357659123 35763186276429776036488685)
      ·
        refine ⟨13411194853661166013683257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35763186276429776036488685 13411194853661166013683257)
        ·
          refine ⟨10058396140245874510262443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13411194853661166013683257 10058396140245874510262443)
          ·
            refine ⟨15087594210368811765393665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10058396140245874510262443 15087594210368811765393665)
            ·
              refine ⟨11315695657776608824045249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15087594210368811765393665 11315695657776608824045249)
              ·
                refine ⟨8486771743332456618033937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11315695657776608824045249 8486771743332456618033937)
                ·
                  refine ⟨6365078807499342463525453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8486771743332456618033937 6365078807499342463525453)
                  ·
                    refine ⟨2386904552812253423822045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6365078807499342463525453 2386904552812253423822045)
                    ·
                      refine ⟨895089207304595033933267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2386904552812253423822045 895089207304595033933267)
                      ·
                        rfl

theorem cell23_1743180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1743180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743180 prefixEnd_1743180 := by exact prefixLift 1743180
  have htrace : WordTrace (prefixWord ++ tailWord_1743180) baseStart_1743180 baseEnd_1743180 := by
    simpa [prefixWord, tailWord_1743180, baseEnd_1743180] using wordTrace_append hprefix tailTrace_1743180
  have hstable : (prefixWord ++ tailWord_1743180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743180).length < 2 ^ (prefixWord ++ tailWord_1743180).sum := by decide
  have hdescent : baseEnd_1743180 < baseStart_1743180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743183 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 4, 5]
def baseStart_1743183 : Nat := 118140960795 + 1743183 * 2 ^ 59
def prefixEnd_1743183 : Nat := 4983230072969 + 3 ^ 40 * 1743183 * 2
def baseEnd_1743183 : Nat := 298363582582186174065251

theorem tailTrace_1743183 : CollatzResearch.WordTrace tailWord_1743183 prefixEnd_1743183 298363582582186174065251 := by
  unfold tailWord_1743183
  simp only [CollatzResearch.WordTrace]
  refine ⟨63579107243753177799450203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42386071495835451866300135 63579107243753177799450203)
  ·
    refine ⟨95368660865629766699175305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63579107243753177799450203 95368660865629766699175305)
    ·
      refine ⟨71526495649222325024381479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95368660865629766699175305 71526495649222325024381479)
      ·
        refine ⟨107289743473833487536572219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71526495649222325024381479 107289743473833487536572219)
        ·
          refine ⟨160934615210750231304858329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107289743473833487536572219 160934615210750231304858329)
          ·
            refine ⟨120700961408062673478643747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160934615210750231304858329 120700961408062673478643747)
            ·
              refine ⟨181051442112094010217965621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120700961408062673478643747 181051442112094010217965621)
              ·
                refine ⟨16973572698008813457934277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181051442112094010217965621 16973572698008813457934277)
                ·
                  refine ⟨3182544880876652523362677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16973572698008813457934277 3182544880876652523362677)
                  ·
                    refine ⟨298363582582186174065251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3182544880876652523362677 298363582582186174065251)
                    ·
                      rfl

theorem cell23_1743183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_1743183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743183 prefixEnd_1743183 := by exact prefixLift 1743183
  have htrace : WordTrace (prefixWord ++ tailWord_1743183) baseStart_1743183 baseEnd_1743183 := by
    simpa [prefixWord, tailWord_1743183, baseEnd_1743183] using wordTrace_append hprefix tailTrace_1743183
  have hstable : (prefixWord ++ tailWord_1743183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743183).length < 2 ^ (prefixWord ++ tailWord_1743183).sum := by decide
  have hdescent : baseEnd_1743183 < baseStart_1743183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743223 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_1743223 : Nat := 118140960795 + 1743223 * 2 ^ 59
def prefixEnd_1743223 : Nat := 4983230072969 + 3 ^ 40 * 1743223 * 2
def baseEnd_1743223 : Nat := 895111286972738365695569

theorem tailTrace_1743223 : CollatzResearch.WordTrace tailWord_1743223 prefixEnd_1743223 895111286972738365695569 := by
  unfold tailWord_1743223
  simp only [CollatzResearch.WordTrace]
  refine ⟨63580566163608264630906323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42387044109072176420604215 63580566163608264630906323)
  ·
    refine ⟨95370849245412396946359485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63580566163608264630906323 95370849245412396946359485)
    ·
      refine ⟨35764068467029648854884807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95370849245412396946359485 35764068467029648854884807)
      ·
        refine ⟨53646102700544473282327211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35764068467029648854884807 53646102700544473282327211)
        ·
          refine ⟨80469154050816709923490817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53646102700544473282327211 80469154050816709923490817)
          ·
            refine ⟨60351865538112532442618113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80469154050816709923490817 60351865538112532442618113)
            ·
              refine ⟨45263899153584399331963585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60351865538112532442618113 45263899153584399331963585)
              ·
                refine ⟨33947924365188299498972689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45263899153584399331963585 33947924365188299498972689)
                ·
                  refine ⟨25460943273891224624229517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33947924365188299498972689 25460943273891224624229517)
                  ·
                    refine ⟨9547853727709209234086069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25460943273891224624229517 9547853727709209234086069)
                    ·
                      refine ⟨895111286972738365695569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9547853727709209234086069 895111286972738365695569)
                      ·
                        rfl

theorem cell23_1743223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_1743223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743223 prefixEnd_1743223 := by exact prefixLift 1743223
  have htrace : WordTrace (prefixWord ++ tailWord_1743223) baseStart_1743223 baseEnd_1743223 := by
    simpa [prefixWord, tailWord_1743223, baseEnd_1743223] using wordTrace_append hprefix tailTrace_1743223
  have hstable : (prefixWord ++ tailWord_1743223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743223).length < 2 ^ (prefixWord ++ tailWord_1743223).sum := by decide
  have hdescent : baseEnd_1743223 < baseStart_1743223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743273 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 2, 9]
def baseStart_1743273 : Nat := 118140960795 + 1743273 * 2 ^ 59
def prefixEnd_1743273 : Nat := 4983230072969 + 3 ^ 40 * 1743273 * 2
def baseEnd_1743273 : Nat := 298378987001821056690113

theorem tailTrace_1743273 : CollatzResearch.WordTrace tailWord_1743273 prefixEnd_1743273 298378987001821056690113 := by
  unfold tailWord_1743273
  simp only [CollatzResearch.WordTrace]
  refine ⟨63582389813427123170226473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42388259875618082113484315 63582389813427123170226473)
  ·
    refine ⟨47686792360070342377669855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63582389813427123170226473 47686792360070342377669855)
    ·
      refine ⟨71530188540105513566504783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47686792360070342377669855 71530188540105513566504783)
      ·
        refine ⟨107295282810158270349757175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71530188540105513566504783 107295282810158270349757175)
        ·
          refine ⟨160942924215237405524635763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107295282810158270349757175 160942924215237405524635763)
          ·
            refine ⟨241414386322856108286953645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160942924215237405524635763 241414386322856108286953645)
            ·
              refine ⟨90530394871071040607607617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241414386322856108286953645 90530394871071040607607617)
              ·
                refine ⟨67897796153303280455705713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90530394871071040607607617 67897796153303280455705713)
                ·
                  refine ⟨50923347114977460341779285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67897796153303280455705713 50923347114977460341779285)
                  ·
                    refine ⟨298378987001821056690113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 50923347114977460341779285 298378987001821056690113)
                    ·
                      rfl

theorem cell23_1743273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_1743273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743273 prefixEnd_1743273 := by exact prefixLift 1743273
  have htrace : WordTrace (prefixWord ++ tailWord_1743273) baseStart_1743273 baseEnd_1743273 := by
    simpa [prefixWord, tailWord_1743273, baseEnd_1743273] using wordTrace_append hprefix tailTrace_1743273
  have hstable : (prefixWord ++ tailWord_1743273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743273).length < 2 ^ (prefixWord ++ tailWord_1743273).sum := by decide
  have hdescent : baseEnd_1743273 < baseStart_1743273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743281 : List Nat := [1, 2, 2, 4, 1, 4, 1, 3, 1, 4]
def baseStart_1743281 : Nat := 118140960795 + 1743281 * 2 ^ 59
def prefixEnd_1743281 : Nat := 4983230072969 + 3 ^ 40 * 1743281 * 2
def baseEnd_1743281 : Nat := 298380356283566379590101

theorem tailTrace_1743281 : CollatzResearch.WordTrace tailWord_1743281 prefixEnd_1743281 298380356283566379590101 := by
  unfold tailWord_1743281
  simp only [CollatzResearch.WordTrace]
  refine ⟨63582681597398140536517697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42388454398265427024345131 63582681597398140536517697)
  ·
    refine ⟨47687011198048605402388273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63582681597398140536517697 47687011198048605402388273)
    ·
      refine ⟨35765258398536454051791205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47687011198048605402388273 35765258398536454051791205)
      ·
        refine ⟨6705985949725585134710851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35765258398536454051791205 6705985949725585134710851)
        ·
          refine ⟨10058978924588377702066277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6705985949725585134710851 10058978924588377702066277)
          ·
            refine ⟨1886058548360320819137427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10058978924588377702066277 1886058548360320819137427)
            ·
              refine ⟨2829087822540481228706141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886058548360320819137427 2829087822540481228706141)
              ·
                refine ⟨1060907933452680460764803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2829087822540481228706141 1060907933452680460764803)
                ·
                  refine ⟨1591361900179020691147205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060907933452680460764803 1591361900179020691147205)
                  ·
                    refine ⟨298380356283566379590101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1591361900179020691147205 298380356283566379590101)
                    ·
                      rfl

theorem cell23_1743281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_1743281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743281 prefixEnd_1743281 := by exact prefixLift 1743281
  have htrace : WordTrace (prefixWord ++ tailWord_1743281) baseStart_1743281 baseEnd_1743281 := by
    simpa [prefixWord, tailWord_1743281, baseEnd_1743281] using wordTrace_append hprefix tailTrace_1743281
  have hstable : (prefixWord ++ tailWord_1743281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743281).length < 2 ^ (prefixWord ++ tailWord_1743281).sum := by decide
  have hdescent : baseEnd_1743281 < baseStart_1743281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743304 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_1743304 : Nat := 118140960795 + 1743304 * 2 ^ 59
def prefixEnd_1743304 : Nat := 4983230072969 + 3 ^ 40 * 1743304 * 2
def baseEnd_1743304 : Nat := 895152878905752548782697

theorem tailTrace_1743304 : CollatzResearch.WordTrace tailWord_1743304 prefixEnd_1743304 895152878905752548782697 := by
  unfold tailWord_1743304
  simp only [CollatzResearch.WordTrace]
  refine ⟨31791760238157407732302483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42389013650876543643069977 31791760238157407732302483)
  ·
    refine ⟨47687640357236111598453725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31791760238157407732302483 47687640357236111598453725)
    ·
      refine ⟨17882865133963541849420147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47687640357236111598453725 17882865133963541849420147)
      ·
        refine ⟨26824297700945312774130221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17882865133963541849420147 26824297700945312774130221)
        ·
          refine ⟨10059111637854492290298833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26824297700945312774130221 10059111637854492290298833)
          ·
            refine ⟨7544333728390869217724125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10059111637854492290298833 7544333728390869217724125)
            ·
              refine ⟨2829125148146575956646547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7544333728390869217724125 2829125148146575956646547)
              ·
                refine ⟨4243687722219863934969821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829125148146575956646547 4243687722219863934969821)
                ·
                  refine ⟨1591382895832448975613683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4243687722219863934969821 1591382895832448975613683)
                  ·
                    refine ⟨2387074343748673463420525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1591382895832448975613683 2387074343748673463420525)
                    ·
                      refine ⟨895152878905752548782697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2387074343748673463420525 895152878905752548782697)
                      ·
                        rfl

theorem cell23_1743304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_1743304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743304 prefixEnd_1743304 := by exact prefixLift 1743304
  have htrace : WordTrace (prefixWord ++ tailWord_1743304) baseStart_1743304 baseEnd_1743304 := by
    simpa [prefixWord, tailWord_1743304, baseEnd_1743304] using wordTrace_append hprefix tailTrace_1743304
  have hstable : (prefixWord ++ tailWord_1743304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743304).length < 2 ^ (prefixWord ++ tailWord_1743304).sum := by decide
  have hdescent : baseEnd_1743304 < baseStart_1743304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743310 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_1743310 : Nat := 118140960795 + 1743310 * 2 ^ 59
def prefixEnd_1743310 : Nat := 4983230072969 + 3 ^ 40 * 1743310 * 2
def baseEnd_1743310 : Nat := 895155959789679525307669

theorem tailTrace_1743310 : CollatzResearch.WordTrace tailWord_1743310 prefixEnd_1743310 895155959789679525307669 := by
  unfold tailWord_1743310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7947967414286634811165423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42389159542862052326215589 7947967414286634811165423)
  ·
    refine ⟨11921951121429952216748135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7947967414286634811165423 11921951121429952216748135)
    ·
      refine ⟨17882926682144928325122203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11921951121429952216748135 17882926682144928325122203)
      ·
        refine ⟨26824390023217392487683305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17882926682144928325122203 26824390023217392487683305)
        ·
          refine ⟨20118292517413044365762479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26824390023217392487683305 20118292517413044365762479)
          ·
            refine ⟨30177438776119566548643719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20118292517413044365762479 30177438776119566548643719)
            ·
              refine ⟨45266158164179349822965579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30177438776119566548643719 45266158164179349822965579)
              ·
                refine ⟨67899237246269024734448369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45266158164179349822965579 67899237246269024734448369)
                ·
                  refine ⟨50924427934701768550836277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67899237246269024734448369 50924427934701768550836277)
                  ·
                    refine ⟨4774165118878290801640901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50924427934701768550836277 4774165118878290801640901)
                    ·
                      refine ⟨895155959789679525307669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4774165118878290801640901 895155959789679525307669)
                      ·
                        rfl

theorem cell23_1743310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_1743310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743310 prefixEnd_1743310 := by exact prefixLift 1743310
  have htrace : WordTrace (prefixWord ++ tailWord_1743310) baseStart_1743310 baseEnd_1743310 := by
    simpa [prefixWord, tailWord_1743310, baseEnd_1743310] using wordTrace_append hprefix tailTrace_1743310
  have hstable : (prefixWord ++ tailWord_1743310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743310).length < 2 ^ (prefixWord ++ tailWord_1743310).sum := by decide
  have hdescent : baseEnd_1743310 < baseStart_1743310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743320 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 1, 6]
def baseStart_1743320 : Nat := 118140960795 + 1743320 * 2 ^ 59
def prefixEnd_1743320 : Nat := 4983230072969 + 3 ^ 40 * 1743320 * 2
def baseEnd_1743320 : Nat := 298387031532074828727541

theorem tailTrace_1743320 : CollatzResearch.WordTrace tailWord_1743320 prefixEnd_1743320 298387031532074828727541 := by
  unfold tailWord_1743320
  simp only [CollatzResearch.WordTrace]
  refine ⟨31792052022128425098593707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42389402696171233464791609 31792052022128425098593707)
  ·
    refine ⟨47688078033192637647890561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31792052022128425098593707 47688078033192637647890561)
    ·
      refine ⟨35766058524894478235917921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47688078033192637647890561 35766058524894478235917921)
      ·
        refine ⟨26824543893670858676938441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35766058524894478235917921 26824543893670858676938441)
        ·
          refine ⟨20118407920253144007703831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26824543893670858676938441 20118407920253144007703831)
          ·
            refine ⟨30177611880379716011555747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20118407920253144007703831 30177611880379716011555747)
            ·
              refine ⟨45266417820569574017333621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30177611880379716011555747 45266417820569574017333621)
              ·
                refine ⟨4243726670678397564125027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45266417820569574017333621 4243726670678397564125027)
                ·
                  refine ⟨6365590006017596346187541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243726670678397564125027 6365590006017596346187541)
                  ·
                    refine ⟨298387031532074828727541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6365590006017596346187541 298387031532074828727541)
                    ·
                      rfl

theorem cell23_1743320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_1743320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743320 prefixEnd_1743320 := by exact prefixLift 1743320
  have htrace : WordTrace (prefixWord ++ tailWord_1743320) baseStart_1743320 baseEnd_1743320 := by
    simpa [prefixWord, tailWord_1743320, baseEnd_1743320] using wordTrace_append hprefix tailTrace_1743320
  have hstable : (prefixWord ++ tailWord_1743320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743320).length < 2 ^ (prefixWord ++ tailWord_1743320).sum := by decide
  have hdescent : baseEnd_1743320 < baseStart_1743320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743327 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 4]
def baseStart_1743327 : Nat := 118140960795 + 1743327 * 2 ^ 59
def prefixEnd_1743327 : Nat := 4983230072969 + 3 ^ 40 * 1743327 * 2
def baseEnd_1743327 : Nat := 895164688960805958795091

theorem tailTrace_1743327 : CollatzResearch.WordTrace tailWord_1743327 prefixEnd_1743327 895164688960805958795091 := by
  unfold tailWord_1743327
  simp only [CollatzResearch.WordTrace]
  refine ⟨63584359355231490392692235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42389572903487660261794823 63584359355231490392692235)
  ·
    refine ⟨95376539032847235589038353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63584359355231490392692235 95376539032847235589038353)
    ·
      refine ⟨71532404274635426691778765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95376539032847235589038353 71532404274635426691778765)
      ·
        refine ⟨26824651602988285009417037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71532404274635426691778765 26824651602988285009417037)
        ·
          refine ⟨10059244351120606878531389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26824651602988285009417037 10059244351120606878531389)
          ·
            refine ⟨3772216631670227579449271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10059244351120606878531389 3772216631670227579449271)
            ·
              refine ⟨5658324947505341369173907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772216631670227579449271 5658324947505341369173907)
              ·
                refine ⟨8487487421258012053760861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658324947505341369173907 8487487421258012053760861)
                ·
                  refine ⟨3182807782971754520160323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8487487421258012053760861 3182807782971754520160323)
                  ·
                    refine ⟨4774211674457631780240485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3182807782971754520160323 4774211674457631780240485)
                    ·
                      refine ⟨895164688960805958795091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4774211674457631780240485 895164688960805958795091)
                      ·
                        rfl

theorem cell23_1743327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_1743327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743327 prefixEnd_1743327 := by exact prefixLift 1743327
  have htrace : WordTrace (prefixWord ++ tailWord_1743327) baseStart_1743327 baseEnd_1743327 := by
    simpa [prefixWord, tailWord_1743327, baseEnd_1743327] using wordTrace_append hprefix tailTrace_1743327
  have hstable : (prefixWord ++ tailWord_1743327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743327).length < 2 ^ (prefixWord ++ tailWord_1743327).sum := by decide
  have hdescent : baseEnd_1743327 < baseStart_1743327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743331 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 2, 3, 2]
def baseStart_1743331 : Nat := 118140960795 + 1743331 * 2 ^ 59
def prefixEnd_1743331 : Nat := 4983230072969 + 3 ^ 40 * 1743331 * 2
def baseEnd_1743331 : Nat := 895166742883423943145073

theorem tailTrace_1743331 : CollatzResearch.WordTrace tailWord_1743331 prefixEnd_1743331 895166742883423943145073 := by
  unfold tailWord_1743331
  simp only [CollatzResearch.WordTrace]
  refine ⟨63584505247216999075837847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42389670164811332717225231 63584505247216999075837847)
  ·
    refine ⟨95376757870825498613756771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63584505247216999075837847 95376757870825498613756771)
    ·
      refine ⟨143065136806238247920635157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95376757870825498613756771 143065136806238247920635157)
      ·
        refine ⟨6706178287792417871279773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143065136806238247920635157 6706178287792417871279773)
        ·
          refine ⟨2514816857922156701729915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6706178287792417871279773 2514816857922156701729915)
          ·
            refine ⟨3772225286883235052594873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514816857922156701729915 3772225286883235052594873)
            ·
              refine ⟨2829168965162426289446155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3772225286883235052594873 2829168965162426289446155)
              ·
                refine ⟨4243753447743639434169233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829168965162426289446155 4243753447743639434169233)
                ·
                  refine ⟨3182815085807729575626925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4243753447743639434169233 3182815085807729575626925)
                  ·
                    refine ⟨1193555657177898590860097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3182815085807729575626925 1193555657177898590860097)
                    ·
                      refine ⟨895166742883423943145073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193555657177898590860097 895166742883423943145073)
                      ·
                        rfl

theorem cell23_1743331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_1743331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743331 prefixEnd_1743331 := by exact prefixLift 1743331
  have htrace : WordTrace (prefixWord ++ tailWord_1743331) baseStart_1743331 baseEnd_1743331 := by
    simpa [prefixWord, tailWord_1743331, baseEnd_1743331] using wordTrace_append hprefix tailTrace_1743331
  have hstable : (prefixWord ++ tailWord_1743331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743331).length < 2 ^ (prefixWord ++ tailWord_1743331).sum := by decide
  have hdescent : baseEnd_1743331 < baseStart_1743331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743341 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_1743341 : Nat := 118140960795 + 1743341 * 2 ^ 59
def prefixEnd_1743341 : Nat := 4983230072969 + 3 ^ 40 * 1743341 * 2
def baseEnd_1743341 : Nat := 298390625896656301340009

theorem tailTrace_1743341 : CollatzResearch.WordTrace tailWord_1743341 prefixEnd_1743341 298390625896656301340009 := by
  unfold tailWord_1743341
  simp only [CollatzResearch.WordTrace]
  refine ⟨63584869977180770783701877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42389913318120513855801251 63584869977180770783701877)
  ·
    refine ⟨5961081560360697260972051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63584869977180770783701877 5961081560360697260972051)
    ·
      refine ⟨8941622340541045891458077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5961081560360697260972051 8941622340541045891458077)
      ·
        refine ⟨3353108377702892209296779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8941622340541045891458077 3353108377702892209296779)
        ·
          refine ⟨5029662566554338313945169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353108377702892209296779 5029662566554338313945169)
          ·
            refine ⟨3772246924915753735458877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5029662566554338313945169 3772246924915753735458877)
            ·
              refine ⟨1414592596843407650797079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3772246924915753735458877 1414592596843407650797079)
              ·
                refine ⟨2121888895265111476195619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414592596843407650797079 2121888895265111476195619)
                ·
                  refine ⟨3182833342897667214293429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121888895265111476195619 3182833342897667214293429)
                  ·
                    refine ⟨298390625896656301340009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3182833342897667214293429 298390625896656301340009)
                    ·
                      rfl

theorem cell23_1743341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_1743341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743341 prefixEnd_1743341 := by exact prefixLift 1743341
  have htrace : WordTrace (prefixWord ++ tailWord_1743341) baseStart_1743341 baseEnd_1743341 := by
    simpa [prefixWord, tailWord_1743341, baseEnd_1743341] using wordTrace_append hprefix tailTrace_1743341
  have hstable : (prefixWord ++ tailWord_1743341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743341).length < 2 ^ (prefixWord ++ tailWord_1743341).sum := by decide
  have hdescent : baseEnd_1743341 < baseStart_1743341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743344 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 1, 1, 4]
def baseStart_1743344 : Nat := 118140960795 + 1743344 * 2 ^ 59
def prefixEnd_1743344 : Nat := 4983230072969 + 3 ^ 40 * 1743344 * 2
def baseEnd_1743344 : Nat := 895173418131932392282513

theorem tailTrace_1743344 : CollatzResearch.WordTrace tailWord_1743344 prefixEnd_1743344 895173418131932392282513 := by
  unfold tailWord_1743344
  simp only [CollatzResearch.WordTrace]
  refine ⟨31792489698084951148030543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42389986264113268197374057 31792489698084951148030543)
  ·
    refine ⟨47688734547127426722045815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31792489698084951148030543 47688734547127426722045815)
    ·
      refine ⟨71533101820691140083068723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47688734547127426722045815 71533101820691140083068723)
      ·
        refine ⟨107299652731036710124603085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71533101820691140083068723 107299652731036710124603085)
        ·
          refine ⟨40237369774138766296726157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107299652731036710124603085 40237369774138766296726157)
          ·
            refine ⟨15089013665302037361272309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40237369774138766296726157 15089013665302037361272309)
            ·
              refine ⟨1414595031122066002619279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15089013665302037361272309 1414595031122066002619279)
              ·
                refine ⟨2121892546683099003928919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414595031122066002619279 2121892546683099003928919)
                ·
                  refine ⟨3182838820024648505893379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121892546683099003928919 3182838820024648505893379)
                  ·
                    refine ⟨4774258230036972758840069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3182838820024648505893379 4774258230036972758840069)
                    ·
                      refine ⟨895173418131932392282513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4774258230036972758840069 895173418131932392282513)
                      ·
                        rfl

theorem cell23_1743344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 1, 1, 4].length) (baseStart_1743344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743344 prefixEnd_1743344 := by exact prefixLift 1743344
  have htrace : WordTrace (prefixWord ++ tailWord_1743344) baseStart_1743344 baseEnd_1743344 := by
    simpa [prefixWord, tailWord_1743344, baseEnd_1743344] using wordTrace_append hprefix tailTrace_1743344
  have hstable : (prefixWord ++ tailWord_1743344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743344).length < 2 ^ (prefixWord ++ tailWord_1743344).sum := by decide
  have hdescent : baseEnd_1743344 < baseStart_1743344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743364 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1743364 : Nat := 118140960795 + 1743364 * 2 ^ 59
def prefixEnd_1743364 : Nat := 4983230072969 + 3 ^ 40 * 1743364 * 2
def baseEnd_1743364 : Nat := 895183687745022314032421

theorem tailTrace_1743364 : CollatzResearch.WordTrace tailWord_1743364 prefixEnd_1743364 895183687745022314032421 := by
  unfold tailWord_1743364
  simp only [CollatzResearch.WordTrace]
  refine ⟨31792854428048722855894573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42390472570731630474526097 31792854428048722855894573)
  ·
    refine ⟨11922320410518271070960465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31792854428048722855894573 11922320410518271070960465)
    ·
      refine ⟨8941740307888703303220349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11922320410518271070960465 8941740307888703303220349)
      ·
        refine ⟨3353152615458263738707631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8941740307888703303220349 3353152615458263738707631)
        ·
          refine ⟨5029728923187395608061447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353152615458263738707631 5029728923187395608061447)
          ·
            refine ⟨7544593384781093412092171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5029728923187395608061447 7544593384781093412092171)
            ·
              refine ⟨11316890077171640118138257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544593384781093412092171 11316890077171640118138257)
              ·
                refine ⟨8487667557878730088603693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11316890077171640118138257 8487667557878730088603693)
                ·
                  refine ⟨3182875334204523783226385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8487667557878730088603693 3182875334204523783226385)
                  ·
                    refine ⟨2387156500653392837419789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3182875334204523783226385 2387156500653392837419789)
                    ·
                      refine ⟨895183687745022314032421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2387156500653392837419789 895183687745022314032421)
                      ·
                        rfl

theorem cell23_1743364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1743364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743364 prefixEnd_1743364 := by exact prefixLift 1743364
  have htrace : WordTrace (prefixWord ++ tailWord_1743364) baseStart_1743364 baseEnd_1743364 := by
    simpa [prefixWord, tailWord_1743364, baseEnd_1743364] using wordTrace_append hprefix tailTrace_1743364
  have hstable : (prefixWord ++ tailWord_1743364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743364).length < 2 ^ (prefixWord ++ tailWord_1743364).sum := by decide
  have hdescent : baseEnd_1743364 < baseStart_1743364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743374 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1743374 : Nat := 118140960795 + 1743374 * 2 ^ 59
def prefixEnd_1743374 : Nat := 4983230072969 + 3 ^ 40 * 1743374 * 2
def baseEnd_1743374 : Nat := 895188822551567274907375

theorem tailTrace_1743374 : CollatzResearch.WordTrace tailWord_1743374 prefixEnd_1743374 895188822551567274907375 := by
  unfold tailWord_1743374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7948259198257652177456647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42390715724040811613102117 7948259198257652177456647)
  ·
    refine ⟨11922388797386478266184971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7948259198257652177456647 11922388797386478266184971)
    ·
      refine ⟨17883583196079717399277457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11922388797386478266184971 17883583196079717399277457)
      ·
        refine ⟨13412687397059788049458093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17883583196079717399277457 13412687397059788049458093)
        ·
          refine ⟨5029757773897420518546785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13412687397059788049458093 5029757773897420518546785)
          ·
            refine ⟨3772318330423065388910089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5029757773897420518546785 3772318330423065388910089)
            ·
              refine ⟨2829238747817299041682567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3772318330423065388910089 2829238747817299041682567)
              ·
                refine ⟨4243858121725948562523851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829238747817299041682567 4243858121725948562523851)
                ·
                  refine ⟨6365787182588922843785777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243858121725948562523851 6365787182588922843785777)
                  ·
                    refine ⟨4774340386941692132839333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6365787182588922843785777 4774340386941692132839333)
                    ·
                      refine ⟨895188822551567274907375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4774340386941692132839333 895188822551567274907375)
                      ·
                        rfl

theorem cell23_1743374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1743374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743374 prefixEnd_1743374 := by exact prefixLift 1743374
  have htrace : WordTrace (prefixWord ++ tailWord_1743374) baseStart_1743374 baseEnd_1743374 := by
    simpa [prefixWord, tailWord_1743374, baseEnd_1743374] using wordTrace_append hprefix tailTrace_1743374
  have hstable : (prefixWord ++ tailWord_1743374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743374).length < 2 ^ (prefixWord ++ tailWord_1743374).sum := by decide
  have hdescent : baseEnd_1743374 < baseStart_1743374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743394 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_1743394 : Nat := 118140960795 + 1743394 * 2 ^ 59
def prefixEnd_1743394 : Nat := 4983230072969 + 3 ^ 40 * 1743394 * 2
def baseEnd_1743394 : Nat := 895199092164657196657283

theorem tailTrace_1743394 : CollatzResearch.WordTrace tailWord_1743394 prefixEnd_1743394 895199092164657196657283 := by
  unfold tailWord_1743394
  simp only [CollatzResearch.WordTrace]
  refine ⟨15896700761497190208845309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42391202030659173890254157 15896700761497190208845309)
  ·
    refine ⟨5961262785561446328316991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15896700761497190208845309 5961262785561446328316991)
    ·
      refine ⟨8941894178342169492475487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5961262785561446328316991 8941894178342169492475487)
      ·
        refine ⟨13412841267513254238713231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8941894178342169492475487 13412841267513254238713231)
        ·
          refine ⟨20119261901269881358069847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13412841267513254238713231 20119261901269881358069847)
          ·
            refine ⟨30178892851904822037104771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20119261901269881358069847 30178892851904822037104771)
            ·
              refine ⟨45268339277857233055657157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30178892851904822037104771 45268339277857233055657157)
              ·
                refine ⟨8487813614598231197935717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45268339277857233055657157 8487813614598231197935717)
                ·
                  refine ⟨1591465052737168349612947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8487813614598231197935717 1591465052737168349612947)
                  ·
                    refine ⟨2387197579105752524419421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1591465052737168349612947 2387197579105752524419421)
                    ·
                      refine ⟨895199092164657196657283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2387197579105752524419421 895199092164657196657283)
                      ·
                        rfl

theorem cell23_1743394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_1743394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743394 prefixEnd_1743394 := by exact prefixLift 1743394
  have htrace : WordTrace (prefixWord ++ tailWord_1743394) baseStart_1743394 baseEnd_1743394 := by
    simpa [prefixWord, tailWord_1743394, baseEnd_1743394] using wordTrace_append hprefix tailTrace_1743394
  have hstable : (prefixWord ++ tailWord_1743394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743394).length < 2 ^ (prefixWord ++ tailWord_1743394).sum := by decide
  have hdescent : baseEnd_1743394 < baseStart_1743394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743440 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 9]
def baseStart_1743440 : Nat := 118140960795 + 1743440 * 2 ^ 59
def prefixEnd_1743440 : Nat := 4983230072969 + 3 ^ 40 * 1743440 * 2
def baseEnd_1743440 : Nat := 99469190252751557409119

theorem tailTrace_1743440 : CollatzResearch.WordTrace tailWord_1743440 prefixEnd_1743440 99469190252751557409119 := by
  unfold tailWord_1743440
  simp only [CollatzResearch.WordTrace]
  refine ⟨31794240401911055345777887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42392320535881407127703849 31794240401911055345777887)
  ·
    refine ⟨47691360602866583018666831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31794240401911055345777887 47691360602866583018666831)
    ·
      refine ⟨71537040904299874528000247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47691360602866583018666831 71537040904299874528000247)
      ·
        refine ⟨107305561356449811792000371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71537040904299874528000247 107305561356449811792000371)
        ·
          refine ⟨160958342034674717688000557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107305561356449811792000371 160958342034674717688000557)
          ·
            refine ⟨60359378263003019133000209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160958342034674717688000557 60359378263003019133000209)
            ·
              refine ⟨45269533697252264349750157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60359378263003019133000209 45269533697252264349750157)
              ·
                refine ⟨16976075136469599131156309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45269533697252264349750157 16976075136469599131156309)
                ·
                  refine ⟨99469190252751557409119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16976075136469599131156309 99469190252751557409119)
                  ·
                    rfl

theorem cell23_1743440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 9].length) (baseStart_1743440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743440 prefixEnd_1743440 := by exact prefixLift 1743440
  have htrace : WordTrace (prefixWord ++ tailWord_1743440) baseStart_1743440 baseEnd_1743440 := by
    simpa [prefixWord, tailWord_1743440, baseEnd_1743440] using wordTrace_append hprefix tailTrace_1743440
  have hstable : (prefixWord ++ tailWord_1743440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743440).length < 2 ^ (prefixWord ++ tailWord_1743440).sum := by decide
  have hdescent : baseEnd_1743440 < baseStart_1743440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743467 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 3]
def baseStart_1743467 : Nat := 118140960795 + 1743467 * 2 ^ 59
def prefixEnd_1743467 : Nat := 4983230072969 + 3 ^ 40 * 1743467 * 2
def baseEnd_1743467 : Nat := 895236576252435411044447

theorem tailTrace_1743467 : CollatzResearch.WordTrace tailWord_1743467 prefixEnd_1743467 895236576252435411044447 := by
  unfold tailWord_1743467
  simp only [CollatzResearch.WordTrace]
  refine ⟨63589465574724294302788655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42392977049816196201859103 63589465574724294302788655)
  ·
    refine ⟨95384198362086441454182983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63589465574724294302788655 95384198362086441454182983)
    ·
      refine ⟨143076297543129662181274475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95384198362086441454182983 143076297543129662181274475)
      ·
        refine ⟨214614446314694493271911713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143076297543129662181274475 214614446314694493271911713)
        ·
          refine ⟨160960834736020869953933785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214614446314694493271911713 160960834736020869953933785)
          ·
            refine ⟨120720626052015652465450339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160960834736020869953933785 120720626052015652465450339)
            ·
              refine ⟨181080939078023478698175509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120720626052015652465450339 181080939078023478698175509)
              ·
                refine ⟨8488169019282350563976977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181080939078023478698175509 8488169019282350563976977)
                ·
                  refine ⟨6366126764461762922982733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8488169019282350563976977 6366126764461762922982733)
                  ·
                    refine ⟨2387297536673161096118525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6366126764461762922982733 2387297536673161096118525)
                    ·
                      refine ⟨895236576252435411044447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2387297536673161096118525 895236576252435411044447)
                      ·
                        rfl

theorem cell23_1743467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 3].length) (baseStart_1743467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743467 prefixEnd_1743467 := by exact prefixLift 1743467
  have htrace : WordTrace (prefixWord ++ tailWord_1743467) baseStart_1743467 baseEnd_1743467 := by
    simpa [prefixWord, tailWord_1743467, baseEnd_1743467] using wordTrace_append hprefix tailTrace_1743467
  have hstable : (prefixWord ++ tailWord_1743467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743467).length < 2 ^ (prefixWord ++ tailWord_1743467).sum := by decide
  have hdescent : baseEnd_1743467 < baseStart_1743467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743507 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 4]
def baseStart_1743507 : Nat := 118140960795 + 1743507 * 2 ^ 59
def prefixEnd_1743507 : Nat := 4983230072969 + 3 ^ 40 * 1743507 * 2
def baseEnd_1743507 : Nat := 895257115478615254544263

theorem tailTrace_1743507 : CollatzResearch.WordTrace tailWord_1743507 prefixEnd_1743507 895257115478615254544263 := by
  unfold tailWord_1743507
  simp only [CollatzResearch.WordTrace]
  refine ⟨63590924494579381134244775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42393949663052920756163183 63590924494579381134244775)
  ·
    refine ⟨95386386741869071701367163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63590924494579381134244775 95386386741869071701367163)
    ·
      refine ⟨143079580112803607552050745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95386386741869071701367163 143079580112803607552050745)
      ·
        refine ⟨107309685084602705664038059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143079580112803607552050745 107309685084602705664038059)
        ·
          refine ⟨160964527626904058496057089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107309685084602705664038059 160964527626904058496057089)
          ·
            refine ⟨120723395720178043872042817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160964527626904058496057089 120723395720178043872042817)
            ·
              refine ⟨90542546790133532904032113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120723395720178043872042817 90542546790133532904032113)
              ·
                refine ⟨67906910092600149678024085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90542546790133532904032113 67906910092600149678024085)
                ·
                  refine ⟨3183136410590632016157379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67906910092600149678024085 3183136410590632016157379)
                  ·
                    refine ⟨4774704615885948024236069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183136410590632016157379 4774704615885948024236069)
                    ·
                      refine ⟨895257115478615254544263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4774704615885948024236069 895257115478615254544263)
                      ·
                        rfl

theorem cell23_1743507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_1743507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743507 prefixEnd_1743507 := by exact prefixLift 1743507
  have htrace : WordTrace (prefixWord ++ tailWord_1743507) baseStart_1743507 baseEnd_1743507 := by
    simpa [prefixWord, tailWord_1743507, baseEnd_1743507] using wordTrace_append hprefix tailTrace_1743507
  have hstable : (prefixWord ++ tailWord_1743507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743507).length < 2 ^ (prefixWord ++ tailWord_1743507).sum := by decide
  have hdescent : baseEnd_1743507 < baseStart_1743507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743524 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_1743524 : Nat := 118140960795 + 1743524 * 2 ^ 59
def prefixEnd_1743524 : Nat := 4983230072969 + 3 ^ 40 * 1743524 * 2
def baseEnd_1743524 : Nat := 895265844649741688031685

theorem tailTrace_1743524 : CollatzResearch.WordTrace tailWord_1743524 prefixEnd_1743524 895265844649741688031685 := by
  unfold tailWord_1743524
  simp only [CollatzResearch.WordTrace]
  refine ⟨31795772267758896518806813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42394363023678528691742417 31795772267758896518806813)
  ·
    refine ⟨11923414600409586194552555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31795772267758896518806813 11923414600409586194552555)
    ·
      refine ⟨17885121900614379291828833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11923414600409586194552555 17885121900614379291828833)
      ·
        refine ⟨13413841425460784468871625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17885121900614379291828833 13413841425460784468871625)
        ·
          refine ⟨10060381069095588351653719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13413841425460784468871625 10060381069095588351653719)
          ·
            refine ⟨15090571603643382527480579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10060381069095588351653719 15090571603643382527480579)
            ·
              refine ⟨22635857405465073791220869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15090571603643382527480579 22635857405465073791220869)
              ·
                refine ⟨4244223263524701335853913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22635857405465073791220869 4244223263524701335853913)
                ·
                  refine ⟨3183167447643526001890435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4244223263524701335853913 3183167447643526001890435)
                  ·
                    refine ⟨4774751171465289002835653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183167447643526001890435 4774751171465289002835653)
                    ·
                      refine ⟨895265844649741688031685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4774751171465289002835653 895265844649741688031685)
                      ·
                        rfl

theorem cell23_1743524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_1743524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743524 prefixEnd_1743524 := by exact prefixLift 1743524
  have htrace : WordTrace (prefixWord ++ tailWord_1743524) baseStart_1743524 baseEnd_1743524 := by
    simpa [prefixWord, tailWord_1743524, baseEnd_1743524] using wordTrace_append hprefix tailTrace_1743524
  have hstable : (prefixWord ++ tailWord_1743524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743524).length < 2 ^ (prefixWord ++ tailWord_1743524).sum := by decide
  have hdescent : baseEnd_1743524 < baseStart_1743524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743541 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_1743541 : Nat := 118140960795 + 1743541 * 2 ^ 59
def prefixEnd_1743541 : Nat := 4983230072969 + 3 ^ 40 * 1743541 * 2
def baseEnd_1743541 : Nat := 895274573820868121519107

theorem tailTrace_1743541 : CollatzResearch.WordTrace tailWord_1743541 prefixEnd_1743541 895274573820868121519107 := by
  unfold tailWord_1743541
  simp only [CollatzResearch.WordTrace]
  refine ⟨63592164576456204940982477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42394776384304136627321651 63592164576456204940982477)
  ·
    refine ⟨23847061716171076852868429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63592164576456204940982477 23847061716171076852868429)
    ·
      refine ⟨8942648143564153819825661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23847061716171076852868429 8942648143564153819825661)
      ·
        refine ⟨3353493053836557682434623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8942648143564153819825661 3353493053836557682434623)
        ·
          refine ⟨5030239580754836523651935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353493053836557682434623 5030239580754836523651935)
          ·
            refine ⟨7545359371132254785477903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030239580754836523651935 7545359371132254785477903)
            ·
              refine ⟨11318039056698382178216855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7545359371132254785477903 11318039056698382178216855)
              ·
                refine ⟨16977058585047573267325283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11318039056698382178216855 16977058585047573267325283)
                ·
                  refine ⟨25465587877571359900987925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16977058585047573267325283 25465587877571359900987925)
                  ·
                    refine ⟨1193699431761157495358809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25465587877571359900987925 1193699431761157495358809)
                    ·
                      refine ⟨895274573820868121519107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193699431761157495358809 895274573820868121519107)
                      ·
                        rfl

theorem cell23_1743541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_1743541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743541 prefixEnd_1743541 := by exact prefixLift 1743541
  have htrace : WordTrace (prefixWord ++ tailWord_1743541) baseStart_1743541 baseEnd_1743541 := by
    simpa [prefixWord, tailWord_1743541, baseEnd_1743541] using wordTrace_append hprefix tailTrace_1743541
  have hstable : (prefixWord ++ tailWord_1743541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743541).length < 2 ^ (prefixWord ++ tailWord_1743541).sum := by decide
  have hdescent : baseEnd_1743541 < baseStart_1743541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743618 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_1743618 : Nat := 118140960795 + 1743618 * 2 ^ 59
def prefixEnd_1743618 : Nat := 4983230072969 + 3 ^ 40 * 1743618 * 2
def baseEnd_1743618 : Nat := 895314111831264320256253

theorem tailTrace_1743618 : CollatzResearch.WordTrace tailWord_1743618 prefixEnd_1743618 895314111831264320256253 := by
  unfold tailWord_1743618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15898743249294311772883877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42396648664784831394357005 15898743249294311772883877)
  ·
    refine ⟨2981014359242683457415727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15898743249294311772883877 2981014359242683457415727)
    ·
      refine ⟨4471521538864025186123591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2981014359242683457415727 4471521538864025186123591)
      ·
        refine ⟨6707282308296037779185387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471521538864025186123591 6707282308296037779185387)
        ·
          refine ⟨10060923462444056668778081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6707282308296037779185387 10060923462444056668778081)
          ·
            refine ⟨7545692596833042501583561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10060923462444056668778081 7545692596833042501583561)
            ·
              refine ⟨5659269447624781876187671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7545692596833042501583561 5659269447624781876187671)
              ·
                refine ⟨8488904171437172814281507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5659269447624781876187671 8488904171437172814281507)
                ·
                  refine ⟨12733356257155759221422261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8488904171437172814281507 12733356257155759221422261)
                  ·
                    refine ⟨1193752149108352427008337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12733356257155759221422261 1193752149108352427008337)
                    ·
                      refine ⟨895314111831264320256253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193752149108352427008337 895314111831264320256253)
                      ·
                        rfl

theorem cell23_1743618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_1743618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743618 prefixEnd_1743618 := by exact prefixLift 1743618
  have htrace : WordTrace (prefixWord ++ tailWord_1743618) baseStart_1743618 baseEnd_1743618 := by
    simpa [prefixWord, tailWord_1743618, baseEnd_1743618] using wordTrace_append hprefix tailTrace_1743618
  have hstable : (prefixWord ++ tailWord_1743618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743618).length < 2 ^ (prefixWord ++ tailWord_1743618).sum := by decide
  have hdescent : baseEnd_1743618 < baseStart_1743618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743644 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1743644 : Nat := 118140960795 + 1743644 * 2 ^ 59
def prefixEnd_1743644 : Nat := 4983230072969 + 3 ^ 40 * 1743644 * 2
def baseEnd_1743644 : Nat := 895327462328281218531133

theorem tailTrace_1743644 : CollatzResearch.WordTrace tailWord_1743644 prefixEnd_1743644 895327462328281218531133 := by
  unfold tailWord_1743644
  simp only [CollatzResearch.WordTrace]
  refine ⟨31797960647541526765990993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42397280863388702354654657 31797960647541526765990993)
  ·
    refine ⟨23848470485656145074493245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31797960647541526765990993 23848470485656145074493245)
    ·
      refine ⟨8943176432121054402934967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23848470485656145074493245 8943176432121054402934967)
      ·
        refine ⟨13414764648181581604402451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8943176432121054402934967 13414764648181581604402451)
        ·
          refine ⟨20122146972272372406603677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13414764648181581604402451 20122146972272372406603677)
          ·
            refine ⟨7545805114602139652476379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20122146972272372406603677 7545805114602139652476379)
            ·
              refine ⟨11318707671903209478714569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7545805114602139652476379 11318707671903209478714569)
              ·
                refine ⟨8489030753927407109035927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11318707671903209478714569 8489030753927407109035927)
                ·
                  refine ⟨12733546130891110663553891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8489030753927407109035927 12733546130891110663553891)
                  ·
                    refine ⟨19100319196336665995330837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12733546130891110663553891 19100319196336665995330837)
                    ·
                      refine ⟨895327462328281218531133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19100319196336665995330837 895327462328281218531133)
                      ·
                        rfl

theorem cell23_1743644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1743644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743644 prefixEnd_1743644 := by exact prefixLift 1743644
  have htrace : WordTrace (prefixWord ++ tailWord_1743644) baseStart_1743644 baseEnd_1743644 := by
    simpa [prefixWord, tailWord_1743644, baseEnd_1743644] using wordTrace_append hprefix tailTrace_1743644
  have hstable : (prefixWord ++ tailWord_1743644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743644).length < 2 ^ (prefixWord ++ tailWord_1743644).sum := by decide
  have hdescent : baseEnd_1743644 < baseStart_1743644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743664 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 3]
def baseStart_1743664 : Nat := 118140960795 + 1743664 * 2 ^ 59
def prefixEnd_1743664 : Nat := 4983230072969 + 3 ^ 40 * 1743664 * 2
def baseEnd_1743664 : Nat := 895337731941371140281041

theorem tailTrace_1743664 : CollatzResearch.WordTrace tailWord_1743664 prefixEnd_1743664 895337731941371140281041 := by
  unfold tailWord_1743664
  simp only [CollatzResearch.WordTrace]
  refine ⟨31798325377505298473855023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42397767170007064631806697 31798325377505298473855023)
  ·
    refine ⟨47697488066257947710782535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31798325377505298473855023 47697488066257947710782535)
    ·
      refine ⟨71546232099386921566173803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47697488066257947710782535 71546232099386921566173803)
      ·
        refine ⟨107319348149080382349260705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71546232099386921566173803 107319348149080382349260705)
        ·
          refine ⟨80489511111810286761945529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107319348149080382349260705 80489511111810286761945529)
          ·
            refine ⟨60367133333857715071459147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80489511111810286761945529 60367133333857715071459147)
            ·
              refine ⟨90550700000786572607188721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60367133333857715071459147 90550700000786572607188721)
              ·
                refine ⟨67913025000589929455391541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90550700000786572607188721 67913025000589929455391541)
                ·
                  refine ⟨6366846093805305886442957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67913025000589929455391541 6366846093805305886442957)
                  ·
                    refine ⟨2387567285176989707416109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6366846093805305886442957 2387567285176989707416109)
                    ·
                      refine ⟨895337731941371140281041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2387567285176989707416109 895337731941371140281041)
                      ·
                        rfl

theorem cell23_1743664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 3].length) (baseStart_1743664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743664 prefixEnd_1743664 := by exact prefixLift 1743664
  have htrace : WordTrace (prefixWord ++ tailWord_1743664) baseStart_1743664 baseEnd_1743664 := by
    simpa [prefixWord, tailWord_1743664, baseEnd_1743664] using wordTrace_append hprefix tailTrace_1743664
  have hstable : (prefixWord ++ tailWord_1743664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743664).length < 2 ^ (prefixWord ++ tailWord_1743664).sum := by decide
  have hdescent : baseEnd_1743664 < baseStart_1743664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743678 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1743678 : Nat := 118140960795 + 1743678 * 2 ^ 59
def prefixEnd_1743678 : Nat := 4983230072969 + 3 ^ 40 * 1743678 * 2
def baseEnd_1743678 : Nat := 895344920670534085505977

theorem tailTrace_1743678 : CollatzResearch.WordTrace tailWord_1743678 prefixEnd_1743678 895344920670534085505977 := by
  unfold tailWord_1743678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949645172119984667339961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42398107584639918225813125 7949645172119984667339961)
  ·
    refine ⟨5962233879089988500504971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7949645172119984667339961 5962233879089988500504971)
    ·
      refine ⟨8943350818634982750757457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5962233879089988500504971 8943350818634982750757457)
      ·
        refine ⟨6707513113976237063068093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8943350818634982750757457 6707513113976237063068093)
        ·
          refine ⟨2515317417741088898650535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6707513113976237063068093 2515317417741088898650535)
          ·
            refine ⟨3772976126611633347975803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515317417741088898650535 3772976126611633347975803)
            ·
              refine ⟨5659464189917450021963705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772976126611633347975803 5659464189917450021963705)
              ·
                refine ⟨4244598142438087516472779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5659464189917450021963705 4244598142438087516472779)
                ·
                  refine ⟨6366897213657131274709169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244598142438087516472779 6366897213657131274709169)
                  ·
                    refine ⟨4775172910242848456031877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6366897213657131274709169 4775172910242848456031877)
                    ·
                      refine ⟨895344920670534085505977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4775172910242848456031877 895344920670534085505977)
                      ·
                        rfl

theorem cell23_1743678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1743678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743678 prefixEnd_1743678 := by exact prefixLift 1743678
  have htrace : WordTrace (prefixWord ++ tailWord_1743678) baseStart_1743678 baseEnd_1743678 := by
    simpa [prefixWord, tailWord_1743678, baseEnd_1743678] using wordTrace_append hprefix tailTrace_1743678
  have hstable : (prefixWord ++ tailWord_1743678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743678).length < 2 ^ (prefixWord ++ tailWord_1743678).sum := by decide
  have hdescent : baseEnd_1743678 < baseStart_1743678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743694 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1743694 : Nat := 118140960795 + 1743694 * 2 ^ 59
def prefixEnd_1743694 : Nat := 4983230072969 + 3 ^ 40 * 1743694 * 2
def baseEnd_1743694 : Nat := 895353136361006022905903

theorem tailTrace_1743694 : CollatzResearch.WordTrace tailWord_1743694 prefixEnd_1743694 895353136361006022905903 := by
  unfold tailWord_1743694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949718118112739008912767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42398496629934608047534757 7949718118112739008912767)
  ·
    refine ⟨11924577177169108513369151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7949718118112739008912767 11924577177169108513369151)
    ·
      refine ⟨17886865765753662770053727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11924577177169108513369151 17886865765753662770053727)
      ·
        refine ⟨26830298648630494155080591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17886865765753662770053727 26830298648630494155080591)
        ·
          refine ⟨40245447972945741232620887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26830298648630494155080591 40245447972945741232620887)
          ·
            refine ⟨60368171959418611848931331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40245447972945741232620887 60368171959418611848931331)
            ·
              refine ⟨90552257939127917773396997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60368171959418611848931331 90552257939127917773396997)
              ·
                refine ⟨16978548363586484582511937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90552257939127917773396997 16978548363586484582511937)
                ·
                  refine ⟨12733911272689863436883953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16978548363586484582511937 12733911272689863436883953)
                  ·
                    refine ⟨9550433454517397577662965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12733911272689863436883953 9550433454517397577662965)
                    ·
                      refine ⟨895353136361006022905903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9550433454517397577662965 895353136361006022905903)
                      ·
                        rfl

theorem cell23_1743694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1743694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743694 prefixEnd_1743694 := by exact prefixLift 1743694
  have htrace : WordTrace (prefixWord ++ tailWord_1743694) baseStart_1743694 baseEnd_1743694 := by
    simpa [prefixWord, tailWord_1743694, baseEnd_1743694] using wordTrace_append hprefix tailTrace_1743694
  have hstable : (prefixWord ++ tailWord_1743694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743694).length < 2 ^ (prefixWord ++ tailWord_1743694).sum := by decide
  have hdescent : baseEnd_1743694 < baseStart_1743694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743738 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2]
def baseStart_1743738 : Nat := 118140960795 + 1743738 * 2 ^ 59
def prefixEnd_1743738 : Nat := 4983230072969 + 3 ^ 40 * 1743738 * 2
def baseEnd_1743738 : Nat := 895375729509803850755701

theorem tailTrace_1743738 : CollatzResearch.WordTrace tailWord_1743738 prefixEnd_1743738 895375729509803850755701 := by
  unfold tailWord_1743738
  simp only [CollatzResearch.WordTrace]
  refine ⟨15899837439185626896475967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42399566504495005057269245 15899837439185626896475967)
  ·
    refine ⟨23849756158778440344713951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15899837439185626896475967 23849756158778440344713951)
    ·
      refine ⟨35774634238167660517070927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23849756158778440344713951 35774634238167660517070927)
      ·
        refine ⟨53661951357251490775606391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35774634238167660517070927 53661951357251490775606391)
        ·
          refine ⟨80492927035877236163409587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53661951357251490775606391 80492927035877236163409587)
          ·
            refine ⟨120739390553815854245114381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80492927035877236163409587 120739390553815854245114381)
            ·
              refine ⟨45277271457680945341917893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120739390553815854245114381 45277271457680945341917893)
              ·
                refine ⟨8489488398315177251609605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45277271457680945341917893 8489488398315177251609605)
                ·
                  refine ⟨1591779074684095734676801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8489488398315177251609605 1591779074684095734676801)
                  ·
                    refine ⟨1193834306013071801007601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1591779074684095734676801 1193834306013071801007601)
                    ·
                      refine ⟨895375729509803850755701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193834306013071801007601 895375729509803850755701)
                      ·
                        rfl

theorem cell23_1743738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_1743738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743738 prefixEnd_1743738 := by exact prefixLift 1743738
  have htrace : WordTrace (prefixWord ++ tailWord_1743738) baseStart_1743738 baseEnd_1743738 := by
    simpa [prefixWord, tailWord_1743738, baseEnd_1743738] using wordTrace_append hprefix tailTrace_1743738
  have hstable : (prefixWord ++ tailWord_1743738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743738).length < 2 ^ (prefixWord ++ tailWord_1743738).sum := by decide
  have hdescent : baseEnd_1743738 < baseStart_1743738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743751 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_1743751 : Nat := 118140960795 + 1743751 * 2 ^ 59
def prefixEnd_1743751 : Nat := 4983230072969 + 3 ^ 40 * 1743751 * 2
def baseEnd_1743751 : Nat := 895382404758312299893141

theorem tailTrace_1743751 : CollatzResearch.WordTrace tailWord_1743751 prefixEnd_1743751 895382404758312299893141 := by
  unfold tailWord_1743751
  simp only [CollatzResearch.WordTrace]
  refine ⟨63599823905695410806127107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42399882603796940537418071 63599823905695410806127107)
  ·
    refine ⟨95399735858543116209190661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63599823905695410806127107 95399735858543116209190661)
    ·
      refine ⟨17887450473476834289223249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95399735858543116209190661 17887450473476834289223249)
      ·
        refine ⟨13415587855107625716917437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17887450473476834289223249 13415587855107625716917437)
        ·
          refine ⟨5030845445665359643844039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13415587855107625716917437 5030845445665359643844039)
          ·
            refine ⟨7546268168498039465766059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030845445665359643844039 7546268168498039465766059)
            ·
              refine ⟨11319402252747059198649089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7546268168498039465766059 11319402252747059198649089)
              ·
                refine ⟨8489551689560294398986817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11319402252747059198649089 8489551689560294398986817)
                ·
                  refine ⟨6367163767170220799240113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8489551689560294398986817 6367163767170220799240113)
                  ·
                    refine ⟨4775372825377665599430085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6367163767170220799240113 4775372825377665599430085)
                    ·
                      refine ⟨895382404758312299893141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4775372825377665599430085 895382404758312299893141)
                      ·
                        rfl

theorem cell23_1743751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_1743751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743751 prefixEnd_1743751 := by exact prefixLift 1743751
  have htrace : WordTrace (prefixWord ++ tailWord_1743751) baseStart_1743751 baseEnd_1743751 := by
    simpa [prefixWord, tailWord_1743751, baseEnd_1743751] using wordTrace_append hprefix tailTrace_1743751
  have hstable : (prefixWord ++ tailWord_1743751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743751).length < 2 ^ (prefixWord ++ tailWord_1743751).sum := by decide
  have hdescent : baseEnd_1743751 < baseStart_1743751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743755 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 2, 2, 2]
def baseStart_1743755 : Nat := 118140960795 + 1743755 * 2 ^ 59
def prefixEnd_1743755 : Nat := 4983230072969 + 3 ^ 40 * 1743755 * 2
def baseEnd_1743755 : Nat := 895384458680930284243123

theorem tailTrace_1743755 : CollatzResearch.WordTrace tailWord_1743755 prefixEnd_1743755 895384458680930284243123 := by
  unfold tailWord_1743755
  simp only [CollatzResearch.WordTrace]
  refine ⟨63599969797680919489272719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42399979865120612992848479 63599969797680919489272719)
  ·
    refine ⟨95399954696521379233909079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63599969797680919489272719 95399954696521379233909079)
    ·
      refine ⟨143099932044782068850863619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95399954696521379233909079 143099932044782068850863619)
      ·
        refine ⟨214649898067173103276295429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143099932044782068850863619 214649898067173103276295429)
        ·
          refine ⟨40246855887594956864305393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214649898067173103276295429 40246855887594956864305393)
          ·
            refine ⟨30185141915696217648229045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40246855887594956864305393 30185141915696217648229045)
            ·
              refine ⟨2829857054596520404521473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30185141915696217648229045 2829857054596520404521473)
              ·
                refine ⟨2122392790947390303391105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2829857054596520404521473 2122392790947390303391105)
                ·
                  refine ⟨1591794593210542727543329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2122392790947390303391105 1591794593210542727543329)
                  ·
                    refine ⟨1193845944907907045657497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1591794593210542727543329 1193845944907907045657497)
                    ·
                      refine ⟨895384458680930284243123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193845944907907045657497 895384458680930284243123)
                      ·
                        rfl

theorem cell23_1743755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 2, 2].length) (baseStart_1743755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743755 prefixEnd_1743755 := by exact prefixLift 1743755
  have htrace : WordTrace (prefixWord ++ tailWord_1743755) baseStart_1743755 baseEnd_1743755 := by
    simpa [prefixWord, tailWord_1743755, baseEnd_1743755] using wordTrace_append hprefix tailTrace_1743755
  have hstable : (prefixWord ++ tailWord_1743755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743755).length < 2 ^ (prefixWord ++ tailWord_1743755).sum := by decide
  have hdescent : baseEnd_1743755 < baseStart_1743755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743766 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_1743766 : Nat := 118140960795 + 1743766 * 2 ^ 59
def prefixEnd_1743766 : Nat := 4983230072969 + 3 ^ 40 * 1743766 * 2
def baseEnd_1743766 : Nat := 895390106968129741205573

theorem tailTrace_1743766 : CollatzResearch.WordTrace tailWord_1743766 prefixEnd_1743766 895390106968129741205573 := by
  unfold tailWord_1743766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3975023187540066772995197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42400247333760712245282101 3975023187540066772995197)
  ·
    refine ⟨1490633695327525039873199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3975023187540066772995197 1490633695327525039873199)
    ·
      refine ⟨2235950542991287559809799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1490633695327525039873199 2235950542991287559809799)
      ·
        refine ⟨3353925814486931339714699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235950542991287559809799 3353925814486931339714699)
        ·
          refine ⟨5030888721730397009572049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353925814486931339714699 5030888721730397009572049)
          ·
            refine ⟨3773166541297797757179037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5030888721730397009572049 3773166541297797757179037)
            ·
              refine ⟨1414937452986674158942139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3773166541297797757179037 1414937452986674158942139)
              ·
                refine ⟨2122406179480011238413209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414937452986674158942139 2122406179480011238413209)
                ·
                  refine ⟨1591804634610008428809907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2122406179480011238413209 1591804634610008428809907)
                  ·
                    refine ⟨2387706951915012643214861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1591804634610008428809907 2387706951915012643214861)
                    ·
                      refine ⟨895390106968129741205573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2387706951915012643214861 895390106968129741205573)
                      ·
                        rfl

theorem cell23_1743766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_1743766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743766 prefixEnd_1743766 := by exact prefixLift 1743766
  have htrace : WordTrace (prefixWord ++ tailWord_1743766) baseStart_1743766 baseEnd_1743766 := by
    simpa [prefixWord, tailWord_1743766, baseEnd_1743766] using wordTrace_append hprefix tailTrace_1743766
  have hstable : (prefixWord ++ tailWord_1743766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743766).length < 2 ^ (prefixWord ++ tailWord_1743766).sum := by decide
  have hdescent : baseEnd_1743766 < baseStart_1743766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743772 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1743772 : Nat := 118140960795 + 1743772 * 2 ^ 59
def prefixEnd_1743772 : Nat := 4983230072969 + 3 ^ 40 * 1743772 * 2
def baseEnd_1743772 : Nat := 895393187852056717730545

theorem tailTrace_1743772 : CollatzResearch.WordTrace tailWord_1743772 prefixEnd_1743772 895393187852056717730545 := by
  unfold tailWord_1743772
  simp only [CollatzResearch.WordTrace]
  refine ⟨31800294919309665696320785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42400393225746220928427713 31800294919309665696320785)
  ·
    refine ⟨23850221189482249272240589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31800294919309665696320785 23850221189482249272240589)
    ·
      refine ⟨8943832946055843477090221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23850221189482249272240589 8943832946055843477090221)
      ·
        refine ⟨3353937354770941303908833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8943832946055843477090221 3353937354770941303908833)
        ·
          refine ⟨2515453016078205977931625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3353937354770941303908833 2515453016078205977931625)
          ·
            refine ⟨1886589762058654483448719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2515453016078205977931625 1886589762058654483448719)
            ·
              refine ⟨2829884643087981725173079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886589762058654483448719 2829884643087981725173079)
              ·
                refine ⟨4244826964631972587759619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829884643087981725173079 4244826964631972587759619)
                ·
                  refine ⟨6367240446947958881639429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244826964631972587759619 6367240446947958881639429)
                  ·
                    refine ⟨1193857583802742290307393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6367240446947958881639429 1193857583802742290307393)
                    ·
                      refine ⟨895393187852056717730545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193857583802742290307393 895393187852056717730545)
                      ·
                        rfl

theorem cell23_1743772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1743772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743772 prefixEnd_1743772 := by exact prefixLift 1743772
  have htrace : WordTrace (prefixWord ++ tailWord_1743772) baseStart_1743772 baseEnd_1743772 := by
    simpa [prefixWord, tailWord_1743772, baseEnd_1743772] using wordTrace_append hprefix tailTrace_1743772
  have hstable : (prefixWord ++ tailWord_1743772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743772).length < 2 ^ (prefixWord ++ tailWord_1743772).sum := by decide
  have hdescent : baseEnd_1743772 < baseStart_1743772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743811 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 4]
def baseStart_1743811 : Nat := 118140960795 + 1743811 * 2 ^ 59
def prefixEnd_1743811 : Nat := 4983230072969 + 3 ^ 40 * 1743811 * 2
def baseEnd_1743811 : Nat := 895413213597582065142865

theorem tailTrace_1743811 : CollatzResearch.WordTrace tailWord_1743811 prefixEnd_1743811 895413213597582065142865 := by
  unfold tailWord_1743811
  simp only [CollatzResearch.WordTrace]
  refine ⟨63602012285478041053311287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42401341523652027368874191 63602012285478041053311287)
  ·
    refine ⟨95403018428217061579966931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63602012285478041053311287 95403018428217061579966931)
    ·
      refine ⟨143104527642325592369950397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95403018428217061579966931 143104527642325592369950397)
      ·
        refine ⟨53664197865872097138731399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143104527642325592369950397 53664197865872097138731399)
        ·
          refine ⟨80496296798808145708097099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53664197865872097138731399 80496296798808145708097099)
          ·
            refine ⟨120744445198212218562145649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80496296798808145708097099 120744445198212218562145649)
            ·
              refine ⟨90558333898659163921609237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120744445198212218562145649 90558333898659163921609237)
              ·
                refine ⟨4244921901499648308825433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90558333898659163921609237 4244921901499648308825433)
                ·
                  refine ⟨3183691426124736231619075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4244921901499648308825433 3183691426124736231619075)
                  ·
                    refine ⟨4775537139187104347428613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3183691426124736231619075 4775537139187104347428613)
                    ·
                      refine ⟨895413213597582065142865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4775537139187104347428613 895413213597582065142865)
                      ·
                        rfl

theorem cell23_1743811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_1743811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743811 prefixEnd_1743811 := by exact prefixLift 1743811
  have htrace : WordTrace (prefixWord ++ tailWord_1743811) baseStart_1743811 baseEnd_1743811 := by
    simpa [prefixWord, tailWord_1743811, baseEnd_1743811] using wordTrace_append hprefix tailTrace_1743811
  have hstable : (prefixWord ++ tailWord_1743811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743811).length < 2 ^ (prefixWord ++ tailWord_1743811).sum := by decide
  have hdescent : baseEnd_1743811 < baseStart_1743811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743812 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 7]
def baseStart_1743812 : Nat := 118140960795 + 1743812 * 2 ^ 59
def prefixEnd_1743812 : Nat := 4983230072969 + 3 ^ 40 * 1743812 * 2
def baseEnd_1743812 : Nat := 99490414119804062358929

theorem tailTrace_1743812 : CollatzResearch.WordTrace tailWord_1743812 prefixEnd_1743812 99490414119804062358929 := by
  unfold tailWord_1743812
  simp only [CollatzResearch.WordTrace]
  refine ⟨31801024379237209112048845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42401365838982945482731793 31801024379237209112048845)
  ·
    refine ⟨11925384142213953417018317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31801024379237209112048845 11925384142213953417018317)
    ·
      refine ⟨4472019053330232531381869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11925384142213953417018317 4472019053330232531381869)
      ·
        refine ⟨1677007144998837199268201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4472019053330232531381869 1677007144998837199268201)
        ·
          refine ⟨1257755358749127899451151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1677007144998837199268201 1257755358749127899451151)
          ·
            refine ⟨1886633038123691849176727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257755358749127899451151 1886633038123691849176727)
            ·
              refine ⟨2829949557185537773765091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886633038123691849176727 2829949557185537773765091)
              ·
                refine ⟨4244924335778306660647637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829949557185537773765091 4244924335778306660647637)
                ·
                  refine ⟨99490414119804062358929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4244924335778306660647637 99490414119804062358929)
                  ·
                    rfl

theorem cell23_1743812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_1743812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743812 prefixEnd_1743812 := by exact prefixLift 1743812
  have htrace : WordTrace (prefixWord ++ tailWord_1743812) baseStart_1743812 baseEnd_1743812 := by
    simpa [prefixWord, tailWord_1743812, baseEnd_1743812] using wordTrace_append hprefix tailTrace_1743812
  have hstable : (prefixWord ++ tailWord_1743812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743812).length < 2 ^ (prefixWord ++ tailWord_1743812).sum := by decide
  have hdescent : baseEnd_1743812 < baseStart_1743812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743831 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 3]
def baseStart_1743831 : Nat := 118140960795 + 1743831 * 2 ^ 59
def prefixEnd_1743831 : Nat := 4983230072969 + 3 ^ 40 * 1743831 * 2
def baseEnd_1743831 : Nat := 895423483210671986892773

theorem tailTrace_1743831 : CollatzResearch.WordTrace tailWord_1743831 prefixEnd_1743831 895423483210671986892773 := by
  unfold tailWord_1743831
  simp only [CollatzResearch.WordTrace]
  refine ⟨63602741745405584469039347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42401827830270389646026231 63602741745405584469039347)
  ·
    refine ⟨95404112618108376703559021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63602741745405584469039347 95404112618108376703559021)
    ·
      refine ⟨35776542231790641263834633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95404112618108376703559021 35776542231790641263834633)
      ·
        refine ⟨26832406673842980947875975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35776542231790641263834633 26832406673842980947875975)
        ·
          refine ⟨40248610010764471421813963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26832406673842980947875975 40248610010764471421813963)
          ·
            refine ⟨60372915016146707132720945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40248610010764471421813963 60372915016146707132720945)
            ·
              refine ⟨45279686262110030349540709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60372915016146707132720945 45279686262110030349540709)
              ·
                refine ⟨8489941174145630690538883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45279686262110030349540709 8489941174145630690538883)
                ·
                  refine ⟨12734911761218446035808325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8489941174145630690538883 12734911761218446035808325)
                  ·
                    refine ⟨2387795955228458631714061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12734911761218446035808325 2387795955228458631714061)
                    ·
                      refine ⟨895423483210671986892773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2387795955228458631714061 895423483210671986892773)
                      ·
                        rfl

theorem cell23_1743831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_1743831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743831 prefixEnd_1743831 := by exact prefixLift 1743831
  have htrace : WordTrace (prefixWord ++ tailWord_1743831) baseStart_1743831 baseEnd_1743831 := by
    simpa [prefixWord, tailWord_1743831, baseEnd_1743831] using wordTrace_append hprefix tailTrace_1743831
  have hstable : (prefixWord ++ tailWord_1743831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743831).length < 2 ^ (prefixWord ++ tailWord_1743831).sum := by decide
  have hdescent : baseEnd_1743831 < baseStart_1743831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743848 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1743848 : Nat := 118140960795 + 1743848 * 2 ^ 59
def prefixEnd_1743848 : Nat := 4983230072969 + 3 ^ 40 * 1743848 * 2
def baseEnd_1743848 : Nat := 895432212381798420380195

theorem tailTrace_1743848 : CollatzResearch.WordTrace tailWord_1743848 prefixEnd_1743848 895432212381798420380195 := by
  unfold tailWord_1743848
  simp only [CollatzResearch.WordTrace]
  refine ⟨31801680893171998186204099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42402241190895997581605465 31801680893171998186204099)
  ·
    refine ⟨47702521339757997279306149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31801680893171998186204099 47702521339757997279306149)
    ·
      refine ⟨8944222751204624489869903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47702521339757997279306149 8944222751204624489869903)
      ·
        refine ⟨13416334126806936734804855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8944222751204624489869903 13416334126806936734804855)
        ·
          refine ⟨20124501190210405102207283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13416334126806936734804855 20124501190210405102207283)
          ·
            refine ⟨30186751785315607653310925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20124501190210405102207283 30186751785315607653310925)
            ·
              refine ⟨11320031919493352869991597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30186751785315607653310925 11320031919493352869991597)
              ·
                refine ⟨4245011969810007326246849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11320031919493352869991597 4245011969810007326246849)
                ·
                  refine ⟨3183758977357505494685137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4245011969810007326246849 3183758977357505494685137)
                  ·
                    refine ⟨2387819233018129121013853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3183758977357505494685137 2387819233018129121013853)
                    ·
                      refine ⟨895432212381798420380195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2387819233018129121013853 895432212381798420380195)
                      ·
                        rfl

theorem cell23_1743848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1743848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743848 prefixEnd_1743848 := by exact prefixLift 1743848
  have htrace : WordTrace (prefixWord ++ tailWord_1743848) baseStart_1743848 baseEnd_1743848 := by
    simpa [prefixWord, tailWord_1743848, baseEnd_1743848] using wordTrace_append hprefix tailTrace_1743848
  have hstable : (prefixWord ++ tailWord_1743848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743848).length < 2 ^ (prefixWord ++ tailWord_1743848).sum := by decide
  have hdescent : baseEnd_1743848 < baseStart_1743848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743868 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 6]
def baseStart_1743868 : Nat := 118140960795 + 1743868 * 2 ^ 59
def prefixEnd_1743868 : Nat := 4983230072969 + 3 ^ 40 * 1743868 * 2
def baseEnd_1743868 : Nat := 99493609110543149125567

theorem tailTrace_1743868 : CollatzResearch.WordTrace tailWord_1743868 prefixEnd_1743868 99493609110543149125567 := by
  unfold tailWord_1743868
  simp only [CollatzResearch.WordTrace]
  refine ⟨31802045623135769894068129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42402727497514359858757505 31802045623135769894068129)
  ·
    refine ⟨23851534217351827420551097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31802045623135769894068129 23851534217351827420551097)
    ·
      refine ⟨17888650663013870565413323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23851534217351827420551097 17888650663013870565413323)
      ·
        refine ⟨26832975994520805848119985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17888650663013870565413323 26832975994520805848119985)
        ·
          refine ⟨20124731995890604386089989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26832975994520805848119985 20124731995890604386089989)
          ·
            refine ⟨3773387249229488322391873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20124731995890604386089989 3773387249229488322391873)
            ·
              refine ⟨2830040436922116241793905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3773387249229488322391873 2830040436922116241793905)
              ·
                refine ⟨2122530327691587181345429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2830040436922116241793905 2122530327691587181345429)
                ·
                  refine ⟨99493609110543149125567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2122530327691587181345429 99493609110543149125567)
                  ·
                    rfl

theorem cell23_1743868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_1743868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743868 prefixEnd_1743868 := by exact prefixLift 1743868
  have htrace : WordTrace (prefixWord ++ tailWord_1743868) baseStart_1743868 baseEnd_1743868 := by
    simpa [prefixWord, tailWord_1743868, baseEnd_1743868] using wordTrace_append hprefix tailTrace_1743868
  have hstable : (prefixWord ++ tailWord_1743868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743868).length < 2 ^ (prefixWord ++ tailWord_1743868).sum := by decide
  have hdescent : baseEnd_1743868 < baseStart_1743868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743895 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1743895 : Nat := 118140960795 + 1743895 * 2 ^ 59
def prefixEnd_1743895 : Nat := 4983230072969 + 3 ^ 40 * 1743895 * 2
def baseEnd_1743895 : Nat := 895456345972559736492479

theorem tailTrace_1743895 : CollatzResearch.WordTrace tailWord_1743895 prefixEnd_1743895 895456345972559736492479 := by
  unfold tailWord_1743895
  simp only [CollatzResearch.WordTrace]
  refine ⟨63605076017173723399369139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42403384011449148932912759 63605076017173723399369139)
  ·
    refine ⟨95407614025760585099053709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63605076017173723399369139 95407614025760585099053709)
    ·
      refine ⟨35777855259660219412145141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95407614025760585099053709 35777855259660219412145141)
      ·
        refine ⟨3354173930593145569888607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35777855259660219412145141 3354173930593145569888607)
        ·
          refine ⟨5031260895889718354832911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354173930593145569888607 5031260895889718354832911)
          ·
            refine ⟨7546891343834577532249367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031260895889718354832911 7546891343834577532249367)
            ·
              refine ⟨11320337015751866298374051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7546891343834577532249367 11320337015751866298374051)
              ·
                refine ⟨16980505523627799447561077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11320337015751866298374051 16980505523627799447561077)
                ·
                  refine ⟨1591922392840106198208851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16980505523627799447561077 1591922392840106198208851)
                  ·
                    refine ⟨2387883589260159297313277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1591922392840106198208851 2387883589260159297313277)
                    ·
                      refine ⟨895456345972559736492479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2387883589260159297313277 895456345972559736492479)
                      ·
                        rfl

theorem cell23_1743895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1743895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743895 prefixEnd_1743895 := by exact prefixLift 1743895
  have htrace : WordTrace (prefixWord ++ tailWord_1743895) baseStart_1743895 baseEnd_1743895 := by
    simpa [prefixWord, tailWord_1743895, baseEnd_1743895] using wordTrace_append hprefix tailTrace_1743895
  have hstable : (prefixWord ++ tailWord_1743895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743895).length < 2 ^ (prefixWord ++ tailWord_1743895).sum := by decide
  have hdescent : baseEnd_1743895 < baseStart_1743895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743898 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_1743898 : Nat := 118140960795 + 1743898 * 2 ^ 59
def prefixEnd_1743898 : Nat := 4983230072969 + 3 ^ 40 * 1743898 * 2
def baseEnd_1743898 : Nat := 298485962138174408251655

theorem tailTrace_1743898 : CollatzResearch.WordTrace tailWord_1743898 prefixEnd_1743898 298485962138174408251655 := by
  unfold tailWord_1743898
  simp only [CollatzResearch.WordTrace]
  refine ⟨15901296359040713727932087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42403456957441903274485565 15901296359040713727932087)
  ·
    refine ⟨23851944538561070591898131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15901296359040713727932087 23851944538561070591898131)
    ·
      refine ⟨35777916807841605887847197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23851944538561070591898131 35777916807841605887847197)
      ·
        refine ⟨13416718802940602207942699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35777916807841605887847197 13416718802940602207942699)
        ·
          refine ⟨20125078204410903311914049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13416718802940602207942699 20125078204410903311914049)
          ·
            refine ⟨15093808653308177483935537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20125078204410903311914049 15093808653308177483935537)
            ·
              refine ⟨11320356489981133112951653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15093808653308177483935537 11320356489981133112951653)
              ·
                refine ⟨2122566841871462458678435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11320356489981133112951653 2122566841871462458678435)
                ·
                  refine ⟨3183850262807193688017653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122566841871462458678435 3183850262807193688017653)
                  ·
                    refine ⟨298485962138174408251655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3183850262807193688017653 298485962138174408251655)
                    ·
                      rfl

theorem cell23_1743898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_1743898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743898 prefixEnd_1743898 := by exact prefixLift 1743898
  have htrace : WordTrace (prefixWord ++ tailWord_1743898) baseStart_1743898 baseEnd_1743898 := by
    simpa [prefixWord, tailWord_1743898, baseEnd_1743898] using wordTrace_append hprefix tailTrace_1743898
  have hstable : (prefixWord ++ tailWord_1743898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743898).length < 2 ^ (prefixWord ++ tailWord_1743898).sum := by decide
  have hdescent : baseEnd_1743898 < baseStart_1743898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743905 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 1, 5, 2]
def baseStart_1743905 : Nat := 118140960795 + 1743905 * 2 ^ 59
def prefixEnd_1743905 : Nat := 4983230072969 + 3 ^ 40 * 1743905 * 2
def baseEnd_1743905 : Nat := 895461480779104697367433

theorem tailTrace_1743905 : CollatzResearch.WordTrace tailWord_1743905 prefixEnd_1743905 895461480779104697367433 := by
  unfold tailWord_1743905
  simp only [CollatzResearch.WordTrace]
  refine ⟨63605440747137495107233169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42403627164758330071488779 63605440747137495107233169)
  ·
    refine ⟨47704080560353121330424877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63605440747137495107233169 47704080560353121330424877)
    ·
      refine ⟨17889030210132420498909329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47704080560353121330424877 17889030210132420498909329)
      ·
        refine ⟨13416772657599315374181997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17889030210132420498909329 13416772657599315374181997)
        ·
          refine ⟨5031289746599743265318249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13416772657599315374181997 5031289746599743265318249)
          ·
            refine ⟨3773467309949807448988687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5031289746599743265318249 3773467309949807448988687)
            ·
              refine ⟨5660200964924711173483031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773467309949807448988687 5660200964924711173483031)
              ·
                refine ⟨8490301447387066760224547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5660200964924711173483031 8490301447387066760224547)
                ·
                  refine ⟨12735452171080600140336821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8490301447387066760224547 12735452171080600140336821)
                  ·
                    refine ⟨1193948641038806263156577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12735452171080600140336821 1193948641038806263156577)
                    ·
                      refine ⟨895461480779104697367433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193948641038806263156577 895461480779104697367433)
                      ·
                        rfl

theorem cell23_1743905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_1743905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743905 prefixEnd_1743905 := by exact prefixLift 1743905
  have htrace : WordTrace (prefixWord ++ tailWord_1743905) baseStart_1743905 baseEnd_1743905 := by
    simpa [prefixWord, tailWord_1743905, baseEnd_1743905] using wordTrace_append hprefix tailTrace_1743905
  have hstable : (prefixWord ++ tailWord_1743905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743905).length < 2 ^ (prefixWord ++ tailWord_1743905).sum := by decide
  have hdescent : baseEnd_1743905 < baseStart_1743905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743968 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 3]
def baseStart_1743968 : Nat := 118140960795 + 1743968 * 2 ^ 59
def prefixEnd_1743968 : Nat := 4983230072969 + 3 ^ 40 * 1743968 * 2
def baseEnd_1743968 : Nat := 895493830060337950879643

theorem tailTrace_1743968 : CollatzResearch.WordTrace tailWord_1743968 prefixEnd_1743968 895493830060337950879643 := by
  unfold tailWord_1743968
  simp only [CollatzResearch.WordTrace]
  refine ⟨31803869272954628433388279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42405159030606171244517705 31803869272954628433388279)
  ·
    refine ⟨47705803909431942650082419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31803869272954628433388279 47705803909431942650082419)
    ·
      refine ⟨71558705864147913975123629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47705803909431942650082419 71558705864147913975123629)
      ·
        refine ⟨26834514699055467740671361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71558705864147913975123629 26834514699055467740671361)
        ·
          refine ⟨20125886024291600805503521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26834514699055467740671361 20125886024291600805503521)
          ·
            refine ⟨15094414518218700604127641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20125886024291600805503521 15094414518218700604127641)
            ·
              refine ⟨11320810888664025453095731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15094414518218700604127641 11320810888664025453095731)
              ·
                refine ⟨16981216332996038179643597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11320810888664025453095731 16981216332996038179643597)
                ·
                  refine ⟨6367956124873514317366349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16981216332996038179643597 6367956124873514317366349)
                  ·
                    refine ⟨2387983546827567869012381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6367956124873514317366349 2387983546827567869012381)
                    ·
                      refine ⟨895493830060337950879643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2387983546827567869012381 895493830060337950879643)
                      ·
                        rfl

theorem cell23_1743968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_1743968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743968 prefixEnd_1743968 := by exact prefixLift 1743968
  have htrace : WordTrace (prefixWord ++ tailWord_1743968) baseStart_1743968 baseEnd_1743968 := by
    simpa [prefixWord, tailWord_1743968, baseEnd_1743968] using wordTrace_append hprefix tailTrace_1743968
  have hstable : (prefixWord ++ tailWord_1743968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743968).length < 2 ^ (prefixWord ++ tailWord_1743968).sum := by decide
  have hdescent : baseEnd_1743968 < baseStart_1743968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743969 : List Nat := [1, 2, 3, 1, 1, 2, 5, 3, 1, 2, 2]
def baseStart_1743969 : Nat := 118140960795 + 1743969 * 2 ^ 59
def prefixEnd_1743969 : Nat := 4983230072969 + 3 ^ 40 * 1743969 * 2
def baseEnd_1743969 : Nat := 895494343540992446967139

theorem tailTrace_1743969 : CollatzResearch.WordTrace tailWord_1743969 prefixEnd_1743969 895494343540992446967139 := by
  unfold tailWord_1743969
  simp only [CollatzResearch.WordTrace]
  refine ⟨63607775018905634037562961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42405183345937089358375307 63607775018905634037562961)
  ·
    refine ⟨47705831264179225528172221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63607775018905634037562961 47705831264179225528172221)
    ·
      refine ⟨17889686724067209573064583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47705831264179225528172221 17889686724067209573064583)
      ·
        refine ⟨26834530086100814359596875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17889686724067209573064583 26834530086100814359596875)
        ·
          refine ⟨40251795129151221539395313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26834530086100814359596875 40251795129151221539395313)
          ·
            refine ⟨30188846346863416154546485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40251795129151221539395313 30188846346863416154546485)
            ·
              refine ⟨2830204345018445264488733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30188846346863416154546485 2830204345018445264488733)
              ·
                refine ⟨1061326629381916974183275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2830204345018445264488733 1061326629381916974183275)
                ·
                  refine ⟨1591989944072875461274913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1061326629381916974183275 1591989944072875461274913)
                  ·
                    refine ⟨1193992458054656595956185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1591989944072875461274913 1193992458054656595956185)
                    ·
                      refine ⟨895494343540992446967139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1193992458054656595956185 895494343540992446967139)
                      ·
                        rfl

theorem cell23_1743969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_1743969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743969 prefixEnd_1743969 := by exact prefixLift 1743969
  have htrace : WordTrace (prefixWord ++ tailWord_1743969) baseStart_1743969 baseEnd_1743969 := by
    simpa [prefixWord, tailWord_1743969, baseEnd_1743969] using wordTrace_append hprefix tailTrace_1743969
  have hstable : (prefixWord ++ tailWord_1743969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743969).length < 2 ^ (prefixWord ++ tailWord_1743969).sum := by decide
  have hdescent : baseEnd_1743969 < baseStart_1743969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743971 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 1, 9]
def baseStart_1743971 : Nat := 118140960795 + 1743971 * 2 ^ 59
def prefixEnd_1743971 : Nat := 4983230072969 + 3 ^ 40 * 1743971 * 2
def baseEnd_1743971 : Nat := 298498456834100479714043

theorem tailTrace_1743971 : CollatzResearch.WordTrace tailWord_1743971 prefixEnd_1743971 298498456834100479714043 := by
  unfold tailWord_1743971
  simp only [CollatzResearch.WordTrace]
  refine ⟨63607847964898388379135767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42405231976598925586090511 63607847964898388379135767)
  ·
    refine ⟨95411771947347582568703651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63607847964898388379135767 95411771947347582568703651)
    ·
      refine ⟨143117657921021373853055477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95411771947347582568703651 143117657921021373853055477)
      ·
        refine ⟨13417280430095753798723951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143117657921021373853055477 13417280430095753798723951)
        ·
          refine ⟨20125920645143630698085927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13417280430095753798723951 20125920645143630698085927)
          ·
            refine ⟨30188880967715446047128891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20125920645143630698085927 30188880967715446047128891)
            ·
              refine ⟨45283321451573169070693337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30188880967715446047128891 45283321451573169070693337)
              ·
                refine ⟨33962491088679876803020003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45283321451573169070693337 33962491088679876803020003)
                ·
                  refine ⟨50943736633019815204530005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33962491088679876803020003 50943736633019815204530005)
                  ·
                    refine ⟨298498456834100479714043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 50943736633019815204530005 298498456834100479714043)
                    ·
                      rfl

theorem cell23_1743971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 9].length) (baseStart_1743971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743971 prefixEnd_1743971 := by exact prefixLift 1743971
  have htrace : WordTrace (prefixWord ++ tailWord_1743971) baseStart_1743971 baseEnd_1743971 := by
    simpa [prefixWord, tailWord_1743971, baseEnd_1743971] using wordTrace_append hprefix tailTrace_1743971
  have hstable : (prefixWord ++ tailWord_1743971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743971).length < 2 ^ (prefixWord ++ tailWord_1743971).sum := by decide
  have hdescent : baseEnd_1743971 < baseStart_1743971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743986 : List Nat := [3, 2, 1, 2, 2, 1, 5, 2, 1, 2, 2]
def baseStart_1743986 : Nat := 118140960795 + 1743986 * 2 ^ 59
def prefixEnd_1743986 : Nat := 4983230072969 + 3 ^ 40 * 1743986 * 2
def baseEnd_1743986 : Nat := 895503072712118880454561

theorem tailTrace_1743986 : CollatzResearch.WordTrace tailWord_1743986 prefixEnd_1743986 895503072712118880454561 := by
  unfold tailWord_1743986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902098764961011485232953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42405596706562697293954541 15902098764961011485232953)
  ·
    refine ⟨11926574073720758613924715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15902098764961011485232953 11926574073720758613924715)
    ·
      refine ⟨17889861110581137920887073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11926574073720758613924715 17889861110581137920887073)
      ·
        refine ⟨13417395832935853440665305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17889861110581137920887073 13417395832935853440665305)
        ·
          refine ⟨10063046874701890080498979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13417395832935853440665305 10063046874701890080498979)
          ·
            refine ⟨15094570312052835120748469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10063046874701890080498979 15094570312052835120748469)
            ·
              refine ⟨1415115966754953292570169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15094570312052835120748469 1415115966754953292570169)
              ·
                refine ⟨1061336975066214969427627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415115966754953292570169 1061336975066214969427627)
                ·
                  refine ⟨1592005462599322454141441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1061336975066214969427627 1592005462599322454141441)
                  ·
                    refine ⟨1194004096949491840606081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1592005462599322454141441 1194004096949491840606081)
                    ·
                      refine ⟨895503072712118880454561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1194004096949491840606081 895503072712118880454561)
                      ·
                        rfl

theorem cell23_1743986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_1743986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1743986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1743986 prefixEnd_1743986 := by exact prefixLift 1743986
  have htrace : WordTrace (prefixWord ++ tailWord_1743986) baseStart_1743986 baseEnd_1743986 := by
    simpa [prefixWord, tailWord_1743986, baseEnd_1743986] using wordTrace_append hprefix tailTrace_1743986
  have hstable : (prefixWord ++ tailWord_1743986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743986).length < 2 ^ (prefixWord ++ tailWord_1743986).sum := by decide
  have hdescent : baseEnd_1743986 < baseStart_1743986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744029 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_1744029 : Nat := 118140960795 + 1744029 * 2 ^ 59
def prefixEnd_1744029 : Nat := 4983230072969 + 3 ^ 40 * 1744029 * 2
def baseEnd_1744029 : Nat := 895525152380262212216863

theorem tailTrace_1744029 : CollatzResearch.WordTrace tailWord_1744029 prefixEnd_1744029 895525152380262212216863 := by
  unfold tailWord_1744029
  simp only [CollatzResearch.WordTrace]
  refine ⟨63609963398688264284747141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42406642265792176189831427 63609963398688264284747141)
  ·
    refine ⟨11926868137254049553390089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63609963398688264284747141 11926868137254049553390089)
    ·
      refine ⟨8945151102940537165042567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11926868137254049553390089 8945151102940537165042567)
      ·
        refine ⟨13417726654410805747563851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8945151102940537165042567 13417726654410805747563851)
        ·
          refine ⟨20126589981616208621345777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13417726654410805747563851 20126589981616208621345777)
          ·
            refine ⟨15094942486212156466009333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20126589981616208621345777 15094942486212156466009333)
            ·
              refine ⟨1415150858082389668688375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15094942486212156466009333 1415150858082389668688375)
              ·
                refine ⟨2122726287123584503032563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1415150858082389668688375 2122726287123584503032563)
                ·
                  refine ⟨3184089430685376754548845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122726287123584503032563 3184089430685376754548845)
                  ·
                    refine ⟨1194033536507016282955817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3184089430685376754548845 1194033536507016282955817)
                    ·
                      refine ⟨895525152380262212216863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1194033536507016282955817 895525152380262212216863)
                      ·
                        rfl

theorem cell23_1744029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_1744029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744029 prefixEnd_1744029 := by exact prefixLift 1744029
  have htrace : WordTrace (prefixWord ++ tailWord_1744029) baseStart_1744029 baseEnd_1744029 := by
    simpa [prefixWord, tailWord_1744029, baseEnd_1744029] using wordTrace_append hprefix tailTrace_1744029
  have hstable : (prefixWord ++ tailWord_1744029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744029).length < 2 ^ (prefixWord ++ tailWord_1744029).sum := by decide
  have hdescent : baseEnd_1744029 < baseStart_1744029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744065 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 9]
def baseStart_1744065 : Nat := 118140960795 + 1744065 * 2 ^ 59
def prefixEnd_1744065 : Nat := 4983230072969 + 3 ^ 40 * 1744065 * 2
def baseEnd_1744065 : Nat := 99504848631536007929633

theorem tailTrace_1744065 : CollatzResearch.WordTrace tailWord_1744065 prefixEnd_1744065 99504848631536007929633 := by
  unfold tailWord_1744065
  simp only [CollatzResearch.WordTrace]
  refine ⟨63611276426557842433057649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42407517617705228288705099 63611276426557842433057649)
  ·
    refine ⟨47708457319918381824793237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63611276426557842433057649 47708457319918381824793237)
    ·
      refine ⟨2236333936871174148037183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47708457319918381824793237 2236333936871174148037183)
      ·
        refine ⟨3354500905306761222055775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2236333936871174148037183 3354500905306761222055775)
        ·
          refine ⟨5031751357960141833083663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354500905306761222055775 5031751357960141833083663)
          ·
            refine ⟨7547627036940212749625495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031751357960141833083663 7547627036940212749625495)
            ·
              refine ⟨11321440555410319124438243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7547627036940212749625495 11321440555410319124438243)
              ·
                refine ⟨16982160833115478686657365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11321440555410319124438243 16982160833115478686657365)
                ·
                  refine ⟨99504848631536007929633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16982160833115478686657365 99504848631536007929633)
                  ·
                    rfl

theorem cell23_1744065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 9].length) (baseStart_1744065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744065 prefixEnd_1744065 := by exact prefixLift 1744065
  have htrace : WordTrace (prefixWord ++ tailWord_1744065) baseStart_1744065 baseEnd_1744065 := by
    simpa [prefixWord, tailWord_1744065, baseEnd_1744065] using wordTrace_append hprefix tailTrace_1744065
  have hstable : (prefixWord ++ tailWord_1744065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744065).length < 2 ^ (prefixWord ++ tailWord_1744065).sum := by decide
  have hdescent : baseEnd_1744065 < baseStart_1744065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744082 : List Nat := [3, 2, 2, 2, 1, 1, 4, 3, 5]
def baseStart_1744082 : Nat := 118140960795 + 1744082 * 2 ^ 59
def prefixEnd_1744082 : Nat := 4983230072969 + 3 ^ 40 * 1744082 * 2
def baseEnd_1744082 : Nat := 99505818539438944983791

theorem tailTrace_1744082 : CollatzResearch.WordTrace tailWord_1744082 prefixEnd_1744082 99505818539438944983791 := by
  unfold tailWord_1744082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902974116874063584106625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42407930978330836224284333 15902974116874063584106625)
  ·
    refine ⟨11927230587655547688079969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15902974116874063584106625 11927230587655547688079969)
    ·
      refine ⟨8945422940741660766059977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11927230587655547688079969 8945422940741660766059977)
      ·
        refine ⟨6709067205556245574544983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8945422940741660766059977 6709067205556245574544983)
        ·
          refine ⟨10063600808334368361817475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6709067205556245574544983 10063600808334368361817475)
          ·
            refine ⟨15095401212501552542726213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10063600808334368361817475 15095401212501552542726213)
            ·
              refine ⟨2830387727344041101761165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15095401212501552542726213 2830387727344041101761165)
              ·
                refine ⟨1061395397754015413160437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2830387727344041101761165 1061395397754015413160437)
                ·
                  refine ⟨99505818539438944983791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1061395397754015413160437 99505818539438944983791)
                  ·
                    rfl

theorem cell23_1744082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_1744082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744082 prefixEnd_1744082 := by exact prefixLift 1744082
  have htrace : WordTrace (prefixWord ++ tailWord_1744082) baseStart_1744082 baseEnd_1744082 := by
    simpa [prefixWord, tailWord_1744082, baseEnd_1744082] using wordTrace_append hprefix tailTrace_1744082
  have hstable : (prefixWord ++ tailWord_1744082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744082).length < 2 ^ (prefixWord ++ tailWord_1744082).sum := by decide
  have hdescent : baseEnd_1744082 < baseStart_1744082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744093 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1744093 : Nat := 118140960795 + 1744093 * 2 ^ 59
def prefixEnd_1744093 : Nat := 4983230072969 + 3 ^ 40 * 1744093 * 2
def baseEnd_1744093 : Nat := 895558015142149961816569

theorem tailTrace_1744093 : CollatzResearch.WordTrace tailWord_1744093 prefixEnd_1744093 895558015142149961816569 := by
  unfold tailWord_1744093
  simp only [CollatzResearch.WordTrace]
  refine ⟨63612297670456403215076933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42408198446970935476717955 63612297670456403215076933)
  ·
    refine ⟨11927305813210575602826925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63612297670456403215076933 11927305813210575602826925)
    ·
      refine ⟨4472739679953965851060097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11927305813210575602826925 4472739679953965851060097)
      ·
        refine ⟨3354554759965474388295073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4472739679953965851060097 3354554759965474388295073)
        ·
          refine ⟨2515916069974105791221305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3354554759965474388295073 2515916069974105791221305)
          ·
            refine ⟨1886937052480579343415979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2515916069974105791221305 1886937052480579343415979)
            ·
              refine ⟨2830405578720869015123969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886937052480579343415979 2830405578720869015123969)
              ·
                refine ⟨2122804184040651761342977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2830405578720869015123969 2122804184040651761342977)
                ·
                  refine ⟨1592103138030488821007233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2122804184040651761342977 1592103138030488821007233)
                  ·
                    refine ⟨1194077353522866615755425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1592103138030488821007233 1194077353522866615755425)
                    ·
                      refine ⟨895558015142149961816569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1194077353522866615755425 895558015142149961816569)
                      ·
                        rfl

theorem cell23_1744093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1744093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744093 prefixEnd_1744093 := by exact prefixLift 1744093
  have htrace : WordTrace (prefixWord ++ tailWord_1744093) baseStart_1744093 baseEnd_1744093 := by
    simpa [prefixWord, tailWord_1744093, baseEnd_1744093] using wordTrace_append hprefix tailTrace_1744093
  have hstable : (prefixWord ++ tailWord_1744093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744093).length < 2 ^ (prefixWord ++ tailWord_1744093).sum := by decide
  have hdescent : baseEnd_1744093 < baseStart_1744093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744128 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_1744128 : Nat := 118140960795 + 1744128 * 2 ^ 59
def prefixEnd_1744128 : Nat := 4983230072969 + 3 ^ 40 * 1744128 * 2
def baseEnd_1744128 : Nat := 895575986965057324878907

theorem tailTrace_1744128 : CollatzResearch.WordTrace tailWord_1744128 prefixEnd_1744128 895575986965057324878907 := by
  unfold tailWord_1744128
  simp only [CollatzResearch.WordTrace]
  refine ⟨31806787112664802096300519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42409049483553069461734025 31806787112664802096300519)
  ·
    refine ⟨47710180668997203144450779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31806787112664802096300519 47710180668997203144450779)
    ·
      refine ⟨71565271003495804716676169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47710180668997203144450779 71565271003495804716676169)
      ·
        refine ⟨53673953252621853537507127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71565271003495804716676169 53673953252621853537507127)
        ·
          refine ⟨80510929878932780306260691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53673953252621853537507127 80510929878932780306260691)
          ·
            refine ⟨120766394818399170459391037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80510929878932780306260691 120766394818399170459391037)
            ·
              refine ⟨45287398056899688922271639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120766394818399170459391037 45287398056899688922271639)
              ·
                refine ⟨67931097085349533383407459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45287398056899688922271639 67931097085349533383407459)
                ·
                  refine ⟨101896645628024300075111189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67931097085349533383407459 101896645628024300075111189)
                  ·
                    refine ⟨4776405263813639066020837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101896645628024300075111189 4776405263813639066020837)
                    ·
                      refine ⟨895575986965057324878907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4776405263813639066020837 895575986965057324878907)
                      ·
                        rfl

theorem cell23_1744128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_1744128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744128 prefixEnd_1744128 := by exact prefixLift 1744128
  have htrace : WordTrace (prefixWord ++ tailWord_1744128) baseStart_1744128 baseEnd_1744128 := by
    simpa [prefixWord, tailWord_1744128, baseEnd_1744128] using wordTrace_append hprefix tailTrace_1744128
  have hstable : (prefixWord ++ tailWord_1744128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744128).length < 2 ^ (prefixWord ++ tailWord_1744128).sum := by decide
  have hdescent : baseEnd_1744128 < baseStart_1744128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744152 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1744152 : Nat := 118140960795 + 1744152 * 2 ^ 59
def prefixEnd_1744152 : Nat := 4983230072969 + 3 ^ 40 * 1744152 * 2
def baseEnd_1744152 : Nat := 895588310500765230978797

theorem tailTrace_1744152 : CollatzResearch.WordTrace tailWord_1744152 prefixEnd_1744152 895588310500765230978797 := by
  unfold tailWord_1744152
  simp only [CollatzResearch.WordTrace]
  refine ⟨31807224788621328145737355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42409633051495104194316473 31807224788621328145737355)
  ·
    refine ⟨47710837182931992218606033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31807224788621328145737355 47710837182931992218606033)
    ·
      refine ⟨35783127887198994163954525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47710837182931992218606033 35783127887198994163954525)
      ·
        refine ⟨13418672957699622811482947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35783127887198994163954525 13418672957699622811482947)
        ·
          refine ⟨20128009436549434217224421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13418672957699622811482947 20128009436549434217224421)
          ·
            refine ⟨3774001769353018915729579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20128009436549434217224421 3774001769353018915729579)
            ·
              refine ⟨5661002654029528373594369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774001769353018915729579 5661002654029528373594369)
              ·
                refine ⟨4245751990522146280195777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5661002654029528373594369 4245751990522146280195777)
                ·
                  refine ⟨3184313992891609710146833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4245751990522146280195777 3184313992891609710146833)
                  ·
                    refine ⟨2388235494668707282610125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3184313992891609710146833 2388235494668707282610125)
                    ·
                      refine ⟨895588310500765230978797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2388235494668707282610125 895588310500765230978797)
                      ·
                        rfl

theorem cell23_1744152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1744152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744152 prefixEnd_1744152 := by exact prefixLift 1744152
  have htrace : WordTrace (prefixWord ++ tailWord_1744152) baseStart_1744152 baseEnd_1744152 := by
    simpa [prefixWord, tailWord_1744152, baseEnd_1744152] using wordTrace_append hprefix tailTrace_1744152
  have hstable : (prefixWord ++ tailWord_1744152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744152).length < 2 ^ (prefixWord ++ tailWord_1744152).sum := by decide
  have hdescent : baseEnd_1744152 < baseStart_1744152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744159 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 3, 4]
def baseStart_1744159 : Nat := 118140960795 + 1744159 * 2 ^ 59
def prefixEnd_1744159 : Nat := 4983230072969 + 3 ^ 40 * 1744159 * 2
def baseEnd_1744159 : Nat := 298530634955115567863755

theorem tailTrace_1744159 : CollatzResearch.WordTrace tailWord_1744159 prefixEnd_1744159 298530634955115567863755 := by
  unfold tailWord_1744159
  simp only [CollatzResearch.WordTrace]
  refine ⟨63614704888217296486979531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42409803258811530991319687 63614704888217296486979531)
  ·
    refine ⟨95422057332325944730469297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63614704888217296486979531 95422057332325944730469297)
    ·
      refine ⟨71566542999244458547851973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95422057332325944730469297 71566542999244458547851973)
      ·
        refine ⟨13418726812358335977722245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71566542999244458547851973 13418726812358335977722245)
        ·
          refine ⟨2516011277317187995822921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13418726812358335977722245 2516011277317187995822921)
          ·
            refine ⟨1887008457987890996867191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2516011277317187995822921 1887008457987890996867191)
            ·
              refine ⟨2830512686981836495300787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887008457987890996867191 2830512686981836495300787)
              ·
                refine ⟨4245769030472754742951181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830512686981836495300787 4245769030472754742951181)
                ·
                  refine ⟨1592163386427283028606693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4245769030472754742951181 1592163386427283028606693)
                  ·
                    refine ⟨298530634955115567863755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1592163386427283028606693 298530634955115567863755)
                    ·
                      rfl

theorem cell23_1744159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 4].length) (baseStart_1744159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744159 prefixEnd_1744159 := by exact prefixLift 1744159
  have htrace : WordTrace (prefixWord ++ tailWord_1744159) baseStart_1744159 baseEnd_1744159 := by
    simpa [prefixWord, tailWord_1744159, baseEnd_1744159] using wordTrace_append hprefix tailTrace_1744159
  have hstable : (prefixWord ++ tailWord_1744159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744159).length < 2 ^ (prefixWord ++ tailWord_1744159).sum := by decide
  have hdescent : baseEnd_1744159 < baseStart_1744159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744225 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_1744225 : Nat := 118140960795 + 1744225 * 2 ^ 59
def prefixEnd_1744225 : Nat := 4983230072969 + 3 ^ 40 * 1744225 * 2
def baseEnd_1744225 : Nat := 895625794588543445365961

theorem tailTrace_1744225 : CollatzResearch.WordTrace tailWord_1744225 prefixEnd_1744225 895625794588543445365961 := by
  unfold tailWord_1744225
  simp only [CollatzResearch.WordTrace]
  refine ⟨63617112105978189758882129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42411408070652126505921419 63617112105978189758882129)
  ·
    refine ⟨47712834079483642319161597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63617112105978189758882129 47712834079483642319161597)
    ·
      refine ⟨17892312779806365869685599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47712834079483642319161597 17892312779806365869685599)
      ·
        refine ⟨26838469169709548804528399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17892312779806365869685599 26838469169709548804528399)
        ·
          refine ⟨40257703754564323206792599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26838469169709548804528399 40257703754564323206792599)
          ·
            refine ⟨60386555631846484810188899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40257703754564323206792599 60386555631846484810188899)
            ·
              refine ⟨90579833447769727215283349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60386555631846484810188899 90579833447769727215283349)
              ·
                refine ⟨4245929692864205963216407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90579833447769727215283349 4245929692864205963216407)
                ·
                  refine ⟨6368894539296308944824611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245929692864205963216407 6368894539296308944824611)
                  ·
                    refine ⟨9553341808944463417236917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6368894539296308944824611 9553341808944463417236917)
                    ·
                      refine ⟨895625794588543445365961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9553341808944463417236917 895625794588543445365961)
                      ·
                        rfl

theorem cell23_1744225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_1744225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744225 prefixEnd_1744225 := by exact prefixLift 1744225
  have htrace : WordTrace (prefixWord ++ tailWord_1744225) baseStart_1744225 baseEnd_1744225 := by
    simpa [prefixWord, tailWord_1744225, baseEnd_1744225] using wordTrace_append hprefix tailTrace_1744225
  have hstable : (prefixWord ++ tailWord_1744225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744225).length < 2 ^ (prefixWord ++ tailWord_1744225).sum := by decide
  have hdescent : baseEnd_1744225 < baseStart_1744225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744239 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 3, 2, 2]
def baseStart_1744239 : Nat := 118140960795 + 1744239 * 2 ^ 59
def prefixEnd_1744239 : Nat := 4983230072969 + 3 ^ 40 * 1744239 * 2
def baseEnd_1744239 : Nat := 895632983317706390590897

theorem tailTrace_1744239 : CollatzResearch.WordTrace tailWord_1744239 prefixEnd_1744239 895632983317706390590897 := by
  unfold tailWord_1744239
  simp only [CollatzResearch.WordTrace]
  refine ⟨63617622727927470149891771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42411748485284980099927847 63617622727927470149891771)
  ·
    refine ⟨95426434091891205224837657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63617622727927470149891771 95426434091891205224837657)
    ·
      refine ⟨71569825568918403918628243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95426434091891205224837657 71569825568918403918628243)
      ·
        refine ⟨107354738353377605877942365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71569825568918403918628243 107354738353377605877942365)
        ·
          refine ⟨40258026882516602204228387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107354738353377605877942365 40258026882516602204228387)
          ·
            refine ⟨60387040323774903306342581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40258026882516602204228387 60387040323774903306342581)
            ·
              refine ⟨5661285030353897184969617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60387040323774903306342581 5661285030353897184969617)
              ·
                refine ⟨4245963772765422888727213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5661285030353897184969617 4245963772765422888727213)
                ·
                  refine ⟨1592236414787033583272705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4245963772765422888727213 1592236414787033583272705)
                  ·
                    refine ⟨1194177311090275187454529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1592236414787033583272705 1194177311090275187454529)
                    ·
                      refine ⟨895632983317706390590897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1194177311090275187454529 895632983317706390590897)
                      ·
                        rfl

theorem cell23_1744239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 2, 2].length) (baseStart_1744239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744239 prefixEnd_1744239 := by exact prefixLift 1744239
  have htrace : WordTrace (prefixWord ++ tailWord_1744239) baseStart_1744239 baseEnd_1744239 := by
    simpa [prefixWord, tailWord_1744239, baseEnd_1744239] using wordTrace_append hprefix tailTrace_1744239
  have hstable : (prefixWord ++ tailWord_1744239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744239).length < 2 ^ (prefixWord ++ tailWord_1744239).sum := by decide
  have hdescent : baseEnd_1744239 < baseStart_1744239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744242 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1744242 : Nat := 118140960795 + 1744242 * 2 ^ 59
def prefixEnd_1744242 : Nat := 4983230072969 + 3 ^ 40 * 1744242 * 2
def baseEnd_1744242 : Nat := 895634523759669878853383

theorem tailTrace_1744242 : CollatzResearch.WordTrace tailWord_1744242 prefixEnd_1744242 895634523759669878853383 := by
  unfold tailWord_1744242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15904433036729150415562745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42411821431277734441500653 15904433036729150415562745)
  ·
    refine ⟨11928324777546862811672059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15904433036729150415562745 11928324777546862811672059)
    ·
      refine ⟨17892487166320294217508089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11928324777546862811672059 17892487166320294217508089)
      ·
        refine ⟨13419365374740220663131067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17892487166320294217508089 13419365374740220663131067)
        ·
          refine ⟨20129048062110330994696601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13419365374740220663131067 20129048062110330994696601)
          ·
            refine ⟨15096786046582748246022451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20129048062110330994696601 15096786046582748246022451)
            ·
              refine ⟨22645179069874122369033677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15096786046582748246022451 22645179069874122369033677)
              ·
                refine ⟨8491942151202795888387629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22645179069874122369033677 8491942151202795888387629)
                ·
                  refine ⟨3184478306701048458145361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8491942151202795888387629 3184478306701048458145361)
                  ·
                    refine ⟨2388358730025786343609021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3184478306701048458145361 2388358730025786343609021)
                    ·
                      refine ⟨895634523759669878853383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2388358730025786343609021 895634523759669878853383)
                      ·
                        rfl

theorem cell23_1744242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1744242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744242 prefixEnd_1744242 := by exact prefixLift 1744242
  have htrace : WordTrace (prefixWord ++ tailWord_1744242) baseStart_1744242 baseEnd_1744242 := by
    simpa [prefixWord, tailWord_1744242, baseEnd_1744242] using wordTrace_append hprefix tailTrace_1744242
  have hstable : (prefixWord ++ tailWord_1744242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744242).length < 2 ^ (prefixWord ++ tailWord_1744242).sum := by decide
  have hdescent : baseEnd_1744242 < baseStart_1744242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744259 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 1, 2, 3]
def baseStart_1744259 : Nat := 118140960795 + 1744259 * 2 ^ 59
def prefixEnd_1744259 : Nat := 4983230072969 + 3 ^ 40 * 1744259 * 2
def baseEnd_1744259 : Nat := 895643252930796312340805

theorem tailTrace_1744259 : CollatzResearch.WordTrace tailWord_1744259 prefixEnd_1744259 895643252930796312340805 := by
  unfold tailWord_1744259
  simp only [CollatzResearch.WordTrace]
  refine ⟨63618352187855013565619831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42412234791903342377079887 63618352187855013565619831)
  ·
    refine ⟨95427528281782520348429747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63618352187855013565619831 95427528281782520348429747)
    ·
      refine ⟨143141292422673780522644621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95427528281782520348429747 143141292422673780522644621)
      ·
        refine ⟨53677984658502667695991733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143141292422673780522644621 53677984658502667695991733)
        ·
          refine ⟨5032311061734625096499225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53677984658502667695991733 5032311061734625096499225)
          ·
            refine ⟨3774233296300968822374419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5032311061734625096499225 3774233296300968822374419)
            ·
              refine ⟨5661349944451453233561629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774233296300968822374419 5661349944451453233561629)
              ·
                refine ⟨2123006229169294962585611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5661349944451453233561629 2123006229169294962585611)
                ·
                  refine ⟨3184509343753942443878417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2123006229169294962585611 3184509343753942443878417)
                  ·
                    refine ⟨2388382007815456832908813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3184509343753942443878417 2388382007815456832908813)
                    ·
                      refine ⟨895643252930796312340805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2388382007815456832908813 895643252930796312340805)
                      ·
                        rfl

theorem cell23_1744259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_1744259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744259 prefixEnd_1744259 := by exact prefixLift 1744259
  have htrace : WordTrace (prefixWord ++ tailWord_1744259) baseStart_1744259 baseEnd_1744259 := by
    simpa [prefixWord, tailWord_1744259, baseEnd_1744259] using wordTrace_append hprefix tailTrace_1744259
  have hstable : (prefixWord ++ tailWord_1744259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744259).length < 2 ^ (prefixWord ++ tailWord_1744259).sum := by decide
  have hdescent : baseEnd_1744259 < baseStart_1744259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744296 : List Nat := [2, 1, 6, 1, 2, 2, 2, 7]
def baseStart_1744296 : Nat := 118140960795 + 1744296 * 2 ^ 59
def prefixEnd_1744296 : Nat := 4983230072969 + 3 ^ 40 * 1744296 * 2
def baseEnd_1744296 : Nat := 33172675989444913614005

theorem tailTrace_1744296 : CollatzResearch.WordTrace tailWord_1744296 prefixEnd_1744296 33172675989444913614005 := by
  unfold tailWord_1744296
  simp only [CollatzResearch.WordTrace]
  refine ⟨31809850844360484442358371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42413134459147312589811161 31809850844360484442358371)
  ·
    refine ⟨47714776266540726663537557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31809850844360484442358371 47714776266540726663537557)
    ·
      refine ⟨2236630137494096562353323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47714776266540726663537557 2236630137494096562353323)
      ·
        refine ⟨3354945206241144843529985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2236630137494096562353323 3354945206241144843529985)
        ·
          refine ⟨2516208904680858632647489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3354945206241144843529985 2516208904680858632647489)
          ·
            refine ⟨1887156678510643974485617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2516208904680858632647489 1887156678510643974485617)
            ·
              refine ⟨1415367508882982980864213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887156678510643974485617 1415367508882982980864213)
              ·
                refine ⟨33172675989444913614005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1415367508882982980864213 33172675989444913614005)
                ·
                  rfl

theorem cell23_1744296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 7].length) (baseStart_1744296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744296 prefixEnd_1744296 := by exact prefixLift 1744296
  have htrace : WordTrace (prefixWord ++ tailWord_1744296) baseStart_1744296 baseEnd_1744296 := by
    simpa [prefixWord, tailWord_1744296, baseEnd_1744296] using wordTrace_append hprefix tailTrace_1744296
  have hstable : (prefixWord ++ tailWord_1744296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744296).length < 2 ^ (prefixWord ++ tailWord_1744296).sum := by decide
  have hdescent : baseEnd_1744296 < baseStart_1744296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744340 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_1744340 : Nat := 118140960795 + 1744340 * 2 ^ 59
def prefixEnd_1744340 : Nat := 4983230072969 + 3 ^ 40 * 1744340 * 2
def baseEnd_1744340 : Nat := 895684844863810495427933

theorem tailTrace_1744340 : CollatzResearch.WordTrace tailWord_1744340 prefixEnd_1744340 895684844863810495427933 := by
  unfold tailWord_1744340
  simp only [CollatzResearch.WordTrace]
  refine ⟨31810653250280782199659237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42414204333707709599545649 31810653250280782199659237)
  ·
    refine ⟨5964497484427646662436107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31810653250280782199659237 5964497484427646662436107)
    ·
      refine ⟨8946746226641469993654161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5964497484427646662436107 8946746226641469993654161)
      ·
        refine ⟨6710059669981102495240621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8946746226641469993654161 6710059669981102495240621)
        ·
          refine ⟨2516272376242913435715233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6710059669981102495240621 2516272376242913435715233)
          ·
            refine ⟨1887204282182185076786425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2516272376242913435715233 1887204282182185076786425)
            ·
              refine ⟨1415403211636638807589819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887204282182185076786425 1415403211636638807589819)
              ·
                refine ⟨2123104817454958211384729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1415403211636638807589819 2123104817454958211384729)
                ·
                  refine ⟨1592328613091218658538547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2123104817454958211384729 1592328613091218658538547)
                  ·
                    refine ⟨2388492919636827987807821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1592328613091218658538547 2388492919636827987807821)
                    ·
                      refine ⟨895684844863810495427933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2388492919636827987807821 895684844863810495427933)
                      ·
                        rfl

theorem cell23_1744340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_1744340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744340 prefixEnd_1744340 := by exact prefixLift 1744340
  have htrace : WordTrace (prefixWord ++ tailWord_1744340) baseStart_1744340 baseEnd_1744340 := by
    simpa [prefixWord, tailWord_1744340, baseEnd_1744340] using wordTrace_append hprefix tailTrace_1744340
  have hstable : (prefixWord ++ tailWord_1744340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744340).length < 2 ^ (prefixWord ++ tailWord_1744340).sum := by decide
  have hdescent : baseEnd_1744340 < baseStart_1744340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744392 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1744392 : Nat := 118140960795 + 1744392 * 2 ^ 59
def prefixEnd_1744392 : Nat := 4983230072969 + 3 ^ 40 * 1744392 * 2
def baseEnd_1744392 : Nat := 895711545857844291977693

theorem tailTrace_1744392 : CollatzResearch.WordTrace tailWord_1744392 prefixEnd_1744392 895711545857844291977693 := by
  unfold tailWord_1744392
  simp only [CollatzResearch.WordTrace]
  refine ⟨31811601548186588640105715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42415468730915451520140953 31811601548186588640105715)
  ·
    refine ⟨47717402322279882960158573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31811601548186588640105715 47717402322279882960158573)
    ·
      refine ⟨17894025870854956110059465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47717402322279882960158573 17894025870854956110059465)
      ·
        refine ⟨13420519403141217082544599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17894025870854956110059465 13420519403141217082544599)
        ·
          refine ⟨20130779104711825623816899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13420519403141217082544599 20130779104711825623816899)
          ·
            refine ⟨30196168657067738435725349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20130779104711825623816899 30196168657067738435725349)
            ·
              refine ⟨5661781623200200956698503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30196168657067738435725349 5661781623200200956698503)
              ·
                refine ⟨8492672434800301435047755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661781623200200956698503 8492672434800301435047755)
                ·
                  refine ⟨12739008652200452152571633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8492672434800301435047755 12739008652200452152571633)
                  ·
                    refine ⟨9554256489150339114428725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12739008652200452152571633 9554256489150339114428725)
                    ·
                      refine ⟨895711545857844291977693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9554256489150339114428725 895711545857844291977693)
                      ·
                        rfl

theorem cell23_1744392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1744392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744392 prefixEnd_1744392 := by exact prefixLift 1744392
  have htrace : WordTrace (prefixWord ++ tailWord_1744392) baseStart_1744392 baseEnd_1744392 := by
    simpa [prefixWord, tailWord_1744392, baseEnd_1744392] using wordTrace_append hprefix tailTrace_1744392
  have hstable : (prefixWord ++ tailWord_1744392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744392).length < 2 ^ (prefixWord ++ tailWord_1744392).sum := by decide
  have hdescent : baseEnd_1744392 < baseStart_1744392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744416 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 2, 5]
def baseStart_1744416 : Nat := 118140960795 + 1744416 * 2 ^ 59
def prefixEnd_1744416 : Nat := 4983230072969 + 3 ^ 40 * 1744416 * 2
def baseEnd_1744416 : Nat := 298574623131184066025861

theorem tailTrace_1744416 : CollatzResearch.WordTrace tailWord_1744416 prefixEnd_1744416 298574623131184066025861 := by
  unfold tailWord_1744416
  simp only [CollatzResearch.WordTrace]
  refine ⟨31812039224143114689542551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42416052298857486252723401 31812039224143114689542551)
  ·
    refine ⟨47718058836214672034313827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31812039224143114689542551 47718058836214672034313827)
    ·
      refine ⟨71577088254322008051470741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47718058836214672034313827 71577088254322008051470741)
      ·
        refine ⟨3355176011921344127412691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71577088254322008051470741 3355176011921344127412691)
        ·
          refine ⟨5032764017882016191119037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3355176011921344127412691 5032764017882016191119037)
          ·
            refine ⟨1887286506705756071669639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5032764017882016191119037 1887286506705756071669639)
            ·
              refine ⟨2830929760058634107504459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887286506705756071669639 2830929760058634107504459)
              ·
                refine ⟨4246394640087951161256689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830929760058634107504459 4246394640087951161256689)
                ·
                  refine ⟨3184795980065963370942517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4246394640087951161256689 3184795980065963370942517)
                  ·
                    refine ⟨298574623131184066025861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3184795980065963370942517 298574623131184066025861)
                    ·
                      rfl

theorem cell23_1744416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 5].length) (baseStart_1744416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744416 prefixEnd_1744416 := by exact prefixLift 1744416
  have htrace : WordTrace (prefixWord ++ tailWord_1744416) baseStart_1744416 baseEnd_1744416 := by
    simpa [prefixWord, tailWord_1744416, baseEnd_1744416] using wordTrace_append hprefix tailTrace_1744416
  have hstable : (prefixWord ++ tailWord_1744416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744416).length < 2 ^ (prefixWord ++ tailWord_1744416).sum := by decide
  have hdescent : baseEnd_1744416 < baseStart_1744416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744419 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 4]
def baseStart_1744419 : Nat := 118140960795 + 1744419 * 2 ^ 59
def prefixEnd_1744419 : Nat := 4983230072969 + 3 ^ 40 * 1744419 * 2
def baseEnd_1744419 : Nat := 895725409835515686340069

theorem tailTrace_1744419 : CollatzResearch.WordTrace tailWord_1744419 prefixEnd_1744419 895725409835515686340069 := by
  unfold tailWord_1744419
  simp only [CollatzResearch.WordTrace]
  refine ⟨63624187867275360891444311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42416125244850240594296207 63624187867275360891444311)
  ·
    refine ⟨95436281800913041337166467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63624187867275360891444311 95436281800913041337166467)
    ·
      refine ⟨143154422701369562005749701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95436281800913041337166467 143154422701369562005749701)
      ·
        refine ⟨26841454256506792876078069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143154422701369562005749701 26841454256506792876078069)
        ·
          refine ⟨2516386336547511832132319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26841454256506792876078069 2516386336547511832132319)
          ·
            refine ⟨3774579504821267748198479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516386336547511832132319 3774579504821267748198479)
            ·
              refine ⟨5661869257231901622297719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774579504821267748198479 5661869257231901622297719)
              ·
                refine ⟨8492803885847852433446579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661869257231901622297719 8492803885847852433446579)
                ·
                  refine ⟨12739205828771778650169869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8492803885847852433446579 12739205828771778650169869)
                  ·
                    refine ⟨4777202185789416993813701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12739205828771778650169869 4777202185789416993813701)
                    ·
                      refine ⟨895725409835515686340069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4777202185789416993813701 895725409835515686340069)
                      ·
                        rfl

theorem cell23_1744419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_1744419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744419 prefixEnd_1744419 := by exact prefixLift 1744419
  have htrace : WordTrace (prefixWord ++ tailWord_1744419) baseStart_1744419 baseEnd_1744419 := by
    simpa [prefixWord, tailWord_1744419, baseEnd_1744419] using wordTrace_append hprefix tailTrace_1744419
  have hstable : (prefixWord ++ tailWord_1744419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744419).length < 2 ^ (prefixWord ++ tailWord_1744419).sum := by decide
  have hdescent : baseEnd_1744419 < baseStart_1744419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744442 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 8]
def baseStart_1744442 : Nat := 118140960795 + 1744442 * 2 ^ 59
def prefixEnd_1744442 : Nat := 4983230072969 + 3 ^ 40 * 1744442 * 2
def baseEnd_1744442 : Nat := 99526357765618788483607

theorem tailTrace_1744442 : CollatzResearch.WordTrace tailWord_1744442 prefixEnd_1744442 99526357765618788483607 := by
  unfold tailWord_1744442
  simp only [CollatzResearch.WordTrace]
  refine ⟨15906256686548008954882895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42416684497461357213021053 15906256686548008954882895)
  ·
    refine ⟨23859385029822013432324343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15906256686548008954882895 23859385029822013432324343)
    ·
      refine ⟨35789077544733020148486515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23859385029822013432324343 35789077544733020148486515)
      ·
        refine ⟨53683616317099530222729773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35789077544733020148486515 53683616317099530222729773)
        ·
          refine ⟨20131356118912323833523665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53683616317099530222729773 20131356118912323833523665)
          ·
            refine ⟨15098517089184242875142749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20131356118912323833523665 15098517089184242875142749)
            ·
              refine ⟨5661943908444091078178531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15098517089184242875142749 5661943908444091078178531)
              ·
                refine ⟨8492915862666136617267797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661943908444091078178531 8492915862666136617267797)
                ·
                  refine ⟨99526357765618788483607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8492915862666136617267797 99526357765618788483607)
                  ·
                    rfl

theorem cell23_1744442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_1744442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744442 prefixEnd_1744442 := by exact prefixLift 1744442
  have htrace : WordTrace (prefixWord ++ tailWord_1744442) baseStart_1744442 baseEnd_1744442 := by
    simpa [prefixWord, tailWord_1744442, baseEnd_1744442] using wordTrace_append hprefix tailTrace_1744442
  have hstable : (prefixWord ++ tailWord_1744442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744442).length < 2 ^ (prefixWord ++ tailWord_1744442).sum := by decide
  have hdescent : baseEnd_1744442 < baseStart_1744442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744462 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1744462 : Nat := 118140960795 + 1744462 * 2 ^ 59
def prefixEnd_1744462 : Nat := 4983230072969 + 3 ^ 40 * 1744462 * 2
def baseEnd_1744462 : Nat := 895747489503659018102371

theorem tailTrace_1744462 : CollatzResearch.WordTrace tailWord_1744462 prefixEnd_1744462 895747489503659018102371 := by
  unfold tailWord_1744462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7953219525764947404407455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42417170804079719490173093 7953219525764947404407455)
  ·
    refine ⟨11929829288647421106611183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7953219525764947404407455 11929829288647421106611183)
    ·
      refine ⟨17894743932971131659916775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11929829288647421106611183 17894743932971131659916775)
      ·
        refine ⟨26842115899456697489875163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17894743932971131659916775 26842115899456697489875163)
        ·
          refine ⟨40263173849185046234812745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26842115899456697489875163 40263173849185046234812745)
          ·
            refine ⟨30197380386888784676109559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40263173849185046234812745 30197380386888784676109559)
            ·
              refine ⟨45296070580333177014164339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30197380386888784676109559 45296070580333177014164339)
              ·
                refine ⟨67944105870499765521246509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45296070580333177014164339 67944105870499765521246509)
                ·
                  refine ⟨25479039701437412070467441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67944105870499765521246509 25479039701437412070467441)
                  ·
                    refine ⟨19109279776078059052850581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25479039701437412070467441 19109279776078059052850581)
                    ·
                      refine ⟨895747489503659018102371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19109279776078059052850581 895747489503659018102371)
                      ·
                        rfl

theorem cell23_1744462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1744462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744462 prefixEnd_1744462 := by exact prefixLift 1744462
  have htrace : WordTrace (prefixWord ++ tailWord_1744462) baseStart_1744462 baseEnd_1744462 := by
    simpa [prefixWord, tailWord_1744462, baseEnd_1744462] using wordTrace_append hprefix tailTrace_1744462
  have hstable : (prefixWord ++ tailWord_1744462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744462).length < 2 ^ (prefixWord ++ tailWord_1744462).sum := by decide
  have hdescent : baseEnd_1744462 < baseStart_1744462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744489 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 1, 5]
def baseStart_1744489 : Nat := 118140960795 + 1744489 * 2 ^ 59
def prefixEnd_1744489 : Nat := 4983230072969 + 3 ^ 40 * 1744489 * 2
def baseEnd_1744489 : Nat := 298587117827110137488249

theorem tailTrace_1744489 : CollatzResearch.WordTrace tailWord_1744489 prefixEnd_1744489 298587117827110137488249 := by
  unfold tailWord_1744489
  simp only [CollatzResearch.WordTrace]
  refine ⟨63626740977021762846492521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42417827318014508564328347 63626740977021762846492521)
  ·
    refine ⟨47720055732766322134869391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63626740977021762846492521 47720055732766322134869391)
    ·
      refine ⟨71580083599149483202304087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47720055732766322134869391 71580083599149483202304087)
      ·
        refine ⟨107370125398724224803456131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71580083599149483202304087 107370125398724224803456131)
        ·
          refine ⟨161055188098086337205184197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107370125398724224803456131 161055188098086337205184197)
          ·
            refine ⟨30197847768391188225972037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161055188098086337205184197 30197847768391188225972037)
            ·
              refine ⟨5662096456573347792369757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30197847768391188225972037 5662096456573347792369757)
              ·
                refine ⟨2123286171215005422138659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5662096456573347792369757 2123286171215005422138659)
                ·
                  refine ⟨3184929256822508133207989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2123286171215005422138659 3184929256822508133207989)
                  ·
                    refine ⟨298587117827110137488249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3184929256822508133207989 298587117827110137488249)
                    ·
                      rfl

theorem cell23_1744489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 5].length) (baseStart_1744489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744489 prefixEnd_1744489 := by exact prefixLift 1744489
  have htrace : WordTrace (prefixWord ++ tailWord_1744489) baseStart_1744489 baseEnd_1744489 := by
    simpa [prefixWord, tailWord_1744489, baseEnd_1744489] using wordTrace_append hprefix tailTrace_1744489
  have hstable : (prefixWord ++ tailWord_1744489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744489).length < 2 ^ (prefixWord ++ tailWord_1744489).sum := by decide
  have hdescent : baseEnd_1744489 < baseStart_1744489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744496 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 4, 3, 2]
def baseStart_1744496 : Nat := 118140960795 + 1744496 * 2 ^ 59
def prefixEnd_1744496 : Nat := 4983230072969 + 3 ^ 40 * 1744496 * 2
def baseEnd_1744496 : Nat := 895764947845911885077215

theorem tailTrace_1744496 : CollatzResearch.WordTrace tailWord_1744496 prefixEnd_1744496 895764947845911885077215 := by
  unfold tailWord_1744496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31813498143998201520998671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42417997525330935361331561 31813498143998201520998671)
  ·
    refine ⟨47720247215997302281498007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31813498143998201520998671 47720247215997302281498007)
    ·
      refine ⟨71580370823995953422247011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47720247215997302281498007 71580370823995953422247011)
      ·
        refine ⟨107370556235993930133370517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71580370823995953422247011 107370556235993930133370517)
        ·
          refine ⟨5032994823562215475001743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107370556235993930133370517 5032994823562215475001743)
          ·
            refine ⟨7549492235343323212502615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5032994823562215475001743 7549492235343323212502615)
            ·
              refine ⟨11324238353014984818753923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7549492235343323212502615 11324238353014984818753923)
              ·
                refine ⟨16986357529522477228130885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11324238353014984818753923 16986357529522477228130885)
                ·
                  refine ⟨3184942036785464480274541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16986357529522477228130885 3184942036785464480274541)
                  ·
                    refine ⟨1194353263794549180102953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3184942036785464480274541 1194353263794549180102953)
                    ·
                      refine ⟨895764947845911885077215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1194353263794549180102953 895764947845911885077215)
                      ·
                        rfl

theorem cell23_1744496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 3, 2].length) (baseStart_1744496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744496 prefixEnd_1744496 := by exact prefixLift 1744496
  have htrace : WordTrace (prefixWord ++ tailWord_1744496) baseStart_1744496 baseEnd_1744496 := by
    simpa [prefixWord, tailWord_1744496, baseEnd_1744496] using wordTrace_append hprefix tailTrace_1744496
  have hstable : (prefixWord ++ tailWord_1744496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744496).length < 2 ^ (prefixWord ++ tailWord_1744496).sum := by decide
  have hdescent : baseEnd_1744496 < baseStart_1744496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744526 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1744526 : Nat := 118140960795 + 1744526 * 2 ^ 59
def prefixEnd_1744526 : Nat := 4983230072969 + 3 ^ 40 * 1744526 * 2
def baseEnd_1744526 : Nat := 895780352265546767702077

theorem tailTrace_1744526 : CollatzResearch.WordTrace tailWord_1744526 prefixEnd_1744526 895780352265546767702077 := by
  unfold tailWord_1744526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7953511309735964770698679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42418726985258478777059621 7953511309735964770698679)
  ·
    refine ⟨11930266964603947156048019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7953511309735964770698679 11930266964603947156048019)
    ·
      refine ⟨17895400446905920734072029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11930266964603947156048019 17895400446905920734072029)
      ·
        refine ⟨6710775167589720275277011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17895400446905920734072029 6710775167589720275277011)
        ·
          refine ⟨10066162751384580412915517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710775167589720275277011 10066162751384580412915517)
          ·
            refine ⟨3774811031769217654843319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10066162751384580412915517 3774811031769217654843319)
            ·
              refine ⟨5662216547653826482264979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774811031769217654843319 5662216547653826482264979)
              ·
                refine ⟨8493324821480739723397469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5662216547653826482264979 8493324821480739723397469)
                ·
                  refine ⟨3184996808055277396274051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8493324821480739723397469 3184996808055277396274051)
                  ·
                    refine ⟨4777495212082916094411077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3184996808055277396274051 4777495212082916094411077)
                    ·
                      refine ⟨895780352265546767702077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4777495212082916094411077 895780352265546767702077)
                      ·
                        rfl

theorem cell23_1744526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1744526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744526 prefixEnd_1744526 := by exact prefixLift 1744526
  have htrace : WordTrace (prefixWord ++ tailWord_1744526) baseStart_1744526 baseEnd_1744526 := by
    simpa [prefixWord, tailWord_1744526, baseEnd_1744526] using wordTrace_append hprefix tailTrace_1744526
  have hstable : (prefixWord ++ tailWord_1744526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744526).length < 2 ^ (prefixWord ++ tailWord_1744526).sum := by decide
  have hdescent : baseEnd_1744526 < baseStart_1744526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744530 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_1744530 : Nat := 118140960795 + 1744530 * 2 ^ 59
def prefixEnd_1744530 : Nat := 4983230072969 + 3 ^ 40 * 1744530 * 2
def baseEnd_1744530 : Nat := 895782406188164752052059

theorem tailTrace_1744530 : CollatzResearch.WordTrace tailWord_1744530 prefixEnd_1744530 895782406188164752052059 := by
  unfold tailWord_1744530
  simp only [CollatzResearch.WordTrace]
  refine ⟨15907059092468306712183761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42418824246582151232490029 15907059092468306712183761)
  ·
    refine ⟨11930294319351230034137821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15907059092468306712183761 11930294319351230034137821)
    ·
      refine ⟨4473860369756711262801683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11930294319351230034137821 4473860369756711262801683)
      ·
        refine ⟨6710790554635066894202525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473860369756711262801683 6710790554635066894202525)
        ·
          refine ⟨2516546457988150085325947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6710790554635066894202525 2516546457988150085325947)
          ·
            refine ⟨3774819686982225127988921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516546457988150085325947 3774819686982225127988921)
            ·
              refine ⟨2831114765236668845991691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3774819686982225127988921 2831114765236668845991691)
              ·
                refine ⟨4246672147855003268987537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831114765236668845991691 4246672147855003268987537)
                ·
                  refine ⟨3185004110891252451740653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4246672147855003268987537 3185004110891252451740653)
                  ·
                    refine ⟨1194376541584219669402745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3185004110891252451740653 1194376541584219669402745)
                    ·
                      refine ⟨895782406188164752052059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1194376541584219669402745 895782406188164752052059)
                      ·
                        rfl

theorem cell23_1744530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_1744530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1744530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1744530 prefixEnd_1744530 := by exact prefixLift 1744530
  have htrace : WordTrace (prefixWord ++ tailWord_1744530) baseStart_1744530 baseEnd_1744530 := by
    simpa [prefixWord, tailWord_1744530, baseEnd_1744530] using wordTrace_append hprefix tailTrace_1744530
  have hstable : (prefixWord ++ tailWord_1744530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744530).length < 2 ^ (prefixWord ++ tailWord_1744530).sum := by decide
  have hdescent : baseEnd_1744530 < baseStart_1744530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
