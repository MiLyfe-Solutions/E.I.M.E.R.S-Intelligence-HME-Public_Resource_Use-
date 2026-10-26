import V185TrunkScan20Chunk057

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_352342 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_352342 : Nat := 118140960795 + 352342 * 2 ^ 59
def prefixEnd_352342 : Nat := 4983230072969 + 3 ^ 40 * 352342 * 2
def baseEnd_352342 : Nat := 160818489570280616892991

theorem tailTrace_352342 : CollatzResearch.WordTrace tailWord_352342 prefixEnd_352342 160818489570280616892991 := by
  unfold tailWord_352342
  simp only [CollatzResearch.WordTrace]
  refine ⟨803185530595786504244705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8567312326355056045276853 803185530595786504244705)
  ·
    refine ⟨602389147946839878183529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 803185530595786504244705 602389147946839878183529)
    ·
      refine ⟨451791860960129908637647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 602389147946839878183529 451791860960129908637647)
      ·
        refine ⟨677687791440194862956471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451791860960129908637647 677687791440194862956471)
        ·
          refine ⟨1016531687160292294434707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677687791440194862956471 1016531687160292294434707)
          ·
            refine ⟨1524797530740438441652061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016531687160292294434707 1524797530740438441652061)
            ·
              refine ⟨571799074027664415619523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1524797530740438441652061 571799074027664415619523)
              ·
                refine ⟨857698611041496623429285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571799074027664415619523 857698611041496623429285)
                ·
                  refine ⟨160818489570280616892991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 857698611041496623429285 160818489570280616892991)
                  ·
                    rfl

theorem cell20_352342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_352342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352342 prefixEnd_352342 := by exact prefixLift 352342
  have htrace : WordTrace (prefixWord ++ tailWord_352342) baseStart_352342 baseEnd_352342 := by
    simpa [prefixWord, tailWord_352342, baseEnd_352342] using wordTrace_append hprefix tailTrace_352342
  have hstable : (prefixWord ++ tailWord_352342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352342).length < 2 ^ (prefixWord ++ tailWord_352342).sum := by decide
  have hdescent : baseEnd_352342 < baseStart_352342 := by decide
  rcases family_descends (prefixWord ++ tailWord_352342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352384 : List Nat := [2, 1, 1, 2, 1, 3, 1, 7, 2]
def baseStart_352384 : Nat := 118140960795 + 352384 * 2 ^ 59
def prefixEnd_352384 : Nat := 4983230072969 + 3 ^ 40 * 352384 * 2
def baseEnd_352384 : Nat := 160837659514715137492819

theorem tailTrace_352384 : CollatzResearch.WordTrace tailWord_352384 prefixEnd_352384 160837659514715137492819 := by
  unfold tailWord_352384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6426250177690212620472103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8568333570253616827296137 6426250177690212620472103)
  ·
    refine ⟨9639375266535318930708155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6426250177690212620472103 9639375266535318930708155)
    ·
      refine ⟨14459062899802978396062233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9639375266535318930708155 14459062899802978396062233)
      ·
        refine ⟨10844297174852233797046675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14459062899802978396062233 10844297174852233797046675)
        ·
          refine ⟨16266445762278350695570013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10844297174852233797046675 16266445762278350695570013)
          ·
            refine ⟨6099917160854381510838755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16266445762278350695570013 6099917160854381510838755)
            ·
              refine ⟨9149875741281572266258133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6099917160854381510838755 9149875741281572266258133)
              ·
                refine ⟨214450212686286849990425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9149875741281572266258133 214450212686286849990425)
                ·
                  refine ⟨160837659514715137492819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214450212686286849990425 160837659514715137492819)
                  ·
                    rfl

theorem cell20_352384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_352384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352384 prefixEnd_352384 := by exact prefixLift 352384
  have htrace : WordTrace (prefixWord ++ tailWord_352384) baseStart_352384 baseEnd_352384 := by
    simpa [prefixWord, tailWord_352384, baseEnd_352384] using wordTrace_append hprefix tailTrace_352384
  have hstable : (prefixWord ++ tailWord_352384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352384).length < 2 ^ (prefixWord ++ tailWord_352384).sum := by decide
  have hdescent : baseEnd_352384 < baseStart_352384 := by decide
  rcases family_descends (prefixWord ++ tailWord_352384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352404 : List Nat := [2, 4, 2, 3, 2, 1, 1, 5]
def baseStart_352404 : Nat := 118140960795 + 352404 * 2 ^ 59
def prefixEnd_352404 : Nat := 4983230072969 + 3 ^ 40 * 352404 * 2
def baseEnd_352404 : Nat := 53615596019894652275357

theorem tailTrace_352404 : CollatzResearch.WordTrace tailWord_352404 prefixEnd_352404 53615596019894652275357 := by
  unfold tailWord_352404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6426614907653984328336133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8568819876871979104448177 6426614907653984328336133)
  ·
    refine ⟨1204990295185122061563025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6426614907653984328336133 1204990295185122061563025)
    ·
      refine ⟨903742721388841546172269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1204990295185122061563025 903742721388841546172269)
      ·
        refine ⟨338903520520815579814601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 903742721388841546172269 338903520520815579814601)
        ·
          refine ⟨254177640390611684860951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338903520520815579814601 254177640390611684860951)
          ·
            refine ⟨381266460585917527291427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254177640390611684860951 381266460585917527291427)
            ·
              refine ⟨571899690878876290937141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381266460585917527291427 571899690878876290937141)
              ·
                refine ⟨53615596019894652275357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 571899690878876290937141 53615596019894652275357)
                ·
                  rfl

theorem cell20_352404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_352404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352404 prefixEnd_352404 := by exact prefixLift 352404
  have htrace : WordTrace (prefixWord ++ tailWord_352404) baseStart_352404 baseEnd_352404 := by
    simpa [prefixWord, tailWord_352404, baseEnd_352404] using wordTrace_append hprefix tailTrace_352404
  have hstable : (prefixWord ++ tailWord_352404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352404).length < 2 ^ (prefixWord ++ tailWord_352404).sum := by decide
  have hdescent : baseEnd_352404 < baseStart_352404 := by decide
  rcases family_descends (prefixWord ++ tailWord_352404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352405 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_352405 : Nat := 118140960795 + 352405 * 2 ^ 59
def prefixEnd_352405 : Nat := 4983230072969 + 3 ^ 40 * 352405 * 2
def baseEnd_352405 : Nat := 160847244486932397792733

theorem tailTrace_352405 : CollatzResearch.WordTrace tailWord_352405 prefixEnd_352405 160847244486932397792733 := by
  unfold tailWord_352405
  simp only [CollatzResearch.WordTrace]
  refine ⟨12853266288304345827458669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8568844192202897218305779 12853266288304345827458669)
  ·
    refine ⟨4819974858114129685297001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12853266288304345827458669 4819974858114129685297001)
    ·
      refine ⟨3614981143585597263972751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4819974858114129685297001 3614981143585597263972751)
      ·
        refine ⟨5422471715378395895959127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3614981143585597263972751 5422471715378395895959127)
        ·
          refine ⟨8133707573067593843938691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422471715378395895959127 8133707573067593843938691)
          ·
            refine ⟨12200561359601390765908037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8133707573067593843938691 12200561359601390765908037)
            ·
              refine ⟨2287605254925260768607757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12200561359601390765908037 2287605254925260768607757)
              ·
                refine ⟨857851970596972788227909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2287605254925260768607757 857851970596972788227909)
                ·
                  refine ⟨160847244486932397792733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 857851970596972788227909 160847244486932397792733)
                  ·
                    rfl

theorem cell20_352405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_352405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352405 prefixEnd_352405 := by exact prefixLift 352405
  have htrace : WordTrace (prefixWord ++ tailWord_352405) baseStart_352405 baseEnd_352405 := by
    simpa [prefixWord, tailWord_352405, baseEnd_352405] using wordTrace_append hprefix tailTrace_352405
  have hstable : (prefixWord ++ tailWord_352405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352405).length < 2 ^ (prefixWord ++ tailWord_352405).sum := by decide
  have hdescent : baseEnd_352405 < baseStart_352405 := by decide
  rcases family_descends (prefixWord ++ tailWord_352405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352408 : List Nat := [2, 1, 2, 4, 3, 2, 1, 5]
def baseStart_352408 : Nat := 118140960795 + 352408 * 2 ^ 59
def prefixEnd_352408 : Nat := 4983230072969 + 3 ^ 40 * 352408 * 2
def baseEnd_352408 : Nat := 53616204589559240230907

theorem tailTrace_352408 : CollatzResearch.WordTrace tailWord_352408 prefixEnd_352408 53616204589559240230907 := by
  unfold tailWord_352408
  simp only [CollatzResearch.WordTrace]
  refine ⟨6426687853646738669908939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8568917138195651559878585 6426687853646738669908939)
  ·
    refine ⟨9640031780470108004863409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6426687853646738669908939 9640031780470108004863409)
    ·
      refine ⟨7230023835352581003647557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9640031780470108004863409 7230023835352581003647557)
      ·
        refine ⟨1355629469128608938183917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7230023835352581003647557 1355629469128608938183917)
        ·
          refine ⟨508361050923228351818969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1355629469128608938183917 508361050923228351818969)
          ·
            refine ⟨381270788192421263864227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508361050923228351818969 381270788192421263864227)
            ·
              refine ⟨571906182288631895796341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381270788192421263864227 571906182288631895796341)
              ·
                refine ⟨53616204589559240230907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 571906182288631895796341 53616204589559240230907)
                ·
                  rfl

theorem cell20_352408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_352408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352408 prefixEnd_352408 := by exact prefixLift 352408
  have htrace : WordTrace (prefixWord ++ tailWord_352408) baseStart_352408 baseEnd_352408 := by
    simpa [prefixWord, tailWord_352408, baseEnd_352408] using wordTrace_append hprefix tailTrace_352408
  have hstable : (prefixWord ++ tailWord_352408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352408).length < 2 ^ (prefixWord ++ tailWord_352408).sum := by decide
  have hdescent : baseEnd_352408 < baseStart_352408 := by decide
  rcases family_descends (prefixWord ++ tailWord_352408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352415 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 3]
def baseStart_352415 : Nat := 118140960795 + 352415 * 2 ^ 59
def prefixEnd_352415 : Nat := 4983230072969 + 3 ^ 40 * 352415 * 2
def baseEnd_352415 : Nat := 160851808759416807459359

theorem tailTrace_352415 : CollatzResearch.WordTrace tailWord_352415 prefixEnd_352415 160851808759416807459359 := by
  unfold tailWord_352415
  simp only [CollatzResearch.WordTrace]
  refine ⟨12853631018268117535322699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8569087345512078356881799 12853631018268117535322699)
  ·
    refine ⟨19280446527402176302984049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12853631018268117535322699 19280446527402176302984049)
    ·
      refine ⟨14460334895551632227238037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19280446527402176302984049 14460334895551632227238037)
      ·
        refine ⟨677828198228982760651783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14460334895551632227238037 677828198228982760651783)
        ·
          refine ⟨1016742297343474140977675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677828198228982760651783 1016742297343474140977675)
          ·
            refine ⟨1525113446015211211466513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016742297343474140977675 1525113446015211211466513)
            ·
              refine ⟨1143835084511408408599885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1525113446015211211466513 1143835084511408408599885)
              ·
                refine ⟨428938156691778153224957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1143835084511408408599885 428938156691778153224957)
                ·
                  refine ⟨160851808759416807459359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428938156691778153224957 160851808759416807459359)
                  ·
                    rfl

theorem cell20_352415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 3].length) (baseStart_352415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352415 prefixEnd_352415 := by exact prefixLift 352415
  have htrace : WordTrace (prefixWord ++ tailWord_352415) baseStart_352415 baseEnd_352415 := by
    simpa [prefixWord, tailWord_352415, baseEnd_352415] using wordTrace_append hprefix tailTrace_352415
  have hstable : (prefixWord ++ tailWord_352415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352415).length < 2 ^ (prefixWord ++ tailWord_352415).sum := by decide
  have hdescent : baseEnd_352415 < baseStart_352415 := by decide
  rcases family_descends (prefixWord ++ tailWord_352415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352419 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_352419 : Nat := 118140960795 + 352419 * 2 ^ 59
def prefixEnd_352419 : Nat := 4983230072969 + 3 ^ 40 * 352419 * 2
def baseEnd_352419 : Nat := 160853634468410571326009

theorem tailTrace_352419 : CollatzResearch.WordTrace tailWord_352419 prefixEnd_352419 160853634468410571326009 := by
  unfold tailWord_352419
  simp only [CollatzResearch.WordTrace]
  refine ⟨12853776910253626218468311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8569184606835750812312207 12853776910253626218468311)
  ·
    refine ⟨19280665365380439327702467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12853776910253626218468311 19280665365380439327702467)
    ·
      refine ⟨28920998048070658991553701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19280665365380439327702467 28920998048070658991553701)
      ·
        refine ⟨5422687134013248560916319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28920998048070658991553701 5422687134013248560916319)
        ·
          refine ⟨8134030701019872841374479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422687134013248560916319 8134030701019872841374479)
          ·
            refine ⟨12201046051529809262061719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8134030701019872841374479 12201046051529809262061719)
            ·
              refine ⟨18301569077294713893092579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12201046051529809262061719 18301569077294713893092579)
              ·
                refine ⟨27452353615942070839638869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18301569077294713893092579 27452353615942070839638869)
                ·
                  refine ⟨160853634468410571326009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27452353615942070839638869 160853634468410571326009)
                  ·
                    rfl

theorem cell20_352419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_352419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352419 prefixEnd_352419 := by exact prefixLift 352419
  have htrace : WordTrace (prefixWord ++ tailWord_352419) baseStart_352419 baseEnd_352419 := by
    simpa [prefixWord, tailWord_352419, baseEnd_352419] using wordTrace_append hprefix tailTrace_352419
  have hstable : (prefixWord ++ tailWord_352419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352419).length < 2 ^ (prefixWord ++ tailWord_352419).sum := by decide
  have hdescent : baseEnd_352419 < baseStart_352419 := by decide
  rcases family_descends (prefixWord ++ tailWord_352419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352439 : List Nat := [1, 1, 3, 1, 4, 3, 2, 3, 2]
def baseStart_352439 : Nat := 118140960795 + 352439 * 2 ^ 59
def prefixEnd_352439 : Nat := 4983230072969 + 3 ^ 40 * 352439 * 2
def baseEnd_352439 : Nat := 160862763013379390659261

theorem tailTrace_352439 : CollatzResearch.WordTrace tailWord_352439 prefixEnd_352439 160862763013379390659261 := by
  unfold tailWord_352439
  simp only [CollatzResearch.WordTrace]
  refine ⟨12854506370181169634196371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8569670913454113089464247 12854506370181169634196371)
  ·
    refine ⟨19281759555271754451294557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12854506370181169634196371 19281759555271754451294557)
    ·
      refine ⟨7230659833226907919235459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19281759555271754451294557 7230659833226907919235459)
      ·
        refine ⟨10845989749840361878853189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7230659833226907919235459 10845989749840361878853189)
        ·
          refine ⟨2033623078095067852284973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10845989749840361878853189 2033623078095067852284973)
          ·
            refine ⟨762608654285650444606865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2033623078095067852284973 762608654285650444606865)
            ·
              refine ⟨571956490714237833455149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762608654285650444606865 571956490714237833455149)
              ·
                refine ⟨214483684017839187545681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 571956490714237833455149 214483684017839187545681)
                ·
                  refine ⟨160862763013379390659261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214483684017839187545681 160862763013379390659261)
                  ·
                    rfl

theorem cell20_352439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 2].length) (baseStart_352439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352439 prefixEnd_352439 := by exact prefixLift 352439
  have htrace : WordTrace (prefixWord ++ tailWord_352439) baseStart_352439 baseEnd_352439 := by
    simpa [prefixWord, tailWord_352439, baseEnd_352439] using wordTrace_append hprefix tailTrace_352439
  have hstable : (prefixWord ++ tailWord_352439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352439).length < 2 ^ (prefixWord ++ tailWord_352439).sum := by decide
  have hdescent : baseEnd_352439 < baseStart_352439 := by decide
  rcases family_descends (prefixWord ++ tailWord_352439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352449 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 3]
def baseStart_352449 : Nat := 118140960795 + 352449 * 2 ^ 59
def prefixEnd_352449 : Nat := 4983230072969 + 3 ^ 40 * 352449 * 2
def baseEnd_352449 : Nat := 160867327285863800325887

theorem tailTrace_352449 : CollatzResearch.WordTrace tailWord_352449 prefixEnd_352449 160867327285863800325887 := by
  unfold tailWord_352449
  simp only [CollatzResearch.WordTrace]
  refine ⟨12854871100144941342060401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8569914066763294228040267 12854871100144941342060401)
  ·
    refine ⟨9641153325108706006545301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12854871100144941342060401 9641153325108706006545301)
    ·
      refine ⟨451929062114470594056811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9641153325108706006545301 451929062114470594056811)
      ·
        refine ⟨677893593171705891085217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451929062114470594056811 677893593171705891085217)
        ·
          refine ⟨508420194878779418313913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677893593171705891085217 508420194878779418313913)
          ·
            refine ⟨381315146159084563735435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508420194878779418313913 381315146159084563735435)
            ·
              refine ⟨571972719238626845603153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381315146159084563735435 571972719238626845603153)
              ·
                refine ⟨428979539428970134202365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571972719238626845603153 428979539428970134202365)
                ·
                  refine ⟨160867327285863800325887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428979539428970134202365 160867327285863800325887)
                  ·
                    rfl

theorem cell20_352449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_352449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352449 prefixEnd_352449 := by exact prefixLift 352449
  have htrace : WordTrace (prefixWord ++ tailWord_352449) baseStart_352449 baseEnd_352449 := by
    simpa [prefixWord, tailWord_352449, baseEnd_352449] using wordTrace_append hprefix tailTrace_352449
  have hstable : (prefixWord ++ tailWord_352449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352449).length < 2 ^ (prefixWord ++ tailWord_352449).sum := by decide
  have hdescent : baseEnd_352449 < baseStart_352449 := by decide
  rcases family_descends (prefixWord ++ tailWord_352449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352474 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_352474 : Nat := 118140960795 + 352474 * 2 ^ 59
def prefixEnd_352474 : Nat := 4983230072969 + 3 ^ 40 * 352474 * 2
def baseEnd_352474 : Nat := 160878737967074824492451

theorem tailTrace_352474 : CollatzResearch.WordTrace tailWord_352474 prefixEnd_352474 160878737967074824492451 := by
  unfold tailWord_352474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3213945731263592652930119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8570521950036247074480317 3213945731263592652930119)
  ·
    refine ⟨4820918596895388979395179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3213945731263592652930119 4820918596895388979395179)
    ·
      refine ⟨7231377895343083469092769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4820918596895388979395179 7231377895343083469092769)
      ·
        refine ⟨5423533421507312601819577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7231377895343083469092769 5423533421507312601819577)
        ·
          refine ⟨4067650066130484451364683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5423533421507312601819577 4067650066130484451364683)
          ·
            refine ⟨6101475099195726677047025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067650066130484451364683 6101475099195726677047025)
            ·
              refine ⟨4576106324396795007785269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6101475099195726677047025 4576106324396795007785269)
              ·
                refine ⟨429009967912199531979869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4576106324396795007785269 429009967912199531979869)
                ·
                  refine ⟨160878737967074824492451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429009967912199531979869 160878737967074824492451)
                  ·
                    rfl

theorem cell20_352474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_352474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352474 prefixEnd_352474 := by exact prefixLift 352474
  have htrace : WordTrace (prefixWord ++ tailWord_352474) baseStart_352474 baseEnd_352474 := by
    simpa [prefixWord, tailWord_352474, baseEnd_352474] using wordTrace_append hprefix tailTrace_352474
  have hstable : (prefixWord ++ tailWord_352474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352474).length < 2 ^ (prefixWord ++ tailWord_352474).sum := by decide
  have hdescent : baseEnd_352474 < baseStart_352474 := by decide
  rcases family_descends (prefixWord ++ tailWord_352474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352481 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_352481 : Nat := 118140960795 + 352481 * 2 ^ 59
def prefixEnd_352481 : Nat := 4983230072969 + 3 ^ 40 * 352481 * 2
def baseEnd_352481 : Nat := 160881932957813911259089

theorem tailTrace_352481 : CollatzResearch.WordTrace tailWord_352481 prefixEnd_352481 160881932957813911259089 := by
  unfold tailWord_352481
  simp only [CollatzResearch.WordTrace]
  refine ⟨12856038236029010807225297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8570692157352673871483531 12856038236029010807225297)
  ·
    refine ⟨9642028677021758105418973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12856038236029010807225297 9642028677021758105418973)
    ·
      refine ⟨3615760753883159289532115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9642028677021758105418973 3615760753883159289532115)
      ·
        refine ⟨5423641130824738934298173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615760753883159289532115 5423641130824738934298173)
        ·
          refine ⟨2033865424059277100361815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5423641130824738934298173 2033865424059277100361815)
          ·
            refine ⟨3050798136088915650542723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033865424059277100361815 3050798136088915650542723)
            ·
              refine ⟨4576197204133373475814085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050798136088915650542723 4576197204133373475814085)
              ·
                refine ⟨858036975775007526715141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4576197204133373475814085 858036975775007526715141)
                ·
                  refine ⟨160881932957813911259089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 858036975775007526715141 160881932957813911259089)
                  ·
                    rfl

theorem cell20_352481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_352481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352481 prefixEnd_352481 := by exact prefixLift 352481
  have htrace : WordTrace (prefixWord ++ tailWord_352481) baseStart_352481 baseEnd_352481 := by
    simpa [prefixWord, tailWord_352481, baseEnd_352481] using wordTrace_append hprefix tailTrace_352481
  have hstable : (prefixWord ++ tailWord_352481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352481).length < 2 ^ (prefixWord ++ tailWord_352481).sum := by decide
  have hdescent : baseEnd_352481 < baseStart_352481 := by decide
  rcases family_descends (prefixWord ++ tailWord_352481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352515 : List Nat := [1, 1, 1, 3, 2, 3, 5, 2, 2]
def baseStart_352515 : Nat := 118140960795 + 352515 * 2 ^ 59
def prefixEnd_352515 : Nat := 4983230072969 + 3 ^ 40 * 352515 * 2
def baseEnd_352515 : Nat := 160897451484260904125617

theorem tailTrace_352515 : CollatzResearch.WordTrace tailWord_352515 prefixEnd_352515 160897451484260904125617 := by
  unfold tailWord_352515
  simp only [CollatzResearch.WordTrace]
  refine ⟨12857278317905834613962999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8571518878603889742641999 12857278317905834613962999)
  ·
    refine ⟨19285917476858751920944499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12857278317905834613962999 19285917476858751920944499)
    ·
      refine ⟨28928876215288127881416749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19285917476858751920944499 28928876215288127881416749)
      ·
        refine ⟨10848328580733047955531281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28928876215288127881416749 10848328580733047955531281)
        ·
          refine ⟨8136246435549785966648461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10848328580733047955531281 8136246435549785966648461)
          ·
            refine ⟨3051092413331169737493173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8136246435549785966648461 3051092413331169737493173)
            ·
              refine ⟨286039913749797162889985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3051092413331169737493173 286039913749797162889985)
              ·
                refine ⟨214529935312347872167489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286039913749797162889985 214529935312347872167489)
                ·
                  refine ⟨160897451484260904125617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214529935312347872167489 160897451484260904125617)
                  ·
                    rfl

theorem cell20_352515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 2].length) (baseStart_352515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352515 prefixEnd_352515 := by exact prefixLift 352515
  have htrace : WordTrace (prefixWord ++ tailWord_352515) baseStart_352515 baseEnd_352515 := by
    simpa [prefixWord, tailWord_352515, baseEnd_352515] using wordTrace_append hprefix tailTrace_352515
  have hstable : (prefixWord ++ tailWord_352515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352515).length < 2 ^ (prefixWord ++ tailWord_352515).sum := by decide
  have hdescent : baseEnd_352515 < baseStart_352515 := by decide
  rcases family_descends (prefixWord ++ tailWord_352515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352529 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 3]
def baseStart_352529 : Nat := 118140960795 + 352529 * 2 ^ 59
def prefixEnd_352529 : Nat := 4983230072969 + 3 ^ 40 * 352529 * 2
def baseEnd_352529 : Nat := 160903841465739077658893

theorem tailTrace_352529 : CollatzResearch.WordTrace tailWord_352529 prefixEnd_352529 160903841465739077658893 := by
  unfold tailWord_352529
  simp only [CollatzResearch.WordTrace]
  refine ⟨12857788939855115004972641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8571859293236743336648427 12857788939855115004972641)
  ·
    refine ⟨9643341704891336253729481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12857788939855115004972641 9643341704891336253729481)
    ·
      refine ⟨7232506278668502190297111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9643341704891336253729481 7232506278668502190297111)
      ·
        refine ⟨10848759418002753285445667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7232506278668502190297111 10848759418002753285445667)
        ·
          refine ⟨16273139127004129928168501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10848759418002753285445667 16273139127004129928168501)
          ·
            refine ⟨1525606793156637180765797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16273139127004129928168501 1525606793156637180765797)
            ·
              refine ⟨286051273716869471393587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1525606793156637180765797 286051273716869471393587)
              ·
                refine ⟨429076910575304207090381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286051273716869471393587 429076910575304207090381)
                ·
                  refine ⟨160903841465739077658893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429076910575304207090381 160903841465739077658893)
                  ·
                    rfl

theorem cell20_352529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_352529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352529 prefixEnd_352529 := by exact prefixLift 352529
  have htrace : WordTrace (prefixWord ++ tailWord_352529) baseStart_352529 baseEnd_352529 := by
    simpa [prefixWord, tailWord_352529, baseEnd_352529] using wordTrace_append hprefix tailTrace_352529
  have hstable : (prefixWord ++ tailWord_352529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352529).length < 2 ^ (prefixWord ++ tailWord_352529).sum := by decide
  have hdescent : baseEnd_352529 < baseStart_352529 := by decide
  rcases family_descends (prefixWord ++ tailWord_352529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352570 : List Nat := [3, 1, 1, 1, 4, 4, 2, 2, 2]
def baseStart_352570 : Nat := 118140960795 + 352570 * 2 ^ 59
def prefixEnd_352570 : Nat := 4983230072969 + 3 ^ 40 * 352570 * 2
def baseEnd_352570 : Nat := 160922554982925157292059

theorem tailTrace_352570 : CollatzResearch.WordTrace tailWord_352570 prefixEnd_352570 160922554982925157292059 := by
  unfold tailWord_352570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3214821083176644751803791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8572856221804386004810109 3214821083176644751803791)
  ·
    refine ⟨4822231624764967127705687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3214821083176644751803791 4822231624764967127705687)
    ·
      refine ⟨7233347437147450691558531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4822231624764967127705687 7233347437147450691558531)
      ·
        refine ⟨10850021155721176037337797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7233347437147450691558531 10850021155721176037337797)
        ·
          refine ⟨2034378966697720507000837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10850021155721176037337797 2034378966697720507000837)
          ·
            refine ⟨381446056255822595062657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2034378966697720507000837 381446056255822595062657)
            ·
              refine ⟨286084542191866946296993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381446056255822595062657 286084542191866946296993)
              ·
                refine ⟨214563406643900209722745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286084542191866946296993 214563406643900209722745)
                ·
                  refine ⟨160922554982925157292059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214563406643900209722745 160922554982925157292059)
                  ·
                    rfl

theorem cell20_352570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_352570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352570 prefixEnd_352570 := by exact prefixLift 352570
  have htrace : WordTrace (prefixWord ++ tailWord_352570) baseStart_352570 baseEnd_352570 := by
    simpa [prefixWord, tailWord_352570, baseEnd_352570] using wordTrace_append hprefix tailTrace_352570
  have hstable : (prefixWord ++ tailWord_352570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352570).length < 2 ^ (prefixWord ++ tailWord_352570).sum := by decide
  have hdescent : baseEnd_352570 < baseStart_352570 := by decide
  rcases family_descends (prefixWord ++ tailWord_352570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352577 : List Nat := [1, 2, 5, 2, 3, 1, 1, 5]
def baseStart_352577 : Nat := 118140960795 + 352577 * 2 ^ 59
def prefixEnd_352577 : Nat := 4983230072969 + 3 ^ 40 * 352577 * 2
def baseEnd_352577 : Nat := 53641916657888081352899

theorem tailTrace_352577 : CollatzResearch.WordTrace tailWord_352577 prefixEnd_352577 53641916657888081352899 := by
  unfold tailWord_352577
  simp only [CollatzResearch.WordTrace]
  refine ⟨12859539643681219202719985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8573026429120812801813323 12859539643681219202719985)
  ·
    refine ⟨9644654732760914402039989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12859539643681219202719985 9644654732760914402039989)
    ·
      refine ⟨904186381196335725191249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9644654732760914402039989 904186381196335725191249)
      ·
        refine ⟨678139785897251793893437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 904186381196335725191249 678139785897251793893437)
        ·
          refine ⟨254302419711469422710039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 678139785897251793893437 254302419711469422710039)
          ·
            refine ⟨381453629567204134065059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254302419711469422710039 381453629567204134065059)
            ·
              refine ⟨572180444350806201097589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381453629567204134065059 572180444350806201097589)
              ·
                refine ⟨53641916657888081352899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 572180444350806201097589 53641916657888081352899)
                ·
                  rfl

theorem cell20_352577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 5].length) (baseStart_352577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352577 prefixEnd_352577 := by exact prefixLift 352577
  have htrace : WordTrace (prefixWord ++ tailWord_352577) baseStart_352577 baseEnd_352577 := by
    simpa [prefixWord, tailWord_352577, baseEnd_352577] using wordTrace_append hprefix tailTrace_352577
  have hstable : (prefixWord ++ tailWord_352577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352577).length < 2 ^ (prefixWord ++ tailWord_352577).sum := by decide
  have hdescent : baseEnd_352577 < baseStart_352577 := by decide
  rcases family_descends (prefixWord ++ tailWord_352577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352588 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 3]
def baseStart_352588 : Nat := 118140960795 + 352588 * 2 ^ 59
def prefixEnd_352588 : Nat := 4983230072969 + 3 ^ 40 * 352588 * 2
def baseEnd_352588 : Nat := 160930770673397094691985

theorem tailTrace_352588 : CollatzResearch.WordTrace tailWord_352588 prefixEnd_352588 160930770673397094691985 := by
  unfold tailWord_352588
  simp only [CollatzResearch.WordTrace]
  refine ⟨6429970423320684040685209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8573293897760912054246945 6429970423320684040685209)
  ·
    refine ⟨4822477817490513030513907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6429970423320684040685209 4822477817490513030513907)
    ·
      refine ⟨7233716726235769545770861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4822477817490513030513907 7233716726235769545770861)
      ·
        refine ⟨2712643772338413579664073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7233716726235769545770861 2712643772338413579664073)
        ·
          refine ⟨2034482829253810184748055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2712643772338413579664073 2034482829253810184748055)
          ·
            refine ⟨3051724243880715277122083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034482829253810184748055 3051724243880715277122083)
            ·
              refine ⟨4577586365821072915683125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051724243880715277122083 4577586365821072915683125)
              ·
                refine ⟨429148721795725585845293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4577586365821072915683125 429148721795725585845293)
                ·
                  refine ⟨160930770673397094691985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429148721795725585845293 160930770673397094691985)
                  ·
                    rfl

theorem cell20_352588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_352588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352588 prefixEnd_352588 := by exact prefixLift 352588
  have htrace : WordTrace (prefixWord ++ tailWord_352588) baseStart_352588 baseEnd_352588 := by
    simpa [prefixWord, tailWord_352588, baseEnd_352588] using wordTrace_append hprefix tailTrace_352588
  have hstable : (prefixWord ++ tailWord_352588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352588).length < 2 ^ (prefixWord ++ tailWord_352588).sum := by decide
  have hdescent : baseEnd_352588 < baseStart_352588 := by decide
  rcases family_descends (prefixWord ++ tailWord_352588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352626 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_352626 : Nat := 118140960795 + 352626 * 2 ^ 59
def prefixEnd_352626 : Nat := 4983230072969 + 3 ^ 40 * 352626 * 2
def baseEnd_352626 : Nat := 160948114908837851425163

theorem tailTrace_352626 : CollatzResearch.WordTrace tailWord_352626 prefixEnd_352626 160948114908837851425163 := by
  unfold tailWord_352626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215331705125925142813433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8574217880335800380835821 3215331705125925142813433)
  ·
    refine ⟨2411498778844443857110075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3215331705125925142813433 2411498778844443857110075)
    ·
      refine ⟨3617248168266665785665113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2411498778844443857110075 3617248168266665785665113)
      ·
        refine ⟨2712936126199999339248835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3617248168266665785665113 2712936126199999339248835)
        ·
          refine ⟨4069404189299999008873253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712936126199999339248835 4069404189299999008873253)
          ·
            refine ⟨763013285493749814163735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4069404189299999008873253 763013285493749814163735)
            ·
              refine ⟨1144519928240624721245603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763013285493749814163735 1144519928240624721245603)
              ·
                refine ⟨1716779892360937081868405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144519928240624721245603 1716779892360937081868405)
                ·
                  refine ⟨160948114908837851425163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1716779892360937081868405 160948114908837851425163)
                  ·
                    rfl

theorem cell20_352626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_352626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352626 prefixEnd_352626 := by exact prefixLift 352626
  have htrace : WordTrace (prefixWord ++ tailWord_352626) baseStart_352626 baseEnd_352626 := by
    simpa [prefixWord, tailWord_352626, baseEnd_352626] using wordTrace_append hprefix tailTrace_352626
  have hstable : (prefixWord ++ tailWord_352626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352626).length < 2 ^ (prefixWord ++ tailWord_352626).sum := by decide
  have hdescent : baseEnd_352626 < baseStart_352626 := by decide
  rcases family_descends (prefixWord ++ tailWord_352626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352629 : List Nat := [1, 3, 4, 1, 2, 1, 2, 4, 2]
def baseStart_352629 : Nat := 118140960795 + 352629 * 2 ^ 59
def prefixEnd_352629 : Nat := 4983230072969 + 3 ^ 40 * 352629 * 2
def baseEnd_352629 : Nat := 160949484190583174325151

theorem tailTrace_352629 : CollatzResearch.WordTrace tailWord_352629 prefixEnd_352629 160949484190583174325151 := by
  unfold tailWord_352629
  simp only [CollatzResearch.WordTrace]
  refine ⟨12861436239492832083612941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8574290826328554722408627 12861436239492832083612941)
  ·
    refine ⟨4823038589809812031354853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12861436239492832083612941 4823038589809812031354853)
    ·
      refine ⟨904319735589339755879035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4823038589809812031354853 904319735589339755879035)
      ·
        refine ⟨1356479603384009633818553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904319735589339755879035 1356479603384009633818553)
        ·
          refine ⟨1017359702538007225363915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1356479603384009633818553 1017359702538007225363915)
          ·
            refine ⟨1526039553807010838045873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017359702538007225363915 1526039553807010838045873)
            ·
              refine ⟨1144529665355258128534405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526039553807010838045873 1144529665355258128534405)
              ·
                refine ⟨214599312254110899100201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1144529665355258128534405 214599312254110899100201)
                ·
                  refine ⟨160949484190583174325151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214599312254110899100201 160949484190583174325151)
                  ·
                    rfl

theorem cell20_352629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_352629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352629 prefixEnd_352629 := by exact prefixLift 352629
  have htrace : WordTrace (prefixWord ++ tailWord_352629) baseStart_352629 baseEnd_352629 := by
    simpa [prefixWord, tailWord_352629, baseEnd_352629] using wordTrace_append hprefix tailTrace_352629
  have hstable : (prefixWord ++ tailWord_352629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352629).length < 2 ^ (prefixWord ++ tailWord_352629).sum := by decide
  have hdescent : baseEnd_352629 < baseStart_352629 := by decide
  rcases family_descends (prefixWord ++ tailWord_352629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352664 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_352664 : Nat := 118140960795 + 352664 * 2 ^ 59
def prefixEnd_352664 : Nat := 4983230072969 + 3 ^ 40 * 352664 * 2
def baseEnd_352664 : Nat := 160965459144278608158341

theorem tailTrace_352664 : CollatzResearch.WordTrace tailWord_352664 prefixEnd_352664 160965459144278608158341 := by
  unfold tailWord_352664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6431356397183016530568523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8575141862910688707424697 6431356397183016530568523)
  ·
    refine ⟨9647034595774524795852785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6431356397183016530568523 9647034595774524795852785)
    ·
      refine ⟨7235275946830893596889589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9647034595774524795852785 7235275946830893596889589)
      ·
        refine ⟨678307120015396274708399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7235275946830893596889589 678307120015396274708399)
        ·
          refine ⟨1017460680023094412062599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678307120015396274708399 1017460680023094412062599)
          ·
            refine ⟨1526191020034641618093899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017460680023094412062599 1526191020034641618093899)
            ·
              refine ⟨2289286530051962427140849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526191020034641618093899 2289286530051962427140849)
              ·
                refine ⟨1716964897538971820355637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289286530051962427140849 1716964897538971820355637)
                ·
                  refine ⟨160965459144278608158341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1716964897538971820355637 160965459144278608158341)
                  ·
                    rfl

theorem cell20_352664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_352664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352664 prefixEnd_352664 := by exact prefixLift 352664
  have htrace : WordTrace (prefixWord ++ tailWord_352664) baseStart_352664 baseEnd_352664 := by
    simpa [prefixWord, tailWord_352664, baseEnd_352664] using wordTrace_append hprefix tailTrace_352664
  have hstable : (prefixWord ++ tailWord_352664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352664).length < 2 ^ (prefixWord ++ tailWord_352664).sum := by decide
  have hdescent : baseEnd_352664 < baseStart_352664 := by decide
  rcases family_descends (prefixWord ++ tailWord_352664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352739 : List Nat := [1, 1, 1, 6, 4, 1, 2, 2, 2]
def baseStart_352739 : Nat := 118140960795 + 352739 * 2 ^ 59
def prefixEnd_352739 : Nat := 4983230072969 + 3 ^ 40 * 352739 * 2
def baseEnd_352739 : Nat := 160999691187911680658035

theorem tailTrace_352739 : CollatzResearch.WordTrace tailWord_352739 prefixEnd_352739 160999691187911680658035 := by
  unfold tailWord_352739
  simp only [CollatzResearch.WordTrace]
  refine ⟨12865448269094320870117271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8576965512729547246744847 12865448269094320870117271)
  ·
    refine ⟨19298172403641481305175907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12865448269094320870117271 19298172403641481305175907)
    ·
      refine ⟨28947258605462221957763861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19298172403641481305175907 28947258605462221957763861)
      ·
        refine ⟨1356902747131041654270181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28947258605462221957763861 1356902747131041654270181)
        ·
          refine ⟨254419265087070310175659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1356902747131041654270181 254419265087070310175659)
          ·
            refine ⟨381628897630605465263489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254419265087070310175659 381628897630605465263489)
            ·
              refine ⟨286221673222954098947617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381628897630605465263489 286221673222954098947617)
              ·
                refine ⟨214666254917215574210713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286221673222954098947617 214666254917215574210713)
                ·
                  refine ⟨160999691187911680658035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214666254917215574210713 160999691187911680658035)
                  ·
                    rfl

theorem cell20_352739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 2].length) (baseStart_352739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352739 prefixEnd_352739 := by exact prefixLift 352739
  have htrace : WordTrace (prefixWord ++ tailWord_352739) baseStart_352739 baseEnd_352739 := by
    simpa [prefixWord, tailWord_352739, baseEnd_352739] using wordTrace_append hprefix tailTrace_352739
  have hstable : (prefixWord ++ tailWord_352739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352739).length < 2 ^ (prefixWord ++ tailWord_352739).sum := by decide
  have hdescent : baseEnd_352739 < baseStart_352739 := by decide
  rcases family_descends (prefixWord ++ tailWord_352739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352791 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 3]
def baseStart_352791 : Nat := 118140960795 + 352791 * 2 ^ 59
def prefixEnd_352791 : Nat := 4983230072969 + 3 ^ 40 * 352791 * 2
def baseEnd_352791 : Nat := 161023425404830610924489

theorem tailTrace_352791 : CollatzResearch.WordTrace tailWord_352791 prefixEnd_352791 161023425404830610924489 := by
  unfold tailWord_352791
  simp only [CollatzResearch.WordTrace]
  refine ⟨12867344864905933751010227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8578229909937289167340151 12867344864905933751010227)
  ·
    refine ⟨19301017297358900626515341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12867344864905933751010227 19301017297358900626515341)
    ·
      refine ⟨7237881486509587734943253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19301017297358900626515341 7237881486509587734943253)
      ·
        refine ⟨339275694680136925075465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7237881486509587734943253 339275694680136925075465)
        ·
          refine ⟨254456771010102693806599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339275694680136925075465 254456771010102693806599)
          ·
            refine ⟨381685156515154040709899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254456771010102693806599 381685156515154040709899)
            ·
              refine ⟨572527734772731061064849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381685156515154040709899 572527734772731061064849)
              ·
                refine ⟨429395801079548295798637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572527734772731061064849 429395801079548295798637)
                ·
                  refine ⟨161023425404830610924489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429395801079548295798637 161023425404830610924489)
                  ·
                    rfl

theorem cell20_352791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 3].length) (baseStart_352791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352791 prefixEnd_352791 := by exact prefixLift 352791
  have htrace : WordTrace (prefixWord ++ tailWord_352791) baseStart_352791 baseEnd_352791 := by
    simpa [prefixWord, tailWord_352791, baseEnd_352791] using wordTrace_append hprefix tailTrace_352791
  have hstable : (prefixWord ++ tailWord_352791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352791).length < 2 ^ (prefixWord ++ tailWord_352791).sum := by decide
  have hdescent : baseEnd_352791 < baseStart_352791 := by decide
  rcases family_descends (prefixWord ++ tailWord_352791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352792 : List Nat := [2, 1, 2, 3, 3, 2, 7]
def baseStart_352792 : Nat := 118140960795 + 352792 * 2 ^ 59
def prefixEnd_352792 : Nat := 4983230072969 + 3 ^ 40 * 352792 * 2
def baseEnd_352792 : Nat := 17891542425786561321239

theorem tailTrace_352792 : CollatzResearch.WordTrace tailWord_352792 prefixEnd_352792 17891542425786561321239 := by
  unfold tailWord_352792
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433690668951155460898315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8578254225268207281197753 6433690668951155460898315)
  ·
    refine ⟨9650536003426733191347473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6433690668951155460898315 9650536003426733191347473)
    ·
      refine ⟨7237902002570049893510605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9650536003426733191347473 7237902002570049893510605)
      ·
        refine ⟨2714213250963768710066477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7237902002570049893510605 2714213250963768710066477)
        ·
          refine ⟨1017829969111413266274929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2714213250963768710066477 1017829969111413266274929)
          ·
            refine ⟨763372476833559949706197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1017829969111413266274929 763372476833559949706197)
            ·
              refine ⟨17891542425786561321239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 763372476833559949706197 17891542425786561321239)
              ·
                rfl

theorem cell20_352792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 7].length) (baseStart_352792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352792 prefixEnd_352792 := by exact prefixLift 352792
  have htrace : WordTrace (prefixWord ++ tailWord_352792) baseStart_352792 baseEnd_352792 := by
    simpa [prefixWord, tailWord_352792, baseEnd_352792] using wordTrace_append hprefix tailTrace_352792
  have hstable : (prefixWord ++ tailWord_352792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352792).length < 2 ^ (prefixWord ++ tailWord_352792).sum := by decide
  have hdescent : baseEnd_352792 < baseStart_352792 := by decide
  rcases family_descends (prefixWord ++ tailWord_352792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352837 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_352837 : Nat := 118140960795 + 352837 * 2 ^ 59
def prefixEnd_352837 : Nat := 4983230072969 + 3 ^ 40 * 352837 * 2
def baseEnd_352837 : Nat := 161044421058258895390967

theorem tailTrace_352837 : CollatzResearch.WordTrace tailWord_352837 prefixEnd_352837 161044421058258895390967 := by
  unfold tailWord_352837
  simp only [CollatzResearch.WordTrace]
  refine ⟨12869022622739283607184765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8579348415159522404789843 12869022622739283607184765)
  ·
    refine ⟨4825883483527231352694287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12869022622739283607184765 4825883483527231352694287)
    ·
      refine ⟨7238825225290847029041431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4825883483527231352694287 7238825225290847029041431)
      ·
        refine ⟨10858237837936270543562147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7238825225290847029041431 10858237837936270543562147)
        ·
          refine ⟨16287356756904405815343221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10858237837936270543562147 16287356756904405815343221)
          ·
            refine ⟨1526939695959788045188427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16287356756904405815343221 1526939695959788045188427)
            ·
              refine ⟨2290409543939682067782641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526939695959788045188427 2290409543939682067782641)
              ·
                refine ⟨1717807157954761550836981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2290409543939682067782641 1717807157954761550836981)
                ·
                  refine ⟨161044421058258895390967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1717807157954761550836981 161044421058258895390967)
                  ·
                    rfl

theorem cell20_352837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_352837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352837 prefixEnd_352837 := by exact prefixLift 352837
  have htrace : WordTrace (prefixWord ++ tailWord_352837) baseStart_352837 baseEnd_352837 := by
    simpa [prefixWord, tailWord_352837, baseEnd_352837] using wordTrace_append hprefix tailTrace_352837
  have hstable : (prefixWord ++ tailWord_352837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352837).length < 2 ^ (prefixWord ++ tailWord_352837).sum := by decide
  have hdescent : baseEnd_352837 < baseStart_352837 := by decide
  rcases family_descends (prefixWord ++ tailWord_352837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352868 : List Nat := [2, 3, 1, 1, 2, 2, 4, 5]
def baseStart_352868 : Nat := 118140960795 + 352868 * 2 ^ 59
def prefixEnd_352868 : Nat := 4983230072969 + 3 ^ 40 * 352868 * 2
def baseEnd_352868 : Nat := 53686190100986855119169

theorem tailTrace_352868 : CollatzResearch.WordTrace tailWord_352868 prefixEnd_352868 53686190100986855119169 := by
  unfold tailWord_352868
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435076642813487950781629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8580102190417983934375505 6435076642813487950781629)
  ·
    refine ⟨2413153741055057981543111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6435076642813487950781629 2413153741055057981543111)
    ·
      refine ⟨3619730611582586972314667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2413153741055057981543111 3619730611582586972314667)
      ·
        refine ⟨5429595917373880458472001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3619730611582586972314667 5429595917373880458472001)
        ·
          refine ⟨4072196938030410343854001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5429595917373880458472001 4072196938030410343854001)
          ·
            refine ⟨3054147703522807757890501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4072196938030410343854001 3054147703522807757890501)
            ·
              refine ⟨572652694410526454604469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3054147703522807757890501 572652694410526454604469)
              ·
                refine ⟨53686190100986855119169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 572652694410526454604469 53686190100986855119169)
                ·
                  rfl

theorem cell20_352868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_352868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352868 prefixEnd_352868 := by exact prefixLift 352868
  have htrace : WordTrace (prefixWord ++ tailWord_352868) baseStart_352868 baseEnd_352868 := by
    simpa [prefixWord, tailWord_352868, baseEnd_352868] using wordTrace_append hprefix tailTrace_352868
  have hstable : (prefixWord ++ tailWord_352868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352868).length < 2 ^ (prefixWord ++ tailWord_352868).sum := by decide
  have hdescent : baseEnd_352868 < baseStart_352868 := by decide
  rcases family_descends (prefixWord ++ tailWord_352868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352906 : List Nat := [3, 1, 2, 3, 3, 8]
def baseStart_352906 : Nat := 118140960795 + 352906 * 2 ^ 59
def prefixEnd_352906 : Nat := 4983230072969 + 3 ^ 40 * 352906 * 2
def baseEnd_352906 : Nat := 5965774612533382299655

theorem tailTrace_352906 : CollatzResearch.WordTrace tailWord_352906 prefixEnd_352906 5965774612533382299655 := by
  unfold tailWord_352906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3217884814872327097861643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8581026172992872260964381 3217884814872327097861643)
  ·
    refine ⟨4826827222308490646792465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3217884814872327097861643 4826827222308490646792465)
    ·
      refine ⟨3620120416731367985094349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4826827222308490646792465 3620120416731367985094349)
      ·
        refine ⟨1357545156274262994410381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3620120416731367985094349 1357545156274262994410381)
        ·
          refine ⟨509079433602848622903893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1357545156274262994410381 509079433602848622903893)
          ·
            refine ⟨5965774612533382299655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 509079433602848622903893 5965774612533382299655)
            ·
              rfl

theorem cell20_352906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 8].length) (baseStart_352906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352906 prefixEnd_352906 := by exact prefixLift 352906
  have htrace : WordTrace (prefixWord ++ tailWord_352906) baseStart_352906 baseEnd_352906 := by
    simpa [prefixWord, tailWord_352906, baseEnd_352906] using wordTrace_append hprefix tailTrace_352906
  have hstable : (prefixWord ++ tailWord_352906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352906).length < 2 ^ (prefixWord ++ tailWord_352906).sum := by decide
  have hdescent : baseEnd_352906 < baseStart_352906 := by decide
  rcases family_descends (prefixWord ++ tailWord_352906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352954 : List Nat := [3, 1, 1, 1, 2, 3, 4, 3, 2]
def baseStart_352954 : Nat := 118140960795 + 352954 * 2 ^ 59
def prefixEnd_352954 : Nat := 4983230072969 + 3 ^ 40 * 352954 * 2
def baseEnd_352954 : Nat := 161097823046326488490489

theorem tailTrace_352954 : CollatzResearch.WordTrace tailWord_352954 prefixEnd_352954 161097823046326488490489 := by
  unfold tailWord_352954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3218322490828853147298479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8582193308876941726129277 3218322490828853147298479)
  ·
    refine ⟨4827483736243279720947719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3218322490828853147298479 4827483736243279720947719)
    ·
      refine ⟨7241225604364919581421579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4827483736243279720947719 7241225604364919581421579)
      ·
        refine ⟨10861838406547379372132369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7241225604364919581421579 10861838406547379372132369)
        ·
          refine ⟨8146378804910534529099277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10861838406547379372132369 8146378804910534529099277)
          ·
            refine ⟨3054892051841450448412229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8146378804910534529099277 3054892051841450448412229)
            ·
              refine ⟨572792259720271959077293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3054892051841450448412229 572792259720271959077293)
              ·
                refine ⟨214797097395101984653985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 572792259720271959077293 214797097395101984653985)
                ·
                  refine ⟨161097823046326488490489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214797097395101984653985 161097823046326488490489)
                  ·
                    rfl

theorem cell20_352954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_352954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352954 prefixEnd_352954 := by exact prefixLift 352954
  have htrace : WordTrace (prefixWord ++ tailWord_352954) baseStart_352954 baseEnd_352954 := by
    simpa [prefixWord, tailWord_352954, baseEnd_352954] using wordTrace_append hprefix tailTrace_352954
  have hstable : (prefixWord ++ tailWord_352954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352954).length < 2 ^ (prefixWord ++ tailWord_352954).sum := by decide
  have hdescent : baseEnd_352954 < baseStart_352954 := by decide
  rcases family_descends (prefixWord ++ tailWord_352954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352968 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 3]
def baseStart_352968 : Nat := 118140960795 + 352968 * 2 ^ 59
def prefixEnd_352968 : Nat := 4983230072969 + 3 ^ 40 * 352968 * 2
def baseEnd_352968 : Nat := 161104213027804662023765

theorem tailTrace_352968 : CollatzResearch.WordTrace tailWord_352968 prefixEnd_352968 161104213027804662023765 := by
  unfold tailWord_352968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6436900292632346490101779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8582533723509795320135705 6436900292632346490101779)
  ·
    refine ⟨9655350438948519735152669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6436900292632346490101779 9655350438948519735152669)
    ·
      refine ⟨3620756414605694900682251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9655350438948519735152669 3620756414605694900682251)
      ·
        refine ⟨5431134621908542351023377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3620756414605694900682251 5431134621908542351023377)
        ·
          refine ⟨4073350966431406763267533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5431134621908542351023377 4073350966431406763267533)
          ·
            refine ⟨1527506612411777536225325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4073350966431406763267533 1527506612411777536225325)
            ·
              refine ⟨572814979654416576084497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1527506612411777536225325 572814979654416576084497)
              ·
                refine ⟨429611234740812432063373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572814979654416576084497 429611234740812432063373)
                ·
                  refine ⟨161104213027804662023765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429611234740812432063373 161104213027804662023765)
                  ·
                    rfl

theorem cell20_352968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_352968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352968 prefixEnd_352968 := by exact prefixLift 352968
  have htrace : WordTrace (prefixWord ++ tailWord_352968) baseStart_352968 baseEnd_352968 := by
    simpa [prefixWord, tailWord_352968, baseEnd_352968] using wordTrace_append hprefix tailTrace_352968
  have hstable : (prefixWord ++ tailWord_352968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352968).length < 2 ^ (prefixWord ++ tailWord_352968).sum := by decide
  have hdescent : baseEnd_352968 < baseStart_352968 := by decide
  rcases family_descends (prefixWord ++ tailWord_352968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353020 : List Nat := [2, 2, 2, 1, 3, 4, 6]
def baseStart_353020 : Nat := 118140960795 + 353020 * 2 ^ 59
def prefixEnd_353020 : Nat := 4983230072969 + 3 ^ 40 * 353020 * 2
def baseEnd_353020 : Nat := 17903105249413732476691

theorem tailTrace_353020 : CollatzResearch.WordTrace tailWord_353020 prefixEnd_353020 17903105249413732476691 := by
  unfold tailWord_353020
  simp only [CollatzResearch.WordTrace]
  refine ⟨6437848590538152930548257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8583798120717537240731009 6437848590538152930548257)
  ·
    refine ⟨4828386442903614697911193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6437848590538152930548257 4828386442903614697911193)
    ·
      refine ⟨3621289832177711023433395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4828386442903614697911193 3621289832177711023433395)
      ·
        refine ⟨5431934748266566535150093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3621289832177711023433395 5431934748266566535150093)
        ·
          refine ⟨2036975530599962450681285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5431934748266566535150093 2036975530599962450681285)
          ·
            refine ⟨381932911987492959502741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2036975530599962450681285 381932911987492959502741)
            ·
              refine ⟨17903105249413732476691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 381932911987492959502741 17903105249413732476691)
              ·
                rfl

theorem cell20_353020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 6].length) (baseStart_353020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353020 prefixEnd_353020 := by exact prefixLift 353020
  have htrace : WordTrace (prefixWord ++ tailWord_353020) baseStart_353020 baseEnd_353020 := by
    simpa [prefixWord, tailWord_353020, baseEnd_353020] using wordTrace_append hprefix tailTrace_353020
  have hstable : (prefixWord ++ tailWord_353020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353020).length < 2 ^ (prefixWord ++ tailWord_353020).sum := by decide
  have hdescent : baseEnd_353020 < baseStart_353020 := by decide
  rcases family_descends (prefixWord ++ tailWord_353020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353026 : List Nat := [3, 4, 1, 1, 1, 3, 3, 2, 2]
def baseStart_353026 : Nat := 118140960795 + 353026 * 2 ^ 59
def prefixEnd_353026 : Nat := 4983230072969 + 3 ^ 40 * 353026 * 2
def baseEnd_353026 : Nat := 161130685808214238090195

theorem tailTrace_353026 : CollatzResearch.WordTrace tailWord_353026 prefixEnd_353026 161130685808214238090195 := by
  unfold tailWord_353026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3218979004763642221453733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8583944012703045923876621 3218979004763642221453733)
  ·
    refine ⟨603558563393182916522575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3218979004763642221453733 603558563393182916522575)
    ·
      refine ⟨905337845089774374783863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603558563393182916522575 905337845089774374783863)
      ·
        refine ⟨1358006767634661562175795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905337845089774374783863 1358006767634661562175795)
        ·
          refine ⟨2037010151451992343263693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1358006767634661562175795 2037010151451992343263693)
          ·
            refine ⟨763878806794497128723885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2037010151451992343263693 763878806794497128723885)
            ·
              refine ⟨286454552547936423271457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 763878806794497128723885 286454552547936423271457)
              ·
                refine ⟨214840914410952317453593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286454552547936423271457 214840914410952317453593)
                ·
                  refine ⟨161130685808214238090195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214840914410952317453593 161130685808214238090195)
                  ·
                    rfl

theorem cell20_353026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_353026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353026 prefixEnd_353026 := by exact prefixLift 353026
  have htrace : WordTrace (prefixWord ++ tailWord_353026) baseStart_353026 baseEnd_353026 := by
    simpa [prefixWord, tailWord_353026, baseEnd_353026] using wordTrace_append hprefix tailTrace_353026
  have hstable : (prefixWord ++ tailWord_353026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353026).length < 2 ^ (prefixWord ++ tailWord_353026).sum := by decide
  have hdescent : baseEnd_353026 < baseStart_353026 := by decide
  rcases family_descends (prefixWord ++ tailWord_353026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353027 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 3]
def baseStart_353027 : Nat := 118140960795 + 353027 * 2 ^ 59
def prefixEnd_353027 : Nat := 4983230072969 + 3 ^ 40 * 353027 * 2
def baseEnd_353027 : Nat := 161131142235462679056857

theorem tailTrace_353027 : CollatzResearch.WordTrace tailWord_353027 prefixEnd_353027 161131142235462679056857 := by
  unfold tailWord_353027
  simp only [CollatzResearch.WordTrace]
  refine ⟨12875952492050946056601335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8583968328033964037734223 12875952492050946056601335)
  ·
    refine ⟨19313928738076419084902003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12875952492050946056601335 19313928738076419084902003)
    ·
      refine ⟨28970893107114628627353005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19313928738076419084902003 28970893107114628627353005)
      ·
        refine ⟨10864084915167985735257377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28970893107114628627353005 10864084915167985735257377)
        ·
          refine ⟨8148063686375989301443033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10864084915167985735257377 8148063686375989301443033)
          ·
            refine ⟨6111047764781991976082275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8148063686375989301443033 6111047764781991976082275)
            ·
              refine ⟨9166571647172987964123413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6111047764781991976082275 9166571647172987964123413)
              ·
                refine ⟨429683045961233810818285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9166571647172987964123413 429683045961233810818285)
                ·
                  refine ⟨161131142235462679056857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429683045961233810818285 161131142235462679056857)
                  ·
                    rfl

theorem cell20_353027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 3].length) (baseStart_353027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353027 prefixEnd_353027 := by exact prefixLift 353027
  have htrace : WordTrace (prefixWord ++ tailWord_353027) baseStart_353027 baseEnd_353027 := by
    simpa [prefixWord, tailWord_353027, baseEnd_353027] using wordTrace_append hprefix tailTrace_353027
  have hstable : (prefixWord ++ tailWord_353027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353027).length < 2 ^ (prefixWord ++ tailWord_353027).sum := by decide
  have hdescent : baseEnd_353027 < baseStart_353027 := by decide
  rcases family_descends (prefixWord ++ tailWord_353027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353041 : List Nat := [1, 2, 2, 1, 1, 3, 3, 7]
def baseStart_353041 : Nat := 118140960795 + 353041 * 2 ^ 59
def prefixEnd_353041 : Nat := 4983230072969 + 3 ^ 40 * 353041 * 2
def baseEnd_353041 : Nat := 53712510738980284196711

theorem tailTrace_353041 : CollatzResearch.WordTrace tailWord_353041 prefixEnd_353041 53712510738980284196711 := by
  unfold tailWord_353041
  simp only [CollatzResearch.WordTrace]
  refine ⟨12876463114000226447610977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8584308742666817631740651 12876463114000226447610977)
  ·
    refine ⟨9657347335500169835708233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12876463114000226447610977 9657347335500169835708233)
    ·
      refine ⟨7243010501625127376781175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9657347335500169835708233 7243010501625127376781175)
      ·
        refine ⟨10864515752437691065171763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7243010501625127376781175 10864515752437691065171763)
        ·
          refine ⟨16296773628656536597757645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10864515752437691065171763 16296773628656536597757645)
          ·
            refine ⟨6111290110746201224159117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16296773628656536597757645 6111290110746201224159117)
            ·
              refine ⟨2291733791529825459059669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6111290110746201224159117 2291733791529825459059669)
              ·
                refine ⟨53712510738980284196711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2291733791529825459059669 53712510738980284196711)
                ·
                  rfl

theorem cell20_353041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_353041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353041 prefixEnd_353041 := by exact prefixLift 353041
  have htrace : WordTrace (prefixWord ++ tailWord_353041) baseStart_353041 baseEnd_353041 := by
    simpa [prefixWord, tailWord_353041, baseEnd_353041] using wordTrace_append hprefix tailTrace_353041
  have hstable : (prefixWord ++ tailWord_353041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353041).length < 2 ^ (prefixWord ++ tailWord_353041).sum := by decide
  have hdescent : baseEnd_353041 < baseStart_353041 := by decide
  rcases family_descends (prefixWord ++ tailWord_353041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353058 : List Nat := [3, 3, 1, 1, 2, 2, 2, 6]
def baseStart_353058 : Nat := 118140960795 + 353058 * 2 ^ 59
def prefixEnd_353058 : Nat := 4983230072969 + 3 ^ 40 * 353058 * 2
def baseEnd_353058 : Nat := 53715097160054783007799

theorem tailTrace_353058 : CollatzResearch.WordTrace tailWord_353058 prefixEnd_353058 53715097160054783007799 := by
  unfold tailWord_353058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219270788734659587744957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8584722103292425567319885 3219270788734659587744957)
  ·
    refine ⟨1207226545775497345404359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3219270788734659587744957 1207226545775497345404359)
    ·
      refine ⟨1810839818663246018106539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1207226545775497345404359 1810839818663246018106539)
      ·
        refine ⟨2716259727994869027159809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810839818663246018106539 2716259727994869027159809)
        ·
          refine ⟨2037194795996151770369857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716259727994869027159809 2037194795996151770369857)
          ·
            refine ⟨1527896096997113827777393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2037194795996151770369857 1527896096997113827777393)
            ·
              refine ⟨1145922072747835370833045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1527896096997113827777393 1145922072747835370833045)
              ·
                refine ⟨53715097160054783007799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1145922072747835370833045 53715097160054783007799)
                ·
                  rfl

theorem cell20_353058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_353058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353058 prefixEnd_353058 := by exact prefixLift 353058
  have htrace : WordTrace (prefixWord ++ tailWord_353058) baseStart_353058 baseEnd_353058 := by
    simpa [prefixWord, tailWord_353058, baseEnd_353058] using wordTrace_append hprefix tailTrace_353058
  have hstable : (prefixWord ++ tailWord_353058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353058).length < 2 ^ (prefixWord ++ tailWord_353058).sum := by decide
  have hdescent : baseEnd_353058 < baseStart_353058 := by decide
  rcases family_descends (prefixWord ++ tailWord_353058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353078 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_353078 : Nat := 118140960795 + 353078 * 2 ^ 59
def prefixEnd_353078 : Nat := 4983230072969 + 3 ^ 40 * 353078 * 2
def baseEnd_353078 : Nat := 161154420025133168356649

theorem tailTrace_353078 : CollatzResearch.WordTrace tailWord_353078 prefixEnd_353078 161154420025133168356649 := by
  unfold tailWord_353078
  simp only [CollatzResearch.WordTrace]
  refine ⟨804863288429136360419243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8585208409910787844471925 804863288429136360419243)
  ·
    refine ⟨1207294932643704540628865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 804863288429136360419243 1207294932643704540628865)
    ·
      refine ⟨905471199482778405471649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1207294932643704540628865 905471199482778405471649)
      ·
        refine ⟨679103399612083804103737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 905471199482778405471649 679103399612083804103737)
        ·
          refine ⟨509327549709062853077803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 679103399612083804103737 509327549709062853077803)
          ·
            refine ⟨763991324563594279616705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509327549709062853077803 763991324563594279616705)
            ·
              refine ⟨572993493422695709712529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763991324563594279616705 572993493422695709712529)
              ·
                refine ⟨429745120067021782284397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572993493422695709712529 429745120067021782284397)
                ·
                  refine ⟨161154420025133168356649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429745120067021782284397 161154420025133168356649)
                  ·
                    rfl

theorem cell20_353078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_353078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353078 prefixEnd_353078 := by exact prefixLift 353078
  have htrace : WordTrace (prefixWord ++ tailWord_353078) baseStart_353078 baseEnd_353078 := by
    simpa [prefixWord, tailWord_353078, baseEnd_353078] using wordTrace_append hprefix tailTrace_353078
  have hstable : (prefixWord ++ tailWord_353078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353078).length < 2 ^ (prefixWord ++ tailWord_353078).sum := by decide
  have hdescent : baseEnd_353078 < baseStart_353078 := by decide
  rcases family_descends (prefixWord ++ tailWord_353078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353085 : List Nat := [1, 4, 1, 4, 2, 1, 1, 4, 2]
def baseStart_353085 : Nat := 118140960795 + 353085 * 2 ^ 59
def prefixEnd_353085 : Nat := 4983230072969 + 3 ^ 40 * 353085 * 2
def baseEnd_353085 : Nat := 161157615015872255123287

theorem tailTrace_353085 : CollatzResearch.WordTrace tailWord_353085 prefixEnd_353085 161157615015872255123287 := by
  unfold tailWord_353085
  simp only [CollatzResearch.WordTrace]
  refine ⟨12878067925840821962212709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8585378617227214641475139 12878067925840821962212709)
  ·
    refine ⟨2414637736095154117914883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12878067925840821962212709 2414637736095154117914883)
    ·
      refine ⟨3621956604142731176872325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414637736095154117914883 3621956604142731176872325)
      ·
        refine ⟨679116863276762095663561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3621956604142731176872325 679116863276762095663561)
        ·
          refine ⟨509337647457571571747671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 679116863276762095663561 509337647457571571747671)
          ·
            refine ⟨764006471186357357621507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509337647457571571747671 764006471186357357621507)
            ·
              refine ⟨1146009706779536036432261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764006471186357357621507 1146009706779536036432261)
              ·
                refine ⟨214876820021163006831049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1146009706779536036432261 214876820021163006831049)
                ·
                  refine ⟨161157615015872255123287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214876820021163006831049 161157615015872255123287)
                  ·
                    rfl

theorem cell20_353085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_353085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353085 prefixEnd_353085 := by exact prefixLift 353085
  have htrace : WordTrace (prefixWord ++ tailWord_353085) baseStart_353085 baseEnd_353085 := by
    simpa [prefixWord, tailWord_353085, baseEnd_353085] using wordTrace_append hprefix tailTrace_353085
  have hstable : (prefixWord ++ tailWord_353085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353085).length < 2 ^ (prefixWord ++ tailWord_353085).sum := by decide
  have hdescent : baseEnd_353085 < baseStart_353085 := by decide
  rcases family_descends (prefixWord ++ tailWord_353085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353155 : List Nat := [1, 1, 1, 3, 4, 1, 2, 7]
def baseStart_353155 : Nat := 118140960795 + 353155 * 2 ^ 59
def prefixEnd_353155 : Nat := 4983230072969 + 3 ^ 40 * 353155 * 2
def baseEnd_353155 : Nat := 53729854974421040929889

theorem tailTrace_353155 : CollatzResearch.WordTrace tailWord_353155 prefixEnd_353155 53729854974421040929889 := by
  unfold tailWord_353155
  simp only [CollatzResearch.WordTrace]
  refine ⟨12880621035587223917260919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8587080690391482611507279 12880621035587223917260919)
  ·
    refine ⟨19320931553380835875891379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12880621035587223917260919 19320931553380835875891379)
    ·
      refine ⟨28981397330071253813837069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19320931553380835875891379 28981397330071253813837069)
      ·
        refine ⟨10868023998776720180188901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28981397330071253813837069 10868023998776720180188901)
        ·
          refine ⟨2037754499770635033785419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10868023998776720180188901 2037754499770635033785419)
          ·
            refine ⟨3056631749655952550678129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037754499770635033785419 3056631749655952550678129)
            ·
              refine ⟨2292473812241964413008597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056631749655952550678129 2292473812241964413008597)
              ·
                refine ⟨53729854974421040929889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2292473812241964413008597 53729854974421040929889)
                ·
                  rfl

theorem cell20_353155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_353155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353155 prefixEnd_353155 := by exact prefixLift 353155
  have htrace : WordTrace (prefixWord ++ tailWord_353155) baseStart_353155 baseEnd_353155 := by
    simpa [prefixWord, tailWord_353155, baseEnd_353155] using wordTrace_append hprefix tailTrace_353155
  have hstable : (prefixWord ++ tailWord_353155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353155).length < 2 ^ (prefixWord ++ tailWord_353155).sum := by decide
  have hdescent : baseEnd_353155 < baseStart_353155 := by decide
  rcases family_descends (prefixWord ++ tailWord_353155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353172 : List Nat := [2, 4, 2, 1, 1, 1, 3, 6]
def baseStart_353172 : Nat := 118140960795 + 353172 * 2 ^ 59
def prefixEnd_353172 : Nat := 4983230072969 + 3 ^ 40 * 353172 * 2
def baseEnd_353172 : Nat := 53732441395495539740977

theorem tailTrace_353172 : CollatzResearch.WordTrace tailWord_353172 prefixEnd_353172 53732441395495539740977 := by
  unfold tailWord_353172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6440620538262817910314885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8587494051017090547086513 6440620538262817910314885)
  ·
    refine ⟨1207616350924278358184041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6440620538262817910314885 1207616350924278358184041)
    ·
      refine ⟨905712263193208768638031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1207616350924278358184041 905712263193208768638031)
      ·
        refine ⟨1358568394789813152957047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905712263193208768638031 1358568394789813152957047)
        ·
          refine ⟨2037852592184719729435571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1358568394789813152957047 2037852592184719729435571)
          ·
            refine ⟨3056778888277079594153357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037852592184719729435571 3056778888277079594153357)
            ·
              refine ⟨1146292083103904847807509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3056778888277079594153357 1146292083103904847807509)
              ·
                refine ⟨53732441395495539740977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1146292083103904847807509 53732441395495539740977)
                ·
                  rfl

theorem cell20_353172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_353172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353172 prefixEnd_353172 := by exact prefixLift 353172
  have htrace : WordTrace (prefixWord ++ tailWord_353172) baseStart_353172 baseEnd_353172 := by
    simpa [prefixWord, tailWord_353172, baseEnd_353172] using wordTrace_append hprefix tailTrace_353172
  have hstable : (prefixWord ++ tailWord_353172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353172).length < 2 ^ (prefixWord ++ tailWord_353172).sum := by decide
  have hdescent : baseEnd_353172 < baseStart_353172 := by decide
  rcases family_descends (prefixWord ++ tailWord_353172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353178 : List Nat := [3, 1, 1, 4, 4, 1, 1, 3, 2]
def baseStart_353178 : Nat := 118140960795 + 353178 * 2 ^ 59
def prefixEnd_353178 : Nat := 4983230072969 + 3 ^ 40 * 353178 * 2
def baseEnd_353178 : Nat := 161200062749977265022907

theorem tailTrace_353178 : CollatzResearch.WordTrace tailWord_353178 prefixEnd_353178 161200062749977265022907 := by
  unfold tailWord_353178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220364978625974711337047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8587639943002599230232125 3220364978625974711337047)
  ·
    refine ⟨4830547467938962067005571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3220364978625974711337047 4830547467938962067005571)
    ·
      refine ⟨7245821201908443100508357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830547467938962067005571 7245821201908443100508357)
      ·
        refine ⟨1358591475357833081345317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7245821201908443100508357 1358591475357833081345317)
        ·
          refine ⟨254735901629593702752247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1358591475357833081345317 254735901629593702752247)
          ·
            refine ⟨382103852444390554128371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254735901629593702752247 382103852444390554128371)
            ·
              refine ⟨573155778666585831192557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382103852444390554128371 573155778666585831192557)
              ·
                refine ⟨214933416999969686697209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 573155778666585831192557 214933416999969686697209)
                ·
                  refine ⟨161200062749977265022907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214933416999969686697209 161200062749977265022907)
                  ·
                    rfl

theorem cell20_353178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_353178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353178 prefixEnd_353178 := by exact prefixLift 353178
  have htrace : WordTrace (prefixWord ++ tailWord_353178) baseStart_353178 baseEnd_353178 := by
    simpa [prefixWord, tailWord_353178, baseEnd_353178] using wordTrace_append hprefix tailTrace_353178
  have hstable : (prefixWord ++ tailWord_353178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353178).length < 2 ^ (prefixWord ++ tailWord_353178).sum := by decide
  have hdescent : baseEnd_353178 < baseStart_353178 := by decide
  rcases family_descends (prefixWord ++ tailWord_353178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353231 : List Nat := [1, 1, 2, 1, 1, 6, 2, 6]
def baseStart_353231 : Nat := 118140960795 + 353231 * 2 ^ 59
def prefixEnd_353231 : Nat := 4983230072969 + 3 ^ 40 * 353231 * 2
def baseEnd_353231 : Nat := 53741417798048212085341

theorem tailTrace_353231 : CollatzResearch.WordTrace tailWord_353231 prefixEnd_353231 53741417798048212085341 := by
  unfold tailWord_353231
  simp only [CollatzResearch.WordTrace]
  refine ⟨12883392983311888897027547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8588928655541259264685031 12883392983311888897027547)
  ·
    refine ⟨19325089474967833345541321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12883392983311888897027547 19325089474967833345541321)
    ·
      refine ⟨14493817106225875009155991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19325089474967833345541321 14493817106225875009155991)
      ·
        refine ⟨21740725659338812513733987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14493817106225875009155991 21740725659338812513733987)
        ·
          refine ⟨32611088489008218770600981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21740725659338812513733987 32611088489008218770600981)
          ·
            refine ⟨1528644772922260254871921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32611088489008218770600981 1528644772922260254871921)
            ·
              refine ⟨1146483579691695191153941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528644772922260254871921 1146483579691695191153941)
              ·
                refine ⟨53741417798048212085341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1146483579691695191153941 53741417798048212085341)
                ·
                  rfl

theorem cell20_353231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_353231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353231 prefixEnd_353231 := by exact prefixLift 353231
  have htrace : WordTrace (prefixWord ++ tailWord_353231) baseStart_353231 baseEnd_353231 := by
    simpa [prefixWord, tailWord_353231, baseEnd_353231] using wordTrace_append hprefix tailTrace_353231
  have hstable : (prefixWord ++ tailWord_353231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353231).length < 2 ^ (prefixWord ++ tailWord_353231).sum := by decide
  have hdescent : baseEnd_353231 < baseStart_353231 := by decide
  rcases family_descends (prefixWord ++ tailWord_353231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353258 : List Nat := [3, 1, 3, 1, 2, 3, 1, 4, 2]
def baseStart_353258 : Nat := 118140960795 + 353258 * 2 ^ 59
def prefixEnd_353258 : Nat := 4983230072969 + 3 ^ 40 * 353258 * 2
def baseEnd_353258 : Nat := 161236576929852542355913

theorem tailTrace_353258 : CollatzResearch.WordTrace tailWord_353258 prefixEnd_353258 161236576929852542355913 := by
  unfold tailWord_353258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221094438553518127065107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8589585169476048338840285 3221094438553518127065107)
  ·
    refine ⟨4831641657830277190597661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3221094438553518127065107 4831641657830277190597661)
    ·
      refine ⟨1811865621686353946474123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4831641657830277190597661 1811865621686353946474123)
      ·
        refine ⟨2717798432529530919711185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811865621686353946474123 2717798432529530919711185)
        ·
          refine ⟨2038348824397148189783389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2717798432529530919711185 2038348824397148189783389)
          ·
            refine ⟨764380809148930571168771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2038348824397148189783389 764380809148930571168771)
            ·
              refine ⟨1146571213723395856753157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764380809148930571168771 1146571213723395856753157)
              ·
                refine ⟨214982102573136723141217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1146571213723395856753157 214982102573136723141217)
                ·
                  refine ⟨161236576929852542355913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214982102573136723141217 161236576929852542355913)
                  ·
                    rfl

theorem cell20_353258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_353258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353258 prefixEnd_353258 := by exact prefixLift 353258
  have htrace : WordTrace (prefixWord ++ tailWord_353258) baseStart_353258 baseEnd_353258 := by
    simpa [prefixWord, tailWord_353258, baseEnd_353258] using wordTrace_append hprefix tailTrace_353258
  have hstable : (prefixWord ++ tailWord_353258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353258).length < 2 ^ (prefixWord ++ tailWord_353258).sum := by decide
  have hdescent : baseEnd_353258 < baseStart_353258 := by decide
  rcases family_descends (prefixWord ++ tailWord_353258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353317 : List Nat := [1, 3, 1, 2, 2, 2, 1, 6, 2]
def baseStart_353317 : Nat := 118140960795 + 353317 * 2 ^ 59
def prefixEnd_353317 : Nat := 4983230072969 + 3 ^ 40 * 353317 * 2
def baseEnd_353317 : Nat := 161263506137510559389005

theorem tailTrace_353317 : CollatzResearch.WordTrace tailWord_353317 prefixEnd_353317 161263506137510559389005 := by
  unfold tailWord_353317
  simp only [CollatzResearch.WordTrace]
  refine ⟨12886529661000325584658205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8591019774000217056438803 12886529661000325584658205)
  ·
    refine ⟨4832448622875122094246827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12886529661000325584658205 4832448622875122094246827)
    ·
      refine ⟨7248672934312683141370241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4832448622875122094246827 7248672934312683141370241)
      ·
        refine ⟨5436504700734512356027681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7248672934312683141370241 5436504700734512356027681)
        ·
          refine ⟨4077378525550884267020761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5436504700734512356027681 4077378525550884267020761)
          ·
            refine ⟨3058033894163163200265571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4077378525550884267020761 3058033894163163200265571)
            ·
              refine ⟨4587050841244744800398357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3058033894163163200265571 4587050841244744800398357)
              ·
                refine ⟨215018008183347412518673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4587050841244744800398357 215018008183347412518673)
                ·
                  refine ⟨161263506137510559389005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215018008183347412518673 161263506137510559389005)
                  ·
                    rfl

theorem cell20_353317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_353317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353317 prefixEnd_353317 := by exact prefixLift 353317
  have htrace : WordTrace (prefixWord ++ tailWord_353317) baseStart_353317 baseEnd_353317 := by
    simpa [prefixWord, tailWord_353317, baseEnd_353317] using wordTrace_append hprefix tailTrace_353317
  have hstable : (prefixWord ++ tailWord_353317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353317).length < 2 ^ (prefixWord ++ tailWord_353317).sum := by decide
  have hdescent : baseEnd_353317 < baseStart_353317 := by decide
  rcases family_descends (prefixWord ++ tailWord_353317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353338 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_353338 : Nat := 118140960795 + 353338 * 2 ^ 59
def prefixEnd_353338 : Nat := 4983230072969 + 3 ^ 40 * 353338 * 2
def baseEnd_353338 : Nat := 161273091109727819688919

theorem tailTrace_353338 : CollatzResearch.WordTrace tailWord_353338 prefixEnd_353338 161273091109727819688919 := by
  unfold tailWord_353338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221823898481061542793167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8591530395949497447448445 3221823898481061542793167)
  ·
    refine ⟨4832735847721592314189751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3221823898481061542793167 4832735847721592314189751)
    ·
      refine ⟨7249103771582388471284627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4832735847721592314189751 7249103771582388471284627)
      ·
        refine ⟨10873655657373582706926941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7249103771582388471284627 10873655657373582706926941)
        ·
          refine ⟨4077620871515093515097603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10873655657373582706926941 4077620871515093515097603)
          ·
            refine ⟨6116431307272640272646405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4077620871515093515097603 6116431307272640272646405)
            ·
              refine ⟨1146830870113620051121201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6116431307272640272646405 1146830870113620051121201)
              ·
                refine ⟨860123152585215038340901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146830870113620051121201 860123152585215038340901)
                ·
                  refine ⟨161273091109727819688919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 860123152585215038340901 161273091109727819688919)
                  ·
                    rfl

theorem cell20_353338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_353338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353338 prefixEnd_353338 := by exact prefixLift 353338
  have htrace : WordTrace (prefixWord ++ tailWord_353338) baseStart_353338 baseEnd_353338 := by
    simpa [prefixWord, tailWord_353338, baseEnd_353338] using wordTrace_append hprefix tailTrace_353338
  have hstable : (prefixWord ++ tailWord_353338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353338).length < 2 ^ (prefixWord ++ tailWord_353338).sum := by decide
  have hdescent : baseEnd_353338 < baseStart_353338 := by decide
  rcases family_descends (prefixWord ++ tailWord_353338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353341 : List Nat := [1, 4, 1, 3, 1, 4, 2, 4]
def baseStart_353341 : Nat := 118140960795 + 353341 * 2 ^ 59
def prefixEnd_353341 : Nat := 4983230072969 + 3 ^ 40 * 353341 * 2
def baseEnd_353341 : Nat := 53758153463824380862969

theorem tailTrace_353341 : CollatzResearch.WordTrace tailWord_353341 prefixEnd_353341 53758153463824380862969 := by
  unfold tailWord_353341
  simp only [CollatzResearch.WordTrace]
  refine ⟨12887405012913377683531877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8591603341942251789021251 12887405012913377683531877)
  ·
    refine ⟨2416388439921258315662227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12887405012913377683531877 2416388439921258315662227)
    ·
      refine ⟨3624582659881887473493341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416388439921258315662227 3624582659881887473493341)
      ·
        refine ⟨1359218497455707802560003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3624582659881887473493341 1359218497455707802560003)
        ·
          refine ⟨2038827746183561703840005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359218497455707802560003 2038827746183561703840005)
          ·
            refine ⟨382280202409417819470001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2038827746183561703840005 382280202409417819470001)
            ·
              refine ⟨286710151807063364602501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382280202409417819470001 286710151807063364602501)
              ·
                refine ⟨53758153463824380862969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286710151807063364602501 53758153463824380862969)
                ·
                  rfl

theorem cell20_353341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 4].length) (baseStart_353341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353341 prefixEnd_353341 := by exact prefixLift 353341
  have htrace : WordTrace (prefixWord ++ tailWord_353341) baseStart_353341 baseEnd_353341 := by
    simpa [prefixWord, tailWord_353341, baseEnd_353341] using wordTrace_append hprefix tailTrace_353341
  have hstable : (prefixWord ++ tailWord_353341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353341).length < 2 ^ (prefixWord ++ tailWord_353341).sum := by decide
  have hdescent : baseEnd_353341 < baseStart_353341 := by decide
  rcases family_descends (prefixWord ++ tailWord_353341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353352 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_353352 : Nat := 118140960795 + 353352 * 2 ^ 59
def prefixEnd_353352 : Nat := 4983230072969 + 3 ^ 40 * 353352 * 2
def baseEnd_353352 : Nat := 161279481091205993222195

theorem tailTrace_353352 : CollatzResearch.WordTrace tailWord_353352 prefixEnd_353352 161279481091205993222195 := by
  unfold tailWord_353352
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443903107936763281091155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8591870810582351041454873 6443903107936763281091155)
  ·
    refine ⟨9665854661905144921636733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6443903107936763281091155 9665854661905144921636733)
    ·
      refine ⟨3624695498214429345613775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9665854661905144921636733 3624695498214429345613775)
      ·
        refine ⟨5437043247321644018420663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624695498214429345613775 5437043247321644018420663)
        ·
          refine ⟨8155564870982466027630995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5437043247321644018420663 8155564870982466027630995)
          ·
            refine ⟨12233347306473699041446493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8155564870982466027630995 12233347306473699041446493)
            ·
              refine ⟨4587505239927637140542435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12233347306473699041446493 4587505239927637140542435)
              ·
                refine ⟨6881257859891455710813653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587505239927637140542435 6881257859891455710813653)
                ·
                  refine ⟨161279481091205993222195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6881257859891455710813653 161279481091205993222195)
                  ·
                    rfl

theorem cell20_353352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_353352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353352 prefixEnd_353352 := by exact prefixLift 353352
  have htrace : WordTrace (prefixWord ++ tailWord_353352) baseStart_353352 baseEnd_353352 := by
    simpa [prefixWord, tailWord_353352, baseEnd_353352] using wordTrace_append hprefix tailTrace_353352
  have hstable : (prefixWord ++ tailWord_353352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353352).length < 2 ^ (prefixWord ++ tailWord_353352).sum := by decide
  have hdescent : baseEnd_353352 < baseStart_353352 := by decide
  rcases family_descends (prefixWord ++ tailWord_353352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353362 : List Nat := [3, 2, 2, 1, 3, 3, 6]
def baseStart_353362 : Nat := 118140960795 + 353362 * 2 ^ 59
def prefixEnd_353362 : Nat := 4983230072969 + 3 ^ 40 * 353362 * 2
def baseEnd_353362 : Nat := 17920449484854489209869

theorem tailTrace_353362 : CollatzResearch.WordTrace tailWord_353362 prefixEnd_353362 17920449484854489209869 := by
  unfold tailWord_353362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222042736459324567511585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8592113963891532180030893 3222042736459324567511585)
  ·
    refine ⟨2416532052344493425633689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3222042736459324567511585 2416532052344493425633689)
    ·
      refine ⟨1812399039258370069225267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2416532052344493425633689 1812399039258370069225267)
      ·
        refine ⟨2718598558887555103837901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1812399039258370069225267 2718598558887555103837901)
        ·
          refine ⟨1019474459582833163939213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2718598558887555103837901 1019474459582833163939213)
          ·
            refine ⟨382302922343562436477205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1019474459582833163939213 382302922343562436477205)
            ·
              refine ⟨17920449484854489209869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 382302922343562436477205 17920449484854489209869)
              ·
                rfl

theorem cell20_353362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 6].length) (baseStart_353362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353362 prefixEnd_353362 := by exact prefixLift 353362
  have htrace : WordTrace (prefixWord ++ tailWord_353362) baseStart_353362 baseEnd_353362 := by
    simpa [prefixWord, tailWord_353362, baseEnd_353362] using wordTrace_append hprefix tailTrace_353362
  have hstable : (prefixWord ++ tailWord_353362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353362).length < 2 ^ (prefixWord ++ tailWord_353362).sum := by decide
  have hdescent : baseEnd_353362 < baseStart_353362 := by decide
  rcases family_descends (prefixWord ++ tailWord_353362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353383 : List Nat := [1, 1, 5, 1, 1, 3, 1, 7]
def baseStart_353383 : Nat := 118140960795 + 353383 * 2 ^ 59
def prefixEnd_353383 : Nat := 4983230072969 + 3 ^ 40 * 353383 * 2
def baseEnd_353383 : Nat := 53764543445302554396245

theorem tailTrace_353383 : CollatzResearch.WordTrace tailWord_353383 prefixEnd_353383 53764543445302554396245 := by
  unfold tailWord_353383
  simp only [CollatzResearch.WordTrace]
  refine ⟨12888936878761218856560803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8592624585840812571040535 12888936878761218856560803)
  ·
    refine ⟨19333405318141828284841205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12888936878761218856560803 19333405318141828284841205)
    ·
      refine ⟨1812506748575796401703863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19333405318141828284841205 1812506748575796401703863)
      ·
        refine ⟨2718760122863694602555795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1812506748575796401703863 2718760122863694602555795)
        ·
          refine ⟨4078140184295541903833693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718760122863694602555795 4078140184295541903833693)
          ·
            refine ⟨1529302569110828213937635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4078140184295541903833693 1529302569110828213937635)
            ·
              refine ⟨2293953853666242320906453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529302569110828213937635 2293953853666242320906453)
              ·
                refine ⟨53764543445302554396245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2293953853666242320906453 53764543445302554396245)
                ·
                  rfl

theorem cell20_353383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_353383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353383 prefixEnd_353383 := by exact prefixLift 353383
  have htrace : WordTrace (prefixWord ++ tailWord_353383) baseStart_353383 baseEnd_353383 := by
    simpa [prefixWord, tailWord_353383, baseEnd_353383] using wordTrace_append hprefix tailTrace_353383
  have hstable : (prefixWord ++ tailWord_353383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353383).length < 2 ^ (prefixWord ++ tailWord_353383).sum := by decide
  have hdescent : baseEnd_353383 < baseStart_353383 := by decide
  rcases family_descends (prefixWord ++ tailWord_353383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353386 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_353386 : Nat := 118140960795 + 353386 * 2 ^ 59
def prefixEnd_353386 : Nat := 4983230072969 + 3 ^ 40 * 353386 * 2
def baseEnd_353386 : Nat := 161294999617652986088723

theorem tailTrace_353386 : CollatzResearch.WordTrace tailWord_353386 prefixEnd_353386 161294999617652986088723 := by
  unfold tailWord_353386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222261574437587592230003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8592697531833566912613341 3222261574437587592230003)
  ·
    refine ⟨4833392361656381388345005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3222261574437587592230003 4833392361656381388345005)
    ·
      refine ⟨1812522135621143020629377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4833392361656381388345005 1812522135621143020629377)
      ·
        refine ⟨1359391601715857265472033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1812522135621143020629377 1359391601715857265472033)
        ·
          refine ⟨1019543701286892949104025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1359391601715857265472033 1019543701286892949104025)
          ·
            refine ⟨764657775965169711828019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1019543701286892949104025 764657775965169711828019)
            ·
              refine ⟨1146986663947754567742029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764657775965169711828019 1146986663947754567742029)
              ·
                refine ⟨430119998980407962903261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1146986663947754567742029 430119998980407962903261)
                ·
                  refine ⟨161294999617652986088723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430119998980407962903261 161294999617652986088723)
                  ·
                    rfl

theorem cell20_353386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_353386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353386 prefixEnd_353386 := by exact prefixLift 353386
  have htrace : WordTrace (prefixWord ++ tailWord_353386) baseStart_353386 baseEnd_353386 := by
    simpa [prefixWord, tailWord_353386, baseEnd_353386] using wordTrace_append hprefix tailTrace_353386
  have hstable : (prefixWord ++ tailWord_353386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353386).length < 2 ^ (prefixWord ++ tailWord_353386).sum := by decide
  have hdescent : baseEnd_353386 < baseStart_353386 := by decide
  rcases family_descends (prefixWord ++ tailWord_353386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353445 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 3]
def baseStart_353445 : Nat := 118140960795 + 353445 * 2 ^ 59
def prefixEnd_353445 : Nat := 4983230072969 + 3 ^ 40 * 353445 * 2
def baseEnd_353445 : Nat := 161321928825311003121815

theorem tailTrace_353445 : CollatzResearch.WordTrace tailWord_353445 prefixEnd_353445 161321928825311003121815 := by
  unfold tailWord_353445
  simp only [CollatzResearch.WordTrace]
  refine ⟨12891198204536603445317789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8594132136357735630211859 12891198204536603445317789)
  ·
    refine ⟨4834199326701226291994171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12891198204536603445317789 4834199326701226291994171)
    ·
      refine ⟨7251298990051839437991257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4834199326701226291994171 7251298990051839437991257)
      ·
        refine ⟨5438474242538879578493443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7251298990051839437991257 5438474242538879578493443)
        ·
          refine ⟨8157711363808319367740165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5438474242538879578493443 8157711363808319367740165)
          ·
            refine ⟨1529570880714059881451281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8157711363808319367740165 1529570880714059881451281)
            ·
              refine ⟨1147178160535544911088461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529570880714059881451281 1147178160535544911088461)
              ·
                refine ⟨430191810200829341658173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1147178160535544911088461 430191810200829341658173)
                ·
                  refine ⟨161321928825311003121815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430191810200829341658173 161321928825311003121815)
                  ·
                    rfl

theorem cell20_353445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_353445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353445 prefixEnd_353445 := by exact prefixLift 353445
  have htrace : WordTrace (prefixWord ++ tailWord_353445) baseStart_353445 baseEnd_353445 := by
    simpa [prefixWord, tailWord_353445, baseEnd_353445] using wordTrace_append hprefix tailTrace_353445
  have hstable : (prefixWord ++ tailWord_353445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353445).length < 2 ^ (prefixWord ++ tailWord_353445).sum := by decide
  have hdescent : baseEnd_353445 < baseStart_353445 := by decide
  rcases family_descends (prefixWord ++ tailWord_353445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353466 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_353466 : Nat := 118140960795 + 353466 * 2 ^ 59
def prefixEnd_353466 : Nat := 4983230072969 + 3 ^ 40 * 353466 * 2
def baseEnd_353466 : Nat := 161331513797528263421729

theorem tailTrace_353466 : CollatzResearch.WordTrace tailWord_353466 prefixEnd_353466 161331513797528263421729 := by
  unfold tailWord_353466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222991034365131007958063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8594642758307016021221501 3222991034365131007958063)
  ·
    refine ⟨4834486551547696511937095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3222991034365131007958063 4834486551547696511937095)
    ·
      refine ⟨7251729827321544767905643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4834486551547696511937095 7251729827321544767905643)
      ·
        refine ⟨10877594740982317151858465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7251729827321544767905643 10877594740982317151858465)
        ·
          refine ⟨8158196055736737863893849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10877594740982317151858465 8158196055736737863893849)
          ·
            refine ⟨6118647041802553397920387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8158196055736737863893849 6118647041802553397920387)
            ·
              refine ⟨9177970562703830096880581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6118647041802553397920387 9177970562703830096880581)
              ·
                refine ⟨1720869480506968143165109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9177970562703830096880581 1720869480506968143165109)
                ·
                  refine ⟨161331513797528263421729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1720869480506968143165109 161331513797528263421729)
                  ·
                    rfl

theorem cell20_353466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_353466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353466 prefixEnd_353466 := by exact prefixLift 353466
  have htrace : WordTrace (prefixWord ++ tailWord_353466) baseStart_353466 baseEnd_353466 := by
    simpa [prefixWord, tailWord_353466, baseEnd_353466] using wordTrace_append hprefix tailTrace_353466
  have hstable : (prefixWord ++ tailWord_353466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353466).length < 2 ^ (prefixWord ++ tailWord_353466).sum := by decide
  have hdescent : baseEnd_353466 < baseStart_353466 := by decide
  rcases family_descends (prefixWord ++ tailWord_353466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353469 : List Nat := [1, 4, 1, 2, 1, 1, 3, 5, 2]
def baseStart_353469 : Nat := 118140960795 + 353469 * 2 ^ 59
def prefixEnd_353469 : Nat := 4983230072969 + 3 ^ 40 * 353469 * 2
def baseEnd_353469 : Nat := 161332883079273586321717

theorem tailTrace_353469 : CollatzResearch.WordTrace tailWord_353469 prefixEnd_353469 161332883079273586321717 := by
  unfold tailWord_353469
  simp only [CollatzResearch.WordTrace]
  refine ⟨12892073556449655544191461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8594715704299770362794307 12892073556449655544191461)
  ·
    refine ⟨2417263791834310414535899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12892073556449655544191461 2417263791834310414535899)
    ·
      refine ⟨3625895687751465621803849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2417263791834310414535899 3625895687751465621803849)
      ·
        refine ⟨2719421765813599216352887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3625895687751465621803849 2719421765813599216352887)
        ·
          refine ⟨4079132648720398824529331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2719421765813599216352887 4079132648720398824529331)
          ·
            refine ⟨6118698973080598236793997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079132648720398824529331 6118698973080598236793997)
            ·
              refine ⟨2294512114905224338797749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6118698973080598236793997 2294512114905224338797749)
              ·
                refine ⟨215110510772364781762289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2294512114905224338797749 215110510772364781762289)
                ·
                  refine ⟨161332883079273586321717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215110510772364781762289 161332883079273586321717)
                  ·
                    rfl

theorem cell20_353469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_353469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353469 prefixEnd_353469 := by exact prefixLift 353469
  have htrace : WordTrace (prefixWord ++ tailWord_353469) baseStart_353469 baseEnd_353469 := by
    simpa [prefixWord, tailWord_353469, baseEnd_353469] using wordTrace_append hprefix tailTrace_353469
  have hstable : (prefixWord ++ tailWord_353469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353469).length < 2 ^ (prefixWord ++ tailWord_353469).sum := by decide
  have hdescent : baseEnd_353469 < baseStart_353469 := by decide
  rcases family_descends (prefixWord ++ tailWord_353469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353476 : List Nat := [2, 3, 3, 1, 3, 1, 7]
def baseStart_353476 : Nat := 118140960795 + 353476 * 2 ^ 59
def prefixEnd_353476 : Nat := 4983230072969 + 3 ^ 40 * 353476 * 2
def baseEnd_353476 : Nat := 17926230896668074787595

theorem tailTrace_353476 : CollatzResearch.WordTrace tailWord_353476 prefixEnd_353476 17926230896668074787595 := by
  unfold tailWord_353476
  simp only [CollatzResearch.WordTrace]
  refine ⟨6446164433712147869848141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8594885911616197159797521 6446164433712147869848141)
  ·
    refine ⟨2417311662642055451193053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6446164433712147869848141 2417311662642055451193053)
    ·
      refine ⟨906491873490770794197395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2417311662642055451193053 906491873490770794197395)
      ·
        refine ⟨1359737810236156191296093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906491873490770794197395 1359737810236156191296093)
        ·
          refine ⟨509901678838558571736035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1359737810236156191296093 509901678838558571736035)
          ·
            refine ⟨764852518257837857604053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509901678838558571736035 764852518257837857604053)
            ·
              refine ⟨17926230896668074787595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 764852518257837857604053 17926230896668074787595)
              ·
                rfl

theorem cell20_353476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 7].length) (baseStart_353476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353476 prefixEnd_353476 := by exact prefixLift 353476
  have htrace : WordTrace (prefixWord ++ tailWord_353476) baseStart_353476 baseEnd_353476 := by
    simpa [prefixWord, tailWord_353476, baseEnd_353476] using wordTrace_append hprefix tailTrace_353476
  have hstable : (prefixWord ++ tailWord_353476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353476).length < 2 ^ (prefixWord ++ tailWord_353476).sum := by decide
  have hdescent : baseEnd_353476 < baseStart_353476 := by decide
  rcases family_descends (prefixWord ++ tailWord_353476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353514 : List Nat := [3, 1, 3, 1, 1, 3, 4, 4]
def baseStart_353514 : Nat := 118140960795 + 353514 * 2 ^ 59
def prefixEnd_353514 : Nat := 4983230072969 + 3 ^ 40 * 353514 * 2
def baseEnd_353514 : Nat := 53784474101817809940511

theorem tailTrace_353514 : CollatzResearch.WordTrace tailWord_353514 prefixEnd_353514 53784474101817809940511 := by
  unfold tailWord_353514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223428710321657057394899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8595809894191085486386397 3223428710321657057394899)
  ·
    refine ⟨4835143065482485586092349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3223428710321657057394899 4835143065482485586092349)
    ·
      refine ⟨1813178649555932094784631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4835143065482485586092349 1813178649555932094784631)
      ·
        refine ⟨2719767974333898142176947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1813178649555932094784631 2719767974333898142176947)
        ·
          refine ⟨4079651961500847213265421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2719767974333898142176947 4079651961500847213265421)
          ·
            refine ⟨1529869485562817704974533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4079651961500847213265421 1529869485562817704974533)
            ·
              refine ⟨286850528543028319682725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1529869485562817704974533 286850528543028319682725)
              ·
                refine ⟨53784474101817809940511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286850528543028319682725 53784474101817809940511)
                ·
                  rfl

theorem cell20_353514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_353514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353514 prefixEnd_353514 := by exact prefixLift 353514
  have htrace : WordTrace (prefixWord ++ tailWord_353514) baseStart_353514 baseEnd_353514 := by
    simpa [prefixWord, tailWord_353514, baseEnd_353514] using wordTrace_append hprefix tailTrace_353514
  have hstable : (prefixWord ++ tailWord_353514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353514).length < 2 ^ (prefixWord ++ tailWord_353514).sum := by decide
  have hdescent : baseEnd_353514 < baseStart_353514 := by decide
  rcases family_descends (prefixWord ++ tailWord_353514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353535 : List Nat := [1, 1, 2, 2, 1, 7, 6]
def baseStart_353535 : Nat := 118140960795 + 353535 * 2 ^ 59
def prefixEnd_353535 : Nat := 4983230072969 + 3 ^ 40 * 353535 * 2
def baseEnd_353535 : Nat := 17929223030852298902383

theorem tailTrace_353535 : CollatzResearch.WordTrace tailWord_353535 prefixEnd_353535 17929223030852298902383 := by
  unfold tailWord_353535
  simp only [CollatzResearch.WordTrace]
  refine ⟨12894480774210548816094059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8596320516140365877396039 12894480774210548816094059)
  ·
    refine ⟨19341721161315823224141089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12894480774210548816094059 19341721161315823224141089)
    ·
      refine ⟨14506290870986867418105817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19341721161315823224141089 14506290870986867418105817)
      ·
        refine ⟨10879718153240150563579363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14506290870986867418105817 10879718153240150563579363)
        ·
          refine ⟨16319577229860225845369045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10879718153240150563579363 16319577229860225845369045)
          ·
            refine ⟨382490091324849043250837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16319577229860225845369045 382490091324849043250837)
            ·
              refine ⟨17929223030852298902383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 382490091324849043250837 17929223030852298902383)
              ·
                rfl

theorem cell20_353535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 6].length) (baseStart_353535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353535 prefixEnd_353535 := by exact prefixLift 353535
  have htrace : WordTrace (prefixWord ++ tailWord_353535) baseStart_353535 baseEnd_353535 := by
    simpa [prefixWord, tailWord_353535, baseEnd_353535] using wordTrace_append hprefix tailTrace_353535
  have hstable : (prefixWord ++ tailWord_353535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353535).length < 2 ^ (prefixWord ++ tailWord_353535).sum := by decide
  have hdescent : baseEnd_353535 < baseStart_353535 := by decide
  rcases family_descends (prefixWord ++ tailWord_353535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353559 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 3]
def baseStart_353559 : Nat := 118140960795 + 353559 * 2 ^ 59
def prefixEnd_353559 : Nat := 4983230072969 + 3 ^ 40 * 353559 * 2
def baseEnd_353559 : Nat := 161373961531633273321349

theorem tailTrace_353559 : CollatzResearch.WordTrace tailWord_353559 prefixEnd_353559 161373961531633273321349 := by
  unfold tailWord_353559
  simp only [CollatzResearch.WordTrace]
  refine ⟨12895356126123600914967731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8596904084082400609978487 12895356126123600914967731)
  ·
    refine ⟨19343034189185401372451597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12895356126123600914967731 19343034189185401372451597)
    ·
      refine ⟨7253637820944525514669349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19343034189185401372451597 7253637820944525514669349)
      ·
        refine ⟨1360057091427098534000503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7253637820944525514669349 1360057091427098534000503)
        ·
          refine ⟨2040085637140647801000755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360057091427098534000503 2040085637140647801000755)
          ·
            refine ⟨3060128455710971701501133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040085637140647801000755 3060128455710971701501133)
            ·
              refine ⟨1147548170891614388062925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3060128455710971701501133 1147548170891614388062925)
              ·
                refine ⟨430330564084355395523597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1147548170891614388062925 430330564084355395523597)
                ·
                  refine ⟨161373961531633273321349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430330564084355395523597 161373961531633273321349)
                  ·
                    rfl

theorem cell20_353559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 3].length) (baseStart_353559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353559 prefixEnd_353559 := by exact prefixLift 353559
  have htrace : WordTrace (prefixWord ++ tailWord_353559) baseStart_353559 baseEnd_353559 := by
    simpa [prefixWord, tailWord_353559, baseEnd_353559] using wordTrace_append hprefix tailTrace_353559
  have hstable : (prefixWord ++ tailWord_353559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353559).length < 2 ^ (prefixWord ++ tailWord_353559).sum := by decide
  have hdescent : baseEnd_353559 < baseStart_353559 := by decide
  rcases family_descends (prefixWord ++ tailWord_353559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353573 : List Nat := [1, 3, 1, 2, 4, 1, 2, 6]
def baseStart_353573 : Nat := 118140960795 + 353573 * 2 ^ 59
def prefixEnd_353573 : Nat := 4983230072969 + 3 ^ 40 * 353573 * 2
def baseEnd_353573 : Nat := 53793450504370482284875

theorem tailTrace_353573 : CollatzResearch.WordTrace tailWord_353573 prefixEnd_353573 53793450504370482284875 := by
  unfold tailWord_353573
  simp only [CollatzResearch.WordTrace]
  refine ⟨12895866748072881305977373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8597244498715254203984915 12895866748072881305977373)
  ·
    refine ⟨4835950030527330489741515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12895866748072881305977373 4835950030527330489741515)
    ·
      refine ⟨7253925045790995734612273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835950030527330489741515 7253925045790995734612273)
      ·
        refine ⟨5440443784343246800959205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7253925045790995734612273 5440443784343246800959205)
        ·
          refine ⟨1020083209564358775179851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5440443784343246800959205 1020083209564358775179851)
          ·
            refine ⟨1530124814346538162769777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020083209564358775179851 1530124814346538162769777)
            ·
              refine ⟨1147593610759903622077333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530124814346538162769777 1147593610759903622077333)
              ·
                refine ⟨53793450504370482284875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1147593610759903622077333 53793450504370482284875)
                ·
                  rfl

theorem cell20_353573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_353573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353573 prefixEnd_353573 := by exact prefixLift 353573
  have htrace : WordTrace (prefixWord ++ tailWord_353573) baseStart_353573 baseEnd_353573 := by
    simpa [prefixWord, tailWord_353573, baseEnd_353573] using wordTrace_append hprefix tailTrace_353573
  have hstable : (prefixWord ++ tailWord_353573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353573).length < 2 ^ (prefixWord ++ tailWord_353573).sum := by decide
  have hdescent : baseEnd_353573 < baseStart_353573 := by decide
  rcases family_descends (prefixWord ++ tailWord_353573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353590 : List Nat := [5, 1, 2, 3, 9]
def baseStart_353590 : Nat := 118140960795 + 353590 * 2 ^ 59
def prefixEnd_353590 : Nat := 4983230072969 + 3 ^ 40 * 353590 * 2
def baseEnd_353590 : Nat := 1992445812053517818369

theorem tailTrace_353590 : CollatzResearch.WordTrace tailWord_353590 prefixEnd_353590 1992445812053517818369 := by
  unfold tailWord_353590
  simp only [CollatzResearch.WordTrace]
  refine ⟨806030424313205825584139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8597657859340862139564149 806030424313205825584139)
  ·
    refine ⟨1209045636469808738376209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 806030424313205825584139 1209045636469808738376209)
    ·
      refine ⟨906784227352356553782157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1209045636469808738376209 906784227352356553782157)
      ·
        refine ⟨340044085257133707668309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 906784227352356553782157 340044085257133707668309)
        ·
          refine ⟨1992445812053517818369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 340044085257133707668309 1992445812053517818369)
          ·
            rfl

theorem cell20_353590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 9].length) (baseStart_353590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353590 prefixEnd_353590 := by exact prefixLift 353590
  have htrace : WordTrace (prefixWord ++ tailWord_353590) baseStart_353590 baseEnd_353590 := by
    simpa [prefixWord, tailWord_353590, baseEnd_353590] using wordTrace_append hprefix tailTrace_353590
  have hstable : (prefixWord ++ tailWord_353590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353590).length < 2 ^ (prefixWord ++ tailWord_353590).sum := by decide
  have hdescent : baseEnd_353590 < baseStart_353590 := by decide
  rcases family_descends (prefixWord ++ tailWord_353590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353618 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_353618 : Nat := 118140960795 + 353618 * 2 ^ 59
def prefixEnd_353618 : Nat := 4983230072969 + 3 ^ 40 * 353618 * 2
def baseEnd_353618 : Nat := 161400890739291290354441

theorem tailTrace_353618 : CollatzResearch.WordTrace tailWord_353618 prefixEnd_353618 161400890739291290354441 := by
  unfold tailWord_353618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3224377008227463497841377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8598338688606569327577005 3224377008227463497841377)
  ·
    refine ⟨2418282756170597623381033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3224377008227463497841377 2418282756170597623381033)
    ·
      refine ⟨1813712067127948217535775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2418282756170597623381033 1813712067127948217535775)
      ·
        refine ⟨2720568100691922326303663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1813712067127948217535775 2720568100691922326303663)
        ·
          refine ⟨4080852151037883489455495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2720568100691922326303663 4080852151037883489455495)
          ·
            refine ⟨6121278226556825234183243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080852151037883489455495 6121278226556825234183243)
            ·
              refine ⟨9181917339835237851274865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6121278226556825234183243 9181917339835237851274865)
              ·
                refine ⟨6886438004876428388456149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9181917339835237851274865 6886438004876428388456149)
                ·
                  refine ⟨161400890739291290354441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6886438004876428388456149 161400890739291290354441)
                  ·
                    rfl

theorem cell20_353618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_353618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353618 prefixEnd_353618 := by exact prefixLift 353618
  have htrace : WordTrace (prefixWord ++ tailWord_353618) baseStart_353618 baseEnd_353618 := by
    simpa [prefixWord, tailWord_353618, baseEnd_353618] using wordTrace_append hprefix tailTrace_353618
  have hstable : (prefixWord ++ tailWord_353618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353618).length < 2 ^ (prefixWord ++ tailWord_353618).sum := by decide
  have hdescent : baseEnd_353618 < baseStart_353618 := by decide
  rcases family_descends (prefixWord ++ tailWord_353618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353625 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_353625 : Nat := 118140960795 + 353625 * 2 ^ 59
def prefixEnd_353625 : Nat := 4983230072969 + 3 ^ 40 * 353625 * 2
def baseEnd_353625 : Nat := 161404085730030377121079

theorem tailTrace_353625 : CollatzResearch.WordTrace tailWord_353625 prefixEnd_353625 161404085730030377121079 := by
  unfold tailWord_353625
  simp only [CollatzResearch.WordTrace]
  refine ⟨12897763343884494186870329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8598508895922996124580219 12897763343884494186870329)
  ·
    refine ⟨9673322507913370640152747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12897763343884494186870329 9673322507913370640152747)
    ·
      refine ⟨14509983761870055960229121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9673322507913370640152747 14509983761870055960229121)
      ·
        refine ⟨10882487821402541970171841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14509983761870055960229121 10882487821402541970171841)
        ·
          refine ⟨8161865866051906477628881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10882487821402541970171841 8161865866051906477628881)
          ·
            refine ⟨6121399399538929858221661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8161865866051906477628881 6121399399538929858221661)
            ·
              refine ⟨2295524774827098696833123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6121399399538929858221661 2295524774827098696833123)
              ·
                refine ⟨3443287162240648045249685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295524774827098696833123 3443287162240648045249685)
                ·
                  refine ⟨161404085730030377121079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3443287162240648045249685 161404085730030377121079)
                  ·
                    rfl

theorem cell20_353625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_353625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353625 prefixEnd_353625 := by exact prefixLift 353625
  have htrace : WordTrace (prefixWord ++ tailWord_353625) baseStart_353625 baseEnd_353625 := by
    simpa [prefixWord, tailWord_353625, baseEnd_353625] using wordTrace_append hprefix tailTrace_353625
  have hstable : (prefixWord ++ tailWord_353625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353625).length < 2 ^ (prefixWord ++ tailWord_353625).sum := by decide
  have hdescent : baseEnd_353625 < baseStart_353625 := by decide
  rcases family_descends (prefixWord ++ tailWord_353625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353708 : List Nat := [2, 2, 1, 1, 1, 1, 12]
def baseStart_353708 : Nat := 118140960795 + 353708 * 2 ^ 59
def prefixEnd_353708 : Nat := 4983230072969 + 3 ^ 40 * 353708 * 2
def baseEnd_353708 : Nat := 17937996576850108594897

theorem tailTrace_353708 : CollatzResearch.WordTrace tailWord_353708 prefixEnd_353708 17937996576850108594897 := by
  unfold tailWord_353708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6450395301291899681070889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8600527068389199574761185 6450395301291899681070889)
  ·
    refine ⟨4837796475968924760803167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6450395301291899681070889 4837796475968924760803167)
    ·
      refine ⟨7256694713953387141204751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4837796475968924760803167 7256694713953387141204751)
      ·
        refine ⟨10885042070930080711807127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7256694713953387141204751 10885042070930080711807127)
        ·
          refine ⟨16327563106395121067710691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10885042070930080711807127 16327563106395121067710691)
          ·
            refine ⟨24491344659592681601566037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16327563106395121067710691 24491344659592681601566037)
            ·
              refine ⟨17937996576850108594897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 24491344659592681601566037 17937996576850108594897)
              ·
                rfl

theorem cell20_353708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 12].length) (baseStart_353708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353708 prefixEnd_353708 := by exact prefixLift 353708
  have htrace : WordTrace (prefixWord ++ tailWord_353708) baseStart_353708 baseEnd_353708 := by
    simpa [prefixWord, tailWord_353708, baseEnd_353708] using wordTrace_append hprefix tailTrace_353708
  have hstable : (prefixWord ++ tailWord_353708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353708).length < 2 ^ (prefixWord ++ tailWord_353708).sum := by decide
  have hdescent : baseEnd_353708 < baseStart_353708 := by decide
  rcases family_descends (prefixWord ++ tailWord_353708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353724 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 3]
def baseStart_353724 : Nat := 118140960795 + 353724 * 2 ^ 59
def prefixEnd_353724 : Nat := 4983230072969 + 3 ^ 40 * 353724 * 2
def baseEnd_353724 : Nat := 161449272027626032820675

theorem tailTrace_353724 : CollatzResearch.WordTrace tailWord_353724 prefixEnd_353724 161449272027626032820675 := by
  unfold tailWord_353724
  simp only [CollatzResearch.WordTrace]
  refine ⟨6450687085262917047362113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8600916113683889396482817 6450687085262917047362113)
  ·
    refine ⟨4838015313947187785521585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6450687085262917047362113 4838015313947187785521585)
    ·
      refine ⟨3628511485460390839141189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4838015313947187785521585 3628511485460390839141189)
      ·
        refine ⟨680345903523823282338973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3628511485460390839141189 680345903523823282338973)
        ·
          refine ⟨255129713821433730877115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 680345903523823282338973 255129713821433730877115)
          ·
            refine ⟨382694570732150596315673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255129713821433730877115 382694570732150596315673)
            ·
              refine ⟨287020928049112947236755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382694570732150596315673 287020928049112947236755)
              ·
                refine ⟨430531392073669420855133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287020928049112947236755 430531392073669420855133)
                ·
                  refine ⟨161449272027626032820675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430531392073669420855133 161449272027626032820675)
                  ·
                    rfl

theorem cell20_353724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_353724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353724 prefixEnd_353724 := by exact prefixLift 353724
  have htrace : WordTrace (prefixWord ++ tailWord_353724) baseStart_353724 baseEnd_353724 := by
    simpa [prefixWord, tailWord_353724, baseEnd_353724] using wordTrace_append hprefix tailTrace_353724
  have hstable : (prefixWord ++ tailWord_353724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353724).length < 2 ^ (prefixWord ++ tailWord_353724).sum := by decide
  have hdescent : baseEnd_353724 < baseStart_353724 := by decide
  rcases family_descends (prefixWord ++ tailWord_353724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353725 : List Nat := [1, 4, 1, 2, 2, 1, 4, 5]
def baseStart_353725 : Nat := 118140960795 + 353725 * 2 ^ 59
def prefixEnd_353725 : Nat := 4983230072969 + 3 ^ 40 * 353725 * 2
def baseEnd_353725 : Nat := 53816576151624824595779

theorem tailTrace_353725 : CollatzResearch.WordTrace tailWord_353725 prefixEnd_353725 53816576151624824595779 := by
  unfold tailWord_353725
  simp only [CollatzResearch.WordTrace]
  refine ⟨12901410643522211265510629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8600940429014807510340419 12901410643522211265510629)
  ·
    refine ⟨2419014495660414612283243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12901410643522211265510629 2419014495660414612283243)
    ·
      refine ⟨3628521743490621918424865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419014495660414612283243 3628521743490621918424865)
      ·
        refine ⟨2721391307617966438818649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3628521743490621918424865 2721391307617966438818649)
        ·
          refine ⟨2041043480713474829113987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2721391307617966438818649 2041043480713474829113987)
          ·
            refine ⟨3061565221070212243670981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041043480713474829113987 3061565221070212243670981)
            ·
              refine ⟨574043478950664795688309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3061565221070212243670981 574043478950664795688309)
              ·
                refine ⟨53816576151624824595779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 574043478950664795688309 53816576151624824595779)
                ·
                  rfl

theorem cell20_353725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_353725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353725 prefixEnd_353725 := by exact prefixLift 353725
  have htrace : WordTrace (prefixWord ++ tailWord_353725) baseStart_353725 baseEnd_353725 := by
    simpa [prefixWord, tailWord_353725, baseEnd_353725] using wordTrace_append hprefix tailTrace_353725
  have hstable : (prefixWord ++ tailWord_353725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353725).length < 2 ^ (prefixWord ++ tailWord_353725).sum := by decide
  have hdescent : baseEnd_353725 < baseStart_353725 := by decide
  rcases family_descends (prefixWord ++ tailWord_353725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353739 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_353739 : Nat := 118140960795 + 353739 * 2 ^ 59
def prefixEnd_353739 : Nat := 4983230072969 + 3 ^ 40 * 353739 * 2
def baseEnd_353739 : Nat := 161456118436352647320613

theorem tailTrace_353739 : CollatzResearch.WordTrace tailWord_353739 prefixEnd_353739 161456118436352647320613 := by
  unfold tailWord_353739
  simp only [CollatzResearch.WordTrace]
  refine ⟨12901921265471491656520271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8601280843647661104346847 12901921265471491656520271)
  ·
    refine ⟨19352881898207237484780407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12901921265471491656520271 19352881898207237484780407)
    ·
      refine ⟨29029322847310856227170611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19352881898207237484780407 29029322847310856227170611)
      ·
        refine ⟨43543984270966284340755917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29029322847310856227170611 43543984270966284340755917)
        ·
          refine ⟨16328994101612356627783469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43543984270966284340755917 16328994101612356627783469)
          ·
            refine ⟨6123372788104633735418801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16328994101612356627783469 6123372788104633735418801)
            ·
              refine ⟨4592529591078475301564101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6123372788104633735418801 4592529591078475301564101)
              ·
                refine ⟨861099298327214119043269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4592529591078475301564101 861099298327214119043269)
                ·
                  refine ⟨161456118436352647320613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861099298327214119043269 161456118436352647320613)
                  ·
                    rfl

theorem cell20_353739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_353739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353739 prefixEnd_353739 := by exact prefixLift 353739
  have htrace : WordTrace (prefixWord ++ tailWord_353739) baseStart_353739 baseEnd_353739 := by
    simpa [prefixWord, tailWord_353739, baseEnd_353739] using wordTrace_append hprefix tailTrace_353739
  have hstable : (prefixWord ++ tailWord_353739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353739).length < 2 ^ (prefixWord ++ tailWord_353739).sum := by decide
  have hdescent : baseEnd_353739 < baseStart_353739 := by decide
  rcases family_descends (prefixWord ++ tailWord_353739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353790 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_353790 : Nat := 118140960795 + 353790 * 2 ^ 59
def prefixEnd_353790 : Nat := 4983230072969 + 3 ^ 40 * 353790 * 2
def baseEnd_353790 : Nat := 161479396226023136620405

theorem tailTrace_353790 : CollatzResearch.WordTrace tailWord_353790 prefixEnd_353790 161479396226023136620405 := by
  unfold tailWord_353790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612972673535840920828353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8602520925524484911084549 1612972673535840920828353)
  ·
    refine ⟨1209729505151880690621265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1612972673535840920828353 1209729505151880690621265)
    ·
      refine ⟨907297128863910517965949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1209729505151880690621265 907297128863910517965949)
      ·
        refine ⟨340236423323966444237231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 907297128863910517965949 340236423323966444237231)
        ·
          refine ⟨510354634985949666355847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340236423323966444237231 510354634985949666355847)
          ·
            refine ⟨765531952478924499533771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510354634985949666355847 765531952478924499533771)
            ·
              refine ⟨1148297928718386749300657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765531952478924499533771 1148297928718386749300657)
              ·
                refine ⟨861223446538790061975493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148297928718386749300657 861223446538790061975493)
                ·
                  refine ⟨161479396226023136620405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861223446538790061975493 161479396226023136620405)
                  ·
                    rfl

theorem cell20_353790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_353790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353790 prefixEnd_353790 := by exact prefixLift 353790
  have htrace : WordTrace (prefixWord ++ tailWord_353790) baseStart_353790 baseEnd_353790 := by
    simpa [prefixWord, tailWord_353790, baseEnd_353790] using wordTrace_append hprefix tailTrace_353790
  have hstable : (prefixWord ++ tailWord_353790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353790).length < 2 ^ (prefixWord ++ tailWord_353790).sum := by decide
  have hdescent : baseEnd_353790 < baseStart_353790 := by decide
  rcases family_descends (prefixWord ++ tailWord_353790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353801 : List Nat := [1, 2, 1, 1, 3, 1, 7, 4]
def baseStart_353801 : Nat := 118140960795 + 353801 * 2 ^ 59
def prefixEnd_353801 : Nat := 4983230072969 + 3 ^ 40 * 353801 * 2
def baseEnd_353801 : Nat := 53828138975251995751231

theorem tailTrace_353801 : CollatzResearch.WordTrace tailWord_353801 prefixEnd_353801 53828138975251995751231 := by
  unfold tailWord_353801
  simp only [CollatzResearch.WordTrace]
  refine ⟨12904182591246876245277257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8602788394164584163518171 12904182591246876245277257)
  ·
    refine ⟨9678136943435157183957943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12904182591246876245277257 9678136943435157183957943)
    ·
      refine ⟨14517205415152735775936915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9678136943435157183957943 14517205415152735775936915)
      ·
        refine ⟨21775808122729103663905373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14517205415152735775936915 21775808122729103663905373)
        ·
          refine ⟨8165928046023413873964515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21775808122729103663905373 8165928046023413873964515)
          ·
            refine ⟨12248892069035120810946773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8165928046023413873964515 12248892069035120810946773)
            ·
              refine ⟨287083407868010644006565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12248892069035120810946773 287083407868010644006565)
              ·
                refine ⟨53828138975251995751231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287083407868010644006565 53828138975251995751231)
                ·
                  rfl

theorem cell20_353801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 4].length) (baseStart_353801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353801 prefixEnd_353801 := by exact prefixLift 353801
  have htrace : WordTrace (prefixWord ++ tailWord_353801) baseStart_353801 baseEnd_353801 := by
    simpa [prefixWord, tailWord_353801, baseEnd_353801] using wordTrace_append hprefix tailTrace_353801
  have hstable : (prefixWord ++ tailWord_353801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353801).length < 2 ^ (prefixWord ++ tailWord_353801).sum := by decide
  have hdescent : baseEnd_353801 < baseStart_353801 := by decide
  rcases family_descends (prefixWord ++ tailWord_353801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353811 : List Nat := [1, 1, 1, 2, 1, 7, 2, 3, 2]
def baseStart_353811 : Nat := 118140960795 + 353811 * 2 ^ 59
def prefixEnd_353811 : Nat := 4983230072969 + 3 ^ 40 * 353811 * 2
def baseEnd_353811 : Nat := 161488981198240396920319

theorem tailTrace_353811 : CollatzResearch.WordTrace tailWord_353811 prefixEnd_353811 161488981198240396920319 := by
  unfold tailWord_353811
  simp only [CollatzResearch.WordTrace]
  refine ⟨12904547321210647953141287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8603031547473765302094191 12904547321210647953141287)
  ·
    refine ⟨19356820981815971929711931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12904547321210647953141287 19356820981815971929711931)
    ·
      refine ⟨29035231472723957894567897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19356820981815971929711931 29035231472723957894567897)
      ·
        refine ⟨21776423604542968420925923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29035231472723957894567897 21776423604542968420925923)
        ·
          refine ⟨32664635406814452631388885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21776423604542968420925923 32664635406814452631388885)
          ·
            refine ⟨765577392347213733548177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 32664635406814452631388885 765577392347213733548177)
            ·
              refine ⟨574183044260410300161133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765577392347213733548177 574183044260410300161133)
              ·
                refine ⟨215318641597653862560425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 574183044260410300161133 215318641597653862560425)
                ·
                  refine ⟨161488981198240396920319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215318641597653862560425 161488981198240396920319)
                  ·
                    rfl

theorem cell20_353811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 2].length) (baseStart_353811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353811 prefixEnd_353811 := by exact prefixLift 353811
  have htrace : WordTrace (prefixWord ++ tailWord_353811) baseStart_353811 baseEnd_353811 := by
    simpa [prefixWord, tailWord_353811, baseEnd_353811] using wordTrace_append hprefix tailTrace_353811
  have hstable : (prefixWord ++ tailWord_353811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353811).length < 2 ^ (prefixWord ++ tailWord_353811).sum := by decide
  have hdescent : baseEnd_353811 < baseStart_353811 := by decide
  rcases family_descends (prefixWord ++ tailWord_353811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353825 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 3]
def baseStart_353825 : Nat := 118140960795 + 353825 * 2 ^ 59
def prefixEnd_353825 : Nat := 4983230072969 + 3 ^ 40 * 353825 * 2
def baseEnd_353825 : Nat := 161495371179718570453595

theorem tailTrace_353825 : CollatzResearch.WordTrace tailWord_353825 prefixEnd_353825 161495371179718570453595 := by
  unfold tailWord_353825
  simp only [CollatzResearch.WordTrace]
  refine ⟨12905057943159928344150929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8603371962106618896100619 12905057943159928344150929)
  ·
    refine ⟨9678793457369946258113197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12905057943159928344150929 9678793457369946258113197)
    ·
      refine ⟨3629547546513729846792449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9678793457369946258113197 3629547546513729846792449)
      ·
        refine ⟨2722160659885297385094337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3629547546513729846792449 2722160659885297385094337)
        ·
          refine ⟨2041620494913973038820753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2722160659885297385094337 2041620494913973038820753)
          ·
            refine ⟨1531215371185479779115565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041620494913973038820753 1531215371185479779115565)
            ·
              refine ⟨574205764194554917168337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1531215371185479779115565 574205764194554917168337)
              ·
                refine ⟨430654323145916187876253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574205764194554917168337 430654323145916187876253)
                ·
                  refine ⟨161495371179718570453595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430654323145916187876253 161495371179718570453595)
                  ·
                    rfl

theorem cell20_353825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_353825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353825 prefixEnd_353825 := by exact prefixLift 353825
  have htrace : WordTrace (prefixWord ++ tailWord_353825) baseStart_353825 baseEnd_353825 := by
    simpa [prefixWord, tailWord_353825, baseEnd_353825] using wordTrace_append hprefix tailTrace_353825
  have hstable : (prefixWord ++ tailWord_353825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353825).length < 2 ^ (prefixWord ++ tailWord_353825).sum := by decide
  have hdescent : baseEnd_353825 < baseStart_353825 := by decide
  rcases family_descends (prefixWord ++ tailWord_353825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353862 : List Nat := [6, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_353862 : Nat := 118140960795 + 353862 * 2 ^ 59
def prefixEnd_353862 : Nat := 4983230072969 + 3 ^ 40 * 353862 * 2
def baseEnd_353862 : Nat := 161512258987910886220111

theorem tailTrace_353862 : CollatzResearch.WordTrace tailWord_353862 prefixEnd_353862 161512258987910886220111 := by
  unfold tailWord_353862
  simp only [CollatzResearch.WordTrace]
  refine ⟨403325232625808864476495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8604271629350589108831893 403325232625808864476495)
  ·
    refine ⟨604987848938713296714743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403325232625808864476495 604987848938713296714743)
    ·
      refine ⟨907481773408069945072115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 604987848938713296714743 907481773408069945072115)
      ·
        refine ⟨1361222660112104917608173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907481773408069945072115 1361222660112104917608173)
        ·
          refine ⟨510458497542039344103065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1361222660112104917608173 510458497542039344103065)
          ·
            refine ⟨382843873156529508077299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510458497542039344103065 382843873156529508077299)
            ·
              refine ⟨574265809734794262115949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382843873156529508077299 574265809734794262115949)
              ·
                refine ⟨215349678650547848293481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 574265809734794262115949 215349678650547848293481)
                ·
                  refine ⟨161512258987910886220111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215349678650547848293481 161512258987910886220111)
                  ·
                    rfl

theorem cell20_353862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_353862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353862 prefixEnd_353862 := by exact prefixLift 353862
  have htrace : WordTrace (prefixWord ++ tailWord_353862) baseStart_353862 baseEnd_353862 := by
    simpa [prefixWord, tailWord_353862, baseEnd_353862] using wordTrace_append hprefix tailTrace_353862
  have hstable : (prefixWord ++ tailWord_353862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353862).length < 2 ^ (prefixWord ++ tailWord_353862).sum := by decide
  have hdescent : baseEnd_353862 < baseStart_353862 := by decide
  rcases family_descends (prefixWord ++ tailWord_353862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353938 : List Nat := [3, 2, 3, 1, 4, 1, 2, 2, 2]
def baseStart_353938 : Nat := 118140960795 + 353938 * 2 ^ 59
def prefixEnd_353938 : Nat := 4983230072969 + 3 ^ 40 * 353938 * 2
def baseEnd_353938 : Nat := 161546947458792399686467

theorem tailTrace_353938 : CollatzResearch.WordTrace tailWord_353938 prefixEnd_353938 161546947458792399686467 := by
  unfold tailWord_353938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227294847937637160753617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8606119594500365762009645 3227294847937637160753617)
  ·
    refine ⟨2420471135953227870565213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3227294847937637160753617 2420471135953227870565213)
    ·
      refine ⟨907676675982460451461955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2420471135953227870565213 907676675982460451461955)
      ·
        refine ⟨1361515013973690677192933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907676675982460451461955 1361515013973690677192933)
        ·
          refine ⟨255284065120067001973675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1361515013973690677192933 255284065120067001973675)
          ·
            refine ⟨382926097680100502960513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255284065120067001973675 382926097680100502960513)
            ·
              refine ⟨287194573260075377220385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382926097680100502960513 287194573260075377220385)
              ·
                refine ⟨215395929945056532915289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287194573260075377220385 215395929945056532915289)
                ·
                  refine ⟨161546947458792399686467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215395929945056532915289 161546947458792399686467)
                  ·
                    rfl

theorem cell20_353938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_353938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353938 prefixEnd_353938 := by exact prefixLift 353938
  have htrace : WordTrace (prefixWord ++ tailWord_353938) baseStart_353938 baseEnd_353938 := by
    simpa [prefixWord, tailWord_353938, baseEnd_353938] using wordTrace_append hprefix tailTrace_353938
  have hstable : (prefixWord ++ tailWord_353938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353938).length < 2 ^ (prefixWord ++ tailWord_353938).sum := by decide
  have hdescent : baseEnd_353938 < baseStart_353938 := by decide
  rcases family_descends (prefixWord ++ tailWord_353938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353953 : List Nat := [1, 2, 3, 3, 2, 1, 3, 5]
def baseStart_353953 : Nat := 118140960795 + 353953 * 2 ^ 59
def prefixEnd_353953 : Nat := 4983230072969 + 3 ^ 40 * 353953 * 2
def baseEnd_353953 : Nat := 53851264622506338062135

theorem tailTrace_353953 : CollatzResearch.WordTrace tailWord_353953 prefixEnd_353953 53851264622506338062135 := by
  unfold tailWord_353953
  simp only [CollatzResearch.WordTrace]
  refine ⟨12909726486696206204810513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8606484324464137469873675 12909726486696206204810513)
  ·
    refine ⟨9682294865022154653607885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12909726486696206204810513 9682294865022154653607885)
    ·
      refine ⟨3630860574383307995102957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9682294865022154653607885 3630860574383307995102957)
      ·
        refine ⟨1361572715393740498163609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3630860574383307995102957 1361572715393740498163609)
        ·
          refine ⟨1021179536545305373622707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1361572715393740498163609 1021179536545305373622707)
          ·
            refine ⟨1531769304817958060434061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021179536545305373622707 1531769304817958060434061)
            ·
              refine ⟨574413489306734272662773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1531769304817958060434061 574413489306734272662773)
              ·
                refine ⟨53851264622506338062135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 574413489306734272662773 53851264622506338062135)
                ·
                  rfl

theorem cell20_353953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_353953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353953 prefixEnd_353953 := by exact prefixLift 353953
  have htrace : WordTrace (prefixWord ++ tailWord_353953) baseStart_353953 baseEnd_353953 := by
    simpa [prefixWord, tailWord_353953, baseEnd_353953] using wordTrace_append hprefix tailTrace_353953
  have hstable : (prefixWord ++ tailWord_353953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353953).length < 2 ^ (prefixWord ++ tailWord_353953).sum := by decide
  have hdescent : baseEnd_353953 < baseStart_353953 := by decide
  rcases family_descends (prefixWord ++ tailWord_353953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353967 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_353967 : Nat := 118140960795 + 353967 * 2 ^ 59
def prefixEnd_353967 : Nat := 4983230072969 + 3 ^ 40 * 353967 * 2
def baseEnd_353967 : Nat := 161560183848997187719681

theorem tailTrace_353967 : CollatzResearch.WordTrace tailWord_353967 prefixEnd_353967 161560183848997187719681 := by
  unfold tailWord_353967
  simp only [CollatzResearch.WordTrace]
  refine ⟨12910237108645486595820155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8606824739096991063880103 12910237108645486595820155)
  ·
    refine ⟨19365355662968229893730233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12910237108645486595820155 19365355662968229893730233)
    ·
      refine ⟨14524016747226172420297675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19365355662968229893730233 14524016747226172420297675)
      ·
        refine ⟨21786025120839258630446513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14524016747226172420297675 21786025120839258630446513)
        ·
          refine ⟨16339518840629443972834885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21786025120839258630446513 16339518840629443972834885)
          ·
            refine ⟨3063659782618020744906541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16339518840629443972834885 3063659782618020744906541)
            ·
              refine ⟨1148872418481757779339953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3063659782618020744906541 1148872418481757779339953)
              ·
                refine ⟨861654313861318334504965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148872418481757779339953 861654313861318334504965)
                ·
                  refine ⟨161560183848997187719681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861654313861318334504965 161560183848997187719681)
                  ·
                    rfl

theorem cell20_353967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_353967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353967 prefixEnd_353967 := by exact prefixLift 353967
  have htrace : WordTrace (prefixWord ++ tailWord_353967) baseStart_353967 baseEnd_353967 := by
    simpa [prefixWord, tailWord_353967, baseEnd_353967] using wordTrace_append hprefix tailTrace_353967
  have hstable : (prefixWord ++ tailWord_353967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353967).length < 2 ^ (prefixWord ++ tailWord_353967).sum := by decide
  have hdescent : baseEnd_353967 < baseStart_353967 := by decide
  rcases family_descends (prefixWord ++ tailWord_353967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353990 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_353990 : Nat := 118140960795 + 353990 * 2 ^ 59
def prefixEnd_353990 : Nat := 4983230072969 + 3 ^ 40 * 353990 * 2
def baseEnd_353990 : Nat := 161570681675711329952921

theorem tailTrace_353990 : CollatzResearch.WordTrace tailWord_353990 prefixEnd_353990 161570681675711329952921 := by
  unfold tailWord_353990
  simp only [CollatzResearch.WordTrace]
  refine ⟨403471124611317547622107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8607383991708107682604949 403471124611317547622107)
  ·
    refine ⟨605206686916976321433161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403471124611317547622107 605206686916976321433161)
    ·
      refine ⟨453905015187732241074871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 605206686916976321433161 453905015187732241074871)
      ·
        refine ⟨680857522781598361612307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453905015187732241074871 680857522781598361612307)
        ·
          refine ⟨1021286284172397542418461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680857522781598361612307 1021286284172397542418461)
          ·
            refine ⟨382982356564649078406923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1021286284172397542418461 382982356564649078406923)
            ·
              refine ⟨574473534846973617610385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382982356564649078406923 574473534846973617610385)
              ·
                refine ⟨430855151135230213207789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574473534846973617610385 430855151135230213207789)
                ·
                  refine ⟨161570681675711329952921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430855151135230213207789 161570681675711329952921)
                  ·
                    rfl

theorem cell20_353990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_353990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353990 prefixEnd_353990 := by exact prefixLift 353990
  have htrace : WordTrace (prefixWord ++ tailWord_353990) baseStart_353990 baseEnd_353990 := by
    simpa [prefixWord, tailWord_353990, baseEnd_353990] using wordTrace_append hprefix tailTrace_353990
  have hstable : (prefixWord ++ tailWord_353990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353990).length < 2 ^ (prefixWord ++ tailWord_353990).sum := by decide
  have hdescent : baseEnd_353990 < baseStart_353990 := by decide
  rcases family_descends (prefixWord ++ tailWord_353990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353994 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_353994 : Nat := 118140960795 + 353994 * 2 ^ 59
def prefixEnd_353994 : Nat := 4983230072969 + 3 ^ 40 * 353994 * 2
def baseEnd_353994 : Nat := 161572507384705093819571

theorem tailTrace_353994 : CollatzResearch.WordTrace tailWord_353994 prefixEnd_353994 161572507384705093819571 := by
  unfold tailWord_353994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227805469886917551763259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8607481253031780138035357 3227805469886917551763259)
  ·
    refine ⟨4841708204830376327644889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3227805469886917551763259 4841708204830376327644889)
    ·
      refine ⟨3631281153622782245733667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4841708204830376327644889 3631281153622782245733667)
      ·
        refine ⟨5446921730434173368600501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3631281153622782245733667 5446921730434173368600501)
        ·
          refine ⟨510648912228203753306297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5446921730434173368600501 510648912228203753306297)
          ·
            refine ⟨382986684171152814979723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510648912228203753306297 382986684171152814979723)
            ·
              refine ⟨574480026256729222469585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382986684171152814979723 574480026256729222469585)
              ·
                refine ⟨430860019692546916852189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574480026256729222469585 430860019692546916852189)
                ·
                  refine ⟨161572507384705093819571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430860019692546916852189 161572507384705093819571)
                  ·
                    rfl

theorem cell20_353994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_353994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353994 prefixEnd_353994 := by exact prefixLift 353994
  have htrace : WordTrace (prefixWord ++ tailWord_353994) baseStart_353994 baseEnd_353994 := by
    simpa [prefixWord, tailWord_353994, baseEnd_353994] using wordTrace_append hprefix tailTrace_353994
  have hstable : (prefixWord ++ tailWord_353994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353994).length < 2 ^ (prefixWord ++ tailWord_353994).sum := by decide
  have hdescent : baseEnd_353994 < baseStart_353994 := by decide
  rcases family_descends (prefixWord ++ tailWord_353994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353998 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_353998 : Nat := 118140960795 + 353998 * 2 ^ 59
def prefixEnd_353998 : Nat := 4983230072969 + 3 ^ 40 * 353998 * 2
def baseEnd_353998 : Nat := 161574333093698857686221

theorem tailTrace_353998 : CollatzResearch.WordTrace tailWord_353998 prefixEnd_353998 161574333093698857686221 := by
  unfold tailWord_353998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613920971441647361274831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8607578514355452593465765 1613920971441647361274831)
  ·
    refine ⟨2420881457162471041912247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1613920971441647361274831 2420881457162471041912247)
    ·
      refine ⟨3631322185743706562868371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2420881457162471041912247 3631322185743706562868371)
      ·
        refine ⟨5446983278615559844302557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3631322185743706562868371 5446983278615559844302557)
        ·
          refine ⟨2042618729480834941613459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5446983278615559844302557 2042618729480834941613459)
          ·
            refine ⟨3063928094221252412420189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042618729480834941613459 3063928094221252412420189)
            ·
              refine ⟨1148973035332969654657571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3063928094221252412420189 1148973035332969654657571)
              ·
                refine ⟨1723459552999454481986357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148973035332969654657571 1723459552999454481986357)
                ·
                  refine ⟨161574333093698857686221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1723459552999454481986357 161574333093698857686221)
                  ·
                    rfl

theorem cell20_353998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_353998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_353998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_353998 prefixEnd_353998 := by exact prefixLift 353998
  have htrace : WordTrace (prefixWord ++ tailWord_353998) baseStart_353998 baseEnd_353998 := by
    simpa [prefixWord, tailWord_353998, baseEnd_353998] using wordTrace_append hprefix tailTrace_353998
  have hstable : (prefixWord ++ tailWord_353998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353998).length < 2 ^ (prefixWord ++ tailWord_353998).sum := by decide
  have hdescent : baseEnd_353998 < baseStart_353998 := by decide
  rcases family_descends (prefixWord ++ tailWord_353998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354015 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 3]
def baseStart_354015 : Nat := 118140960795 + 354015 * 2 ^ 59
def prefixEnd_354015 : Nat := 4983230072969 + 3 ^ 40 * 354015 * 2
def baseEnd_354015 : Nat := 161582092356922354119485

theorem tailTrace_354015 : CollatzResearch.WordTrace tailWord_354015 prefixEnd_354015 161582092356922354119485 := by
  unfold tailWord_354015
  simp only [CollatzResearch.WordTrace]
  refine ⟨12911987812471590793567499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8607991874981060529044999 12911987812471590793567499)
  ·
    refine ⟨19367981718707386190351249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12911987812471590793567499 19367981718707386190351249)
    ·
      refine ⟨14525986289030539642763437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19367981718707386190351249 14525986289030539642763437)
      ·
        refine ⟨5447244858386452366036289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14525986289030539642763437 5447244858386452366036289)
        ·
          refine ⟨4085433643789839274527217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5447244858386452366036289 4085433643789839274527217)
          ·
            refine ⟨3064075232842379455895413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4085433643789839274527217 3064075232842379455895413)
            ·
              refine ⟨287257053078973073990195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3064075232842379455895413 287257053078973073990195)
              ·
                refine ⟨430885579618459610985293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287257053078973073990195 430885579618459610985293)
                ·
                  refine ⟨161582092356922354119485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430885579618459610985293 161582092356922354119485)
                  ·
                    rfl

theorem cell20_354015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 3].length) (baseStart_354015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354015 prefixEnd_354015 := by exact prefixLift 354015
  have htrace : WordTrace (prefixWord ++ tailWord_354015) baseStart_354015 baseEnd_354015 := by
    simpa [prefixWord, tailWord_354015, baseEnd_354015] using wordTrace_append hprefix tailTrace_354015
  have hstable : (prefixWord ++ tailWord_354015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354015).length < 2 ^ (prefixWord ++ tailWord_354015).sum := by decide
  have hdescent : baseEnd_354015 < baseStart_354015 := by decide
  rcases family_descends (prefixWord ++ tailWord_354015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354029 : List Nat := [1, 5, 1, 2, 1, 3, 1, 6]
def baseStart_354029 : Nat := 118140960795 + 354029 * 2 ^ 59
def prefixEnd_354029 : Nat := 4983230072969 + 3 ^ 40 * 354029 * 2
def baseEnd_354029 : Nat := 53862827446133509217587

theorem tailTrace_354029 : CollatzResearch.WordTrace tailWord_354029 prefixEnd_354029 53862827446133509217587 := by
  unfold tailWord_354029
  simp only [CollatzResearch.WordTrace]
  refine ⟨12912498434420871184577141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8608332289613914123051427 12912498434420871184577141)
  ·
    refine ⟨1210546728226956673554107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12912498434420871184577141 1210546728226956673554107)
    ·
      refine ⟨1815820092340435010331161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1210546728226956673554107 1815820092340435010331161)
      ·
        refine ⟨1361865069255326257748371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1815820092340435010331161 1361865069255326257748371)
        ·
          refine ⟨2042797603882989386622557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361865069255326257748371 2042797603882989386622557)
          ·
            refine ⟨766049101456121019983459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2042797603882989386622557 766049101456121019983459)
            ·
              refine ⟨1149073652184181529975189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766049101456121019983459 1149073652184181529975189)
              ·
                refine ⟨53862827446133509217587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1149073652184181529975189 53862827446133509217587)
                ·
                  rfl

theorem cell20_354029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_354029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354029 prefixEnd_354029 := by exact prefixLift 354029
  have htrace : WordTrace (prefixWord ++ tailWord_354029) baseStart_354029 baseEnd_354029 := by
    simpa [prefixWord, tailWord_354029, baseEnd_354029] using wordTrace_append hprefix tailTrace_354029
  have hstable : (prefixWord ++ tailWord_354029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354029).length < 2 ^ (prefixWord ++ tailWord_354029).sum := by decide
  have hdescent : baseEnd_354029 < baseStart_354029 := by decide
  rcases family_descends (prefixWord ++ tailWord_354029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354046 : List Nat := [4, 2, 2, 1, 3, 2, 6]
def baseStart_354046 : Nat := 118140960795 + 354046 * 2 ^ 59
def prefixEnd_354046 : Nat := 4983230072969 + 3 ^ 40 * 354046 * 2
def baseEnd_354046 : Nat := 17955137955736002676225

theorem tailTrace_354046 : CollatzResearch.WordTrace tailWord_354046 prefixEnd_354046 17955137955736002676225 := by
  unfold tailWord_354046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614139809419910385993249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8608745650239522058630661 1614139809419910385993249)
  ·
    refine ⟨1210604857064932789494937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1614139809419910385993249 1210604857064932789494937)
    ·
      refine ⟨907953642798699592121203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1210604857064932789494937 907953642798699592121203)
      ·
        refine ⟨1361930464198049388181805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907953642798699592121203 1361930464198049388181805)
        ·
          refine ⟨510723924074268520568177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1361930464198049388181805 510723924074268520568177)
          ·
            refine ⟨383042943055701390426133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510723924074268520568177 383042943055701390426133)
            ·
              refine ⟨17955137955736002676225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 383042943055701390426133 17955137955736002676225)
              ·
                rfl

theorem cell20_354046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 6].length) (baseStart_354046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354046 prefixEnd_354046 := by exact prefixLift 354046
  have htrace : WordTrace (prefixWord ++ tailWord_354046) baseStart_354046 baseEnd_354046 := by
    simpa [prefixWord, tailWord_354046, baseEnd_354046] using wordTrace_append hprefix tailTrace_354046
  have hstable : (prefixWord ++ tailWord_354046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354046).length < 2 ^ (prefixWord ++ tailWord_354046).sum := by decide
  have hdescent : baseEnd_354046 < baseStart_354046 := by decide
  rcases family_descends (prefixWord ++ tailWord_354046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354060 : List Nat := [2, 2, 1, 2, 2, 1, 2, 6, 2]
def baseStart_354060 : Nat := 118140960795 + 354060 * 2 ^ 59
def prefixEnd_354060 : Nat := 4983230072969 + 3 ^ 40 * 354060 * 2
def baseEnd_354060 : Nat := 161602631583102197619301

theorem tailTrace_354060 : CollatzResearch.WordTrace tailWord_354060 prefixEnd_354060 161602631583102197619301 := by
  unfold tailWord_354060
  simp only [CollatzResearch.WordTrace]
  refine ⟨6456814548654281739477817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8609086064872375652637089 6456814548654281739477817)
  ·
    refine ⟨4842610911490711304608363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6456814548654281739477817 4842610911490711304608363)
    ·
      refine ⟨7263916367236066956912545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4842610911490711304608363 7263916367236066956912545)
      ·
        refine ⟨5447937275427050217684409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7263916367236066956912545 5447937275427050217684409)
        ·
          refine ⟨4085952956570287663263307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5447937275427050217684409 4085952956570287663263307)
          ·
            refine ⟨6128929434855431494894961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4085952956570287663263307 6128929434855431494894961)
            ·
              refine ⟨4596697076141573621171221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6128929434855431494894961 4596697076141573621171221)
              ·
                refine ⟨215470175444136263492401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4596697076141573621171221 215470175444136263492401)
                ·
                  refine ⟨161602631583102197619301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215470175444136263492401 161602631583102197619301)
                  ·
                    rfl

theorem cell20_354060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_354060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354060 prefixEnd_354060 := by exact prefixLift 354060
  have htrace : WordTrace (prefixWord ++ tailWord_354060) baseStart_354060 baseEnd_354060 := by
    simpa [prefixWord, tailWord_354060, baseEnd_354060] using wordTrace_append hprefix tailTrace_354060
  have hstable : (prefixWord ++ tailWord_354060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354060).length < 2 ^ (prefixWord ++ tailWord_354060).sum := by decide
  have hdescent : baseEnd_354060 < baseStart_354060 := by decide
  rcases family_descends (prefixWord ++ tailWord_354060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354105 : List Nat := [1, 2, 1, 7, 1, 8]
def baseStart_354105 : Nat := 118140960795 + 354105 * 2 ^ 59
def prefixEnd_354105 : Nat := 4983230072969 + 3 ^ 40 * 354105 * 2
def baseEnd_354105 : Nat := 5986043363306742263671

theorem tailTrace_354105 : CollatzResearch.WordTrace tailWord_354105 prefixEnd_354105 5986043363306742263671 := by
  unfold tailWord_354105
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915270382145536164343769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8610180254763690776229179 12915270382145536164343769)
  ·
    refine ⟨9686452786609152123257827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12915270382145536164343769 9686452786609152123257827)
    ·
      refine ⟨14529679179913728184886741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9686452786609152123257827 14529679179913728184886741)
      ·
        refine ⟨340539355779228004333283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14529679179913728184886741 340539355779228004333283)
        ·
          refine ⟨510809033668842006499925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340539355779228004333283 510809033668842006499925)
          ·
            refine ⟨5986043363306742263671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 510809033668842006499925 5986043363306742263671)
            ·
              rfl

theorem cell20_354105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 8].length) (baseStart_354105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354105 prefixEnd_354105 := by exact prefixLift 354105
  have htrace : WordTrace (prefixWord ++ tailWord_354105) baseStart_354105 baseEnd_354105 := by
    simpa [prefixWord, tailWord_354105, baseEnd_354105] using wordTrace_append hprefix tailTrace_354105
  have hstable : (prefixWord ++ tailWord_354105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354105).length < 2 ^ (prefixWord ++ tailWord_354105).sum := by decide
  have hdescent : baseEnd_354105 < baseStart_354105 := by decide
  rcases family_descends (prefixWord ++ tailWord_354105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354111 : List Nat := [1, 1, 2, 2, 7, 1, 2, 2, 2]
def baseStart_354111 : Nat := 118140960795 + 354111 * 2 ^ 59
def prefixEnd_354111 : Nat := 4983230072969 + 3 ^ 40 * 354111 * 2
def baseEnd_354111 : Nat := 161625909372772686919093

theorem tailTrace_354111 : CollatzResearch.WordTrace tailWord_354111 prefixEnd_354111 161625909372772686919093 := by
  unfold tailWord_354111
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915489220123799189062187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8610326146749199459374791 12915489220123799189062187)
  ·
    refine ⟨19373233830185698783593281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12915489220123799189062187 19373233830185698783593281)
    ·
      refine ⟨14529925372639274087694961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19373233830185698783593281 14529925372639274087694961)
      ·
        refine ⟨10897444029479455565771221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14529925372639274087694961 10897444029479455565771221)
        ·
          refine ⟨255408844440924739822763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10897444029479455565771221 255408844440924739822763)
          ·
            refine ⟨383113266661387109734145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255408844440924739822763 383113266661387109734145)
            ·
              refine ⟨287334949996040332300609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383113266661387109734145 287334949996040332300609)
              ·
                refine ⟨215501212497030249225457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287334949996040332300609 215501212497030249225457)
                ·
                  refine ⟨161625909372772686919093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215501212497030249225457 161625909372772686919093)
                  ·
                    rfl

theorem cell20_354111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 2].length) (baseStart_354111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354111 prefixEnd_354111 := by exact prefixLift 354111
  have htrace : WordTrace (prefixWord ++ tailWord_354111) baseStart_354111 baseEnd_354111 := by
    simpa [prefixWord, tailWord_354111, baseEnd_354111] using wordTrace_append hprefix tailTrace_354111
  have hstable : (prefixWord ++ tailWord_354111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354111).length < 2 ^ (prefixWord ++ tailWord_354111).sum := by decide
  have hdescent : baseEnd_354111 < baseStart_354111 := by decide
  rcases family_descends (prefixWord ++ tailWord_354111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354115 : List Nat := [1, 1, 1, 3, 1, 5, 4, 2, 2]
def baseStart_354115 : Nat := 118140960795 + 354115 * 2 ^ 59
def prefixEnd_354115 : Nat := 4983230072969 + 3 ^ 40 * 354115 * 2
def baseEnd_354115 : Nat := 161627735081766450785743

theorem tailTrace_354115 : CollatzResearch.WordTrace tailWord_354115 prefixEnd_354115 161627735081766450785743 := by
  unfold tailWord_354115
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915635112109307872207799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8610423408072871914805199 12915635112109307872207799)
  ·
    refine ⟨19373452668163961808311699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12915635112109307872207799 19373452668163961808311699)
    ·
      refine ⟨29060179002245942712467549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19373452668163961808311699 29060179002245942712467549)
      ·
        refine ⟨10897567125842228517175331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29060179002245942712467549 10897567125842228517175331)
        ·
          refine ⟨16346350688763342775762997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10897567125842228517175331 16346350688763342775762997)
          ·
            refine ⟨1532470377071563385227781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16346350688763342775762997 1532470377071563385227781)
            ·
              refine ⟨287338195700918134730209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1532470377071563385227781 287338195700918134730209)
              ·
                refine ⟨215503646775688601047657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287338195700918134730209 215503646775688601047657)
                ·
                  refine ⟨161627735081766450785743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215503646775688601047657 161627735081766450785743)
                  ·
                    rfl

theorem cell20_354115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 2].length) (baseStart_354115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354115 prefixEnd_354115 := by exact prefixLift 354115
  have htrace : WordTrace (prefixWord ++ tailWord_354115) baseStart_354115 baseEnd_354115 := by
    simpa [prefixWord, tailWord_354115, baseEnd_354115] using wordTrace_append hprefix tailTrace_354115
  have hstable : (prefixWord ++ tailWord_354115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354115).length < 2 ^ (prefixWord ++ tailWord_354115).sum := by decide
  have hdescent : baseEnd_354115 < baseStart_354115 := by decide
  rcases family_descends (prefixWord ++ tailWord_354115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354143 : List Nat := [1, 1, 2, 3, 1, 5, 3, 4]
def baseStart_354143 : Nat := 118140960795 + 354143 * 2 ^ 59
def prefixEnd_354143 : Nat := 4983230072969 + 3 ^ 40 * 354143 * 2
def baseEnd_354143 : Nat := 53880171681574265950765

theorem tailTrace_354143 : CollatzResearch.WordTrace tailWord_354143 prefixEnd_354143 53880171681574265950765 := by
  unfold tailWord_354143
  simp only [CollatzResearch.WordTrace]
  refine ⟨12916656356007868654227083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8611104237338579102818055 12916656356007868654227083)
  ·
    refine ⟨19374984534011802981340625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12916656356007868654227083 19374984534011802981340625)
    ·
      refine ⟨14531238400508852236005469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19374984534011802981340625 14531238400508852236005469)
      ·
        refine ⟨5449214400190819588502051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14531238400508852236005469 5449214400190819588502051)
        ·
          refine ⟨8173821600286229382753077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449214400190819588502051 8173821600286229382753077)
          ·
            refine ⟨766295775026834004633101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8173821600286229382753077 766295775026834004633101)
            ·
              refine ⟨287360915635062751737413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 766295775026834004633101 287360915635062751737413)
              ·
                refine ⟨53880171681574265950765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287360915635062751737413 53880171681574265950765)
                ·
                  rfl

theorem cell20_354143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 4].length) (baseStart_354143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354143 prefixEnd_354143 := by exact prefixLift 354143
  have htrace : WordTrace (prefixWord ++ tailWord_354143) baseStart_354143 baseEnd_354143 := by
    simpa [prefixWord, tailWord_354143, baseEnd_354143] using wordTrace_append hprefix tailTrace_354143
  have hstable : (prefixWord ++ tailWord_354143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354143).length < 2 ^ (prefixWord ++ tailWord_354143).sum := by decide
  have hdescent : baseEnd_354143 < baseStart_354143 := by decide
  rcases family_descends (prefixWord ++ tailWord_354143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354184 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 3]
def baseStart_354184 : Nat := 118140960795 + 354184 * 2 ^ 59
def prefixEnd_354184 : Nat := 4983230072969 + 3 ^ 40 * 354184 * 2
def baseEnd_354184 : Nat := 161659228561908877485461

theorem tailTrace_354184 : CollatzResearch.WordTrace tailWord_354184 prefixEnd_354184 161659228561908877485461 := by
  unfold tailWord_354184
  simp only [CollatzResearch.WordTrace]
  refine ⟨6459075874429666328234803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8612101165906221770979737 6459075874429666328234803)
  ·
    refine ⟨9688613811644499492352205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6459075874429666328234803 9688613811644499492352205)
    ·
      refine ⟨3633230179366687309632077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9688613811644499492352205 3633230179366687309632077)
      ·
        refine ⟨1362461317262507741112029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3633230179366687309632077 1362461317262507741112029)
        ·
          refine ⟨510922993973440402917011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1362461317262507741112029 510922993973440402917011)
          ·
            refine ⟨766384490960160604375517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510922993973440402917011 766384490960160604375517)
            ·
              refine ⟨287394184110060226640819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 766384490960160604375517 287394184110060226640819)
              ·
                refine ⟨431091276165090339961229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287394184110060226640819 431091276165090339961229)
                ·
                  refine ⟨161659228561908877485461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431091276165090339961229 161659228561908877485461)
                  ·
                    rfl

theorem cell20_354184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_354184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354184 prefixEnd_354184 := by exact prefixLift 354184
  have htrace : WordTrace (prefixWord ++ tailWord_354184) baseStart_354184 baseEnd_354184 := by
    simpa [prefixWord, tailWord_354184, baseEnd_354184] using wordTrace_append hprefix tailTrace_354184
  have hstable : (prefixWord ++ tailWord_354184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354184).length < 2 ^ (prefixWord ++ tailWord_354184).sum := by decide
  have hdescent : baseEnd_354184 < baseStart_354184 := by decide
  rcases family_descends (prefixWord ++ tailWord_354184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354236 : List Nat := [2, 2, 2, 5, 1, 1, 2, 5]
def baseStart_354236 : Nat := 118140960795 + 354236 * 2 ^ 59
def prefixEnd_354236 : Nat := 4983230072969 + 3 ^ 40 * 354236 * 2
def baseEnd_354236 : Nat := 53894320926275935917305

theorem tailTrace_354236 : CollatzResearch.WordTrace tailWord_354236 prefixEnd_354236 53894320926275935917305 := by
  unfold tailWord_354236
  simp only [CollatzResearch.WordTrace]
  refine ⟨6460024172335472768681281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8613365563113963691575041 6460024172335472768681281)
  ·
    refine ⟨4845018129251604576510961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6460024172335472768681281 4845018129251604576510961)
    ·
      refine ⟨3633763596938703432383221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4845018129251604576510961 3633763596938703432383221)
      ·
        refine ⟨340665337213003446785927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3633763596938703432383221 340665337213003446785927)
        ·
          refine ⟨510998005819505170178891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340665337213003446785927 510998005819505170178891)
          ·
            refine ⟨766497008729257755268337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510998005819505170178891 766497008729257755268337)
            ·
              refine ⟨574872756546943316451253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766497008729257755268337 574872756546943316451253)
              ·
                refine ⟨53894320926275935917305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 574872756546943316451253 53894320926275935917305)
                ·
                  rfl

theorem cell20_354236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_354236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354236 prefixEnd_354236 := by exact prefixLift 354236
  have htrace : WordTrace (prefixWord ++ tailWord_354236) baseStart_354236 baseEnd_354236 := by
    simpa [prefixWord, tailWord_354236, baseEnd_354236] using wordTrace_append hprefix tailTrace_354236
  have hstable : (prefixWord ++ tailWord_354236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354236).length < 2 ^ (prefixWord ++ tailWord_354236).sum := by decide
  have hdescent : baseEnd_354236 < baseStart_354236 := by decide
  rcases family_descends (prefixWord ++ tailWord_354236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354240 : List Nat := [2, 1, 1, 2, 3, 2, 4, 5]
def baseStart_354240 : Nat := 118140960795 + 354240 * 2 ^ 59
def prefixEnd_354240 : Nat := 4983230072969 + 3 ^ 40 * 354240 * 2
def baseEnd_354240 : Nat := 53894929495940523872855

theorem tailTrace_354240 : CollatzResearch.WordTrace tailWord_354240 prefixEnd_354240 53894929495940523872855 := by
  unfold tailWord_354240
  simp only [CollatzResearch.WordTrace]
  refine ⟨6460097118328227110254087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8613462824437636147005449 6460097118328227110254087)
  ·
    refine ⟨9690145677492340665381131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6460097118328227110254087 9690145677492340665381131)
    ·
      refine ⟨14535218516238510998071697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9690145677492340665381131 14535218516238510998071697)
      ·
        refine ⟨10901413887178883248553773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14535218516238510998071697 10901413887178883248553773)
        ·
          refine ⟨4088030207692081218207665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10901413887178883248553773 4088030207692081218207665)
          ·
            refine ⟨3066022655769060913655749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4088030207692081218207665 3066022655769060913655749)
            ·
              refine ⟨574879247956698921310453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3066022655769060913655749 574879247956698921310453)
              ·
                refine ⟨53894929495940523872855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 574879247956698921310453 53894929495940523872855)
                ·
                  rfl

theorem cell20_354240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_354240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354240 prefixEnd_354240 := by exact prefixLift 354240
  have htrace : WordTrace (prefixWord ++ tailWord_354240) baseStart_354240 baseEnd_354240 := by
    simpa [prefixWord, tailWord_354240, baseEnd_354240] using wordTrace_append hprefix tailTrace_354240
  have hstable : (prefixWord ++ tailWord_354240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354240).length < 2 ^ (prefixWord ++ tailWord_354240).sum := by decide
  have hdescent : baseEnd_354240 < baseStart_354240 := by decide
  rcases family_descends (prefixWord ++ tailWord_354240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354274 : List Nat := [3, 3, 3, 1, 3, 7]
def baseStart_354274 : Nat := 118140960795 + 354274 * 2 ^ 59
def prefixEnd_354274 : Nat := 4983230072969 + 3 ^ 40 * 354274 * 2
def baseEnd_354274 : Nat := 5988900259787724610559

theorem tailTrace_354274 : CollatzResearch.WordTrace tailWord_354274 prefixEnd_354274 5988900259787724610559 := by
  unfold tailWord_354274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3230358579633319506811469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8614289545688852018163917 3230358579633319506811469)
  ·
    refine ⟨1211384467362494815054301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3230358579633319506811469 1211384467362494815054301)
    ·
      refine ⟨454269175260935555645363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1211384467362494815054301 454269175260935555645363)
      ·
        refine ⟨681403762891403333468045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454269175260935555645363 681403762891403333468045)
        ·
          refine ⟨255526411084276250050517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 681403762891403333468045 255526411084276250050517)
          ·
            refine ⟨5988900259787724610559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 255526411084276250050517 5988900259787724610559)
            ·
              rfl

theorem cell20_354274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 7].length) (baseStart_354274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354274 prefixEnd_354274 := by exact prefixLift 354274
  have htrace : WordTrace (prefixWord ++ tailWord_354274) baseStart_354274 baseEnd_354274 := by
    simpa [prefixWord, tailWord_354274, baseEnd_354274] using wordTrace_append hprefix tailTrace_354274
  have hstable : (prefixWord ++ tailWord_354274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354274).length < 2 ^ (prefixWord ++ tailWord_354274).sum := by decide
  have hdescent : baseEnd_354274 < baseStart_354274 := by decide
  rcases family_descends (prefixWord ++ tailWord_354274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354309 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 4]
def baseStart_354309 : Nat := 118140960795 + 354309 * 2 ^ 59
def prefixEnd_354309 : Nat := 4983230072969 + 3 ^ 40 * 354309 * 2
def baseEnd_354309 : Nat := 161716281967963998318283

theorem tailTrace_354309 : CollatzResearch.WordTrace tailWord_354309 prefixEnd_354309 161716281967963998318283 := by
  unfold tailWord_354309
  simp only [CollatzResearch.WordTrace]
  refine ⟨12922710873406479004769981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8615140582270986003179987 12922710873406479004769981)
  ·
    refine ⟨4846016577527429626788743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12922710873406479004769981 4846016577527429626788743)
    ·
      refine ⟨7269024866291144440183115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4846016577527429626788743 7269024866291144440183115)
      ·
        refine ⟨10903537299436716660274673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7269024866291144440183115 10903537299436716660274673)
        ·
          refine ⟨8177652974577537495206005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10903537299436716660274673 8177652974577537495206005)
          ·
            refine ⟨766654966366644140175563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8177652974577537495206005 766654966366644140175563)
            ·
              refine ⟨1149982449549966210263345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766654966366644140175563 1149982449549966210263345)
              ·
                refine ⟨862486837162474657697509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149982449549966210263345 862486837162474657697509)
                ·
                  refine ⟨161716281967963998318283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 862486837162474657697509 161716281967963998318283)
                  ·
                    rfl

theorem cell20_354309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_354309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354309 prefixEnd_354309 := by exact prefixLift 354309
  have htrace : WordTrace (prefixWord ++ tailWord_354309) baseStart_354309 baseEnd_354309 := by
    simpa [prefixWord, tailWord_354309, baseEnd_354309] using wordTrace_append hprefix tailTrace_354309
  have hstable : (prefixWord ++ tailWord_354309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354309).length < 2 ^ (prefixWord ++ tailWord_354309).sum := by decide
  have hdescent : baseEnd_354309 < baseStart_354309 := by decide
  rcases family_descends (prefixWord ++ tailWord_354309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354343 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 4]
def baseStart_354343 : Nat := 118140960795 + 354343 * 2 ^ 59
def prefixEnd_354343 : Nat := 4983230072969 + 3 ^ 40 * 354343 * 2
def baseEnd_354343 : Nat := 161731800494410991184811

theorem tailTrace_354343 : CollatzResearch.WordTrace tailWord_354343 prefixEnd_354343 161731800494410991184811 := by
  unfold tailWord_354343
  simp only [CollatzResearch.WordTrace]
  refine ⟨12923950955283302811507683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8615967303522201874338455 12923950955283302811507683)
  ·
    refine ⟨19385926432924954217261525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12923950955283302811507683 19385926432924954217261525)
    ·
      refine ⟨454357650771678614467067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19385926432924954217261525 454357650771678614467067)
      ·
        refine ⟨681536476157517921700601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454357650771678614467067 681536476157517921700601)
        ·
          refine ⟨511152357118138441275451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681536476157517921700601 511152357118138441275451)
          ·
            refine ⟨766728535677207661913177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511152357118138441275451 766728535677207661913177)
            ·
              refine ⟨575046401757905746434883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766728535677207661913177 575046401757905746434883)
              ·
                refine ⟨862569602636858619652325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575046401757905746434883 862569602636858619652325)
                ·
                  refine ⟨161731800494410991184811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 862569602636858619652325 161731800494410991184811)
                  ·
                    rfl

theorem cell20_354343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 4].length) (baseStart_354343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354343 prefixEnd_354343 := by exact prefixLift 354343
  have htrace : WordTrace (prefixWord ++ tailWord_354343) baseStart_354343 baseEnd_354343 := by
    simpa [prefixWord, tailWord_354343, baseEnd_354343] using wordTrace_append hprefix tailTrace_354343
  have hstable : (prefixWord ++ tailWord_354343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354343).length < 2 ^ (prefixWord ++ tailWord_354343).sum := by decide
  have hdescent : baseEnd_354343 < baseStart_354343 := by decide
  rcases family_descends (prefixWord ++ tailWord_354343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354392 : List Nat := [2, 1, 2, 2, 1, 6, 6]
def baseStart_354392 : Nat := 118140960795 + 354392 * 2 ^ 59
def prefixEnd_354392 : Nat := 4983230072969 + 3 ^ 40 * 354392 * 2
def baseEnd_354392 : Nat := 17972685047731622061253

theorem tailTrace_354392 : CollatzResearch.WordTrace tailWord_354392 prefixEnd_354392 17972685047731622061253 := by
  unfold tailWord_354392
  simp only [CollatzResearch.WordTrace]
  refine ⟨6462869066052892090020715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8617158754737189453360953 6462869066052892090020715)
  ·
    refine ⟨9694303599079338135031073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6462869066052892090020715 9694303599079338135031073)
    ·
      refine ⟨7270727699309503601273305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9694303599079338135031073 7270727699309503601273305)
      ·
        refine ⟨5453045774482127700954979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7270727699309503601273305 5453045774482127700954979)
        ·
          refine ⟨8179568661723191551432469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453045774482127700954979 8179568661723191551432469)
          ·
            refine ⟨383417281018274603973397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8179568661723191551432469 383417281018274603973397)
            ·
              refine ⟨17972685047731622061253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 383417281018274603973397 17972685047731622061253)
              ·
                rfl

theorem cell20_354392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 6].length) (baseStart_354392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354392 prefixEnd_354392 := by exact prefixLift 354392
  have htrace : WordTrace (prefixWord ++ tailWord_354392) baseStart_354392 baseEnd_354392 := by
    simpa [prefixWord, tailWord_354392, baseEnd_354392] using wordTrace_append hprefix tailTrace_354392
  have hstable : (prefixWord ++ tailWord_354392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354392).length < 2 ^ (prefixWord ++ tailWord_354392).sum := by decide
  have hdescent : baseEnd_354392 < baseStart_354392 := by decide
  rcases family_descends (prefixWord ++ tailWord_354392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354416 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 3]
def baseStart_354416 : Nat := 118140960795 + 354416 * 2 ^ 59
def prefixEnd_354416 : Nat := 4983230072969 + 3 ^ 40 * 354416 * 2
def baseEnd_354416 : Nat := 161765119683547181751179

theorem tailTrace_354416 : CollatzResearch.WordTrace tailWord_354416 prefixEnd_354416 161765119683547181751179 := by
  unfold tailWord_354416
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463306742009418139457551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8617742322679224185943401 6463306742009418139457551)
  ·
    refine ⟨9694960113014127209186327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6463306742009418139457551 9694960113014127209186327)
    ·
      refine ⟨14542440169521190813779491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9694960113014127209186327 14542440169521190813779491)
      ·
        refine ⟨21813660254281786220669237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14542440169521190813779491 21813660254281786220669237)
        ·
          refine ⟨2045030648838917458187741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21813660254281786220669237 2045030648838917458187741)
          ·
            refine ⟨766886493314594046820403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2045030648838917458187741 766886493314594046820403)
            ·
              refine ⟨1150329739971891070230605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766886493314594046820403 1150329739971891070230605)
              ·
                refine ⟨431373652489459151336477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1150329739971891070230605 431373652489459151336477)
                ·
                  refine ⟨161765119683547181751179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431373652489459151336477 161765119683547181751179)
                  ·
                    rfl

theorem cell20_354416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_354416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354416 prefixEnd_354416 := by exact prefixLift 354416
  have htrace : WordTrace (prefixWord ++ tailWord_354416) baseStart_354416 baseEnd_354416 := by
    simpa [prefixWord, tailWord_354416, baseEnd_354416] using wordTrace_append hprefix tailTrace_354416
  have hstable : (prefixWord ++ tailWord_354416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354416).length < 2 ^ (prefixWord ++ tailWord_354416).sum := by decide
  have hdescent : baseEnd_354416 < baseStart_354416 := by decide
  rcases family_descends (prefixWord ++ tailWord_354416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354527 : List Nat := [1, 1, 2, 3, 2, 1, 1, 9]
def baseStart_354527 : Nat := 118140960795 + 354527 * 2 ^ 59
def prefixEnd_354527 : Nat := 4983230072969 + 3 ^ 40 * 354527 * 2
def baseEnd_354527 : Nat := 53938594369374709683575

theorem tailTrace_354527 : CollatzResearch.WordTrace tailWord_354527 prefixEnd_354527 53938594369374709683575 := by
  unfold tailWord_354527
  simp only [CollatzResearch.WordTrace]
  refine ⟨12930661986616702236205835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8620441324411134824137223 12930661986616702236205835)
  ·
    refine ⟨19395992979925053354308753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12930661986616702236205835 19395992979925053354308753)
    ·
      refine ⟨14546994734943790015731565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19395992979925053354308753 14546994734943790015731565)
      ·
        refine ⟨5455123025603921255899337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14546994734943790015731565 5455123025603921255899337)
        ·
          refine ⟨4091342269202940941924503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5455123025603921255899337 4091342269202940941924503)
          ·
            refine ⟨6137013403804411412886755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091342269202940941924503 6137013403804411412886755)
            ·
              refine ⟨9205520105706617119330133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6137013403804411412886755 9205520105706617119330133)
              ·
                refine ⟨53938594369374709683575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9205520105706617119330133 53938594369374709683575)
                ·
                  rfl

theorem cell20_354527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_354527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354527 prefixEnd_354527 := by exact prefixLift 354527
  have htrace : WordTrace (prefixWord ++ tailWord_354527) baseStart_354527 baseEnd_354527 := by
    simpa [prefixWord, tailWord_354527, baseEnd_354527] using wordTrace_append hprefix tailTrace_354527
  have hstable : (prefixWord ++ tailWord_354527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354527).length < 2 ^ (prefixWord ++ tailWord_354527).sum := by decide
  have hdescent : baseEnd_354527 < baseStart_354527 := by decide
  rcases family_descends (prefixWord ++ tailWord_354527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354554 : List Nat := [3, 1, 1, 1, 1, 5, 3, 3, 2]
def baseStart_354554 : Nat := 118140960795 + 354554 * 2 ^ 59
def prefixEnd_354554 : Nat := 4983230072969 + 3 ^ 40 * 354554 * 2
def baseEnd_354554 : Nat := 161828106643832035150615

theorem tailTrace_354554 : CollatzResearch.WordTrace tailWord_354554 prefixEnd_354554 161828106643832035150615 := by
  unfold tailWord_354554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3232911689379721461859679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8621097838345923898292477 3232911689379721461859679)
  ·
    refine ⟨4849367534069582192789519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3232911689379721461859679 4849367534069582192789519)
    ·
      refine ⟨7274051301104373289184279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4849367534069582192789519 7274051301104373289184279)
      ·
        refine ⟨10911076951656559933776419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7274051301104373289184279 10911076951656559933776419)
        ·
          refine ⟨16366615427484839900664629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10911076951656559933776419 16366615427484839900664629)
          ·
            refine ⟨1534370196326703740687309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16366615427484839900664629 1534370196326703740687309)
            ·
              refine ⟨575388823622513902757741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1534370196326703740687309 575388823622513902757741)
              ·
                refine ⟨215770808858442713534153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 575388823622513902757741 215770808858442713534153)
                ·
                  refine ⟨161828106643832035150615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215770808858442713534153 161828106643832035150615)
                  ·
                    rfl

theorem cell20_354554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_354554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354554 prefixEnd_354554 := by exact prefixLift 354554
  have htrace : WordTrace (prefixWord ++ tailWord_354554) baseStart_354554 baseEnd_354554 := by
    simpa [prefixWord, tailWord_354554, baseEnd_354554] using wordTrace_append hprefix tailTrace_354554
  have hstable : (prefixWord ++ tailWord_354554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354554).length < 2 ^ (prefixWord ++ tailWord_354554).sum := by decide
  have hdescent : baseEnd_354554 < baseStart_354554 := by decide
  rcases family_descends (prefixWord ++ tailWord_354554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354575 : List Nat := [1, 1, 2, 1, 1, 1, 3, 8, 2]
def baseStart_354575 : Nat := 118140960795 + 354575 * 2 ^ 59
def prefixEnd_354575 : Nat := 4983230072969 + 3 ^ 40 * 354575 * 2
def baseEnd_354575 : Nat := 161837691616049295450529

theorem tailTrace_354575 : CollatzResearch.WordTrace tailWord_354575 prefixEnd_354575 161837691616049295450529 := by
  unfold tailWord_354575
  simp only [CollatzResearch.WordTrace]
  refine ⟨12932412690442806433953179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8621608460295204289302119 12932412690442806433953179)
  ·
    refine ⟨19398619035664209650929769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12932412690442806433953179 19398619035664209650929769)
    ·
      refine ⟨14548964276748157238197327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19398619035664209650929769 14548964276748157238197327)
      ·
        refine ⟨21823446415122235857295991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14548964276748157238197327 21823446415122235857295991)
        ·
          refine ⟨32735169622683353785943987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21823446415122235857295991 32735169622683353785943987)
          ·
            refine ⟨49102754434025030678915981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32735169622683353785943987 49102754434025030678915981)
            ·
              refine ⟨18413532912759386504593493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49102754434025030678915981 18413532912759386504593493)
              ·
                refine ⟨215783588821399060600705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 18413532912759386504593493 215783588821399060600705)
                ·
                  refine ⟨161837691616049295450529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215783588821399060600705 161837691616049295450529)
                  ·
                    rfl

theorem cell20_354575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 2].length) (baseStart_354575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354575 prefixEnd_354575 := by exact prefixLift 354575
  have htrace : WordTrace (prefixWord ++ tailWord_354575) baseStart_354575 baseEnd_354575 := by
    simpa [prefixWord, tailWord_354575, baseEnd_354575] using wordTrace_append hprefix tailTrace_354575
  have hstable : (prefixWord ++ tailWord_354575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354575).length < 2 ^ (prefixWord ++ tailWord_354575).sum := by decide
  have hdescent : baseEnd_354575 < baseStart_354575 := by decide
  rcases family_descends (prefixWord ++ tailWord_354575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354627 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 3]
def baseStart_354627 : Nat := 118140960795 + 354627 * 2 ^ 59
def prefixEnd_354627 : Nat := 4983230072969 + 3 ^ 40 * 354627 * 2
def baseEnd_354627 : Nat := 161861425832968225716983

theorem tailTrace_354627 : CollatzResearch.WordTrace tailWord_354627 prefixEnd_354627 161861425832968225716983 := by
  unfold tailWord_354627
  simp only [CollatzResearch.WordTrace]
  refine ⟨12934309286254419314846135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8622872857502946209897423 12934309286254419314846135)
  ·
    refine ⟨19401463929381628972269203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12934309286254419314846135 19401463929381628972269203)
    ·
      refine ⟨29102195894072443458403805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19401463929381628972269203 29102195894072443458403805)
      ·
        refine ⟨10913323460277166296901427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29102195894072443458403805 10913323460277166296901427)
        ·
          refine ⟨16369985190415749445352141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10913323460277166296901427 16369985190415749445352141)
          ·
            refine ⟨6138744446405906042007053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16369985190415749445352141 6138744446405906042007053)
            ·
              refine ⟨2302029167402214765752645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6138744446405906042007053 2302029167402214765752645)
              ·
                refine ⟨431630468887915268578621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2302029167402214765752645 431630468887915268578621)
                ·
                  refine ⟨161861425832968225716983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431630468887915268578621 161861425832968225716983)
                  ·
                    rfl

theorem cell20_354627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 3].length) (baseStart_354627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354627 prefixEnd_354627 := by exact prefixLift 354627
  have htrace : WordTrace (prefixWord ++ tailWord_354627) baseStart_354627 baseEnd_354627 := by
    simpa [prefixWord, tailWord_354627, baseEnd_354627] using wordTrace_append hprefix tailTrace_354627
  have hstable : (prefixWord ++ tailWord_354627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354627).length < 2 ^ (prefixWord ++ tailWord_354627).sum := by decide
  have hdescent : baseEnd_354627 < baseStart_354627 := by decide
  rcases family_descends (prefixWord ++ tailWord_354627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354644 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 3]
def baseStart_354644 : Nat := 118140960795 + 354644 * 2 ^ 59
def prefixEnd_354644 : Nat := 4983230072969 + 3 ^ 40 * 354644 * 2
def baseEnd_354644 : Nat := 161869185096191722150247

theorem tailTrace_354644 : CollatzResearch.WordTrace tailWord_354644 prefixEnd_354644 161869185096191722150247 := by
  unfold tailWord_354644
  simp only [CollatzResearch.WordTrace]
  refine ⟨6467464663596415609107493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8623286218128554145476657 6467464663596415609107493)
  ·
    refine ⟨1212649624424327926707655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6467464663596415609107493 1212649624424327926707655)
    ·
      refine ⟨1818974436636491890061483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1212649624424327926707655 1818974436636491890061483)
      ·
        refine ⟨2728461654954737835092225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1818974436636491890061483 2728461654954737835092225)
        ·
          refine ⟨2046346241216053376319169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2728461654954737835092225 2046346241216053376319169)
          ·
            refine ⟨1534759680912040032239377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2046346241216053376319169 1534759680912040032239377)
            ·
              refine ⟨1151069760684030024179533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534759680912040032239377 1151069760684030024179533)
              ·
                refine ⟨431651160256511259067325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1151069760684030024179533 431651160256511259067325)
                ·
                  refine ⟨161869185096191722150247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431651160256511259067325 161869185096191722150247)
                  ·
                    rfl

theorem cell20_354644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_354644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354644 prefixEnd_354644 := by exact prefixLift 354644
  have htrace : WordTrace (prefixWord ++ tailWord_354644) baseStart_354644 baseEnd_354644 := by
    simpa [prefixWord, tailWord_354644, baseEnd_354644] using wordTrace_append hprefix tailTrace_354644
  have hstable : (prefixWord ++ tailWord_354644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354644).length < 2 ^ (prefixWord ++ tailWord_354644).sum := by decide
  have hdescent : baseEnd_354644 < baseStart_354644 := by decide
  rcases family_descends (prefixWord ++ tailWord_354644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354689 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 4]
def baseStart_354689 : Nat := 118140960795 + 354689 * 2 ^ 59
def prefixEnd_354689 : Nat := 4983230072969 + 3 ^ 40 * 354689 * 2
def baseEnd_354689 : Nat := 161889724322371565650063

theorem tailTrace_354689 : CollatzResearch.WordTrace tailWord_354689 prefixEnd_354689 161889724322371565650063 := by
  unfold tailWord_354689
  simp only [CollatzResearch.WordTrace]
  refine ⟨12936570612029803903603121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8624380408019869269068747 12936570612029803903603121)
  ·
    refine ⟨9702427959022352927702341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12936570612029803903603121 9702427959022352927702341)
    ·
      refine ⟨1819205242316691173944189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9702427959022352927702341 1819205242316691173944189)
      ·
        refine ⟨682201965868759190229071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1819205242316691173944189 682201965868759190229071)
        ·
          refine ⟨1023302948803138785343607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682201965868759190229071 1023302948803138785343607)
          ·
            refine ⟨1534954423204708178015411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023302948803138785343607 1534954423204708178015411)
            ·
              refine ⟨2302431634807062267023117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1534954423204708178015411 2302431634807062267023117)
              ·
                refine ⟨863411863052648350133669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2302431634807062267023117 863411863052648350133669)
                ·
                  refine ⟨161889724322371565650063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 863411863052648350133669 161889724322371565650063)
                  ·
                    rfl

theorem cell20_354689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_354689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354689 prefixEnd_354689 := by exact prefixLift 354689
  have htrace : WordTrace (prefixWord ++ tailWord_354689) baseStart_354689 baseEnd_354689 := by
    simpa [prefixWord, tailWord_354689, baseEnd_354689] using wordTrace_append hprefix tailTrace_354689
  have hstable : (prefixWord ++ tailWord_354689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354689).length < 2 ^ (prefixWord ++ tailWord_354689).sum := by decide
  have hdescent : baseEnd_354689 < baseStart_354689 := by decide
  rcases family_descends (prefixWord ++ tailWord_354689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354740 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 4]
def baseStart_354740 : Nat := 118140960795 + 354740 * 2 ^ 59
def prefixEnd_354740 : Nat := 4983230072969 + 3 ^ 40 * 354740 * 2
def baseEnd_354740 : Nat := 161913002112042054949855

theorem tailTrace_354740 : CollatzResearch.WordTrace tailWord_354740 prefixEnd_354740 161913002112042054949855 := by
  unfold tailWord_354740
  simp only [CollatzResearch.WordTrace]
  refine ⟨6469215367422519806854837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8625620489896693075806449 6469215367422519806854837)
  ·
    refine ⟨606488940695861231892641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6469215367422519806854837 606488940695861231892641)
    ·
      refine ⟨454866705521895923919481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 606488940695861231892641 454866705521895923919481)
      ·
        refine ⟨341150029141421942939611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454866705521895923919481 341150029141421942939611)
        ·
          refine ⟨511725043712132914409417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341150029141421942939611 511725043712132914409417)
          ·
            refine ⟨383793782784099685807063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511725043712132914409417 383793782784099685807063)
            ·
              refine ⟨575690674176149528710595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383793782784099685807063 575690674176149528710595)
              ·
                refine ⟨863536011264224293065893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575690674176149528710595 863536011264224293065893)
                ·
                  refine ⟨161913002112042054949855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 863536011264224293065893 161913002112042054949855)
                  ·
                    rfl

theorem cell20_354740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_354740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354740 prefixEnd_354740 := by exact prefixLift 354740
  have htrace : WordTrace (prefixWord ++ tailWord_354740) baseStart_354740 baseEnd_354740 := by
    simpa [prefixWord, tailWord_354740, baseEnd_354740] using wordTrace_append hprefix tailTrace_354740
  have hstable : (prefixWord ++ tailWord_354740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354740).length < 2 ^ (prefixWord ++ tailWord_354740).sum := by decide
  have hdescent : baseEnd_354740 < baseStart_354740 := by decide
  rcases family_descends (prefixWord ++ tailWord_354740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354772 : List Nat := [2, 4, 1, 2, 2, 1, 2, 6]
def baseStart_354772 : Nat := 118140960795 + 354772 * 2 ^ 59
def prefixEnd_354772 : Nat := 4983230072969 + 3 ^ 40 * 354772 * 2
def baseEnd_354772 : Nat := 53975869261330721961019

theorem tailTrace_354772 : CollatzResearch.WordTrace tailWord_354772 prefixEnd_354772 53975869261330721961019 := by
  unfold tailWord_354772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6469798935364554539437285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8626398580486072719249713 6469798935364554539437285)
  ·
    refine ⟨1213087300380853976144491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6469798935364554539437285 1213087300380853976144491)
    ·
      refine ⟨1819630950571280964216737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1213087300380853976144491 1819630950571280964216737)
      ·
        refine ⟨1364723212928460723162553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1819630950571280964216737 1364723212928460723162553)
        ·
          refine ⟨1023542409696345542371915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1364723212928460723162553 1023542409696345542371915)
          ·
            refine ⟨1535313614544518313557873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023542409696345542371915 1535313614544518313557873)
            ·
              refine ⟨1151485210908388735168405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535313614544518313557873 1151485210908388735168405)
              ·
                refine ⟨53975869261330721961019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1151485210908388735168405 53975869261330721961019)
                ·
                  rfl

theorem cell20_354772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_354772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354772 prefixEnd_354772 := by exact prefixLift 354772
  have htrace : WordTrace (prefixWord ++ tailWord_354772) baseStart_354772 baseEnd_354772 := by
    simpa [prefixWord, tailWord_354772, baseEnd_354772] using wordTrace_append hprefix tailTrace_354772
  have hstable : (prefixWord ++ tailWord_354772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354772).length < 2 ^ (prefixWord ++ tailWord_354772).sum := by decide
  have hdescent : baseEnd_354772 < baseStart_354772 := by decide
  rcases family_descends (prefixWord ++ tailWord_354772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354803 : List Nat := [1, 1, 1, 2, 2, 2, 5, 4, 2]
def baseStart_354803 : Nat := 118140960795 + 354803 * 2 ^ 59
def prefixEnd_354803 : Nat := 4983230072969 + 3 ^ 40 * 354803 * 2
def baseEnd_354803 : Nat := 161941757028693835849597

theorem tailTrace_354803 : CollatzResearch.WordTrace tailWord_354803 prefixEnd_354803 161941757028693835849597 := by
  unfold tailWord_354803
  simp only [CollatzResearch.WordTrace]
  refine ⟨12940728533616801373253063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8627152355744534248835375 12940728533616801373253063)
  ·
    refine ⟨19411092800425202059879595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12940728533616801373253063 19411092800425202059879595)
    ·
      refine ⟨29116639200637803089819393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19411092800425202059879595 29116639200637803089819393)
      ·
        refine ⟨21837479400478352317364545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29116639200637803089819393 21837479400478352317364545)
        ·
          refine ⟨16378109550358764238023409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21837479400478352317364545 16378109550358764238023409)
          ·
            refine ⟨12283582162769073178517557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16378109550358764238023409 12283582162769073178517557)
            ·
              refine ⟨1151585827759600610486021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12283582162769073178517557 1151585827759600610486021)
              ·
                refine ⟨215922342704925114466129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1151585827759600610486021 215922342704925114466129)
                ·
                  refine ⟨161941757028693835849597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215922342704925114466129 161941757028693835849597)
                  ·
                    rfl

theorem cell20_354803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 2].length) (baseStart_354803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354803 prefixEnd_354803 := by exact prefixLift 354803
  have htrace : WordTrace (prefixWord ++ tailWord_354803) baseStart_354803 baseEnd_354803 := by
    simpa [prefixWord, tailWord_354803, baseEnd_354803] using wordTrace_append hprefix tailTrace_354803
  have hstable : (prefixWord ++ tailWord_354803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354803).length < 2 ^ (prefixWord ++ tailWord_354803).sum := by decide
  have hdescent : baseEnd_354803 < baseStart_354803 := by decide
  rcases family_descends (prefixWord ++ tailWord_354803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354848 : List Nat := [2, 1, 1, 6, 2, 1, 7]
def baseStart_354848 : Nat := 118140960795 + 354848 * 2 ^ 59
def prefixEnd_354848 : Nat := 4983230072969 + 3 ^ 40 * 354848 * 2
def baseEnd_354848 : Nat := 17995810694985964372157

theorem tailTrace_354848 : CollatzResearch.WordTrace tailWord_354848 prefixEnd_354848 17995810694985964372157 := by
  unfold tailWord_354848
  simp only [CollatzResearch.WordTrace]
  refine ⟨6471184909226887029320599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8628246545635849372427465 6471184909226887029320599)
  ·
    refine ⟨9706777363840330543980899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6471184909226887029320599 9706777363840330543980899)
    ·
      refine ⟨14560166045760495815971349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9706777363840330543980899 14560166045760495815971349)
      ·
        refine ⟨682507783395023241373657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14560166045760495815971349 682507783395023241373657)
        ·
          refine ⟨511880837546267431030243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682507783395023241373657 511880837546267431030243)
          ·
            refine ⟨767821256319401146545365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511880837546267431030243 767821256319401146545365)
            ·
              refine ⟨17995810694985964372157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 767821256319401146545365 17995810694985964372157)
              ·
                rfl

theorem cell20_354848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 7].length) (baseStart_354848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354848 prefixEnd_354848 := by exact prefixLift 354848
  have htrace : WordTrace (prefixWord ++ tailWord_354848) baseStart_354848 baseEnd_354848 := by
    simpa [prefixWord, tailWord_354848, baseEnd_354848] using wordTrace_append hprefix tailTrace_354848
  have hstable : (prefixWord ++ tailWord_354848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354848).length < 2 ^ (prefixWord ++ tailWord_354848).sum := by decide
  have hdescent : baseEnd_354848 < baseStart_354848 := by decide
  rcases family_descends (prefixWord ++ tailWord_354848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354858 : List Nat := [3, 1, 4, 1, 1, 2, 2, 4, 2]
def baseStart_354858 : Nat := 118140960795 + 354858 * 2 ^ 59
def prefixEnd_354858 : Nat := 4983230072969 + 3 ^ 40 * 354858 * 2
def baseEnd_354858 : Nat := 161966860527358089016039

theorem tailTrace_354858 : CollatzResearch.WordTrace tailWord_354858 prefixEnd_354858 161966860527358089016039 := by
  unfold tailWord_354858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3235683637104386441626307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8628489698945030511003485 3235683637104386441626307)
  ·
    refine ⟨4853525455656579662439461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3235683637104386441626307 4853525455656579662439461)
    ·
      refine ⟨910036022935608686707399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4853525455656579662439461 910036022935608686707399)
      ·
        refine ⟨1365054034403413030061099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910036022935608686707399 1365054034403413030061099)
        ·
          refine ⟨2047581051605119545091649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365054034403413030061099 2047581051605119545091649)
          ·
            refine ⟨1535685788703839658818737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2047581051605119545091649 1535685788703839658818737)
            ·
              refine ⟨1151764341527879744114053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535685788703839658818737 1151764341527879744114053)
              ·
                refine ⟨215955814036477452021385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1151764341527879744114053 215955814036477452021385)
                ·
                  refine ⟨161966860527358089016039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215955814036477452021385 161966860527358089016039)
                  ·
                    rfl

theorem cell20_354858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_354858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354858 prefixEnd_354858 := by exact prefixLift 354858
  have htrace : WordTrace (prefixWord ++ tailWord_354858) baseStart_354858 baseEnd_354858 := by
    simpa [prefixWord, tailWord_354858, baseEnd_354858] using wordTrace_append hprefix tailTrace_354858
  have hstable : (prefixWord ++ tailWord_354858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354858).length < 2 ^ (prefixWord ++ tailWord_354858).sum := by decide
  have hdescent : baseEnd_354858 < baseStart_354858 := by decide
  rcases family_descends (prefixWord ++ tailWord_354858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354869 : List Nat := [1, 3, 3, 1, 1, 2, 2, 7]
def baseStart_354869 : Nat := 118140960795 + 354869 * 2 ^ 59
def prefixEnd_354869 : Nat := 4983230072969 + 3 ^ 40 * 354869 * 2
def baseEnd_354869 : Nat := 53990627075696979883109

theorem tailTrace_354869 : CollatzResearch.WordTrace tailWord_354869 prefixEnd_354869 53990627075696979883109 := by
  unfold tailWord_354869
  simp only [CollatzResearch.WordTrace]
  refine ⟨12943135751377694645155661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8628757167585129763437107 12943135751377694645155661)
  ·
    refine ⟨4853675906766635491933373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12943135751377694645155661 4853675906766635491933373)
    ·
      refine ⟨1820128465037488309475015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4853675906766635491933373 1820128465037488309475015)
      ·
        refine ⟨2730192697556232464212523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820128465037488309475015 2730192697556232464212523)
        ·
          refine ⟨4095289046334348696318785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730192697556232464212523 4095289046334348696318785)
          ·
            refine ⟨3071466784750761522239089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4095289046334348696318785 3071466784750761522239089)
            ·
              refine ⟨2303600088563071141679317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3071466784750761522239089 2303600088563071141679317)
              ·
                refine ⟨53990627075696979883109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2303600088563071141679317 53990627075696979883109)
                ·
                  rfl

theorem cell20_354869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_354869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354869 prefixEnd_354869 := by exact prefixLift 354869
  have htrace : WordTrace (prefixWord ++ tailWord_354869) baseStart_354869 baseEnd_354869 := by
    simpa [prefixWord, tailWord_354869, baseEnd_354869] using wordTrace_append hprefix tailTrace_354869
  have hstable : (prefixWord ++ tailWord_354869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354869).length < 2 ^ (prefixWord ++ tailWord_354869).sum := by decide
  have hdescent : baseEnd_354869 < baseStart_354869 := by decide
  rcases family_descends (prefixWord ++ tailWord_354869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354872 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 3]
def baseStart_354872 : Nat := 118140960795 + 354872 * 2 ^ 59
def prefixEnd_354872 : Nat := 4983230072969 + 3 ^ 40 * 354872 * 2
def baseEnd_354872 : Nat := 161973250508836262549315

theorem tailTrace_354872 : CollatzResearch.WordTrace tailWord_354872 prefixEnd_354872 161973250508836262549315 := by
  unfold tailWord_354872
  simp only [CollatzResearch.WordTrace]
  refine ⟨6471622585183413078757435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8628830113577884105009913 6471622585183413078757435)
  ·
    refine ⟨9707433877775119618136153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6471622585183413078757435 9707433877775119618136153)
    ·
      refine ⟨7280575408331339713602115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9707433877775119618136153 7280575408331339713602115)
      ·
        refine ⟨10920863112497009570403173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7280575408331339713602115 10920863112497009570403173)
        ·
          refine ⟨2047661833593189294450595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10920863112497009570403173 2047661833593189294450595)
          ·
            refine ⟨3071492750389783941675893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047661833593189294450595 3071492750389783941675893)
            ·
              refine ⟨287952445349042244532115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3071492750389783941675893 287952445349042244532115)
              ·
                refine ⟨431928668023563366798173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287952445349042244532115 431928668023563366798173)
                ·
                  refine ⟨161973250508836262549315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431928668023563366798173 161973250508836262549315)
                  ·
                    rfl

theorem cell20_354872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_354872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354872 prefixEnd_354872 := by exact prefixLift 354872
  have htrace : WordTrace (prefixWord ++ tailWord_354872) baseStart_354872 baseEnd_354872 := by
    simpa [prefixWord, tailWord_354872, baseEnd_354872] using wordTrace_append hprefix tailTrace_354872
  have hstable : (prefixWord ++ tailWord_354872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354872).length < 2 ^ (prefixWord ++ tailWord_354872).sum := by decide
  have hdescent : baseEnd_354872 < baseStart_354872 := by decide
  rcases family_descends (prefixWord ++ tailWord_354872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354945 : List Nat := [1, 2, 4, 2, 1, 1, 1, 8]
def baseStart_354945 : Nat := 118140960795 + 354945 * 2 ^ 59
def prefixEnd_354945 : Nat := 4983230072969 + 3 ^ 40 * 354945 * 2
def baseEnd_354945 : Nat := 54002189899324151038561

theorem tailTrace_354945 : CollatzResearch.WordTrace tailWord_354945 prefixEnd_354945 54002189899324151038561 := by
  unfold tailWord_354945
  simp only [CollatzResearch.WordTrace]
  refine ⟨12945907699102359624922289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8630605132734906416614859 12945907699102359624922289)
  ·
    refine ⟨9709430774326769718691717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12945907699102359624922289 9709430774326769718691717)
    ·
      refine ⟨1820518270186269322254697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9709430774326769718691717 1820518270186269322254697)
      ·
        refine ⟨1365388702639701991691023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1820518270186269322254697 1365388702639701991691023)
        ·
          refine ⟨2048083053959552987536535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365388702639701991691023 2048083053959552987536535)
          ·
            refine ⟨3072124580939329481304803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048083053959552987536535 3072124580939329481304803)
            ·
              refine ⟨4608186871408994221957205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072124580939329481304803 4608186871408994221957205)
              ·
                refine ⟨54002189899324151038561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4608186871408994221957205 54002189899324151038561)
                ·
                  rfl

theorem cell20_354945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_354945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354945 prefixEnd_354945 := by exact prefixLift 354945
  have htrace : WordTrace (prefixWord ++ tailWord_354945) baseStart_354945 baseEnd_354945 := by
    simpa [prefixWord, tailWord_354945, baseEnd_354945] using wordTrace_append hprefix tailTrace_354945
  have hstable : (prefixWord ++ tailWord_354945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354945).length < 2 ^ (prefixWord ++ tailWord_354945).sum := by decide
  have hdescent : baseEnd_354945 < baseStart_354945 := by decide
  rcases family_descends (prefixWord ++ tailWord_354945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354959 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_354959 : Nat := 118140960795 + 354959 * 2 ^ 59
def prefixEnd_354959 : Nat := 4983230072969 + 3 ^ 40 * 354959 * 2
def baseEnd_354959 : Nat := 162012959679450626648959

theorem tailTrace_354959 : CollatzResearch.WordTrace tailWord_354959 prefixEnd_354959 162012959679450626648959 := by
  unfold tailWord_354959
  simp only [CollatzResearch.WordTrace]
  refine ⟨12946418321051640015931931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8630945547367760010621287 12946418321051640015931931)
  ·
    refine ⟨19419627481577460023897897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12946418321051640015931931 19419627481577460023897897)
    ·
      refine ⟨14564720611183095017923423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19419627481577460023897897 14564720611183095017923423)
      ·
        refine ⟨21847080916774642526885135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14564720611183095017923423 21847080916774642526885135)
        ·
          refine ⟨32770621375161963790327703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21847080916774642526885135 32770621375161963790327703)
          ·
            refine ⟨49155932062742945685491555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32770621375161963790327703 49155932062742945685491555)
            ·
              refine ⟨73733898094114418528237333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49155932062742945685491555 73733898094114418528237333)
              ·
                refine ⟨3456276473161613368511125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73733898094114418528237333 3456276473161613368511125)
                ·
                  refine ⟨162012959679450626648959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3456276473161613368511125 162012959679450626648959)
                  ·
                    rfl

theorem cell20_354959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_354959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354959 prefixEnd_354959 := by exact prefixLift 354959
  have htrace : WordTrace (prefixWord ++ tailWord_354959) baseStart_354959 baseEnd_354959 := by
    simpa [prefixWord, tailWord_354959, baseEnd_354959] using wordTrace_append hprefix tailTrace_354959
  have hstable : (prefixWord ++ tailWord_354959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354959).length < 2 ^ (prefixWord ++ tailWord_354959).sum := by decide
  have hdescent : baseEnd_354959 < baseStart_354959 := by decide
  rcases family_descends (prefixWord ++ tailWord_354959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354969 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 3]
def baseStart_354969 : Nat := 118140960795 + 354969 * 2 ^ 59
def prefixEnd_354969 : Nat := 4983230072969 + 3 ^ 40 * 354969 * 2
def baseEnd_354969 : Nat := 162017523951935036315585

theorem tailTrace_354969 : CollatzResearch.WordTrace tailWord_354969 prefixEnd_354969 162017523951935036315585 := by
  unfold tailWord_354969
  simp only [CollatzResearch.WordTrace]
  refine ⟨12946783051015411723795961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8631188700676941149197307 12946783051015411723795961)
  ·
    refine ⟨9710087288261558792846971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12946783051015411723795961 9710087288261558792846971)
    ·
      refine ⟨14565130932392338189270457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9710087288261558792846971 14565130932392338189270457)
      ·
        refine ⟨10923848199294253641952843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14565130932392338189270457 10923848199294253641952843)
        ·
          refine ⟨16385772298941380462929265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10923848199294253641952843 16385772298941380462929265)
          ·
            refine ⟨12289329224206035347196949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16385772298941380462929265 12289329224206035347196949)
            ·
              refine ⟨576062307384657906899857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12289329224206035347196949 576062307384657906899857)
              ·
                refine ⟨432046730538493430174893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576062307384657906899857 432046730538493430174893)
                ·
                  refine ⟨162017523951935036315585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432046730538493430174893 162017523951935036315585)
                  ·
                    rfl

theorem cell20_354969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_354969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354969 prefixEnd_354969 := by exact prefixLift 354969
  have htrace : WordTrace (prefixWord ++ tailWord_354969) baseStart_354969 baseEnd_354969 := by
    simpa [prefixWord, tailWord_354969, baseEnd_354969] using wordTrace_append hprefix tailTrace_354969
  have hstable : (prefixWord ++ tailWord_354969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354969).length < 2 ^ (prefixWord ++ tailWord_354969).sum := by decide
  have hdescent : baseEnd_354969 < baseStart_354969 := by decide
  rcases family_descends (prefixWord ++ tailWord_354969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354972 : List Nat := [2, 2, 3, 2, 2, 2, 1, 4, 2]
def baseStart_354972 : Nat := 118140960795 + 354972 * 2 ^ 59
def prefixEnd_354972 : Nat := 4983230072969 + 3 ^ 40 * 354972 * 2
def baseEnd_354972 : Nat := 162018893233680359215573

theorem tailTrace_354972 : CollatzResearch.WordTrace tailWord_354972 prefixEnd_354972 162018893233680359215573 := by
  unfold tailWord_354972
  simp only [CollatzResearch.WordTrace]
  refine ⟨6473446235002271618077585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8631261646669695490770113 6473446235002271618077585)
  ·
    refine ⟨4855084676251703713558189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6473446235002271618077585 4855084676251703713558189)
    ·
      refine ⟨1820656753594388892584321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4855084676251703713558189 1820656753594388892584321)
      ·
        refine ⟨1365492565195791669438241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1820656753594388892584321 1365492565195791669438241)
        ·
          refine ⟨1024119423896843752078681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1365492565195791669438241 1024119423896843752078681)
          ·
            refine ⟨768089567922632814059011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024119423896843752078681 768089567922632814059011)
            ·
              refine ⟨1152134351883949221088517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768089567922632814059011 1152134351883949221088517)
              ·
                refine ⟨216025190978240478954097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1152134351883949221088517 216025190978240478954097)
                ·
                  refine ⟨162018893233680359215573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216025190978240478954097 162018893233680359215573)
                  ·
                    rfl

theorem cell20_354972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_354972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_354972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_354972 prefixEnd_354972 := by exact prefixLift 354972
  have htrace : WordTrace (prefixWord ++ tailWord_354972) baseStart_354972 baseEnd_354972 := by
    simpa [prefixWord, tailWord_354972, baseEnd_354972] using wordTrace_append hprefix tailTrace_354972
  have hstable : (prefixWord ++ tailWord_354972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354972).length < 2 ^ (prefixWord ++ tailWord_354972).sum := by decide
  have hdescent : baseEnd_354972 < baseStart_354972 := by decide
  rcases family_descends (prefixWord ++ tailWord_354972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355031 : List Nat := [1, 1, 3, 2, 1, 4, 2, 4, 2]
def baseStart_355031 : Nat := 118140960795 + 355031 * 2 ^ 59
def prefixEnd_355031 : Nat := 4983230072969 + 3 ^ 40 * 355031 * 2
def baseEnd_355031 : Nat := 162045822441338376248665

theorem tailTrace_355031 : CollatzResearch.WordTrace tailWord_355031 prefixEnd_355031 162045822441338376248665 := by
  unfold tailWord_355031
  simp only [CollatzResearch.WordTrace]
  refine ⟨12949044376790796312552947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8632696251193864208368631 12949044376790796312552947)
  ·
    refine ⟨19423566565186194468829421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12949044376790796312552947 19423566565186194468829421)
    ·
      refine ⟨7283837461944822925811033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19423566565186194468829421 7283837461944822925811033)
      ·
        refine ⟨5462878096458617194358275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7283837461944822925811033 5462878096458617194358275)
        ·
          refine ⟨8194317144687925791537413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5462878096458617194358275 8194317144687925791537413)
          ·
            refine ⟨1536434464628986085913265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8194317144687925791537413 1536434464628986085913265)
            ·
              refine ⟨1152325848471739564434949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536434464628986085913265 1152325848471739564434949)
              ·
                refine ⟨216061096588451168331553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1152325848471739564434949 216061096588451168331553)
                ·
                  refine ⟨162045822441338376248665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216061096588451168331553 162045822441338376248665)
                  ·
                    rfl

theorem cell20_355031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 2].length) (baseStart_355031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355031 prefixEnd_355031 := by exact prefixLift 355031
  have htrace : WordTrace (prefixWord ++ tailWord_355031) baseStart_355031 baseEnd_355031 := by
    simpa [prefixWord, tailWord_355031, baseEnd_355031] using wordTrace_append hprefix tailTrace_355031
  have hstable : (prefixWord ++ tailWord_355031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355031).length < 2 ^ (prefixWord ++ tailWord_355031).sum := by decide
  have hdescent : baseEnd_355031 < baseStart_355031 := by decide
  rcases family_descends (prefixWord ++ tailWord_355031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355061 : List Nat := [1, 3, 6, 1, 1, 2, 1, 3, 2]
def baseStart_355061 : Nat := 118140960795 + 355061 * 2 ^ 59
def prefixEnd_355061 : Nat := 4983230072969 + 3 ^ 40 * 355061 * 2
def baseEnd_355061 : Nat := 162059515258791605248543

theorem tailTrace_355061 : CollatzResearch.WordTrace tailWord_355061 prefixEnd_355061 162059515258791605248543 := by
  unfold tailWord_355061
  simp only [CollatzResearch.WordTrace]
  refine ⟨12950138566682111436145037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8633425711121407624096691 12950138566682111436145037)
  ·
    refine ⟨4856301962505791788554389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12950138566682111436145037 4856301962505791788554389)
    ·
      refine ⟨227639154492458990088487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4856301962505791788554389 227639154492458990088487)
      ·
        refine ⟨341458731738688485132731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227639154492458990088487 341458731738688485132731)
        ·
          refine ⟨512188097608032727699097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341458731738688485132731 512188097608032727699097)
          ·
            refine ⟨384141073206024545774323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512188097608032727699097 384141073206024545774323)
            ·
              refine ⟨576211609809036818661485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384141073206024545774323 576211609809036818661485)
              ·
                refine ⟨216079353678388806998057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 576211609809036818661485 216079353678388806998057)
                ·
                  refine ⟨162059515258791605248543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216079353678388806998057 162059515258791605248543)
                  ·
                    rfl

theorem cell20_355061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_355061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355061 prefixEnd_355061 := by exact prefixLift 355061
  have htrace : WordTrace (prefixWord ++ tailWord_355061) baseStart_355061 baseEnd_355061 := by
    simpa [prefixWord, tailWord_355061, baseEnd_355061] using wordTrace_append hprefix tailTrace_355061
  have hstable : (prefixWord ++ tailWord_355061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355061).length < 2 ^ (prefixWord ++ tailWord_355061).sum := by decide
  have hdescent : baseEnd_355061 < baseStart_355061 := by decide
  rcases family_descends (prefixWord ++ tailWord_355061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355066 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_355066 : Nat := 118140960795 + 355066 * 2 ^ 59
def prefixEnd_355066 : Nat := 4983230072969 + 3 ^ 40 * 355066 * 2
def baseEnd_355066 : Nat := 162061797395033810081855

theorem tailTrace_355066 : CollatzResearch.WordTrace tailWord_355066 prefixEnd_355066 162061797395033810081855 := by
  unfold tailWord_355066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237580232915999322519263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8633547287775998193384701 3237580232915999322519263)
  ·
    refine ⟨4856370349373998983778895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3237580232915999322519263 4856370349373998983778895)
    ·
      refine ⟨7284555524060998475668343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4856370349373998983778895 7284555524060998475668343)
      ·
        refine ⟨10926833286091497713502515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7284555524060998475668343 10926833286091497713502515)
        ·
          refine ⟨16390249929137246570253773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10926833286091497713502515 16390249929137246570253773)
          ·
            refine ⟨6146343723426467463845165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16390249929137246570253773 6146343723426467463845165)
            ·
              refine ⟨2304878896284925298941937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6146343723426467463845165 2304878896284925298941937)
              ·
                refine ⟨1728659172213693974206453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2304878896284925298941937 1728659172213693974206453)
                ·
                  refine ⟨162061797395033810081855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1728659172213693974206453 162061797395033810081855)
                  ·
                    rfl

theorem cell20_355066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_355066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355066 prefixEnd_355066 := by exact prefixLift 355066
  have htrace : WordTrace (prefixWord ++ tailWord_355066) baseStart_355066 baseEnd_355066 := by
    simpa [prefixWord, tailWord_355066, baseEnd_355066] using wordTrace_append hprefix tailTrace_355066
  have hstable : (prefixWord ++ tailWord_355066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355066).length < 2 ^ (prefixWord ++ tailWord_355066).sum := by decide
  have hdescent : baseEnd_355066 < baseStart_355066 := by decide
  rcases family_descends (prefixWord ++ tailWord_355066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355100 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 3]
def baseStart_355100 : Nat := 118140960795 + 355100 * 2 ^ 59
def prefixEnd_355100 : Nat := 4983230072969 + 3 ^ 40 * 355100 * 2
def baseEnd_355100 : Nat := 162077315921480802948383

theorem tailTrace_355100 : CollatzResearch.WordTrace tailWord_355100 prefixEnd_355100 162077315921480802948383 := by
  unfold tailWord_355100
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475780506770410548407377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8634374009027214064543169 6475780506770410548407377)
  ·
    refine ⟨4856835380077807911305533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6475780506770410548407377 4856835380077807911305533)
    ·
      refine ⟨1821313267529177966739575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4856835380077807911305533 1821313267529177966739575)
      ·
        refine ⟨2731969901293766950109363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821313267529177966739575 2731969901293766950109363)
        ·
          refine ⟨4097954851940650425164045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731969901293766950109363 4097954851940650425164045)
          ·
            refine ⟨1536733069477743909436517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4097954851940650425164045 1536733069477743909436517)
            ·
              refine ⟨288137450527076983019347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1536733069477743909436517 288137450527076983019347)
              ·
                refine ⟨432206175790615474529021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288137450527076983019347 432206175790615474529021)
                ·
                  refine ⟨162077315921480802948383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432206175790615474529021 162077315921480802948383)
                  ·
                    rfl

theorem cell20_355100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_355100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355100 prefixEnd_355100 := by exact prefixLift 355100
  have htrace : WordTrace (prefixWord ++ tailWord_355100) baseStart_355100 baseEnd_355100 := by
    simpa [prefixWord, tailWord_355100, baseEnd_355100] using wordTrace_append hprefix tailTrace_355100
  have hstable : (prefixWord ++ tailWord_355100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355100).length < 2 ^ (prefixWord ++ tailWord_355100).sum := by decide
  have hdescent : baseEnd_355100 < baseStart_355100 := by decide
  rcases family_descends (prefixWord ++ tailWord_355100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355137 : List Nat := [1, 2, 5, 3, 2, 1, 2, 2, 2]
def baseStart_355137 : Nat := 118140960795 + 355137 * 2 ^ 59
def prefixEnd_355137 : Nat := 4983230072969 + 3 ^ 40 * 355137 * 2
def baseEnd_355137 : Nat := 162094203729673118714899

theorem tailTrace_355137 : CollatzResearch.WordTrace tailWord_355137 prefixEnd_355137 162094203729673118714899 := by
  unfold tailWord_355137
  simp only [CollatzResearch.WordTrace]
  refine ⟨12952910514406776415911665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8635273676271184277274443 12952910514406776415911665)
  ·
    refine ⟨9714682885805082311933749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12952910514406776415911665 9714682885805082311933749)
    ·
      refine ⟨910751520544226466743789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9714682885805082311933749 910751520544226466743789)
      ·
        refine ⟨341531820204084925028921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 910751520544226466743789 341531820204084925028921)
        ·
          refine ⟨256148865153063693771691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341531820204084925028921 256148865153063693771691)
          ·
            refine ⟨384223297729595540657537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256148865153063693771691 384223297729595540657537)
            ·
              refine ⟨288167473297196655493153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384223297729595540657537 288167473297196655493153)
              ·
                refine ⟨216125604972897491619865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288167473297196655493153 216125604972897491619865)
                ·
                  refine ⟨162094203729673118714899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216125604972897491619865 162094203729673118714899)
                  ·
                    rfl

theorem cell20_355137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_355137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355137 prefixEnd_355137 := by exact prefixLift 355137
  have htrace : WordTrace (prefixWord ++ tailWord_355137) baseStart_355137 baseEnd_355137 := by
    simpa [prefixWord, tailWord_355137, baseEnd_355137] using wordTrace_append hprefix tailTrace_355137
  have hstable : (prefixWord ++ tailWord_355137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355137).length < 2 ^ (prefixWord ++ tailWord_355137).sum := by decide
  have hdescent : baseEnd_355137 < baseStart_355137 := by decide
  rcases family_descends (prefixWord ++ tailWord_355137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355145 : List Nat := [1, 2, 1, 1, 2, 6, 1, 4, 2]
def baseStart_355145 : Nat := 118140960795 + 355145 * 2 ^ 59
def prefixEnd_355145 : Nat := 4983230072969 + 3 ^ 40 * 355145 * 2
def baseEnd_355145 : Nat := 162097855147660646448199

theorem tailTrace_355145 : CollatzResearch.WordTrace tailWord_355145 prefixEnd_355145 162097855147660646448199 := by
  unfold tailWord_355145
  simp only [CollatzResearch.WordTrace]
  refine ⟨12953202298377793782202889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8635468198918529188135259 12953202298377793782202889)
  ·
    refine ⟨9714901723783345336652167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12953202298377793782202889 9714901723783345336652167)
    ·
      refine ⟨14572352585675018004978251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9714901723783345336652167 14572352585675018004978251)
      ·
        refine ⟨21858528878512527007467377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14572352585675018004978251 21858528878512527007467377)
        ·
          refine ⟨16393896658884395255600533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21858528878512527007467377 16393896658884395255600533)
          ·
            refine ⟨768463905885206027606275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16393896658884395255600533 768463905885206027606275)
            ·
              refine ⟨1152695858827809041409413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768463905885206027606275 1152695858827809041409413)
              ·
                refine ⟨216130473530214195264265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1152695858827809041409413 216130473530214195264265)
                ·
                  refine ⟨162097855147660646448199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216130473530214195264265 162097855147660646448199)
                  ·
                    rfl

theorem cell20_355145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_355145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355145 prefixEnd_355145 := by exact prefixLift 355145
  have htrace : WordTrace (prefixWord ++ tailWord_355145) baseStart_355145 baseEnd_355145 := by
    simpa [prefixWord, tailWord_355145, baseEnd_355145] using wordTrace_append hprefix tailTrace_355145
  have hstable : (prefixWord ++ tailWord_355145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355145).length < 2 ^ (prefixWord ++ tailWord_355145).sum := by decide
  have hdescent : baseEnd_355145 < baseStart_355145 := by decide
  rcases family_descends (prefixWord ++ tailWord_355145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355159 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 3]
def baseStart_355159 : Nat := 118140960795 + 355159 * 2 ^ 59
def prefixEnd_355159 : Nat := 4983230072969 + 3 ^ 40 * 355159 * 2
def baseEnd_355159 : Nat := 162104245129138819981475

theorem tailTrace_355159 : CollatzResearch.WordTrace tailWord_355159 prefixEnd_355159 162104245129138819981475 := by
  unfold tailWord_355159
  simp only [CollatzResearch.WordTrace]
  refine ⟨12953712920327074173212531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8635808613551382782141687 12953712920327074173212531)
  ·
    refine ⟨19430569380490611259818797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12953712920327074173212531 19430569380490611259818797)
    ·
      refine ⟨7286463517683979222432049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19430569380490611259818797 7286463517683979222432049)
      ·
        refine ⟨5464847638262984416824037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7286463517683979222432049 5464847638262984416824037)
        ·
          refine ⟨1024658932174309578154507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5464847638262984416824037 1024658932174309578154507)
          ·
            refine ⟨1536988398261464367231761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024658932174309578154507 1536988398261464367231761)
            ·
              refine ⟨1152741298696098275423821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536988398261464367231761 1152741298696098275423821)
              ·
                refine ⟨432277987011036853283933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1152741298696098275423821 432277987011036853283933)
                ·
                  refine ⟨162104245129138819981475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432277987011036853283933 162104245129138819981475)
                  ·
                    rfl

theorem cell20_355159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 3].length) (baseStart_355159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355159 prefixEnd_355159 := by exact prefixLift 355159
  have htrace : WordTrace (prefixWord ++ tailWord_355159) baseStart_355159 baseEnd_355159 := by
    simpa [prefixWord, tailWord_355159, baseEnd_355159] using wordTrace_append hprefix tailTrace_355159
  have hstable : (prefixWord ++ tailWord_355159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355159).length < 2 ^ (prefixWord ++ tailWord_355159).sum := by decide
  have hdescent : baseEnd_355159 < baseStart_355159 := by decide
  rcases family_descends (prefixWord ++ tailWord_355159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355180 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_355180 : Nat := 118140960795 + 355180 * 2 ^ 59
def prefixEnd_355180 : Nat := 4983230072969 + 3 ^ 40 * 355180 * 2
def baseEnd_355180 : Nat := 162113830101356080281389

theorem tailTrace_355180 : CollatzResearch.WordTrace tailWord_355180 prefixEnd_355180 162113830101356080281389 := by
  unfold tailWord_355180
  simp only [CollatzResearch.WordTrace]
  refine ⟨6477239426625497379863497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8636319235500663173151329 6477239426625497379863497)
  ·
    refine ⟨4857929569969123034897623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6477239426625497379863497 4857929569969123034897623)
    ·
      refine ⟨7286894354953684552346435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4857929569969123034897623 7286894354953684552346435)
      ·
        refine ⟨10930341532430526828519653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7286894354953684552346435 10930341532430526828519653)
        ·
          refine ⟨2049439037330723780347435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10930341532430526828519653 2049439037330723780347435)
          ·
            refine ⟨3074158555996085670521153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049439037330723780347435 3074158555996085670521153)
            ·
              refine ⟨2305618916997064252890865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3074158555996085670521153 2305618916997064252890865)
              ·
                refine ⟨1729214187747798189668149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2305618916997064252890865 1729214187747798189668149)
                ·
                  refine ⟨162113830101356080281389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1729214187747798189668149 162113830101356080281389)
                  ·
                    rfl

theorem cell20_355180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_355180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355180 prefixEnd_355180 := by exact prefixLift 355180
  have htrace : WordTrace (prefixWord ++ tailWord_355180) baseStart_355180 baseEnd_355180 := by
    simpa [prefixWord, tailWord_355180, baseEnd_355180] using wordTrace_append hprefix tailTrace_355180
  have hstable : (prefixWord ++ tailWord_355180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355180).length < 2 ^ (prefixWord ++ tailWord_355180).sum := by decide
  have hdescent : baseEnd_355180 < baseStart_355180 := by decide
  rcases family_descends (prefixWord ++ tailWord_355180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355190 : List Nat := [5, 1, 1, 3, 1, 2, 7]
def baseStart_355190 : Nat := 118140960795 + 355190 * 2 ^ 59
def prefixEnd_355190 : Nat := 4983230072969 + 3 ^ 40 * 355190 * 2
def baseEnd_355190 : Nat := 18013154930426721105335

theorem tailTrace_355190 : CollatzResearch.WordTrace tailWord_355190 prefixEnd_355190 18013154930426721105335 := by
  unfold tailWord_355190
  simp only [CollatzResearch.WordTrace]
  refine ⟨809677723950922904224439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8636562388809844311727349 809677723950922904224439)
  ·
    refine ⟨1214516585926384356336659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 809677723950922904224439 1214516585926384356336659)
    ·
      refine ⟨1821774878889576534504989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1214516585926384356336659 1821774878889576534504989)
      ·
        refine ⟨683165579583591200439371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1821774878889576534504989 683165579583591200439371)
        ·
          refine ⟨1024748369375386800659057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683165579583591200439371 1024748369375386800659057)
          ·
            refine ⟨768561277031540100494293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024748369375386800659057 768561277031540100494293)
            ·
              refine ⟨18013154930426721105335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 768561277031540100494293 18013154930426721105335)
              ·
                rfl

theorem cell20_355190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 7].length) (baseStart_355190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355190 prefixEnd_355190 := by exact prefixLift 355190
  have htrace : WordTrace (prefixWord ++ tailWord_355190) baseStart_355190 baseEnd_355190 := by
    simpa [prefixWord, tailWord_355190, baseEnd_355190] using wordTrace_append hprefix tailTrace_355190
  have hstable : (prefixWord ++ tailWord_355190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355190).length < 2 ^ (prefixWord ++ tailWord_355190).sum := by decide
  have hdescent : baseEnd_355190 < baseStart_355190 := by decide
  rcases family_descends (prefixWord ++ tailWord_355190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355197 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 3]
def baseStart_355197 : Nat := 118140960795 + 355197 * 2 ^ 59
def prefixEnd_355197 : Nat := 4983230072969 + 3 ^ 40 * 355197 * 2
def baseEnd_355197 : Nat := 162121589364579576714653

theorem tailTrace_355197 : CollatzResearch.WordTrace tailWord_355197 prefixEnd_355197 162121589364579576714653 := by
  unfold tailWord_355197
  simp only [CollatzResearch.WordTrace]
  refine ⟨12955098894189406663095845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8636732596126271108730563 12955098894189406663095845)
  ·
    refine ⟨2429081042660513749330471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12955098894189406663095845 2429081042660513749330471)
    ·
      refine ⟨3643621563990770623995707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2429081042660513749330471 3643621563990770623995707)
      ·
        refine ⟨5465432345986155935993561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3643621563990770623995707 5465432345986155935993561)
        ·
          refine ⟨4099074259489616951995171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5465432345986155935993561 4099074259489616951995171)
          ·
            refine ⟨6148611389234425427992757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4099074259489616951995171 6148611389234425427992757)
            ·
              refine ⟨576432317740727383874321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6148611389234425427992757 576432317740727383874321)
              ·
                refine ⟨432324238305545537905741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576432317740727383874321 432324238305545537905741)
                ·
                  refine ⟨162121589364579576714653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432324238305545537905741 162121589364579576714653)
                  ·
                    rfl

theorem cell20_355197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_355197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355197 prefixEnd_355197 := by exact prefixLift 355197
  have htrace : WordTrace (prefixWord ++ tailWord_355197) baseStart_355197 baseEnd_355197 := by
    simpa [prefixWord, tailWord_355197, baseEnd_355197] using wordTrace_append hprefix tailTrace_355197
  have hstable : (prefixWord ++ tailWord_355197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355197).length < 2 ^ (prefixWord ++ tailWord_355197).sum := by decide
  have hdescent : baseEnd_355197 < baseStart_355197 := by decide
  rcases family_descends (prefixWord ++ tailWord_355197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355228 : List Nat := [2, 2, 3, 3, 2, 1, 1, 6]
def baseStart_355228 : Nat := 118140960795 + 355228 * 2 ^ 59
def prefixEnd_355228 : Nat := 4983230072969 + 3 ^ 40 * 355228 * 2
def baseEnd_355228 : Nat := 54045246203093748893731

theorem tailTrace_355228 : CollatzResearch.WordTrace tailWord_355228 prefixEnd_355228 54045246203093748893731 := by
  unfold tailWord_355228
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478114778538549478737169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8637486371384732638316225 6478114778538549478737169)
  ·
    refine ⟨4858586083903912109052877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6478114778538549478737169 4858586083903912109052877)
    ·
      refine ⟨1821969781463967040894829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4858586083903912109052877 1821969781463967040894829)
      ·
        refine ⟨683238668048987640335561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1821969781463967040894829 683238668048987640335561)
        ·
          refine ⟨512429001036740730251671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683238668048987640335561 512429001036740730251671)
          ·
            refine ⟨768643501555111095377507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512429001036740730251671 768643501555111095377507)
            ·
              refine ⟨1152965252332666643066261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768643501555111095377507 1152965252332666643066261)
              ·
                refine ⟨54045246203093748893731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1152965252332666643066261 54045246203093748893731)
                ·
                  rfl

theorem cell20_355228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_355228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355228 prefixEnd_355228 := by exact prefixLift 355228
  have htrace : WordTrace (prefixWord ++ tailWord_355228) baseStart_355228 baseEnd_355228 := by
    simpa [prefixWord, tailWord_355228, baseEnd_355228] using wordTrace_append hprefix tailTrace_355228
  have hstable : (prefixWord ++ tailWord_355228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355228).length < 2 ^ (prefixWord ++ tailWord_355228).sum := by decide
  have hdescent : baseEnd_355228 < baseStart_355228 := by decide
  rcases family_descends (prefixWord ++ tailWord_355228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355245 : List Nat := [1, 5, 2, 3, 1, 2, 6]
def baseStart_355245 : Nat := 118140960795 + 355245 * 2 ^ 59
def prefixEnd_355245 : Nat := 4983230072969 + 3 ^ 40 * 355245 * 2
def baseEnd_355245 : Nat := 18015944208056082568273

theorem tailTrace_355245 : CollatzResearch.WordTrace tailWord_355245 prefixEnd_355245 18015944208056082568273 := by
  unfold tailWord_355245
  simp only [CollatzResearch.WordTrace]
  refine ⟨12956849598015510860843189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8637899732010340573895459 12956849598015510860843189)
  ·
    refine ⟨1214704649813954143204049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12956849598015510860843189 1214704649813954143204049)
    ·
      refine ⟨911028487360465607403037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1214704649813954143204049 911028487360465607403037)
      ·
        refine ⟨341635682760174602776139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 911028487360465607403037 341635682760174602776139)
        ·
          refine ⟨512453524140261904164209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341635682760174602776139 512453524140261904164209)
          ·
            refine ⟨384340143105196428123157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512453524140261904164209 384340143105196428123157)
            ·
              refine ⟨18015944208056082568273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 384340143105196428123157 18015944208056082568273)
              ·
                rfl

theorem cell20_355245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 6].length) (baseStart_355245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355245 prefixEnd_355245 := by exact prefixLift 355245
  have htrace : WordTrace (prefixWord ++ tailWord_355245) baseStart_355245 baseEnd_355245 := by
    simpa [prefixWord, tailWord_355245, baseEnd_355245] using wordTrace_append hprefix tailTrace_355245
  have hstable : (prefixWord ++ tailWord_355245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355245).length < 2 ^ (prefixWord ++ tailWord_355245).sum := by decide
  have hdescent : baseEnd_355245 < baseStart_355245 := by decide
  rcases family_descends (prefixWord ++ tailWord_355245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355252 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 5]
def baseStart_355252 : Nat := 118140960795 + 355252 * 2 ^ 59
def prefixEnd_355252 : Nat := 4983230072969 + 3 ^ 40 * 355252 * 2
def baseEnd_355252 : Nat := 162146692863243829881095

theorem tailTrace_355252 : CollatzResearch.WordTrace tailWord_355252 prefixEnd_355252 162146692863243829881095 := by
  unfold tailWord_355252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478552454495075528174005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8638069939326767370898673 6478552454495075528174005)
  ·
    refine ⟨607364292608913330766313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6478552454495075528174005 607364292608913330766313)
    ·
      refine ⟨455523219456684998074735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 607364292608913330766313 455523219456684998074735)
      ·
        refine ⟨683284829185027497112103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455523219456684998074735 683284829185027497112103)
        ·
          refine ⟨1024927243777541245668155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683284829185027497112103 1024927243777541245668155)
          ·
            refine ⟨1537390865666311868502233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024927243777541245668155 1537390865666311868502233)
            ·
              refine ⟨1153043149249733901376675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537390865666311868502233 1153043149249733901376675)
              ·
                refine ⟨1729564723874600852065013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153043149249733901376675 1729564723874600852065013)
                ·
                  refine ⟨162146692863243829881095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1729564723874600852065013 162146692863243829881095)
                  ·
                    rfl

theorem cell20_355252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_355252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355252 prefixEnd_355252 := by exact prefixLift 355252
  have htrace : WordTrace (prefixWord ++ tailWord_355252) baseStart_355252 baseEnd_355252 := by
    simpa [prefixWord, tailWord_355252, baseEnd_355252] using wordTrace_append hprefix tailTrace_355252
  have hstable : (prefixWord ++ tailWord_355252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355252).length < 2 ^ (prefixWord ++ tailWord_355252).sum := by decide
  have hdescent : baseEnd_355252 < baseStart_355252 := by decide
  rcases family_descends (prefixWord ++ tailWord_355252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355256 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_355256 : Nat := 118140960795 + 355256 * 2 ^ 59
def prefixEnd_355256 : Nat := 4983230072969 + 3 ^ 40 * 355256 * 2
def baseEnd_355256 : Nat := 162148518572237593747745

theorem tailTrace_355256 : CollatzResearch.WordTrace tailWord_355256 prefixEnd_355256 162148518572237593747745 := by
  unfold tailWord_355256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478625400487829869746811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8638167200650439826329081 6478625400487829869746811)
  ·
    refine ⟨9717938100731744804620217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6478625400487829869746811 9717938100731744804620217)
    ·
      refine ⟨7288453575548808603465163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9717938100731744804620217 7288453575548808603465163)
      ·
        refine ⟨10932680363323212905197745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7288453575548808603465163 10932680363323212905197745)
        ·
          refine ⟨8199510272492409678898309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10932680363323212905197745 8199510272492409678898309)
          ·
            refine ⟨1537408176092326814793433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8199510272492409678898309 1537408176092326814793433)
            ·
              refine ⟨1153056132069245111095075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537408176092326814793433 1153056132069245111095075)
              ·
                refine ⟨1729584198103867666642613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153056132069245111095075 1729584198103867666642613)
                ·
                  refine ⟨162148518572237593747745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1729584198103867666642613 162148518572237593747745)
                  ·
                    rfl

theorem cell20_355256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_355256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355256 prefixEnd_355256 := by exact prefixLift 355256
  have htrace : WordTrace (prefixWord ++ tailWord_355256) baseStart_355256 baseEnd_355256 := by
    simpa [prefixWord, tailWord_355256, baseEnd_355256] using wordTrace_append hprefix tailTrace_355256
  have hstable : (prefixWord ++ tailWord_355256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355256).length < 2 ^ (prefixWord ++ tailWord_355256).sum := by decide
  have hdescent : baseEnd_355256 < baseStart_355256 := by decide
  rcases family_descends (prefixWord ++ tailWord_355256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355263 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_355263 : Nat := 118140960795 + 355263 * 2 ^ 59
def prefixEnd_355263 : Nat := 4983230072969 + 3 ^ 40 * 355263 * 2
def baseEnd_355263 : Nat := 162151713562976680514383

theorem tailTrace_355263 : CollatzResearch.WordTrace tailWord_355263 prefixEnd_355263 162151713562976680514383 := by
  unfold tailWord_355263
  simp only [CollatzResearch.WordTrace]
  refine ⟨12957506111950299934998443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8638337407966866623332295 12957506111950299934998443)
  ·
    refine ⟨19436259167925449902497665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12957506111950299934998443 19436259167925449902497665)
    ·
      refine ⟨14577194375944087426873249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19436259167925449902497665 14577194375944087426873249)
      ·
        refine ⟨10932895781958065570154937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14577194375944087426873249 10932895781958065570154937)
        ·
          refine ⟨8199671836468549177616203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10932895781958065570154937 8199671836468549177616203)
          ·
            refine ⟨12299507754702823766424305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8199671836468549177616203 12299507754702823766424305)
            ·
              refine ⟨9224630816027117824818229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12299507754702823766424305 9224630816027117824818229)
              ·
                refine ⟨864809139002542296076709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9224630816027117824818229 864809139002542296076709)
                ·
                  refine ⟨162151713562976680514383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 864809139002542296076709 162151713562976680514383)
                  ·
                    rfl

theorem cell20_355263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_355263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355263 prefixEnd_355263 := by exact prefixLift 355263
  have htrace : WordTrace (prefixWord ++ tailWord_355263) baseStart_355263 baseEnd_355263 := by
    simpa [prefixWord, tailWord_355263, baseEnd_355263] using wordTrace_append hprefix tailTrace_355263
  have hstable : (prefixWord ++ tailWord_355263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355263).length < 2 ^ (prefixWord ++ tailWord_355263).sum := by decide
  have hdescent : baseEnd_355263 < baseStart_355263 := by decide
  rcases family_descends (prefixWord ++ tailWord_355263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355310 : List Nat := [4, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_355310 : Nat := 118140960795 + 355310 * 2 ^ 59
def prefixEnd_355310 : Nat := 4983230072969 + 3 ^ 40 * 355310 * 2
def baseEnd_355310 : Nat := 162173165643653405947525

theorem tailTrace_355310 : CollatzResearch.WordTrace tailWord_355310 prefixEnd_355310 162173165643653405947525 := by
  unfold tailWord_355310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619902542847503370244923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8639480228520017974639589 1619902542847503370244923)
  ·
    refine ⟨2429853814271255055367385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1619902542847503370244923 2429853814271255055367385)
    ·
      refine ⟨1822390360703441291525539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2429853814271255055367385 1822390360703441291525539)
      ·
        refine ⟨2733585541055161937288309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1822390360703441291525539 2733585541055161937288309)
        ·
          refine ⟨256273644473921431620779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2733585541055161937288309 256273644473921431620779)
          ·
            refine ⟨384410466710882147431169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256273644473921431620779 384410466710882147431169)
            ·
              refine ⟨288307850033161610573377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384410466710882147431169 288307850033161610573377)
              ·
                refine ⟨216230887524871207930033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288307850033161610573377 216230887524871207930033)
                ·
                  refine ⟨162173165643653405947525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216230887524871207930033 162173165643653405947525)
                  ·
                    rfl

theorem cell20_355310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_355310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355310 prefixEnd_355310 := by exact prefixLift 355310
  have htrace : WordTrace (prefixWord ++ tailWord_355310) baseStart_355310 baseEnd_355310 := by
    simpa [prefixWord, tailWord_355310, baseEnd_355310] using wordTrace_append hprefix tailTrace_355310
  have hstable : (prefixWord ++ tailWord_355310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355310).length < 2 ^ (prefixWord ++ tailWord_355310).sum := by decide
  have hdescent : baseEnd_355310 < baseStart_355310 := by decide
  rcases family_descends (prefixWord ++ tailWord_355310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355311 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 3]
def baseStart_355311 : Nat := 118140960795 + 355311 * 2 ^ 59
def prefixEnd_355311 : Nat := 4983230072969 + 3 ^ 40 * 355311 * 2
def baseEnd_355311 : Nat := 162173622070901846914187

theorem tailTrace_355311 : CollatzResearch.WordTrace tailWord_355311 prefixEnd_355311 162173622070901846914187 := by
  unfold tailWord_355311
  simp only [CollatzResearch.WordTrace]
  refine ⟨12959256815776404132745787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8639504543850936088497191 12959256815776404132745787)
  ·
    refine ⟨19438885223664606199118681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12959256815776404132745787 19438885223664606199118681)
    ·
      refine ⟨14579163917748454649339011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19438885223664606199118681 14579163917748454649339011)
      ·
        refine ⟨21868745876622681974008517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14579163917748454649339011 21868745876622681974008517)
        ·
          refine ⟨4100389851866752870126597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21868745876622681974008517 4100389851866752870126597)
          ·
            refine ⟨768823097225016163148737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4100389851866752870126597 768823097225016163148737)
            ·
              refine ⟨576617322918762122361553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768823097225016163148737 576617322918762122361553)
              ·
                refine ⟨432462992189071591771165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576617322918762122361553 432462992189071591771165)
                ·
                  refine ⟨162173622070901846914187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432462992189071591771165 162173622070901846914187)
                  ·
                    rfl

theorem cell20_355311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 3].length) (baseStart_355311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355311 prefixEnd_355311 := by exact prefixLift 355311
  have htrace : WordTrace (prefixWord ++ tailWord_355311) baseStart_355311 baseEnd_355311 := by
    simpa [prefixWord, tailWord_355311, baseEnd_355311] using wordTrace_append hprefix tailTrace_355311
  have hstable : (prefixWord ++ tailWord_355311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355311).length < 2 ^ (prefixWord ++ tailWord_355311).sum := by decide
  have hdescent : baseEnd_355311 < baseStart_355311 := by decide
  rcases family_descends (prefixWord ++ tailWord_355311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355339 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_355339 : Nat := 118140960795 + 355339 * 2 ^ 59
def prefixEnd_355339 : Nat := 4983230072969 + 3 ^ 40 * 355339 * 2
def baseEnd_355339 : Nat := 162186402033858193980739

theorem tailTrace_355339 : CollatzResearch.WordTrace tailWord_355339 prefixEnd_355339 162186402033858193980739 := by
  unfold tailWord_355339
  simp only [CollatzResearch.WordTrace]
  refine ⟨12960278059674964914765071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8640185373116643276510047 12960278059674964914765071)
  ·
    refine ⟨19440417089512447372147607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12960278059674964914765071 19440417089512447372147607)
    ·
      refine ⟨29160625634268671058221411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19440417089512447372147607 29160625634268671058221411)
      ·
        refine ⟨43740938451403006587332117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29160625634268671058221411 43740938451403006587332117)
        ·
          refine ⟨2050356489909515933781193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43740938451403006587332117 2050356489909515933781193)
          ·
            refine ⟨1537767367432136950335895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2050356489909515933781193 1537767367432136950335895)
            ·
              refine ⟨2306651051148205425503843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537767367432136950335895 2306651051148205425503843)
              ·
                refine ⟨3459976576722308138255765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306651051148205425503843 3459976576722308138255765)
                ·
                  refine ⟨162186402033858193980739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3459976576722308138255765 162186402033858193980739)
                  ·
                    rfl

theorem cell20_355339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_355339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355339 prefixEnd_355339 := by exact prefixLift 355339
  have htrace : WordTrace (prefixWord ++ tailWord_355339) baseStart_355339 baseEnd_355339 := by
    simpa [prefixWord, tailWord_355339, baseEnd_355339] using wordTrace_append hprefix tailTrace_355339
  have hstable : (prefixWord ++ tailWord_355339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355339).length < 2 ^ (prefixWord ++ tailWord_355339).sum := by decide
  have hdescent : baseEnd_355339 < baseStart_355339 := by decide
  rcases family_descends (prefixWord ++ tailWord_355339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355342 : List Nat := [4, 1, 1, 2, 2, 3, 3, 4]
def baseStart_355342 : Nat := 118140960795 + 355342 * 2 ^ 59
def prefixEnd_355342 : Nat := 4983230072969 + 3 ^ 40 * 355342 * 2
def baseEnd_355342 : Nat := 54062590438534505626909

theorem tailTrace_355342 : CollatzResearch.WordTrace tailWord_355342 prefixEnd_355342 54062590438534505626909 := by
  unfold tailWord_355342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1620048434833012053390535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8640258319109397618082853 1620048434833012053390535)
  ·
    refine ⟨2430072652249518080085803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1620048434833012053390535 2430072652249518080085803)
    ·
      refine ⟨3645108978374277120128705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2430072652249518080085803 3645108978374277120128705)
      ·
        refine ⟨2733831733780707840096529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3645108978374277120128705 2733831733780707840096529)
        ·
          refine ⟨2050373800335530880072397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2733831733780707840096529 2050373800335530880072397)
          ·
            refine ⟨768890175125824080027149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2050373800335530880072397 768890175125824080027149)
            ·
              refine ⟨288333815672184030010181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 768890175125824080027149 288333815672184030010181)
              ·
                refine ⟨54062590438534505626909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 288333815672184030010181 54062590438534505626909)
                ·
                  rfl

theorem cell20_355342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_355342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355342 prefixEnd_355342 := by exact prefixLift 355342
  have htrace : WordTrace (prefixWord ++ tailWord_355342) baseStart_355342 baseEnd_355342 := by
    simpa [prefixWord, tailWord_355342, baseEnd_355342] using wordTrace_append hprefix tailTrace_355342
  have hstable : (prefixWord ++ tailWord_355342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355342).length < 2 ^ (prefixWord ++ tailWord_355342).sum := by decide
  have hdescent : baseEnd_355342 < baseStart_355342 := by decide
  rcases family_descends (prefixWord ++ tailWord_355342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355414 : List Nat := [5, 2, 2, 1, 3, 1, 6]
def baseStart_355414 : Nat := 118140960795 + 355414 * 2 ^ 59
def prefixEnd_355414 : Nat := 4983230072969 + 3 ^ 40 * 355414 * 2
def baseEnd_355414 : Nat := 18024514897499029608937

theorem tailTrace_355414 : CollatzResearch.WordTrace tailWord_355414 prefixEnd_355414 18024514897499029608937 := by
  unfold tailWord_355414
  simp only [CollatzResearch.WordTrace]
  refine ⟨810188345900203295234081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8642009022935501815830197 810188345900203295234081)
  ·
    refine ⟨607641259425152471425561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 810188345900203295234081 607641259425152471425561)
    ·
      refine ⟨455730944568864353569171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 607641259425152471425561 455730944568864353569171)
      ·
        refine ⟨683596416853296530353757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455730944568864353569171 683596416853296530353757)
        ·
          refine ⟨256348656319986198882659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 683596416853296530353757 256348656319986198882659)
          ·
            refine ⟨384522984479979298323989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256348656319986198882659 384522984479979298323989)
            ·
              refine ⟨18024514897499029608937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 384522984479979298323989 18024514897499029608937)
              ·
                rfl

theorem cell20_355414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 6].length) (baseStart_355414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355414 prefixEnd_355414 := by exact prefixLift 355414
  have htrace : WordTrace (prefixWord ++ tailWord_355414) baseStart_355414 baseEnd_355414 := by
    simpa [prefixWord, tailWord_355414, baseEnd_355414] using wordTrace_append hprefix tailTrace_355414
  have hstable : (prefixWord ++ tailWord_355414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355414).length < 2 ^ (prefixWord ++ tailWord_355414).sum := by decide
  have hdescent : baseEnd_355414 < baseStart_355414 := by decide
  rcases family_descends (prefixWord ++ tailWord_355414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355453 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_355453 : Nat := 118140960795 + 355453 * 2 ^ 59
def prefixEnd_355453 : Nat := 4983230072969 + 3 ^ 40 * 355453 * 2
def baseEnd_355453 : Nat := 162238434740180464180273

theorem tailTrace_355453 : CollatzResearch.WordTrace tailWord_355453 prefixEnd_355453 162238434740180464180273 := by
  unfold tailWord_355453
  simp only [CollatzResearch.WordTrace]
  refine ⟨12964435981261962384415013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8642957320841308256276675 12964435981261962384415013)
  ·
    refine ⟨2430831746486617947077815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12964435981261962384415013 2430831746486617947077815)
    ·
      refine ⟨3646247619729926920616723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2430831746486617947077815 3646247619729926920616723)
      ·
        refine ⟨5469371429594890380925085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3646247619729926920616723 5469371429594890380925085)
        ·
          refine ⟨2051014286098083892846907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5469371429594890380925085 2051014286098083892846907)
          ·
            refine ⟨3076521429147125839270361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2051014286098083892846907 3076521429147125839270361)
            ·
              refine ⟨2307391071860344379452771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3076521429147125839270361 2307391071860344379452771)
              ·
                refine ⟨3461086607790516569179157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307391071860344379452771 3461086607790516569179157)
                ·
                  refine ⟨162238434740180464180273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3461086607790516569179157 162238434740180464180273)
                  ·
                    rfl

theorem cell20_355453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_355453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355453 prefixEnd_355453 := by exact prefixLift 355453
  have htrace : WordTrace (prefixWord ++ tailWord_355453) baseStart_355453 baseEnd_355453 := by
    simpa [prefixWord, tailWord_355453, baseEnd_355453] using wordTrace_append hprefix tailTrace_355453
  have hstable : (prefixWord ++ tailWord_355453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355453).length < 2 ^ (prefixWord ++ tailWord_355453).sum := by decide
  have hdescent : baseEnd_355453 < baseStart_355453 := by decide
  rcases family_descends (prefixWord ++ tailWord_355453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355467 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_355467 : Nat := 118140960795 + 355467 * 2 ^ 59
def prefixEnd_355467 : Nat := 4983230072969 + 3 ^ 40 * 355467 * 2
def baseEnd_355467 : Nat := 162244824721658637713549

theorem tailTrace_355467 : CollatzResearch.WordTrace tailWord_355467 prefixEnd_355467 162244824721658637713549 := by
  unfold tailWord_355467
  simp only [CollatzResearch.WordTrace]
  refine ⟨12964946603211242775424655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8643297735474161850283103 12964946603211242775424655)
  ·
    refine ⟨19447419904816864163136983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12964946603211242775424655 19447419904816864163136983)
    ·
      refine ⟨29171129857225296244705475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19447419904816864163136983 29171129857225296244705475)
      ·
        refine ⟨43756694785837944367058213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29171129857225296244705475 43756694785837944367058213)
        ·
          refine ⟨8204380272344614568823415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43756694785837944367058213 8204380272344614568823415)
          ·
            refine ⟨12306570408516921853235123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8204380272344614568823415 12306570408516921853235123)
            ·
              refine ⟨18459855612775382779852685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12306570408516921853235123 18459855612775382779852685)
              ·
                refine ⟨6922445854790768542444757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18459855612775382779852685 6922445854790768542444757)
                ·
                  refine ⟨162244824721658637713549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6922445854790768542444757 162244824721658637713549)
                  ·
                    rfl

theorem cell20_355467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_355467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355467 prefixEnd_355467 := by exact prefixLift 355467
  have htrace : WordTrace (prefixWord ++ tailWord_355467) baseStart_355467 baseEnd_355467 := by
    simpa [prefixWord, tailWord_355467, baseEnd_355467] using wordTrace_append hprefix tailTrace_355467
  have hstable : (prefixWord ++ tailWord_355467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355467).length < 2 ^ (prefixWord ++ tailWord_355467).sum := by decide
  have hdescent : baseEnd_355467 < baseStart_355467 := by decide
  rcases family_descends (prefixWord ++ tailWord_355467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355542 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_355542 : Nat := 118140960795 + 355542 * 2 ^ 59
def prefixEnd_355542 : Nat := 4983230072969 + 3 ^ 40 * 355542 * 2
def baseEnd_355542 : Nat := 162279056765291710213243

theorem tailTrace_355542 : CollatzResearch.WordTrace tailWord_355542 prefixEnd_355542 162279056765291710213243 := by
  unfold tailWord_355542
  simp only [CollatzResearch.WordTrace]
  refine ⟨810480129871220661525305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8645121385293020389603253 810480129871220661525305)
  ·
    refine ⟨607860097403415496143979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 810480129871220661525305 607860097403415496143979)
    ·
      refine ⟨911790146105123244215969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607860097403415496143979 911790146105123244215969)
      ·
        refine ⟨683842609578842433161977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 911790146105123244215969 683842609578842433161977)
        ·
          refine ⟨512881957184131824871483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683842609578842433161977 512881957184131824871483)
          ·
            refine ⟨769322935776197737307225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512881957184131824871483 769322935776197737307225)
            ·
              refine ⟨576992201832148302980419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769322935776197737307225 576992201832148302980419)
              ·
                refine ⟨865488302748222454470629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576992201832148302980419 865488302748222454470629)
                ·
                  refine ⟨162279056765291710213243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865488302748222454470629 162279056765291710213243)
                  ·
                    rfl

theorem cell20_355542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_355542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355542 prefixEnd_355542 := by exact prefixLift 355542
  have htrace : WordTrace (prefixWord ++ tailWord_355542) baseStart_355542 baseEnd_355542 := by
    simpa [prefixWord, tailWord_355542, baseEnd_355542] using wordTrace_append hprefix tailTrace_355542
  have hstable : (prefixWord ++ tailWord_355542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355542).length < 2 ^ (prefixWord ++ tailWord_355542).sum := by decide
  have hdescent : baseEnd_355542 < baseStart_355542 := by decide
  rcases family_descends (prefixWord ++ tailWord_355542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355580 : List Nat := [2, 2, 2, 1, 5, 2, 1, 3, 2]
def baseStart_355580 : Nat := 118140960795 + 355580 * 2 ^ 59
def prefixEnd_355580 : Nat := 4983230072969 + 3 ^ 40 * 355580 * 2
def baseEnd_355580 : Nat := 162296401000732466946421

theorem tailTrace_355580 : CollatzResearch.WordTrace tailWord_355580 prefixEnd_355580 162296401000732466946421 := by
  unfold tailWord_355580
  simp only [CollatzResearch.WordTrace]
  refine ⟨6484534025900931537144097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8646045367867908716192129 6484534025900931537144097)
  ·
    refine ⟨4863400519425698652858073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6484534025900931537144097 4863400519425698652858073)
    ·
      refine ⟨3647550389569273989643555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4863400519425698652858073 3647550389569273989643555)
      ·
        refine ⟨5471325584353910984465333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647550389569273989643555 5471325584353910984465333)
        ·
          refine ⟨512936773533179154793625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5471325584353910984465333 512936773533179154793625)
          ·
            refine ⟨384702580149884366095219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512936773533179154793625 384702580149884366095219)
            ·
              refine ⟨577053870224826549142829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384702580149884366095219 577053870224826549142829)
              ·
                refine ⟨216395201334309955928561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 577053870224826549142829 216395201334309955928561)
                ·
                  refine ⟨162296401000732466946421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216395201334309955928561 162296401000732466946421)
                  ·
                    rfl

theorem cell20_355580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_355580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355580 prefixEnd_355580 := by exact prefixLift 355580
  have htrace : WordTrace (prefixWord ++ tailWord_355580) baseStart_355580 baseEnd_355580 := by
    simpa [prefixWord, tailWord_355580, baseEnd_355580] using wordTrace_append hprefix tailTrace_355580
  have hstable : (prefixWord ++ tailWord_355580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355580).length < 2 ^ (prefixWord ++ tailWord_355580).sum := by decide
  have hdescent : baseEnd_355580 < baseStart_355580 := by decide
  rcases family_descends (prefixWord ++ tailWord_355580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355598 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_355598 : Nat := 118140960795 + 355598 * 2 ^ 59
def prefixEnd_355598 : Nat := 4983230072969 + 3 ^ 40 * 355598 * 2
def baseEnd_355598 : Nat := 162304616691204404346347

theorem tailTrace_355598 : CollatzResearch.WordTrace tailWord_355598 prefixEnd_355598 162304616691204404346347 := by
  unfold tailWord_355598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621215570717081518555431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8646483043824434765628965 1621215570717081518555431)
  ·
    refine ⟨2431823356075622277833147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1621215570717081518555431 2431823356075622277833147)
    ·
      refine ⟨3647735034113433416749721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2431823356075622277833147 3647735034113433416749721)
      ·
        refine ⟨2735801275585075062562291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3647735034113433416749721 2735801275585075062562291)
        ·
          refine ⟨4103701913377612593843437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2735801275585075062562291 4103701913377612593843437)
          ·
            refine ⟨1538888217516604722691289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4103701913377612593843437 1538888217516604722691289)
            ·
              refine ⟨1154166163137453542018467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538888217516604722691289 1154166163137453542018467)
              ·
                refine ⟨1731249244706180313027701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154166163137453542018467 1731249244706180313027701)
                ·
                  refine ⟨162304616691204404346347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1731249244706180313027701 162304616691204404346347)
                  ·
                    rfl

theorem cell20_355598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_355598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355598 prefixEnd_355598 := by exact prefixLift 355598
  have htrace : WordTrace (prefixWord ++ tailWord_355598) baseStart_355598 baseEnd_355598 := by
    simpa [prefixWord, tailWord_355598, baseEnd_355598] using wordTrace_append hprefix tailTrace_355598
  have hstable : (prefixWord ++ tailWord_355598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355598).length < 2 ^ (prefixWord ++ tailWord_355598).sum := by decide
  have hdescent : baseEnd_355598 < baseStart_355598 := by decide
  rcases family_descends (prefixWord ++ tailWord_355598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355601 : List Nat := [1, 2, 2, 1, 1, 4, 5, 2, 2]
def baseStart_355601 : Nat := 118140960795 + 355601 * 2 ^ 59
def prefixEnd_355601 : Nat := 4983230072969 + 3 ^ 40 * 355601 * 2
def baseEnd_355601 : Nat := 162305985972949727246335

theorem tailTrace_355601 : CollatzResearch.WordTrace tailWord_355601 prefixEnd_355601 162305985972949727246335 := by
  unfold tailWord_355601
  simp only [CollatzResearch.WordTrace]
  refine ⟨12969833984725783660802657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8646555989817189107201771 12969833984725783660802657)
  ·
    refine ⟨9727375488544337745601993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12969833984725783660802657 9727375488544337745601993)
    ·
      refine ⟨7295531616408253309201495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9727375488544337745601993 7295531616408253309201495)
      ·
        refine ⟨10943297424612379963802243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7295531616408253309201495 10943297424612379963802243)
        ·
          refine ⟨16414946136918569945703365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10943297424612379963802243 16414946136918569945703365)
          ·
            refine ⟨3077802400672231864819381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16414946136918569945703365 3077802400672231864819381)
            ·
              refine ⟨288543975063021737326817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3077802400672231864819381 288543975063021737326817)
              ·
                refine ⟨216407981297266302995113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288543975063021737326817 216407981297266302995113)
                ·
                  refine ⟨162305985972949727246335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216407981297266302995113 162305985972949727246335)
                  ·
                    rfl

theorem cell20_355601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_355601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355601 prefixEnd_355601 := by exact prefixLift 355601
  have htrace : WordTrace (prefixWord ++ tailWord_355601) baseStart_355601 baseEnd_355601 := by
    simpa [prefixWord, tailWord_355601, baseEnd_355601] using wordTrace_append hprefix tailTrace_355601
  have hstable : (prefixWord ++ tailWord_355601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355601).length < 2 ^ (prefixWord ++ tailWord_355601).sum := by decide
  have hdescent : baseEnd_355601 < baseStart_355601 := by decide
  rcases family_descends (prefixWord ++ tailWord_355601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355612 : List Nat := [2, 2, 3, 1, 1, 1, 3, 7]
def baseStart_355612 : Nat := 118140960795 + 355612 * 2 ^ 59
def prefixEnd_355612 : Nat := 4983230072969 + 3 ^ 40 * 355612 * 2
def baseEnd_355612 : Nat := 54103668890894192626541

theorem tailTrace_355612 : CollatzResearch.WordTrace tailWord_355612 prefixEnd_355612 54103668890894192626541 := by
  unfold tailWord_355612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6485117593842966269726545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8646823458457288359635393 6485117593842966269726545)
  ·
    refine ⟨4863838195382224702294909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6485117593842966269726545 4863838195382224702294909)
    ·
      refine ⟨1823939323268334263360591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4863838195382224702294909 1823939323268334263360591)
      ·
        refine ⟨2735908984902501395040887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1823939323268334263360591 2735908984902501395040887)
        ·
          refine ⟨4103863477353752092561331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2735908984902501395040887 4103863477353752092561331)
          ·
            refine ⟨6155795216030628138841997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103863477353752092561331 6155795216030628138841997)
            ·
              refine ⟨2308423206011485552065749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6155795216030628138841997 2308423206011485552065749)
              ·
                refine ⟨54103668890894192626541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2308423206011485552065749 54103668890894192626541)
                ·
                  rfl

theorem cell20_355612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_355612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355612 prefixEnd_355612 := by exact prefixLift 355612
  have htrace : WordTrace (prefixWord ++ tailWord_355612) baseStart_355612 baseEnd_355612 := by
    simpa [prefixWord, tailWord_355612, baseEnd_355612] using wordTrace_append hprefix tailTrace_355612
  have hstable : (prefixWord ++ tailWord_355612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355612).length < 2 ^ (prefixWord ++ tailWord_355612).sum := by decide
  have hdescent : baseEnd_355612 < baseStart_355612 := by decide
  rcases family_descends (prefixWord ++ tailWord_355612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355615 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 3]
def baseStart_355615 : Nat := 118140960795 + 355615 * 2 ^ 59
def prefixEnd_355615 : Nat := 4983230072969 + 3 ^ 40 * 355615 * 2
def baseEnd_355615 : Nat := 162312375954427900779611

theorem tailTrace_355615 : CollatzResearch.WordTrace tailWord_355615 prefixEnd_355615 162312375954427900779611 := by
  unfold tailWord_355615
  simp only [CollatzResearch.WordTrace]
  refine ⟨12970344606675064051812299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8646896404450042701208199 12970344606675064051812299)
  ·
    refine ⟨19455516910012596077718449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12970344606675064051812299 19455516910012596077718449)
    ·
      refine ⟨14591637682509447058288837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19455516910012596077718449 14591637682509447058288837)
      ·
        refine ⟨2735932065470521323429157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14591637682509447058288837 2735932065470521323429157)
        ·
          refine ⟨512987262275722748142967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2735932065470521323429157 512987262275722748142967)
          ·
            refine ⟨769480893413584122214451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512987262275722748142967 769480893413584122214451)
            ·
              refine ⟨1154221340120376183321677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769480893413584122214451 1154221340120376183321677)
              ·
                refine ⟨432833002545141068745629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1154221340120376183321677 432833002545141068745629)
                ·
                  refine ⟨162312375954427900779611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432833002545141068745629 162312375954427900779611)
                  ·
                    rfl

theorem cell20_355615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 3].length) (baseStart_355615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355615 prefixEnd_355615 := by exact prefixLift 355615
  have htrace : WordTrace (prefixWord ++ tailWord_355615) baseStart_355615 baseEnd_355615 := by
    simpa [prefixWord, tailWord_355615, baseEnd_355615] using wordTrace_append hprefix tailTrace_355615
  have hstable : (prefixWord ++ tailWord_355615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355615).length < 2 ^ (prefixWord ++ tailWord_355615).sum := by decide
  have hdescent : baseEnd_355615 < baseStart_355615 := by decide
  rcases family_descends (prefixWord ++ tailWord_355615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355657 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_355657 : Nat := 118140960795 + 355657 * 2 ^ 59
def prefixEnd_355657 : Nat := 4983230072969 + 3 ^ 40 * 355657 * 2
def baseEnd_355657 : Nat := 162331545898862421379439

theorem tailTrace_355657 : CollatzResearch.WordTrace tailWord_355657 prefixEnd_355657 162331545898862421379439 := by
  unfold tailWord_355657
  simp only [CollatzResearch.WordTrace]
  refine ⟨12971876472522905224841225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8647917648348603483227483 12971876472522905224841225)
  ·
    refine ⟨9728907354392178918630919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12971876472522905224841225 9728907354392178918630919)
    ·
      refine ⟨14593361031588268377946379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9728907354392178918630919 14593361031588268377946379)
      ·
        refine ⟨21890041547382402566919569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14593361031588268377946379 21890041547382402566919569)
        ·
          refine ⟨16417531160536801925189677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21890041547382402566919569 16417531160536801925189677)
          ·
            refine ⟨6156574185201300721946129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16417531160536801925189677 6156574185201300721946129)
            ·
              refine ⟨4617430638900975541459597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6156574185201300721946129 4617430638900975541459597)
              ·
                refine ⟨1731536489587865828047349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4617430638900975541459597 1731536489587865828047349)
                ·
                  refine ⟨162331545898862421379439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1731536489587865828047349 162331545898862421379439)
                  ·
                    rfl

theorem cell20_355657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_355657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355657 prefixEnd_355657 := by exact prefixLift 355657
  have htrace : WordTrace (prefixWord ++ tailWord_355657) baseStart_355657 baseEnd_355657 := by
    simpa [prefixWord, tailWord_355657, baseEnd_355657] using wordTrace_append hprefix tailTrace_355657
  have hstable : (prefixWord ++ tailWord_355657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355657).length < 2 ^ (prefixWord ++ tailWord_355657).sum := by decide
  have hdescent : baseEnd_355657 < baseStart_355657 := by decide
  rcases family_descends (prefixWord ++ tailWord_355657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355674 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_355674 : Nat := 118140960795 + 355674 * 2 ^ 59
def prefixEnd_355674 : Nat := 4983230072969 + 3 ^ 40 * 355674 * 2
def baseEnd_355674 : Nat := 162339305162085917812703

theorem tailTrace_355674 : CollatzResearch.WordTrace tailWord_355674 prefixEnd_355674 162339305162085917812703 := by
  unfold tailWord_355674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3243124128365329282052519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8648331008974211418806717 3243124128365329282052519)
  ·
    refine ⟨4864686192547993923078779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3243124128365329282052519 4864686192547993923078779)
    ·
      refine ⟨7297029288821990884618169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4864686192547993923078779 7297029288821990884618169)
      ·
        refine ⟨5472771966616493163463627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7297029288821990884618169 5472771966616493163463627)
        ·
          refine ⟨8209157949924739745195441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5472771966616493163463627 8209157949924739745195441)
          ·
            refine ⟨6156868462443554808896581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8209157949924739745195441 6156868462443554808896581)
            ·
              refine ⟨1154412836708166526668109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6156868462443554808896581 1154412836708166526668109)
              ·
                refine ⟨432904813765562447500541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1154412836708166526668109 432904813765562447500541)
                ·
                  refine ⟨162339305162085917812703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432904813765562447500541 162339305162085917812703)
                  ·
                    rfl

theorem cell20_355674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_355674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355674 prefixEnd_355674 := by exact prefixLift 355674
  have htrace : WordTrace (prefixWord ++ tailWord_355674) baseStart_355674 baseEnd_355674 := by
    simpa [prefixWord, tailWord_355674, baseEnd_355674] using wordTrace_append hprefix tailTrace_355674
  have hstable : (prefixWord ++ tailWord_355674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355674).length < 2 ^ (prefixWord ++ tailWord_355674).sum := by decide
  have hdescent : baseEnd_355674 < baseStart_355674 := by decide
  rcases family_descends (prefixWord ++ tailWord_355674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355695 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_355695 : Nat := 118140960795 + 355695 * 2 ^ 59
def prefixEnd_355695 : Nat := 4983230072969 + 3 ^ 40 * 355695 * 2
def baseEnd_355695 : Nat := 162348890134303178112617

theorem tailTrace_355695 : CollatzResearch.WordTrace tailWord_355695 prefixEnd_355695 162348890134303178112617 := by
  unfold tailWord_355695
  simp only [CollatzResearch.WordTrace]
  refine ⟨12973262446385237714724539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8648841630923491809816359 12973262446385237714724539)
  ·
    refine ⟨19459893669577856572086809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12973262446385237714724539 19459893669577856572086809)
    ·
      refine ⟨14594920252183392429065107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19459893669577856572086809 14594920252183392429065107)
      ·
        refine ⟨21892380378275088643597661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14594920252183392429065107 21892380378275088643597661)
        ·
          refine ⟨8209642641853158241349123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21892380378275088643597661 8209642641853158241349123)
          ·
            refine ⟨12314463962779737362023685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8209642641853158241349123 12314463962779737362023685)
            ·
              refine ⟨2308961993021200755379441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12314463962779737362023685 2308961993021200755379441)
              ·
                refine ⟨1731721494765900566534581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2308961993021200755379441 1731721494765900566534581)
                ·
                  refine ⟨162348890134303178112617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1731721494765900566534581 162348890134303178112617)
                  ·
                    rfl

theorem cell20_355695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_355695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355695 prefixEnd_355695 := by exact prefixLift 355695
  have htrace : WordTrace (prefixWord ++ tailWord_355695) baseStart_355695 baseEnd_355695 := by
    simpa [prefixWord, tailWord_355695, baseEnd_355695] using wordTrace_append hprefix tailTrace_355695
  have hstable : (prefixWord ++ tailWord_355695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355695).length < 2 ^ (prefixWord ++ tailWord_355695).sum := by decide
  have hdescent : baseEnd_355695 < baseStart_355695 := by decide
  rcases family_descends (prefixWord ++ tailWord_355695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355719 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_355719 : Nat := 118140960795 + 355719 * 2 ^ 59
def prefixEnd_355719 : Nat := 4983230072969 + 3 ^ 40 * 355719 * 2
def baseEnd_355719 : Nat := 162359844388265761312519

theorem tailTrace_355719 : CollatzResearch.WordTrace tailWord_355719 prefixEnd_355719 162359844388265761312519 := by
  unfold tailWord_355719
  simp only [CollatzResearch.WordTrace]
  refine ⟨12974137798298289813598211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8649425198865526542398807 12974137798298289813598211)
  ·
    refine ⟨19461206697447434720397317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12974137798298289813598211 19461206697447434720397317)
    ·
      refine ⟨3648976255771394010074497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19461206697447434720397317 3648976255771394010074497)
      ·
        refine ⟨2736732191828545507555873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3648976255771394010074497 2736732191828545507555873)
        ·
          refine ⟨2052549143871409130666905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2736732191828545507555873 2052549143871409130666905)
          ·
            refine ⟨1539411857903556848000179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2052549143871409130666905 1539411857903556848000179)
            ·
              refine ⟨2309117786855335272000269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539411857903556848000179 2309117786855335272000269)
              ·
                refine ⟨865919170070750727000101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2309117786855335272000269 865919170070750727000101)
                ·
                  refine ⟨162359844388265761312519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865919170070750727000101 162359844388265761312519)
                  ·
                    rfl

theorem cell20_355719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_355719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355719 prefixEnd_355719 := by exact prefixLift 355719
  have htrace : WordTrace (prefixWord ++ tailWord_355719) baseStart_355719 baseEnd_355719 := by
    simpa [prefixWord, tailWord_355719, baseEnd_355719] using wordTrace_append hprefix tailTrace_355719
  have hstable : (prefixWord ++ tailWord_355719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355719).length < 2 ^ (prefixWord ++ tailWord_355719).sum := by decide
  have hdescent : baseEnd_355719 < baseStart_355719 := by decide
  rcases family_descends (prefixWord ++ tailWord_355719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355743 : List Nat := [1, 1, 2, 5, 1, 2, 4, 4]
def baseStart_355743 : Nat := 118140960795 + 355743 * 2 ^ 59
def prefixEnd_355743 : Nat := 4983230072969 + 3 ^ 40 * 355743 * 2
def baseEnd_355743 : Nat := 54123599547409448170807

theorem tailTrace_355743 : CollatzResearch.WordTrace tailWord_355743 prefixEnd_355743 54123599547409448170807 := by
  unfold tailWord_355743
  simp only [CollatzResearch.WordTrace]
  refine ⟨12975013150211341912471883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8650008766807561274981255 12975013150211341912471883)
  ·
    refine ⟨19462519725317012868707825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12975013150211341912471883 19462519725317012868707825)
    ·
      refine ⟨14596889793987759651530869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19462519725317012868707825 14596889793987759651530869)
      ·
        refine ⟨1368458418186352467331019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14596889793987759651530869 1368458418186352467331019)
        ·
          refine ⟨2052687627279528700996529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368458418186352467331019 2052687627279528700996529)
          ·
            refine ⟨1539515720459646525747397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2052687627279528700996529 1539515720459646525747397)
            ·
              refine ⟨288659197586183723577637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1539515720459646525747397 288659197586183723577637)
              ·
                refine ⟨54123599547409448170807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 288659197586183723577637 54123599547409448170807)
                ·
                  rfl

theorem cell20_355743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 4].length) (baseStart_355743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355743 prefixEnd_355743 := by exact prefixLift 355743
  have htrace : WordTrace (prefixWord ++ tailWord_355743) baseStart_355743 baseEnd_355743 := by
    simpa [prefixWord, tailWord_355743, baseEnd_355743] using wordTrace_append hprefix tailTrace_355743
  have hstable : (prefixWord ++ tailWord_355743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355743).length < 2 ^ (prefixWord ++ tailWord_355743).sum := by decide
  have hdescent : baseEnd_355743 < baseStart_355743 := by decide
  rcases family_descends (prefixWord ++ tailWord_355743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355802 : List Nat := [3, 1, 1, 2, 3, 2, 2, 6]
def baseStart_355802 : Nat := 118140960795 + 355802 * 2 ^ 59
def prefixEnd_355802 : Nat := 4983230072969 + 3 ^ 40 * 355802 * 2
def baseEnd_355802 : Nat := 54132575949962120515171

theorem tailTrace_355802 : CollatzResearch.WordTrace tailWord_355802 prefixEnd_355802 54132575949962120515171 := by
  unfold tailWord_355802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244291264249398747217415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8651443371331729992579773 3244291264249398747217415)
  ·
    refine ⟨4866436896374098120826123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3244291264249398747217415 4866436896374098120826123)
    ·
      refine ⟨7299655344561147181239185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4866436896374098120826123 7299655344561147181239185)
      ·
        refine ⟨5474741508420860385929389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7299655344561147181239185 5474741508420860385929389)
        ·
          refine ⟨2053028065657822644723521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5474741508420860385929389 2053028065657822644723521)
          ·
            refine ⟨1539771049243366983542641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2053028065657822644723521 1539771049243366983542641)
            ·
              refine ⟨1154828286932525237656981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539771049243366983542641 1154828286932525237656981)
              ·
                refine ⟨54132575949962120515171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1154828286932525237656981 54132575949962120515171)
                ·
                  rfl

theorem cell20_355802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_355802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355802 prefixEnd_355802 := by exact prefixLift 355802
  have htrace : WordTrace (prefixWord ++ tailWord_355802) baseStart_355802 baseEnd_355802 := by
    simpa [prefixWord, tailWord_355802, baseEnd_355802] using wordTrace_append hprefix tailTrace_355802
  have hstable : (prefixWord ++ tailWord_355802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355802).length < 2 ^ (prefixWord ++ tailWord_355802).sum := by decide
  have hdescent : baseEnd_355802 < baseStart_355802 := by decide
  rcases family_descends (prefixWord ++ tailWord_355802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355916 : List Nat := [2, 2, 1, 3, 1, 4, 1, 6]
def baseStart_355916 : Nat := 118140960795 + 355916 * 2 ^ 59
def prefixEnd_355916 : Nat := 4983230072969 + 3 ^ 40 * 355916 * 2
def baseEnd_355916 : Nat := 54149920185402877248349

theorem tailTrace_355916 : CollatzResearch.WordTrace tailWord_355916 prefixEnd_355916 54149920185402877248349 := by
  unfold tailWord_355916
  simp only [CollatzResearch.WordTrace]
  refine ⟨6490661489292296229259801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8654215319056394972346401 6490661489292296229259801)
  ·
    refine ⟨4867996116969222171944851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6490661489292296229259801 4867996116969222171944851)
    ·
      refine ⟨7301994175453833257917277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4867996116969222171944851 7301994175453833257917277)
      ·
        refine ⟨2738247815795187471718979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7301994175453833257917277 2738247815795187471718979)
        ·
          refine ⟨4107371723692781207578469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2738247815795187471718979 4107371723692781207578469)
          ·
            refine ⟨770132198192396476420963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4107371723692781207578469 770132198192396476420963)
            ·
              refine ⟨1155198297288594714631445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770132198192396476420963 1155198297288594714631445)
              ·
                refine ⟨54149920185402877248349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1155198297288594714631445 54149920185402877248349)
                ·
                  rfl

theorem cell20_355916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_355916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355916 prefixEnd_355916 := by exact prefixLift 355916
  have htrace : WordTrace (prefixWord ++ tailWord_355916) baseStart_355916 baseEnd_355916 := by
    simpa [prefixWord, tailWord_355916, baseEnd_355916] using wordTrace_append hprefix tailTrace_355916
  have hstable : (prefixWord ++ tailWord_355916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355916).length < 2 ^ (prefixWord ++ tailWord_355916).sum := by decide
  have hdescent : baseEnd_355916 < baseStart_355916 := by decide
  rcases family_descends (prefixWord ++ tailWord_355916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355930 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_355930 : Nat := 118140960795 + 355930 * 2 ^ 59
def prefixEnd_355930 : Nat := 4983230072969 + 3 ^ 40 * 355930 * 2
def baseEnd_355930 : Nat := 162456150537686805278323

theorem tailTrace_355930 : CollatzResearch.WordTrace tailWord_355930 prefixEnd_355930 162456150537686805278323 := by
  unfold tailWord_355930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245458400133468212382311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8654555733689248566352829 3245458400133468212382311)
  ·
    refine ⟨4868187600200202318573467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3245458400133468212382311 4868187600200202318573467)
    ·
      refine ⟨7302281400300303477860201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4868187600200202318573467 7302281400300303477860201)
      ·
        refine ⟨5476711050225227608395151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7302281400300303477860201 5476711050225227608395151)
        ·
          refine ⟨8215066575337841412592727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5476711050225227608395151 8215066575337841412592727)
          ·
            refine ⟨12322599863006762118889091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8215066575337841412592727 12322599863006762118889091)
            ·
              refine ⟨18483899794510143178333637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12322599863006762118889091 18483899794510143178333637)
              ·
                refine ⟨3465731211470651845937557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18483899794510143178333637 3465731211470651845937557)
                ·
                  refine ⟨162456150537686805278323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3465731211470651845937557 162456150537686805278323)
                  ·
                    rfl

theorem cell20_355930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_355930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355930 prefixEnd_355930 := by exact prefixLift 355930
  have htrace : WordTrace (prefixWord ++ tailWord_355930) baseStart_355930 baseEnd_355930 := by
    simpa [prefixWord, tailWord_355930, baseEnd_355930] using wordTrace_append hprefix tailTrace_355930
  have hstable : (prefixWord ++ tailWord_355930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355930).length < 2 ^ (prefixWord ++ tailWord_355930).sum := by decide
  have hdescent : baseEnd_355930 < baseStart_355930 := by decide
  rcases family_descends (prefixWord ++ tailWord_355930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355954 : List Nat := [3, 2, 1, 2, 3, 1, 1, 7]
def baseStart_355954 : Nat := 118140960795 + 355954 * 2 ^ 59
def prefixEnd_355954 : Nat := 4983230072969 + 3 ^ 40 * 355954 * 2
def baseEnd_355954 : Nat := 54155701597216462826075

theorem tailTrace_355954 : CollatzResearch.WordTrace tailWord_355954 prefixEnd_355954 54155701597216462826075 := by
  unfold tailWord_355954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245677238111731237100729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8655139301631283298935277 3245677238111731237100729)
  ·
    refine ⟨2434257928583798427825547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3245677238111731237100729 2434257928583798427825547)
    ·
      refine ⟨3651386892875697641738321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434257928583798427825547 3651386892875697641738321)
      ·
        refine ⟨2738540169656773231303741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3651386892875697641738321 2738540169656773231303741)
        ·
          refine ⟨1026952563621289961738903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2738540169656773231303741 1026952563621289961738903)
          ·
            refine ⟨1540428845431934942608355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026952563621289961738903 1540428845431934942608355)
            ·
              refine ⟨2310643268147902413912533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540428845431934942608355 2310643268147902413912533)
              ·
                refine ⟨54155701597216462826075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2310643268147902413912533 54155701597216462826075)
                ·
                  rfl

theorem cell20_355954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_355954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355954 prefixEnd_355954 := by exact prefixLift 355954
  have htrace : WordTrace (prefixWord ++ tailWord_355954) baseStart_355954 baseEnd_355954 := by
    simpa [prefixWord, tailWord_355954, baseEnd_355954] using wordTrace_append hprefix tailTrace_355954
  have hstable : (prefixWord ++ tailWord_355954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355954).length < 2 ^ (prefixWord ++ tailWord_355954).sum := by decide
  have hdescent : baseEnd_355954 < baseStart_355954 := by decide
  rcases family_descends (prefixWord ++ tailWord_355954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355957 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 3]
def baseStart_355957 : Nat := 118140960795 + 355957 * 2 ^ 59
def prefixEnd_355957 : Nat := 4983230072969 + 3 ^ 40 * 355957 * 2
def baseEnd_355957 : Nat := 162468474073394711378213

theorem tailTrace_355957 : CollatzResearch.WordTrace tailWord_355957 prefixEnd_355957 162468474073394711378213 := by
  unfold tailWord_355957
  simp only [CollatzResearch.WordTrace]
  refine ⟨12982818371436056460762125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8655212247624037640508083 12982818371436056460762125)
  ·
    refine ⟨4868556889288521172785797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12982818371436056460762125 4868556889288521172785797)
    ·
      refine ⟨912854416741597719897337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4868556889288521172785797 912854416741597719897337)
      ·
        refine ⟨684640812556198289923003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912854416741597719897337 684640812556198289923003)
        ·
          refine ⟨1026961218834297434884505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684640812556198289923003 1026961218834297434884505)
          ·
            refine ⟨770220914125723076163379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1026961218834297434884505 770220914125723076163379)
            ·
              refine ⟨1155331371188584614245069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770220914125723076163379 1155331371188584614245069)
              ·
                refine ⟨433249264195719230341901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1155331371188584614245069 433249264195719230341901)
                ·
                  refine ⟨162468474073394711378213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433249264195719230341901 162468474073394711378213)
                  ·
                    rfl

theorem cell20_355957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_355957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355957 prefixEnd_355957 := by exact prefixLift 355957
  have htrace : WordTrace (prefixWord ++ tailWord_355957) baseStart_355957 baseEnd_355957 := by
    simpa [prefixWord, tailWord_355957, baseEnd_355957] using wordTrace_append hprefix tailTrace_355957
  have hstable : (prefixWord ++ tailWord_355957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355957).length < 2 ^ (prefixWord ++ tailWord_355957).sum := by decide
  have hdescent : baseEnd_355957 < baseStart_355957 := by decide
  rcases family_descends (prefixWord ++ tailWord_355957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355968 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_355968 : Nat := 118140960795 + 355968 * 2 ^ 59
def prefixEnd_355968 : Nat := 4983230072969 + 3 ^ 40 * 355968 * 2
def baseEnd_355968 : Nat := 162473494773127562011501

theorem tailTrace_355968 : CollatzResearch.WordTrace tailWord_355968 prefixEnd_355968 162473494773127562011501 := by
  unfold tailWord_355968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491609787198102669706279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8655479716264136892941705 6491609787198102669706279)
  ·
    refine ⟨9737414680797154004559419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6491609787198102669706279 9737414680797154004559419)
    ·
      refine ⟨14606122021195731006839129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9737414680797154004559419 14606122021195731006839129)
      ·
        refine ⟨10954591515896798255129347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14606122021195731006839129 10954591515896798255129347)
        ·
          refine ⟨16431887273845197382694021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10954591515896798255129347 16431887273845197382694021)
          ·
            refine ⟨3080978863845974509255129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16431887273845197382694021 3080978863845974509255129)
            ·
              refine ⟨2310734147884480881941347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3080978863845974509255129 2310734147884480881941347)
              ·
                refine ⟨3466101221826721322912021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310734147884480881941347 3466101221826721322912021)
                ·
                  refine ⟨162473494773127562011501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3466101221826721322912021 162473494773127562011501)
                  ·
                    rfl

theorem cell20_355968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_355968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355968 prefixEnd_355968 := by exact prefixLift 355968
  have htrace : WordTrace (prefixWord ++ tailWord_355968) baseStart_355968 baseEnd_355968 := by
    simpa [prefixWord, tailWord_355968, baseEnd_355968] using wordTrace_append hprefix tailTrace_355968
  have hstable : (prefixWord ++ tailWord_355968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355968).length < 2 ^ (prefixWord ++ tailWord_355968).sum := by decide
  have hdescent : baseEnd_355968 < baseStart_355968 := by decide
  rcases family_descends (prefixWord ++ tailWord_355968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355998 : List Nat := [4, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_355998 : Nat := 118140960795 + 355998 * 2 ^ 59
def prefixEnd_355998 : Nat := 4983230072969 + 3 ^ 40 * 355998 * 2
def baseEnd_355998 : Nat := 162487187590580791011379

theorem tailTrace_355998 : CollatzResearch.WordTrace tailWord_355998 prefixEnd_355998 162487187590580791011379 := by
  unfold tailWord_355998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1623039220535940057875581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8656209176191680308669765 1623039220535940057875581)
  ·
    refine ⟨608639707700977521703343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1623039220535940057875581 608639707700977521703343)
    ·
      refine ⟨912959561551466282555015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 608639707700977521703343 912959561551466282555015)
      ·
        refine ⟨1369439342327199423832523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 912959561551466282555015 1369439342327199423832523)
        ·
          refine ⟨2054159013490799135748785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369439342327199423832523 2054159013490799135748785)
          ·
            refine ⟨1540619260118099351811589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2054159013490799135748785 1540619260118099351811589)
            ·
              refine ⟨288866111272143628464673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1540619260118099351811589 288866111272143628464673)
              ·
                refine ⟨216649583454107721348505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288866111272143628464673 216649583454107721348505)
                ·
                  refine ⟨162487187590580791011379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216649583454107721348505 162487187590580791011379)
                  ·
                    rfl

theorem cell20_355998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_355998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_355998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_355998 prefixEnd_355998 := by exact prefixLift 355998
  have htrace : WordTrace (prefixWord ++ tailWord_355998) baseStart_355998 baseEnd_355998 := by
    simpa [prefixWord, tailWord_355998, baseEnd_355998] using wordTrace_append hprefix tailTrace_355998
  have hstable : (prefixWord ++ tailWord_355998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355998).length < 2 ^ (prefixWord ++ tailWord_355998).sum := by decide
  have hdescent : baseEnd_355998 < baseStart_355998 := by decide
  rcases family_descends (prefixWord ++ tailWord_355998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356023 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 4]
def baseStart_356023 : Nat := 118140960795 + 356023 * 2 ^ 59
def prefixEnd_356023 : Nat := 4983230072969 + 3 ^ 40 * 356023 * 2
def baseEnd_356023 : Nat := 162498598271791815177943

theorem tailTrace_356023 : CollatzResearch.WordTrace tailWord_356023 prefixEnd_356023 162498598271791815177943 := by
  unfold tailWord_356023
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985225589196949732664723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8656817059464633155109815 12985225589196949732664723)
  ·
    refine ⟨19477838383795424598997085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12985225589196949732664723 19477838383795424598997085)
    ·
      refine ⟨7304189393923284224623907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19477838383795424598997085 7304189393923284224623907)
      ·
        refine ⟨10956284090884926336935861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7304189393923284224623907 10956284090884926336935861)
        ·
          refine ⟨1027151633520461844087737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10956284090884926336935861 1027151633520461844087737)
          ·
            refine ⟨770363725140346383065803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027151633520461844087737 770363725140346383065803)
            ·
              refine ⟨1155545587710519574598705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770363725140346383065803 1155545587710519574598705)
              ·
                refine ⟨866659190782889680949029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1155545587710519574598705 866659190782889680949029)
                ·
                  refine ⟨162498598271791815177943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 866659190782889680949029 162498598271791815177943)
                  ·
                    rfl

theorem cell20_356023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_356023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356023 prefixEnd_356023 := by exact prefixLift 356023
  have htrace : WordTrace (prefixWord ++ tailWord_356023) baseStart_356023 baseEnd_356023 := by
    simpa [prefixWord, tailWord_356023, baseEnd_356023] using wordTrace_append hprefix tailTrace_356023
  have hstable : (prefixWord ++ tailWord_356023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356023).length < 2 ^ (prefixWord ++ tailWord_356023).sum := by decide
  have hdescent : baseEnd_356023 < baseStart_356023 := by decide
  rcases family_descends (prefixWord ++ tailWord_356023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356040 : List Nat := [2, 1, 3, 1, 2, 2, 4, 3, 2]
def baseStart_356040 : Nat := 118140960795 + 356040 * 2 ^ 59
def prefixEnd_356040 : Nat := 4983230072969 + 3 ^ 40 * 356040 * 2
def baseEnd_356040 : Nat := 162506357535015311611207

theorem tailTrace_356040 : CollatzResearch.WordTrace tailWord_356040 prefixEnd_356040 162506357535015311611207 := by
  unfold tailWord_356040
  simp only [CollatzResearch.WordTrace]
  refine ⟨6492922815067680818016787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8657230420090241090689049 6492922815067680818016787)
  ·
    refine ⟨9739384222601521227025181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6492922815067680818016787 9739384222601521227025181)
    ·
      refine ⟨3652269083475570460134443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9739384222601521227025181 3652269083475570460134443)
      ·
        refine ⟨5478403625213355690201665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652269083475570460134443 5478403625213355690201665)
        ·
          refine ⟨4108802718910016767651249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5478403625213355690201665 4108802718910016767651249)
          ·
            refine ⟨3081602039182512575738437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108802718910016767651249 3081602039182512575738437)
            ·
              refine ⟨577800382346721107950957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3081602039182512575738437 577800382346721107950957)
              ·
                refine ⟨216675143380020415481609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 577800382346721107950957 216675143380020415481609)
                ·
                  refine ⟨162506357535015311611207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216675143380020415481609 162506357535015311611207)
                  ·
                    rfl

theorem cell20_356040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_356040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356040 prefixEnd_356040 := by exact prefixLift 356040
  have htrace : WordTrace (prefixWord ++ tailWord_356040) baseStart_356040 baseEnd_356040 := by
    simpa [prefixWord, tailWord_356040, baseEnd_356040] using wordTrace_append hprefix tailTrace_356040
  have hstable : (prefixWord ++ tailWord_356040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356040).length < 2 ^ (prefixWord ++ tailWord_356040).sum := by decide
  have hdescent : baseEnd_356040 < baseStart_356040 := by decide
  rcases family_descends (prefixWord ++ tailWord_356040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356075 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 3]
def baseStart_356075 : Nat := 118140960795 + 356075 * 2 ^ 59
def prefixEnd_356075 : Nat := 4983230072969 + 3 ^ 40 * 356075 * 2
def baseEnd_356075 : Nat := 162522332488710745444397

theorem tailTrace_356075 : CollatzResearch.WordTrace tailWord_356075 prefixEnd_356075 162522332488710745444397 := by
  unfold tailWord_356075
  simp only [CollatzResearch.WordTrace]
  refine ⟨12987122185008562613557679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8658081456672375075705119 12987122185008562613557679)
  ·
    refine ⟨19480683277512843920336519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12987122185008562613557679 19480683277512843920336519)
    ·
      refine ⟨29221024916269265880504779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19480683277512843920336519 29221024916269265880504779)
      ·
        refine ⟨43831537374403898820757169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29221024916269265880504779 43831537374403898820757169)
        ·
          refine ⟨32873653030802924115567877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43831537374403898820757169 32873653030802924115567877)
          ·
            refine ⟨6163809943275548271668977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32873653030802924115567877 6163809943275548271668977)
            ·
              refine ⟨4622857457456661203751733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6163809943275548271668977 4622857457456661203751733)
              ·
                refine ⟨433392886636561987851725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4622857457456661203751733 433392886636561987851725)
                ·
                  refine ⟨162522332488710745444397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433392886636561987851725 162522332488710745444397)
                  ·
                    rfl

theorem cell20_356075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 3].length) (baseStart_356075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356075 prefixEnd_356075 := by exact prefixLift 356075
  have htrace : WordTrace (prefixWord ++ tailWord_356075) baseStart_356075 baseEnd_356075 := by
    simpa [prefixWord, tailWord_356075, baseEnd_356075] using wordTrace_append hprefix tailTrace_356075
  have hstable : (prefixWord ++ tailWord_356075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356075).length < 2 ^ (prefixWord ++ tailWord_356075).sum := by decide
  have hdescent : baseEnd_356075 < baseStart_356075 := by decide
  rcases family_descends (prefixWord ++ tailWord_356075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356106 : List Nat := [3, 1, 2, 2, 1, 5, 6]
def baseStart_356106 : Nat := 118140960795 + 356106 * 2 ^ 59
def prefixEnd_356106 : Nat := 4983230072969 + 3 ^ 40 * 356106 * 2
def baseEnd_356106 : Nat := 18059609081490268378993

theorem tailTrace_356106 : CollatzResearch.WordTrace tailWord_356106 prefixEnd_356106 18059609081490268378993 := by
  unfold tailWord_356106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3247063211974063726984043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8658835231930836605290781 3247063211974063726984043)
  ·
    refine ⟨4870594817961095590476065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3247063211974063726984043 4870594817961095590476065)
    ·
      refine ⟨3652946113470821692857049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4870594817961095590476065 3652946113470821692857049)
      ·
        refine ⟨2739709585103116269642787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3652946113470821692857049 2739709585103116269642787)
        ·
          refine ⟨4109564377654674404464181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739709585103116269642787 4109564377654674404464181)
          ·
            refine ⟨385271660405125725418517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4109564377654674404464181 385271660405125725418517)
            ·
              refine ⟨18059609081490268378993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 385271660405125725418517 18059609081490268378993)
              ·
                rfl

theorem cell20_356106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 6].length) (baseStart_356106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356106 prefixEnd_356106 := by exact prefixLift 356106
  have htrace : WordTrace (prefixWord ++ tailWord_356106) baseStart_356106 baseEnd_356106 := by
    simpa [prefixWord, tailWord_356106, baseEnd_356106] using wordTrace_append hprefix tailTrace_356106
  have hstable : (prefixWord ++ tailWord_356106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356106).length < 2 ^ (prefixWord ++ tailWord_356106).sum := by decide
  have hdescent : baseEnd_356106 < baseStart_356106 := by decide
  rcases family_descends (prefixWord ++ tailWord_356106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356113 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 3]
def baseStart_356113 : Nat := 118140960795 + 356113 * 2 ^ 59
def prefixEnd_356113 : Nat := 4983230072969 + 3 ^ 40 * 356113 * 2
def baseEnd_356113 : Nat := 162539676724151502177575

theorem tailTrace_356113 : CollatzResearch.WordTrace tailWord_356113 prefixEnd_356113 162539676724151502177575 := by
  unfold tailWord_356113
  simp only [CollatzResearch.WordTrace]
  refine ⟨12988508158870895103440993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8659005439247263402293995 12988508158870895103440993)
  ·
    refine ⟨9741381119153171327580745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12988508158870895103440993 9741381119153171327580745)
    ·
      refine ⟨7306035839364878495685559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9741381119153171327580745 7306035839364878495685559)
      ·
        refine ⟨10959053759047317743528339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7306035839364878495685559 10959053759047317743528339)
        ·
          refine ⟨16438580638570976615292509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10959053759047317743528339 16438580638570976615292509)
          ·
            refine ⟨6164467739464116230734691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16438580638570976615292509 6164467739464116230734691)
            ·
              refine ⟨9246701609196174346102037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164467739464116230734691 9246701609196174346102037)
              ·
                refine ⟨433439137931070672473533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9246701609196174346102037 433439137931070672473533)
                ·
                  refine ⟨162539676724151502177575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433439137931070672473533 162539676724151502177575)
                  ·
                    rfl

theorem cell20_356113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_356113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356113 prefixEnd_356113 := by exact prefixLift 356113
  have htrace : WordTrace (prefixWord ++ tailWord_356113) baseStart_356113 baseEnd_356113 := by
    simpa [prefixWord, tailWord_356113, baseEnd_356113] using wordTrace_append hprefix tailTrace_356113
  have hstable : (prefixWord ++ tailWord_356113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356113).length < 2 ^ (prefixWord ++ tailWord_356113).sum := by decide
  have hdescent : baseEnd_356113 < baseStart_356113 := by decide
  rcases family_descends (prefixWord ++ tailWord_356113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356130 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_356130 : Nat := 118140960795 + 356130 * 2 ^ 59
def prefixEnd_356130 : Nat := 4983230072969 + 3 ^ 40 * 356130 * 2
def baseEnd_356130 : Nat := 162547435987374998610839

theorem tailTrace_356130 : CollatzResearch.WordTrace tailWord_356130 prefixEnd_356130 162547435987374998610839 := by
  unfold tailWord_356130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3247282049952326751702461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8659418799872871337873229 3247282049952326751702461)
  ·
    refine ⟨1217730768732122531888423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3247282049952326751702461 1217730768732122531888423)
    ·
      refine ⟨1826596153098183797832635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1217730768732122531888423 1826596153098183797832635)
      ·
        refine ⟨2739894229647275696748953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826596153098183797832635 2739894229647275696748953)
        ·
          refine ⟨2054920672235456772561715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2739894229647275696748953 2054920672235456772561715)
          ·
            refine ⟨3082381008353185158842573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054920672235456772561715 3082381008353185158842573)
            ·
              refine ⟨1155892878132444434565965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3082381008353185158842573 1155892878132444434565965)
              ·
                refine ⟨433459829299666662962237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1155892878132444434565965 433459829299666662962237)
                ·
                  refine ⟨162547435987374998610839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433459829299666662962237 162547435987374998610839)
                  ·
                    rfl

theorem cell20_356130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_356130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356130 prefixEnd_356130 := by exact prefixLift 356130
  have htrace : WordTrace (prefixWord ++ tailWord_356130) baseStart_356130 baseEnd_356130 := by
    simpa [prefixWord, tailWord_356130, baseEnd_356130] using wordTrace_append hprefix tailTrace_356130
  have hstable : (prefixWord ++ tailWord_356130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356130).length < 2 ^ (prefixWord ++ tailWord_356130).sum := by decide
  have hdescent : baseEnd_356130 < baseStart_356130 := by decide
  rcases family_descends (prefixWord ++ tailWord_356130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356168 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 3]
def baseStart_356168 : Nat := 118140960795 + 356168 * 2 ^ 59
def prefixEnd_356168 : Nat := 4983230072969 + 3 ^ 40 * 356168 * 2
def baseEnd_356168 : Nat := 162564780222815755344017

theorem tailTrace_356168 : CollatzResearch.WordTrace tailWord_356168 prefixEnd_356168 162564780222815755344017 := by
  unfold tailWord_356168
  simp only [CollatzResearch.WordTrace]
  refine ⟨6495257086835819748346579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8660342782447759664462105 6495257086835819748346579)
  ·
    refine ⟨9742885630253729622519869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6495257086835819748346579 9742885630253729622519869)
    ·
      refine ⟨3653582111345148608444951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9742885630253729622519869 3653582111345148608444951)
      ·
        refine ⟨5480373167017722912667427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3653582111345148608444951 5480373167017722912667427)
        ·
          refine ⟨8220559750526584369001141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5480373167017722912667427 8220559750526584369001141)
          ·
            refine ⟨770677476611867284593857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8220559750526584369001141 770677476611867284593857)
            ·
              refine ⟨578008107458900463445393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770677476611867284593857 578008107458900463445393)
              ·
                refine ⟨433506080594175347584045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578008107458900463445393 433506080594175347584045)
                ·
                  refine ⟨162564780222815755344017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433506080594175347584045 162564780222815755344017)
                  ·
                    rfl

theorem cell20_356168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_356168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356168 prefixEnd_356168 := by exact prefixLift 356168
  have htrace : WordTrace (prefixWord ++ tailWord_356168) baseStart_356168 baseEnd_356168 := by
    simpa [prefixWord, tailWord_356168, baseEnd_356168] using wordTrace_append hprefix tailTrace_356168
  have hstable : (prefixWord ++ tailWord_356168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356168).length < 2 ^ (prefixWord ++ tailWord_356168).sum := by decide
  have hdescent : baseEnd_356168 < baseStart_356168 := by decide
  rcases family_descends (prefixWord ++ tailWord_356168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356227 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 5]
def baseStart_356227 : Nat := 118140960795 + 356227 * 2 ^ 59
def prefixEnd_356227 : Nat := 4983230072969 + 3 ^ 40 * 356227 * 2
def baseEnd_356227 : Nat := 162591709430473772377109

theorem tailTrace_356227 : CollatzResearch.WordTrace tailWord_356227 prefixEnd_356227 162591709430473772377109 := by
  unfold tailWord_356227
  simp only [CollatzResearch.WordTrace]
  refine ⟨12992666080457892573090935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8661777386971928382060623 12992666080457892573090935)
  ·
    refine ⟨19488999120686838859636403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12992666080457892573090935 19488999120686838859636403)
    ·
      refine ⟨29233498681030258289454605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19488999120686838859636403 29233498681030258289454605)
      ·
        refine ⟨10962562005386346858545477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29233498681030258289454605 10962562005386346858545477)
        ·
          refine ⟨2055480376009940035977277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10962562005386346858545477 2055480376009940035977277)
          ·
            refine ⟨770805141003727513491479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2055480376009940035977277 770805141003727513491479)
            ·
              refine ⟨1156207711505591270237219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770805141003727513491479 1156207711505591270237219)
              ·
                refine ⟨1734311567258386905355829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156207711505591270237219 1734311567258386905355829)
                ·
                  refine ⟨162591709430473772377109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1734311567258386905355829 162591709430473772377109)
                  ·
                    rfl

theorem cell20_356227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_356227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356227 prefixEnd_356227 := by exact prefixLift 356227
  have htrace : WordTrace (prefixWord ++ tailWord_356227) baseStart_356227 baseEnd_356227 := by
    simpa [prefixWord, tailWord_356227, baseEnd_356227] using wordTrace_append hprefix tailTrace_356227
  have hstable : (prefixWord ++ tailWord_356227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356227).length < 2 ^ (prefixWord ++ tailWord_356227).sum := by decide
  have hdescent : baseEnd_356227 < baseStart_356227 := by decide
  rcases family_descends (prefixWord ++ tailWord_356227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356254 : List Nat := [4, 3, 1, 3, 1, 1, 1, 6]
def baseStart_356254 : Nat := 118140960795 + 356254 * 2 ^ 59
def prefixEnd_356254 : Nat := 4983230072969 + 3 ^ 40 * 356254 * 2
def baseEnd_356254 : Nat := 54201344322060559492333

theorem tailTrace_356254 : CollatzResearch.WordTrace tailWord_356254 prefixEnd_356254 54201344322060559492333 := by
  unfold tailWord_356254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624206356420009523040477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8662433900906717456215877 1624206356420009523040477)
  ·
    refine ⟨609077383657503571140179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1624206356420009523040477 609077383657503571140179)
    ·
      refine ⟨913616075486255356710269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 609077383657503571140179 913616075486255356710269)
      ·
        refine ⟨342606028307345758766351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 913616075486255356710269 342606028307345758766351)
        ·
          refine ⟨513909042461018638149527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342606028307345758766351 513909042461018638149527)
          ·
            refine ⟨770863563691527957224291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513909042461018638149527 770863563691527957224291)
            ·
              refine ⟨1156295345537291935836437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770863563691527957224291 1156295345537291935836437)
              ·
                refine ⟨54201344322060559492333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1156295345537291935836437 54201344322060559492333)
                ·
                  rfl

theorem cell20_356254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_356254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356254 prefixEnd_356254 := by exact prefixLift 356254
  have htrace : WordTrace (prefixWord ++ tailWord_356254) baseStart_356254 baseEnd_356254 := by
    simpa [prefixWord, tailWord_356254, baseEnd_356254] using wordTrace_append hprefix tailTrace_356254
  have hstable : (prefixWord ++ tailWord_356254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356254).length < 2 ^ (prefixWord ++ tailWord_356254).sum := by decide
  have hdescent : baseEnd_356254 < baseStart_356254 := by decide
  rcases family_descends (prefixWord ++ tailWord_356254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356285 : List Nat := [1, 4, 1, 2, 3, 2, 3, 2, 2]
def baseStart_356285 : Nat := 118140960795 + 356285 * 2 ^ 59
def prefixEnd_356285 : Nat := 4983230072969 + 3 ^ 40 * 356285 * 2
def baseEnd_356285 : Nat := 162618182210883348443539

theorem tailTrace_356285 : CollatzResearch.WordTrace tailWord_356285 prefixEnd_356285 162618182210883348443539 := by
  unfold tailWord_356285
  simp only [CollatzResearch.WordTrace]
  refine ⟨12994781514247768478702309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8663187676165178985801539 12994781514247768478702309)
  ·
    refine ⟨2436521533921456589756683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12994781514247768478702309 2436521533921456589756683)
    ·
      refine ⟨3654782300882184884635025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2436521533921456589756683 3654782300882184884635025)
      ·
        refine ⟨2741086725661638663476269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3654782300882184884635025 2741086725661638663476269)
        ·
          refine ⟨1027907522123114498803601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2741086725661638663476269 1027907522123114498803601)
          ·
            refine ⟨770930641592335874102701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027907522123114498803601 770930641592335874102701)
            ·
              refine ⟨289098990597125952788513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 770930641592335874102701 289098990597125952788513)
              ·
                refine ⟨216824242947844464591385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289098990597125952788513 216824242947844464591385)
                ·
                  refine ⟨162618182210883348443539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216824242947844464591385 162618182210883348443539)
                  ·
                    rfl

theorem cell20_356285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_356285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356285 prefixEnd_356285 := by exact prefixLift 356285
  have htrace : WordTrace (prefixWord ++ tailWord_356285) baseStart_356285 baseEnd_356285 := by
    simpa [prefixWord, tailWord_356285, baseEnd_356285] using wordTrace_append hprefix tailTrace_356285
  have hstable : (prefixWord ++ tailWord_356285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356285).length < 2 ^ (prefixWord ++ tailWord_356285).sum := by decide
  have hdescent : baseEnd_356285 < baseStart_356285 := by decide
  rcases family_descends (prefixWord ++ tailWord_356285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356296 : List Nat := [2, 1, 3, 1, 4, 2, 2, 5]
def baseStart_356296 : Nat := 118140960795 + 356296 * 2 ^ 59
def prefixEnd_356296 : Nat := 4983230072969 + 3 ^ 40 * 356296 * 2
def baseEnd_356296 : Nat := 54207734303538733025609

theorem tailTrace_356296 : CollatzResearch.WordTrace tailWord_356296 prefixEnd_356296 54207734303538733025609 := by
  unfold tailWord_356296
  simp only [CollatzResearch.WordTrace]
  refine ⟨6497591358603958678676371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8663455144805278238235161 6497591358603958678676371)
  ·
    refine ⟨9746387037905938018014557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6497591358603958678676371 9746387037905938018014557)
    ·
      refine ⟨3654895139214726756755459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9746387037905938018014557 3654895139214726756755459)
      ·
        refine ⟨5482342708822090135133189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654895139214726756755459 5482342708822090135133189)
        ·
          refine ⟨1027939257904141900337473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5482342708822090135133189 1027939257904141900337473)
          ·
            refine ⟨770954443428106425253105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027939257904141900337473 770954443428106425253105)
            ·
              refine ⟨578215832571079818939829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770954443428106425253105 578215832571079818939829)
              ·
                refine ⟨54207734303538733025609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 578215832571079818939829 54207734303538733025609)
                ·
                  rfl

theorem cell20_356296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_356296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356296 prefixEnd_356296 := by exact prefixLift 356296
  have htrace : WordTrace (prefixWord ++ tailWord_356296) baseStart_356296 baseEnd_356296 := by
    simpa [prefixWord, tailWord_356296, baseEnd_356296] using wordTrace_append hprefix tailTrace_356296
  have hstable : (prefixWord ++ tailWord_356296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356296).length < 2 ^ (prefixWord ++ tailWord_356296).sum := by decide
  have hdescent : baseEnd_356296 < baseStart_356296 := by decide
  rcases family_descends (prefixWord ++ tailWord_356296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356303 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 3]
def baseStart_356303 : Nat := 118140960795 + 356303 * 2 ^ 59
def prefixEnd_356303 : Nat := 4983230072969 + 3 ^ 40 * 356303 * 2
def baseEnd_356303 : Nat := 162626397901355285843465

theorem tailTrace_356303 : CollatzResearch.WordTrace tailWord_356303 prefixEnd_356303 162626397901355285843465 := by
  unfold tailWord_356303
  simp only [CollatzResearch.WordTrace]
  refine ⟨12995438028182557552857563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8663625352121705035238375 12995438028182557552857563)
  ·
    refine ⟨19493157042273836329286345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12995438028182557552857563 19493157042273836329286345)
    ·
      refine ⟨14619867781705377246964759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19493157042273836329286345 14619867781705377246964759)
      ·
        refine ⟨21929801672558065870447139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14619867781705377246964759 21929801672558065870447139)
        ·
          refine ⟨32894702508837098805670709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21929801672558065870447139 32894702508837098805670709)
          ·
            refine ⟨3083878360203478013031629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32894702508837098805670709 3083878360203478013031629)
            ·
              refine ⟨1156454385076304254886861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3083878360203478013031629 1156454385076304254886861)
              ·
                refine ⟨433670394403614095582573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1156454385076304254886861 433670394403614095582573)
                ·
                  refine ⟨162626397901355285843465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433670394403614095582573 162626397901355285843465)
                  ·
                    rfl

theorem cell20_356303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 3].length) (baseStart_356303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356303 prefixEnd_356303 := by exact prefixLift 356303
  have htrace : WordTrace (prefixWord ++ tailWord_356303) baseStart_356303 baseEnd_356303 := by
    simpa [prefixWord, tailWord_356303, baseEnd_356303] using wordTrace_append hprefix tailTrace_356303
  have hstable : (prefixWord ++ tailWord_356303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356303).length < 2 ^ (prefixWord ++ tailWord_356303).sum := by decide
  have hdescent : baseEnd_356303 < baseStart_356303 := by decide
  rcases family_descends (prefixWord ++ tailWord_356303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356344 : List Nat := [2, 1, 2, 1, 1, 3, 6, 2, 2]
def baseStart_356344 : Nat := 118140960795 + 356344 * 2 ^ 59
def prefixEnd_356344 : Nat := 4983230072969 + 3 ^ 40 * 356344 * 2
def baseEnd_356344 : Nat := 162645111418541365476631

theorem tailTrace_356344 : CollatzResearch.WordTrace tailWord_356344 prefixEnd_356344 162645111418541365476631 := by
  unfold tailWord_356344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6498466710517010777550043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8664622280689347703400057 6498466710517010777550043)
  ·
    refine ⟨9747700065775516166325065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6498466710517010777550043 9747700065775516166325065)
    ·
      refine ⟨7310775049331637124743799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9747700065775516166325065 7310775049331637124743799)
      ·
        refine ⟨10966162573997455687115699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7310775049331637124743799 10966162573997455687115699)
        ·
          refine ⟨16449243860996183530673549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10966162573997455687115699 16449243860996183530673549)
          ·
            refine ⟨6168466447873568824002581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16449243860996183530673549 6168466447873568824002581)
            ·
              refine ⟨289146864744073538625121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6168466447873568824002581 289146864744073538625121)
              ·
                refine ⟨216860148558055153968841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289146864744073538625121 216860148558055153968841)
                ·
                  refine ⟨162645111418541365476631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216860148558055153968841 162645111418541365476631)
                  ·
                    rfl

theorem cell20_356344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_356344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356344 prefixEnd_356344 := by exact prefixLift 356344
  have htrace : WordTrace (prefixWord ++ tailWord_356344) baseStart_356344 baseEnd_356344 := by
    simpa [prefixWord, tailWord_356344, baseEnd_356344] using wordTrace_append hprefix tailTrace_356344
  have hstable : (prefixWord ++ tailWord_356344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356344).length < 2 ^ (prefixWord ++ tailWord_356344).sum := by decide
  have hdescent : baseEnd_356344 < baseStart_356344 := by decide
  rcases family_descends (prefixWord ++ tailWord_356344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356348 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_356348 : Nat := 118140960795 + 356348 * 2 ^ 59
def prefixEnd_356348 : Nat := 4983230072969 + 3 ^ 40 * 356348 * 2
def baseEnd_356348 : Nat := 162646937127535129343281

theorem tailTrace_356348 : CollatzResearch.WordTrace tailWord_356348 prefixEnd_356348 162646937127535129343281 := by
  unfold tailWord_356348
  simp only [CollatzResearch.WordTrace]
  refine ⟨6498539656509765119122849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8664719542013020158830465 6498539656509765119122849)
  ·
    refine ⟨4873904742382323839342137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6498539656509765119122849 4873904742382323839342137)
    ·
      refine ⟨3655428556786742879506603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4873904742382323839342137 3655428556786742879506603)
      ·
        refine ⟨5483142835180114319259905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655428556786742879506603 5483142835180114319259905)
        ·
          refine ⟨4112357126385085739444929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5483142835180114319259905 4112357126385085739444929)
          ·
            refine ⟨3084267844788814304583697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4112357126385085739444929 3084267844788814304583697)
            ·
              refine ⟨2313200883591610728437773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084267844788814304583697 2313200883591610728437773)
              ·
                refine ⟨867450331346854023164165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2313200883591610728437773 867450331346854023164165)
                ·
                  refine ⟨162646937127535129343281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867450331346854023164165 162646937127535129343281)
                  ·
                    rfl

theorem cell20_356348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_356348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356348 prefixEnd_356348 := by exact prefixLift 356348
  have htrace : WordTrace (prefixWord ++ tailWord_356348) baseStart_356348 baseEnd_356348 := by
    simpa [prefixWord, tailWord_356348, baseEnd_356348] using wordTrace_append hprefix tailTrace_356348
  have hstable : (prefixWord ++ tailWord_356348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356348).length < 2 ^ (prefixWord ++ tailWord_356348).sum := by decide
  have hdescent : baseEnd_356348 < baseStart_356348 := by decide
  rcases family_descends (prefixWord ++ tailWord_356348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356386 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_356386 : Nat := 118140960795 + 356386 * 2 ^ 59
def prefixEnd_356386 : Nat := 4983230072969 + 3 ^ 40 * 356386 * 2
def baseEnd_356386 : Nat := 162664281362975886076459

theorem tailTrace_356386 : CollatzResearch.WordTrace tailWord_356386 prefixEnd_356386 162664281362975886076459 := by
  unfold tailWord_356386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3249616321720465682032253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8665643524587908485419341 3249616321720465682032253)
  ·
    refine ⟨1218606120645174630762095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3249616321720465682032253 1218606120645174630762095)
    ·
      refine ⟨1827909180967761946143143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218606120645174630762095 1827909180967761946143143)
      ·
        refine ⟨2741863771451642919214715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827909180967761946143143 2741863771451642919214715)
        ·
          refine ⟨4112795657177464378822073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741863771451642919214715 4112795657177464378822073)
          ·
            refine ⟨3084596742883098284116555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4112795657177464378822073 3084596742883098284116555)
            ·
              refine ⟨4626895114324647426174833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3084596742883098284116555 4626895114324647426174833)
              ·
                refine ⟨3470171335743485569631125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4626895114324647426174833 3470171335743485569631125)
                ·
                  refine ⟨162664281362975886076459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3470171335743485569631125 162664281362975886076459)
                  ·
                    rfl

theorem cell20_356386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_356386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356386 prefixEnd_356386 := by exact prefixLift 356386
  have htrace : WordTrace (prefixWord ++ tailWord_356386) baseStart_356386 baseEnd_356386 := by
    simpa [prefixWord, tailWord_356386, baseEnd_356386] using wordTrace_append hprefix tailTrace_356386
  have hstable : (prefixWord ++ tailWord_356386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356386).length < 2 ^ (prefixWord ++ tailWord_356386).sum := by decide
  have hdescent : baseEnd_356386 < baseStart_356386 := by decide
  rcases family_descends (prefixWord ++ tailWord_356386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356392 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 3]
def baseStart_356392 : Nat := 118140960795 + 356392 * 2 ^ 59
def prefixEnd_356392 : Nat := 4983230072969 + 3 ^ 40 * 356392 * 2
def baseEnd_356392 : Nat := 162667019926466531876435

theorem tailTrace_356392 : CollatzResearch.WordTrace tailWord_356392 prefixEnd_356392 162667019926466531876435 := by
  unfold tailWord_356392
  simp only [CollatzResearch.WordTrace]
  refine ⟨6499342062430062876423715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8665789416573417168564953 6499342062430062876423715)
  ·
    refine ⟨9749013093645094314635573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6499342062430062876423715 9749013093645094314635573)
    ·
      refine ⟨913969977529227591997085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9749013093645094314635573 913969977529227591997085)
      ·
        refine ⟨342738741573460346998907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 913969977529227591997085 342738741573460346998907)
        ·
          refine ⟨514108112360190520498361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342738741573460346998907 514108112360190520498361)
          ·
            refine ⟨385581084270142890373771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514108112360190520498361 385581084270142890373771)
            ·
              refine ⟨578371626405214335560657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385581084270142890373771 578371626405214335560657)
              ·
                refine ⟨433778719803910751670493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578371626405214335560657 433778719803910751670493)
                ·
                  refine ⟨162667019926466531876435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433778719803910751670493 162667019926466531876435)
                  ·
                    rfl

theorem cell20_356392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_356392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356392 prefixEnd_356392 := by exact prefixLift 356392
  have htrace : WordTrace (prefixWord ++ tailWord_356392) baseStart_356392 baseEnd_356392 := by
    simpa [prefixWord, tailWord_356392, baseEnd_356392] using wordTrace_append hprefix tailTrace_356392
  have hstable : (prefixWord ++ tailWord_356392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356392).length < 2 ^ (prefixWord ++ tailWord_356392).sum := by decide
  have hdescent : baseEnd_356392 < baseStart_356392 := by decide
  rcases family_descends (prefixWord ++ tailWord_356392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356403 : List Nat := [1, 1, 1, 2, 4, 1, 4, 4, 2]
def baseStart_356403 : Nat := 118140960795 + 356403 * 2 ^ 59
def prefixEnd_356403 : Nat := 4983230072969 + 3 ^ 40 * 356403 * 2
def baseEnd_356403 : Nat := 162672040626199382509723

theorem tailTrace_356403 : CollatzResearch.WordTrace tailWord_356403 prefixEnd_356403 162672040626199382509723 := by
  unfold tailWord_356403
  simp only [CollatzResearch.WordTrace]
  refine ⟨12999085327820274631497863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8666056885213516420998575 12999085327820274631497863)
  ·
    refine ⟨19498627991730411947246795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12999085327820274631497863 19498627991730411947246795)
    ·
      refine ⟨29247941987595617920870193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19498627991730411947246795 29247941987595617920870193)
      ·
        refine ⟨21935956490696713440652645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29247941987595617920870193 21935956490696713440652645)
        ·
          refine ⟨4112991842005633770122371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21935956490696713440652645 4112991842005633770122371)
          ·
            refine ⟨6169487763008450655183557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112991842005633770122371 6169487763008450655183557)
            ·
              refine ⟨1156778955564084497846917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6169487763008450655183557 1156778955564084497846917)
              ·
                refine ⟨216896054168265843346297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1156778955564084497846917 216896054168265843346297)
                ·
                  refine ⟨162672040626199382509723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216896054168265843346297 162672040626199382509723)
                  ·
                    rfl

theorem cell20_356403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 2].length) (baseStart_356403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356403 prefixEnd_356403 := by exact prefixLift 356403
  have htrace : WordTrace (prefixWord ++ tailWord_356403) baseStart_356403 baseEnd_356403 := by
    simpa [prefixWord, tailWord_356403, baseEnd_356403] using wordTrace_append hprefix tailTrace_356403
  have hstable : (prefixWord ++ tailWord_356403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356403).length < 2 ^ (prefixWord ++ tailWord_356403).sum := by decide
  have hdescent : baseEnd_356403 < baseStart_356403 := by decide
  rcases family_descends (prefixWord ++ tailWord_356403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356455 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 3]
def baseStart_356455 : Nat := 118140960795 + 356455 * 2 ^ 59
def prefixEnd_356455 : Nat := 4983230072969 + 3 ^ 40 * 356455 * 2
def baseEnd_356455 : Nat := 162695774843118312776177

theorem tailTrace_356455 : CollatzResearch.WordTrace tailWord_356455 prefixEnd_356455 162695774843118312776177 := by
  unfold tailWord_356455
  simp only [CollatzResearch.WordTrace]
  refine ⟨13000981923631887512390819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8667321282421258341593879 13000981923631887512390819)
  ·
    refine ⟨19501472885447831268586229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13000981923631887512390819 19501472885447831268586229)
    ·
      refine ⟨1828263083010734181429959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19501472885447831268586229 1828263083010734181429959)
      ·
        refine ⟨2742394624516101272144939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828263083010734181429959 2742394624516101272144939)
        ·
          refine ⟨4113591936774151908217409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742394624516101272144939 4113591936774151908217409)
          ·
            refine ⟨3085193952580613931163057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4113591936774151908217409 3085193952580613931163057)
            ·
              refine ⟨2313895464435460448372293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3085193952580613931163057 2313895464435460448372293)
              ·
                refine ⟨433855399581648834069805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2313895464435460448372293 433855399581648834069805)
                ·
                  refine ⟨162695774843118312776177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433855399581648834069805 162695774843118312776177)
                  ·
                    rfl

theorem cell20_356455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 3].length) (baseStart_356455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356455 prefixEnd_356455 := by exact prefixLift 356455
  have htrace : WordTrace (prefixWord ++ tailWord_356455) baseStart_356455 baseEnd_356455 := by
    simpa [prefixWord, tailWord_356455, baseEnd_356455] using wordTrace_append hprefix tailTrace_356455
  have hstable : (prefixWord ++ tailWord_356455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356455).length < 2 ^ (prefixWord ++ tailWord_356455).sum := by decide
  have hdescent : baseEnd_356455 < baseStart_356455 := by decide
  rcases family_descends (prefixWord ++ tailWord_356455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356458 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_356458 : Nat := 118140960795 + 356458 * 2 ^ 59
def prefixEnd_356458 : Nat := 4983230072969 + 3 ^ 40 * 356458 * 2
def baseEnd_356458 : Nat := 162697144124863635676165

theorem tailTrace_356458 : CollatzResearch.WordTrace tailWord_356458 prefixEnd_356458 162697144124863635676165 := by
  unfold tailWord_356458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250272835655254756187507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8667394228414012683166685 3250272835655254756187507)
  ·
    refine ⟨4875409253482882134281261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3250272835655254756187507 4875409253482882134281261)
    ·
      refine ⟨1828278470056080800355473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4875409253482882134281261 1828278470056080800355473)
      ·
        refine ⟨1371208852542060600266605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1828278470056080800355473 1371208852542060600266605)
        ·
          refine ⟨514203319703272725099977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1371208852542060600266605 514203319703272725099977)
          ·
            refine ⟨385652489777454543824983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514203319703272725099977 385652489777454543824983)
            ·
              refine ⟨578478734666181815737475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385652489777454543824983 578478734666181815737475)
              ·
                refine ⟨867718101999272723606213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578478734666181815737475 867718101999272723606213)
                ·
                  refine ⟨162697144124863635676165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867718101999272723606213 162697144124863635676165)
                  ·
                    rfl

theorem cell20_356458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_356458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356458 prefixEnd_356458 := by exact prefixLift 356458
  have htrace : WordTrace (prefixWord ++ tailWord_356458) baseStart_356458 baseEnd_356458 := by
    simpa [prefixWord, tailWord_356458, baseEnd_356458] using wordTrace_append hprefix tailTrace_356458
  have hstable : (prefixWord ++ tailWord_356458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356458).length < 2 ^ (prefixWord ++ tailWord_356458).sum := by decide
  have hdescent : baseEnd_356458 < baseStart_356458 := by decide
  rcases family_descends (prefixWord ++ tailWord_356458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356502 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_356502 : Nat := 118140960795 + 356502 * 2 ^ 59
def prefixEnd_356502 : Nat := 4983230072969 + 3 ^ 40 * 356502 * 2
def baseEnd_356502 : Nat := 162717226923795038209319

theorem tailTrace_356502 : CollatzResearch.WordTrace tailWord_356502 prefixEnd_356502 162717226923795038209319 := by
  unfold tailWord_356502
  simp only [CollatzResearch.WordTrace]
  refine ⟨812668509653850908709485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8668464102974409692901173 812668509653850908709485)
  ·
    refine ⟨304750691120194090766057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 812668509653850908709485 304750691120194090766057)
    ·
      refine ⟨228563018340145568074543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304750691120194090766057 228563018340145568074543)
      ·
        refine ⟨342844527510218352111815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228563018340145568074543 342844527510218352111815)
        ·
          refine ⟨514266791265327528167723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342844527510218352111815 514266791265327528167723)
          ·
            refine ⟨771400186897991292251585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514266791265327528167723 771400186897991292251585)
            ·
              refine ⟨578550140173493469188689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771400186897991292251585 578550140173493469188689)
              ·
                refine ⟨433912605130120101891517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578550140173493469188689 433912605130120101891517)
                ·
                  refine ⟨162717226923795038209319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433912605130120101891517 162717226923795038209319)
                  ·
                    rfl

theorem cell20_356502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_356502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356502 prefixEnd_356502 := by exact prefixLift 356502
  have htrace : WordTrace (prefixWord ++ tailWord_356502) baseStart_356502 baseEnd_356502 := by
    simpa [prefixWord, tailWord_356502, baseEnd_356502] using wordTrace_append hprefix tailTrace_356502
  have hstable : (prefixWord ++ tailWord_356502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356502).length < 2 ^ (prefixWord ++ tailWord_356502).sum := by decide
  have hdescent : baseEnd_356502 < baseStart_356502 := by decide
  rcases family_descends (prefixWord ++ tailWord_356502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356513 : List Nat := [1, 2, 3, 3, 1, 4, 2, 2, 2]
def baseStart_356513 : Nat := 118140960795 + 356513 * 2 ^ 59
def prefixEnd_356513 : Nat := 4983230072969 + 3 ^ 40 * 356513 * 2
def baseEnd_356513 : Nat := 162722247623527888842607

theorem tailTrace_356513 : CollatzResearch.WordTrace tailWord_356513 prefixEnd_356513 162722247623527888842607 := by
  unfold tailWord_356513
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003097357421763418002193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8668731571614508945334795 13003097357421763418002193)
  ·
    refine ⟨9752323018066322563501645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13003097357421763418002193 9752323018066322563501645)
    ·
      refine ⟨3657121131774870961313117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9752323018066322563501645 3657121131774870961313117)
      ·
        refine ⟨1371420424415576610492419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3657121131774870961313117 1371420424415576610492419)
        ·
          refine ⟨2057130636623364915738629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371420424415576610492419 2057130636623364915738629)
          ·
            refine ⟨385711994366880921700993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2057130636623364915738629 385711994366880921700993)
            ·
              refine ⟨289283995775160691275745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385711994366880921700993 289283995775160691275745)
              ·
                refine ⟨216962996831370518456809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289283995775160691275745 216962996831370518456809)
                ·
                  refine ⟨162722247623527888842607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216962996831370518456809 162722247623527888842607)
                  ·
                    rfl

theorem cell20_356513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_356513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356513 prefixEnd_356513 := by exact prefixLift 356513
  have htrace : WordTrace (prefixWord ++ tailWord_356513) baseStart_356513 baseEnd_356513 := by
    simpa [prefixWord, tailWord_356513, baseEnd_356513] using wordTrace_append hprefix tailTrace_356513
  have hstable : (prefixWord ++ tailWord_356513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356513).length < 2 ^ (prefixWord ++ tailWord_356513).sum := by decide
  have hdescent : baseEnd_356513 < baseStart_356513 := by decide
  rcases family_descends (prefixWord ++ tailWord_356513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356517 : List Nat := [1, 3, 1, 2, 1, 3, 3, 4, 2]
def baseStart_356517 : Nat := 118140960795 + 356517 * 2 ^ 59
def prefixEnd_356517 : Nat := 4983230072969 + 3 ^ 40 * 356517 * 2
def baseEnd_356517 : Nat := 162724073332521652709257

theorem tailTrace_356517 : CollatzResearch.WordTrace tailWord_356517 prefixEnd_356517 162724073332521652709257 := by
  unfold tailWord_356517
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003243249407272101147805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8668828832938181400765203 13003243249407272101147805)
  ·
    refine ⟨4876216218527727037930427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13003243249407272101147805 4876216218527727037930427)
    ·
      refine ⟨7314324327791590556895641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4876216218527727037930427 7314324327791590556895641)
      ·
        refine ⟨5485743245843692917671731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7314324327791590556895641 5485743245843692917671731)
        ·
          refine ⟨8228614868765539376507597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485743245843692917671731 8228614868765539376507597)
          ·
            refine ⟨3085730575787077266190349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8228614868765539376507597 3085730575787077266190349)
            ·
              refine ⟨1157148965920153974821381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3085730575787077266190349 1157148965920153974821381)
              ·
                refine ⟨216965431110028870279009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1157148965920153974821381 216965431110028870279009)
                ·
                  refine ⟨162724073332521652709257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216965431110028870279009 162724073332521652709257)
                  ·
                    rfl

theorem cell20_356517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_356517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356517 prefixEnd_356517 := by exact prefixLift 356517
  have htrace : WordTrace (prefixWord ++ tailWord_356517) baseStart_356517 baseEnd_356517 := by
    simpa [prefixWord, tailWord_356517, baseEnd_356517] using wordTrace_append hprefix tailTrace_356517
  have hstable : (prefixWord ++ tailWord_356517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356517).length < 2 ^ (prefixWord ++ tailWord_356517).sum := by decide
  have hdescent : baseEnd_356517 < baseStart_356517 := by decide
  rcases family_descends (prefixWord ++ tailWord_356517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356552 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_356552 : Nat := 118140960795 + 356552 * 2 ^ 59
def prefixEnd_356552 : Nat := 4983230072969 + 3 ^ 40 * 356552 * 2
def baseEnd_356552 : Nat := 162740048286217086542447

theorem tailTrace_356552 : CollatzResearch.WordTrace tailWord_356552 prefixEnd_356552 162740048286217086542447 := by
  unfold tailWord_356552
  simp only [CollatzResearch.WordTrace]
  refine ⟨6502259902140236539335955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8669679869520315385781273 6502259902140236539335955)
  ·
    refine ⟨9753389853210354809003933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6502259902140236539335955 9753389853210354809003933)
    ·
      refine ⟨3657521194953883053376475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9753389853210354809003933 3657521194953883053376475)
      ·
        refine ⟨5486281792430824580064713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657521194953883053376475 5486281792430824580064713)
        ·
          refine ⟨4114711344323118435048535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5486281792430824580064713 4114711344323118435048535)
          ·
            refine ⟨6172067016484677652572803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114711344323118435048535 6172067016484677652572803)
            ·
              refine ⟨9258100524727016478859205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6172067016484677652572803 9258100524727016478859205)
              ·
                refine ⟨1735893848386315589786101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9258100524727016478859205 1735893848386315589786101)
                ·
                  refine ⟨162740048286217086542447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1735893848386315589786101 162740048286217086542447)
                  ·
                    rfl

theorem cell20_356552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_356552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356552 prefixEnd_356552 := by exact prefixLift 356552
  have htrace : WordTrace (prefixWord ++ tailWord_356552) baseStart_356552 baseEnd_356552 := by
    simpa [prefixWord, tailWord_356552, baseEnd_356552] using wordTrace_append hprefix tailTrace_356552
  have hstable : (prefixWord ++ tailWord_356552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356552).length < 2 ^ (prefixWord ++ tailWord_356552).sum := by decide
  have hdescent : baseEnd_356552 < baseStart_356552 := by decide
  rcases family_descends (prefixWord ++ tailWord_356552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356555 : List Nat := [1, 1, 1, 1, 3, 2, 6, 3, 2]
def baseStart_356555 : Nat := 118140960795 + 356555 * 2 ^ 59
def prefixEnd_356555 : Nat := 4983230072969 + 3 ^ 40 * 356555 * 2
def baseEnd_356555 : Nat := 162741417567962409442435

theorem tailTrace_356555 : CollatzResearch.WordTrace tailWord_356555 prefixEnd_356555 162741417567962409442435 := by
  unfold tailWord_356555
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004629223269604591031119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8669752815513069727354079 13004629223269604591031119)
  ·
    refine ⟨19506943834904406886546679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13004629223269604591031119 19506943834904406886546679)
    ·
      refine ⟨29260415752356610329820019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19506943834904406886546679 29260415752356610329820019)
      ·
        refine ⟨43890623628534915494730029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29260415752356610329820019 43890623628534915494730029)
        ·
          refine ⟨16458983860700593310523761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43890623628534915494730029 16458983860700593310523761)
          ·
            refine ⟨12344237895525444982892821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16458983860700593310523761 12344237895525444982892821)
            ·
              refine ⟨578636151352755233573101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12344237895525444982892821 578636151352755233573101)
              ·
                refine ⟨216988556757283212589913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 578636151352755233573101 216988556757283212589913)
                ·
                  refine ⟨162741417567962409442435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216988556757283212589913 162741417567962409442435)
                  ·
                    rfl

theorem cell20_356555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 2].length) (baseStart_356555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356555 prefixEnd_356555 := by exact prefixLift 356555
  have htrace : WordTrace (prefixWord ++ tailWord_356555) baseStart_356555 baseEnd_356555 := by
    simpa [prefixWord, tailWord_356555, baseEnd_356555] using wordTrace_append hprefix tailTrace_356555
  have hstable : (prefixWord ++ tailWord_356555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356555).length < 2 ^ (prefixWord ++ tailWord_356555).sum := by decide
  have hdescent : baseEnd_356555 < baseStart_356555 := by decide
  rcases family_descends (prefixWord ++ tailWord_356555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356559 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_356559 : Nat := 118140960795 + 356559 * 2 ^ 59
def prefixEnd_356559 : Nat := 4983230072969 + 3 ^ 40 * 356559 * 2
def baseEnd_356559 : Nat := 162743243276956173309085

theorem tailTrace_356559 : CollatzResearch.WordTrace tailWord_356559 prefixEnd_356559 162743243276956173309085 := by
  unfold tailWord_356559
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004775115255113274176731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8669850076836742182784487 13004775115255113274176731)
  ·
    refine ⟨19507162672882669911265097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13004775115255113274176731 19507162672882669911265097)
    ·
      refine ⟨14630372004662002433448823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19507162672882669911265097 14630372004662002433448823)
      ·
        refine ⟨21945558006993003650173235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14630372004662002433448823 21945558006993003650173235)
        ·
          refine ⟨32918337010489505475259853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21945558006993003650173235 32918337010489505475259853)
          ·
            refine ⟨12344376378933564553222445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32918337010489505475259853 12344376378933564553222445)
            ·
              refine ⟨4629141142100086707458417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12344376378933564553222445 4629141142100086707458417)
              ·
                refine ⟨3471855856575065030593813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4629141142100086707458417 3471855856575065030593813)
                ·
                  refine ⟨162743243276956173309085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3471855856575065030593813 162743243276956173309085)
                  ·
                    rfl

theorem cell20_356559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_356559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356559 prefixEnd_356559 := by exact prefixLift 356559
  have htrace : WordTrace (prefixWord ++ tailWord_356559) baseStart_356559 baseEnd_356559 := by
    simpa [prefixWord, tailWord_356559, baseEnd_356559] using wordTrace_append hprefix tailTrace_356559
  have hstable : (prefixWord ++ tailWord_356559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356559).length < 2 ^ (prefixWord ++ tailWord_356559).sum := by decide
  have hdescent : baseEnd_356559 < baseStart_356559 := by decide
  rcases family_descends (prefixWord ++ tailWord_356559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356565 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 3]
def baseStart_356565 : Nat := 118140960795 + 356565 * 2 ^ 59
def prefixEnd_356565 : Nat := 4983230072969 + 3 ^ 40 * 356565 * 2
def baseEnd_356565 : Nat := 162745981840446819109061

theorem tailTrace_356565 : CollatzResearch.WordTrace tailWord_356565 prefixEnd_356565 162745981840446819109061 := by
  unfold tailWord_356565
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004993953233376298895149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8669995968822250865930099 13004993953233376298895149)
  ·
    refine ⟨4876872732462516112085681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13004993953233376298895149 4876872732462516112085681)
    ·
      refine ⟨3657654549346887084064261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4876872732462516112085681 3657654549346887084064261)
      ·
        refine ⟨685810228002541328262049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3657654549346887084064261 685810228002541328262049)
        ·
          refine ⟨514357671001905996196537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685810228002541328262049 514357671001905996196537)
          ·
            refine ⟨385768253251429497147403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514357671001905996196537 385768253251429497147403)
            ·
              refine ⟨578652379877144245721105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385768253251429497147403 578652379877144245721105)
              ·
                refine ⟨433989284907858184290829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578652379877144245721105 433989284907858184290829)
                ·
                  refine ⟨162745981840446819109061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433989284907858184290829 162745981840446819109061)
                  ·
                    rfl

theorem cell20_356565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_356565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356565 prefixEnd_356565 := by exact prefixLift 356565
  have htrace : WordTrace (prefixWord ++ tailWord_356565) baseStart_356565 baseEnd_356565 := by
    simpa [prefixWord, tailWord_356565, baseEnd_356565] using wordTrace_append hprefix tailTrace_356565
  have hstable : (prefixWord ++ tailWord_356565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356565).length < 2 ^ (prefixWord ++ tailWord_356565).sum := by decide
  have hdescent : baseEnd_356565 < baseStart_356565 := by decide
  rcases family_descends (prefixWord ++ tailWord_356565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356569 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 3]
def baseStart_356569 : Nat := 118140960795 + 356569 * 2 ^ 59
def prefixEnd_356569 : Nat := 4983230072969 + 3 ^ 40 * 356569 * 2
def baseEnd_356569 : Nat := 162747807549440582975711

theorem tailTrace_356569 : CollatzResearch.WordTrace tailWord_356569 prefixEnd_356569 162747807549440582975711 := by
  unfold tailWord_356569
  simp only [CollatzResearch.WordTrace]
  refine ⟨13005139845218884982040761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8670093230145923321360507 13005139845218884982040761)
  ·
    refine ⟨9753854883914163736530571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13005139845218884982040761 9753854883914163736530571)
    ·
      refine ⟨14630782325871245604795857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9753854883914163736530571 14630782325871245604795857)
      ·
        refine ⟨10973086744403434203596893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14630782325871245604795857 10973086744403434203596893)
        ·
          refine ⟨4114907529151287826348835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10973086744403434203596893 4114907529151287826348835)
          ·
            refine ⟨6172361293726931739523253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114907529151287826348835 6172361293726931739523253)
            ·
              refine ⟨578658871286899850580305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6172361293726931739523253 578658871286899850580305)
              ·
                refine ⟨433994153465174887935229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578658871286899850580305 433994153465174887935229)
                ·
                  refine ⟨162747807549440582975711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433994153465174887935229 162747807549440582975711)
                  ·
                    rfl

theorem cell20_356569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_356569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356569 prefixEnd_356569 := by exact prefixLift 356569
  have htrace : WordTrace (prefixWord ++ tailWord_356569) baseStart_356569 baseEnd_356569 := by
    simpa [prefixWord, tailWord_356569, baseEnd_356569] using wordTrace_append hprefix tailTrace_356569
  have hstable : (prefixWord ++ tailWord_356569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356569).length < 2 ^ (prefixWord ++ tailWord_356569).sum := by decide
  have hdescent : baseEnd_356569 < baseStart_356569 := by decide
  rcases family_descends (prefixWord ++ tailWord_356569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356576 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_356576 : Nat := 118140960795 + 356576 * 2 ^ 59
def prefixEnd_356576 : Nat := 4983230072969 + 3 ^ 40 * 356576 * 2
def baseEnd_356576 : Nat := 162751002540179669742349

theorem tailTrace_356576 : CollatzResearch.WordTrace tailWord_356576 prefixEnd_356576 162751002540179669742349 := by
  unfold tailWord_356576
  simp only [CollatzResearch.WordTrace]
  refine ⟨6502697578096762588772791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8670263437462350118363721 6502697578096762588772791)
  ·
    refine ⟨9754046367145143883159187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6502697578096762588772791 9754046367145143883159187)
    ·
      refine ⟨14631069550717715824738781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9754046367145143883159187 14631069550717715824738781)
      ·
        refine ⟨5486651081519143434277043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14631069550717715824738781 5486651081519143434277043)
        ·
          refine ⟨8229976622278715151415565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5486651081519143434277043 8229976622278715151415565)
          ·
            refine ⟨3086241233354518181780837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8229976622278715151415565 3086241233354518181780837)
            ·
              refine ⟨578670231253972159083907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3086241233354518181780837 578670231253972159083907)
              ·
                refine ⟨868005346880958238625861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578670231253972159083907 868005346880958238625861)
                ·
                  refine ⟨162751002540179669742349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 868005346880958238625861 162751002540179669742349)
                  ·
                    rfl

theorem cell20_356576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_356576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356576 prefixEnd_356576 := by exact prefixLift 356576
  have htrace : WordTrace (prefixWord ++ tailWord_356576) baseStart_356576 baseEnd_356576 := by
    simpa [prefixWord, tailWord_356576, baseEnd_356576] using wordTrace_append hprefix tailTrace_356576
  have hstable : (prefixWord ++ tailWord_356576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356576).length < 2 ^ (prefixWord ++ tailWord_356576).sum := by decide
  have hdescent : baseEnd_356576 < baseStart_356576 := by decide
  rcases family_descends (prefixWord ++ tailWord_356576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356586 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_356586 : Nat := 118140960795 + 356586 * 2 ^ 59
def prefixEnd_356586 : Nat := 4983230072969 + 3 ^ 40 * 356586 * 2
def baseEnd_356586 : Nat := 162755566812664079408975

theorem tailTrace_356586 : CollatzResearch.WordTrace tailWord_356586 prefixEnd_356586 162755566812664079408975 := by
  unfold tailWord_356586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3251439971539324221352403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8670506590771531256939741 3251439971539324221352403)
  ·
    refine ⟨4877159957308986332028605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3251439971539324221352403 4877159957308986332028605)
    ·
      refine ⟨1828934983990869874510727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4877159957308986332028605 1828934983990869874510727)
      ·
        refine ⟨2743402475986304811766091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828934983990869874510727 2743402475986304811766091)
        ·
          refine ⟨4115103713979457217649137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743402475986304811766091 4115103713979457217649137)
          ·
            refine ⟨3086327785484592913236853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4115103713979457217649137 3086327785484592913236853)
            ·
              refine ⟨289343229889180585615955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3086327785484592913236853 289343229889180585615955)
              ·
                refine ⟨434014844833770878423933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289343229889180585615955 434014844833770878423933)
                ·
                  refine ⟨162755566812664079408975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434014844833770878423933 162755566812664079408975)
                  ·
                    rfl

theorem cell20_356586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_356586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356586 prefixEnd_356586 := by exact prefixLift 356586
  have htrace : WordTrace (prefixWord ++ tailWord_356586) baseStart_356586 baseEnd_356586 := by
    simpa [prefixWord, tailWord_356586, baseEnd_356586] using wordTrace_append hprefix tailTrace_356586
  have hstable : (prefixWord ++ tailWord_356586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356586).length < 2 ^ (prefixWord ++ tailWord_356586).sum := by decide
  have hdescent : baseEnd_356586 < baseStart_356586 := by decide
  rcases family_descends (prefixWord ++ tailWord_356586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356631 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 4]
def baseStart_356631 : Nat := 118140960795 + 356631 * 2 ^ 59
def prefixEnd_356631 : Nat := 4983230072969 + 3 ^ 40 * 356631 * 2
def baseEnd_356631 : Nat := 162776106038843922908791

theorem tailTrace_356631 : CollatzResearch.WordTrace tailWord_356631 prefixEnd_356631 162776106038843922908791 := by
  unfold tailWord_356631
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007401170994269570797747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8671600780662846380531831 13007401170994269570797747)
  ·
    refine ⟨19511101756491404356196621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13007401170994269570797747 19511101756491404356196621)
    ·
      refine ⟨7316663158684276633573733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19511101756491404356196621 7316663158684276633573733)
      ·
        refine ⟨1371874342253301868795075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7316663158684276633573733 1371874342253301868795075)
        ·
          refine ⟨2057811513379952803192613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371874342253301868795075 2057811513379952803192613)
          ·
            refine ⟨385839658758741150598615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2057811513379952803192613 385839658758741150598615)
            ·
              refine ⟨578759488138111725897923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385839658758741150598615 578759488138111725897923)
              ·
                refine ⟨868139232207167588846885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578759488138111725897923 868139232207167588846885)
                ·
                  refine ⟨162776106038843922908791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 868139232207167588846885 162776106038843922908791)
                  ·
                    rfl

theorem cell20_356631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 4].length) (baseStart_356631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356631 prefixEnd_356631 := by exact prefixLift 356631
  have htrace : WordTrace (prefixWord ++ tailWord_356631) baseStart_356631 baseEnd_356631 := by
    simpa [prefixWord, tailWord_356631, baseEnd_356631] using wordTrace_append hprefix tailTrace_356631
  have hstable : (prefixWord ++ tailWord_356631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356631).length < 2 ^ (prefixWord ++ tailWord_356631).sum := by decide
  have hdescent : baseEnd_356631 < baseStart_356631 := by decide
  rcases family_descends (prefixWord ++ tailWord_356631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356676 : List Nat := [2, 3, 4, 1, 2, 8]
def baseStart_356676 : Nat := 118140960795 + 356676 * 2 ^ 59
def prefixEnd_356676 : Nat := 4983230072969 + 3 ^ 40 * 356676 * 2
def baseEnd_356676 : Nat := 6029505380186065422541

theorem tailTrace_356676 : CollatzResearch.WordTrace tailWord_356676 prefixEnd_356676 6029505380186065422541 := by
  unfold tailWord_356676
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504521227915621128092941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8672694970554161504123921 6504521227915621128092941)
  ·
    refine ⟨2439195460468357923034853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6504521227915621128092941 2439195460468357923034853)
    ·
      refine ⟨457349148837817110569035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2439195460468357923034853 457349148837817110569035)
      ·
        refine ⟨686023723256725665853553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457349148837817110569035 686023723256725665853553)
        ·
          refine ⟨514517792442544249390165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686023723256725665853553 514517792442544249390165)
          ·
            refine ⟨6029505380186065422541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 514517792442544249390165 6029505380186065422541)
            ·
              rfl

theorem cell20_356676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 8].length) (baseStart_356676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356676 prefixEnd_356676 := by exact prefixLift 356676
  have htrace : WordTrace (prefixWord ++ tailWord_356676) baseStart_356676 baseEnd_356676 := by
    simpa [prefixWord, tailWord_356676, baseEnd_356676] using wordTrace_append hprefix tailTrace_356676
  have hstable : (prefixWord ++ tailWord_356676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356676).length < 2 ^ (prefixWord ++ tailWord_356676).sum := by decide
  have hdescent : baseEnd_356676 < baseStart_356676 := by decide
  rcases family_descends (prefixWord ++ tailWord_356676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356693 : List Nat := [1, 3, 2, 2, 5, 1, 1, 5]
def baseStart_356693 : Nat := 118140960795 + 356693 * 2 ^ 59
def prefixEnd_356693 : Nat := 4983230072969 + 3 ^ 40 * 356693 * 2
def baseEnd_356693 : Nat := 54268134842749087613957

theorem tailTrace_356693 : CollatzResearch.WordTrace tailWord_356693 prefixEnd_356693 54268134842749087613957 := by
  unfold tailWord_356693
  simp only [CollatzResearch.WordTrace]
  refine ⟨13009662496769654159554733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8673108331179769439703155 13009662496769654159554733)
  ·
    refine ⟨4878623436288620309833025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13009662496769654159554733 4878623436288620309833025)
    ·
      refine ⟨3658967577216465232374769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4878623436288620309833025 3658967577216465232374769)
      ·
        refine ⟨2744225682912348924281077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3658967577216465232374769 2744225682912348924281077)
        ·
          refine ⟨257271157773032711651351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2744225682912348924281077 257271157773032711651351)
          ·
            refine ⟨385906736659549067477027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257271157773032711651351 385906736659549067477027)
            ·
              refine ⟨578860104989323601215541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385906736659549067477027 578860104989323601215541)
              ·
                refine ⟨54268134842749087613957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 578860104989323601215541 54268134842749087613957)
                ·
                  rfl

theorem cell20_356693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 5].length) (baseStart_356693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356693 prefixEnd_356693 := by exact prefixLift 356693
  have htrace : WordTrace (prefixWord ++ tailWord_356693) baseStart_356693 baseEnd_356693 := by
    simpa [prefixWord, tailWord_356693, baseEnd_356693] using wordTrace_append hprefix tailTrace_356693
  have hstable : (prefixWord ++ tailWord_356693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356693).length < 2 ^ (prefixWord ++ tailWord_356693).sum := by decide
  have hdescent : baseEnd_356693 < baseStart_356693 := by decide
  rcases family_descends (prefixWord ++ tailWord_356693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356745 : List Nat := [1, 2, 1, 1, 6, 1, 2, 4, 2]
def baseStart_356745 : Nat := 118140960795 + 356745 * 2 ^ 59
def prefixEnd_356745 : Nat := 4983230072969 + 3 ^ 40 * 356745 * 2
def baseEnd_356745 : Nat := 162828138745166193108325

theorem tailTrace_356745 : CollatzResearch.WordTrace tailWord_356745 prefixEnd_356745 162828138745166193108325 := by
  unfold tailWord_356745
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011559092581267040447689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8674372728387511360298459 13011559092581267040447689)
  ·
    refine ⟨9758669319435950280335767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13011559092581267040447689 9758669319435950280335767)
    ·
      refine ⟨14638003979153925420503651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9758669319435950280335767 14638003979153925420503651)
      ·
        refine ⟨21957005968730888130755477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14638003979153925420503651 21957005968730888130755477)
        ·
          refine ⟨1029234654784260381129163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21957005968730888130755477 1029234654784260381129163)
          ·
            refine ⟨1543851982176390571693745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029234654784260381129163 1543851982176390571693745)
            ·
              refine ⟨1157888986632292928770309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543851982176390571693745 1157888986632292928770309)
              ·
                refine ⟨217104184993554924144433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1157888986632292928770309 217104184993554924144433)
                ·
                  refine ⟨162828138745166193108325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217104184993554924144433 162828138745166193108325)
                  ·
                    rfl

theorem cell20_356745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_356745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356745 prefixEnd_356745 := by exact prefixLift 356745
  have htrace : WordTrace (prefixWord ++ tailWord_356745) baseStart_356745 baseEnd_356745 := by
    simpa [prefixWord, tailWord_356745, baseEnd_356745] using wordTrace_append hprefix tailTrace_356745
  have hstable : (prefixWord ++ tailWord_356745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356745).length < 2 ^ (prefixWord ++ tailWord_356745).sum := by decide
  have hdescent : baseEnd_356745 < baseStart_356745 := by decide
  rcases family_descends (prefixWord ++ tailWord_356745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356825 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_356825 : Nat := 118140960795 + 356825 * 2 ^ 59
def prefixEnd_356825 : Nat := 4983230072969 + 3 ^ 40 * 356825 * 2
def baseEnd_356825 : Nat := 162864652925041470441331

theorem tailTrace_356825 : CollatzResearch.WordTrace tailWord_356825 prefixEnd_356825 162864652925041470441331 := by
  unfold tailWord_356825
  simp only [CollatzResearch.WordTrace]
  refine ⟨13014476932291440703359929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8676317954860960468906619 13014476932291440703359929)
  ·
    refine ⟨9760857699218580527519947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13014476932291440703359929 9760857699218580527519947)
    ·
      refine ⟨14641286548827870791279921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9760857699218580527519947 14641286548827870791279921)
      ·
        refine ⟨10980964911620903093459941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14641286548827870791279921 10980964911620903093459941)
        ·
          refine ⟨2058930920928919330023739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10980964911620903093459941 2058930920928919330023739)
          ·
            refine ⟨3088396381393378995035609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058930920928919330023739 3088396381393378995035609)
            ·
              refine ⟨2316297286045034246276707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3088396381393378995035609 2316297286045034246276707)
              ·
                refine ⟨3474445929067551369415061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316297286045034246276707 3474445929067551369415061)
                ·
                  refine ⟨162864652925041470441331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3474445929067551369415061 162864652925041470441331)
                  ·
                    rfl

theorem cell20_356825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_356825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356825 prefixEnd_356825 := by exact prefixLift 356825
  have htrace : WordTrace (prefixWord ++ tailWord_356825) baseStart_356825 baseEnd_356825 := by
    simpa [prefixWord, tailWord_356825, baseEnd_356825] using wordTrace_append hprefix tailTrace_356825
  have hstable : (prefixWord ++ tailWord_356825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356825).length < 2 ^ (prefixWord ++ tailWord_356825).sum := by decide
  have hdescent : baseEnd_356825 < baseStart_356825 := by decide
  rcases family_descends (prefixWord ++ tailWord_356825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356832 : List Nat := [2, 1, 1, 3, 1, 1, 3, 8]
def baseStart_356832 : Nat := 118140960795 + 356832 * 2 ^ 59
def prefixEnd_356832 : Nat := 4983230072969 + 3 ^ 40 * 356832 * 2
def baseEnd_356832 : Nat := 54289282638593519069323

theorem tailTrace_356832 : CollatzResearch.WordTrace tailWord_356832 prefixEnd_356832 54289282638593519069323 := by
  unfold tailWord_356832
  simp only [CollatzResearch.WordTrace]
  refine ⟨6507366121633040449432375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8676488162177387265909833 6507366121633040449432375)
  ·
    refine ⟨9761049182449560674148563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6507366121633040449432375 9761049182449560674148563)
    ·
      refine ⟨14641573773674341011222845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9761049182449560674148563 14641573773674341011222845)
      ·
        refine ⟨5490590165127877879208567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14641573773674341011222845 5490590165127877879208567)
        ·
          refine ⟨8235885247691816818812851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5490590165127877879208567 8235885247691816818812851)
          ·
            refine ⟨12353827871537725228219277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8235885247691816818812851 12353827871537725228219277)
            ·
              refine ⟨4632685451826646960582229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12353827871537725228219277 4632685451826646960582229)
              ·
                refine ⟨54289282638593519069323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4632685451826646960582229 54289282638593519069323)
                ·
                  rfl

theorem cell20_356832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_356832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356832 prefixEnd_356832 := by exact prefixLift 356832
  have htrace : WordTrace (prefixWord ++ tailWord_356832) baseStart_356832 baseEnd_356832 := by
    simpa [prefixWord, tailWord_356832, baseEnd_356832] using wordTrace_append hprefix tailTrace_356832
  have hstable : (prefixWord ++ tailWord_356832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356832).length < 2 ^ (prefixWord ++ tailWord_356832).sum := by decide
  have hdescent : baseEnd_356832 < baseStart_356832 := by decide
  rcases family_descends (prefixWord ++ tailWord_356832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356863 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_356863 : Nat := 118140960795 + 356863 * 2 ^ 59
def prefixEnd_356863 : Nat := 4983230072969 + 3 ^ 40 * 356863 * 2
def baseEnd_356863 : Nat := 162881997160482227174509

theorem tailTrace_356863 : CollatzResearch.WordTrace tailWord_356863 prefixEnd_356863 162881997160482227174509 := by
  unfold tailWord_356863
  simp only [CollatzResearch.WordTrace]
  refine ⟨13015862906153773193243243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8677241937435848795495495 13015862906153773193243243)
  ·
    refine ⟨19523794359230659789864865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13015862906153773193243243 19523794359230659789864865)
    ·
      refine ⟨14642845769422994842398649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19523794359230659789864865 14642845769422994842398649)
      ·
        refine ⟨10982134327067246131798987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14642845769422994842398649 10982134327067246131798987)
        ·
          refine ⟨16473201490600869197698481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10982134327067246131798987 16473201490600869197698481)
          ·
            refine ⟨12354901117950651898273861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16473201490600869197698481 12354901117950651898273861)
            ·
              refine ⟨2316543959615747230926349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12354901117950651898273861 2316543959615747230926349)
              ·
                refine ⟨868703984855905211597381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2316543959615747230926349 868703984855905211597381)
                ·
                  refine ⟨162881997160482227174509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 868703984855905211597381 162881997160482227174509)
                  ·
                    rfl

theorem cell20_356863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_356863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356863 prefixEnd_356863 := by exact prefixLift 356863
  have htrace : WordTrace (prefixWord ++ tailWord_356863) baseStart_356863 baseEnd_356863 := by
    simpa [prefixWord, tailWord_356863, baseEnd_356863] using wordTrace_append hprefix tailTrace_356863
  have hstable : (prefixWord ++ tailWord_356863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356863).length < 2 ^ (prefixWord ++ tailWord_356863).sum := by decide
  have hdescent : baseEnd_356863 < baseStart_356863 := by decide
  rcases family_descends (prefixWord ++ tailWord_356863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356897 : List Nat := [1, 2, 3, 2, 2, 1, 4, 3, 2]
def baseStart_356897 : Nat := 118140960795 + 356897 * 2 ^ 59
def prefixEnd_356897 : Nat := 4983230072969 + 3 ^ 40 * 356897 * 2
def baseEnd_356897 : Nat := 162897515686929220041037

theorem tailTrace_356897 : CollatzResearch.WordTrace tailWord_356897 prefixEnd_356897 162897515686929220041037 := by
  unfold tailWord_356897
  simp only [CollatzResearch.WordTrace]
  refine ⟨13017102988030596999980945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8678068658687064666653963 13017102988030596999980945)
  ·
    refine ⟨9762827241022947749985709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13017102988030596999980945 9762827241022947749985709)
    ·
      refine ⟨3661060215383605406244641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9762827241022947749985709 3661060215383605406244641)
      ·
        refine ⟨2745795161537704054683481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3661060215383605406244641 2745795161537704054683481)
        ·
          refine ⟨2059346371153278041012611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2745795161537704054683481 2059346371153278041012611)
          ·
            refine ⟨3089019556729917061518917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059346371153278041012611 3089019556729917061518917)
            ·
              refine ⟨579191166886859449034797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3089019556729917061518917 579191166886859449034797)
              ·
                refine ⟨217196687582572293388049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 579191166886859449034797 217196687582572293388049)
                ·
                  refine ⟨162897515686929220041037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217196687582572293388049 162897515686929220041037)
                  ·
                    rfl

theorem cell20_356897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_356897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356897 prefixEnd_356897 := by exact prefixLift 356897
  have htrace : WordTrace (prefixWord ++ tailWord_356897) baseStart_356897 baseEnd_356897 := by
    simpa [prefixWord, tailWord_356897, baseEnd_356897] using wordTrace_append hprefix tailTrace_356897
  have hstable : (prefixWord ++ tailWord_356897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356897).length < 2 ^ (prefixWord ++ tailWord_356897).sum := by decide
  have hdescent : baseEnd_356897 < baseStart_356897 := by decide
  rcases family_descends (prefixWord ++ tailWord_356897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356939 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_356939 : Nat := 118140960795 + 356939 * 2 ^ 59
def prefixEnd_356939 : Nat := 4983230072969 + 3 ^ 40 * 356939 * 2
def baseEnd_356939 : Nat := 162916685631363740640865

theorem tailTrace_356939 : CollatzResearch.WordTrace tailWord_356939 prefixEnd_356939 162916685631363740640865 := by
  unfold tailWord_356939
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018634853878438173009871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8679089902585625448673247 13018634853878438173009871)
  ·
    refine ⟨19527952280817657259514807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13018634853878438173009871 19527952280817657259514807)
    ·
      refine ⟨29291928421226485889272211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19527952280817657259514807 29291928421226485889272211)
      ·
        refine ⟨43937892631839728833908317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29291928421226485889272211 43937892631839728833908317)
        ·
          refine ⟨16476709736939898312715619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43937892631839728833908317 16476709736939898312715619)
          ·
            refine ⟨24715064605409847469073429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16476709736939898312715619 24715064605409847469073429)
            ·
              refine ⟨1158518653378586600112817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24715064605409847469073429 1158518653378586600112817)
              ·
                refine ⟨868888990033939950084613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1158518653378586600112817 868888990033939950084613)
                ·
                  refine ⟨162916685631363740640865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 868888990033939950084613 162916685631363740640865)
                  ·
                    rfl

theorem cell20_356939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_356939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356939 prefixEnd_356939 := by exact prefixLift 356939
  have htrace : WordTrace (prefixWord ++ tailWord_356939) baseStart_356939 baseEnd_356939 := by
    simpa [prefixWord, tailWord_356939, baseEnd_356939] using wordTrace_append hprefix tailTrace_356939
  have hstable : (prefixWord ++ tailWord_356939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356939).length < 2 ^ (prefixWord ++ tailWord_356939).sum := by decide
  have hdescent : baseEnd_356939 < baseStart_356939 := by decide
  rcases family_descends (prefixWord ++ tailWord_356939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356970 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_356970 : Nat := 118140960795 + 356970 * 2 ^ 59
def prefixEnd_356970 : Nat := 4983230072969 + 3 ^ 40 * 356970 * 2
def baseEnd_356970 : Nat := 162930834876065410607405

theorem tailTrace_356970 : CollatzResearch.WordTrace tailWord_356970 prefixEnd_356970 162930834876065410607405 := by
  unfold tailWord_356970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254941379191532616847091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8679843677844086978258909 3254941379191532616847091)
  ·
    refine ⟨4882412068787298925270637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254941379191532616847091 4882412068787298925270637)
    ·
      refine ⟨1830904525795237096976489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4882412068787298925270637 1830904525795237096976489)
      ·
        refine ⟨1373178394346427822732367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1830904525795237096976489 1373178394346427822732367)
        ·
          refine ⟨2059767591519641734098551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373178394346427822732367 2059767591519641734098551)
          ·
            refine ⟨3089651387279462601147827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059767591519641734098551 3089651387279462601147827)
            ·
              refine ⟨4634477080919193901721741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089651387279462601147827 4634477080919193901721741)
              ·
                refine ⟨1737928905344697713145653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4634477080919193901721741 1737928905344697713145653)
                ·
                  refine ⟨162930834876065410607405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1737928905344697713145653 162930834876065410607405)
                  ·
                    rfl

theorem cell20_356970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_356970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356970 prefixEnd_356970 := by exact prefixLift 356970
  have htrace : WordTrace (prefixWord ++ tailWord_356970) baseStart_356970 baseEnd_356970 := by
    simpa [prefixWord, tailWord_356970, baseEnd_356970] using wordTrace_append hprefix tailTrace_356970
  have hstable : (prefixWord ++ tailWord_356970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356970).length < 2 ^ (prefixWord ++ tailWord_356970).sum := by decide
  have hdescent : baseEnd_356970 < baseStart_356970 := by decide
  rcases family_descends (prefixWord ++ tailWord_356970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356973 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 4]
def baseStart_356973 : Nat := 118140960795 + 356973 * 2 ^ 59
def prefixEnd_356973 : Nat := 4983230072969 + 3 ^ 40 * 356973 * 2
def baseEnd_356973 : Nat := 162932204157810733507393

theorem tailTrace_356973 : CollatzResearch.WordTrace tailWord_356973 prefixEnd_356973 162932204157810733507393 := by
  unfold tailWord_356973
  simp only [CollatzResearch.WordTrace]
  refine ⟨13019874935755261979747573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8679916623836841319831715 13019874935755261979747573)
  ·
    refine ⟨1220613275227055810601335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13019874935755261979747573 1220613275227055810601335)
    ·
      refine ⟨1830919912840583715902003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1220613275227055810601335 1830919912840583715902003)
      ·
        refine ⟨2746379869260875573853005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1830919912840583715902003 2746379869260875573853005)
        ·
          refine ⟨1029892450972828340194877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2746379869260875573853005 1029892450972828340194877)
          ·
            refine ⟨386209669114810627573079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1029892450972828340194877 386209669114810627573079)
            ·
              refine ⟨579314503672215941359619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386209669114810627573079 579314503672215941359619)
              ·
                refine ⟨868971755508323912039429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579314503672215941359619 868971755508323912039429)
                ·
                  refine ⟨162932204157810733507393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 868971755508323912039429 162932204157810733507393)
                  ·
                    rfl

theorem cell20_356973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_356973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356973 prefixEnd_356973 := by exact prefixLift 356973
  have htrace : WordTrace (prefixWord ++ tailWord_356973) baseStart_356973 baseEnd_356973 := by
    simpa [prefixWord, tailWord_356973, baseEnd_356973] using wordTrace_append hprefix tailTrace_356973
  have hstable : (prefixWord ++ tailWord_356973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356973).length < 2 ^ (prefixWord ++ tailWord_356973).sum := by decide
  have hdescent : baseEnd_356973 < baseStart_356973 := by decide
  rcases family_descends (prefixWord ++ tailWord_356973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356991 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_356991 : Nat := 118140960795 + 356991 * 2 ^ 59
def prefixEnd_356991 : Nat := 4983230072969 + 3 ^ 40 * 356991 * 2
def baseEnd_356991 : Nat := 162940419848282670907319

theorem tailTrace_356991 : CollatzResearch.WordTrace tailWord_356991 prefixEnd_356991 162940419848282670907319 := by
  unfold tailWord_356991
  simp only [CollatzResearch.WordTrace]
  refine ⟨13020531449690051053902827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8680354299793367369268551 13020531449690051053902827)
  ·
    refine ⟨19530797174535076580854241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13020531449690051053902827 19530797174535076580854241)
    ·
      refine ⟨14648097880901307435640681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19530797174535076580854241 14648097880901307435640681)
      ·
        refine ⟨10986073410675980576730511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14648097880901307435640681 10986073410675980576730511)
        ·
          refine ⟨16479110116013970865095767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10986073410675980576730511 16479110116013970865095767)
          ·
            refine ⟨24718665174020956297643651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16479110116013970865095767 24718665174020956297643651)
            ·
              refine ⟨37077997761031434446465477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24718665174020956297643651 37077997761031434446465477)
              ·
                refine ⟨6952124580193393958712277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37077997761031434446465477 6952124580193393958712277)
                ·
                  refine ⟨162940419848282670907319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6952124580193393958712277 162940419848282670907319)
                  ·
                    rfl

theorem cell20_356991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_356991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_356991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_356991 prefixEnd_356991 := by exact prefixLift 356991
  have htrace : WordTrace (prefixWord ++ tailWord_356991) baseStart_356991 baseEnd_356991 := by
    simpa [prefixWord, tailWord_356991, baseEnd_356991] using wordTrace_append hprefix tailTrace_356991
  have hstable : (prefixWord ++ tailWord_356991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356991).length < 2 ^ (prefixWord ++ tailWord_356991).sum := by decide
  have hdescent : baseEnd_356991 < baseStart_356991 := by decide
  rcases family_descends (prefixWord ++ tailWord_356991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357018 : List Nat := [3, 1, 1, 6, 2, 7]
def baseStart_357018 : Nat := 118140960795 + 357018 * 2 ^ 59
def prefixEnd_357018 : Nat := 4983230072969 + 3 ^ 40 * 357018 * 2
def baseEnd_357018 : Nat := 6035286791999651000267

theorem tailTrace_357018 : CollatzResearch.WordTrace tailWord_357018 prefixEnd_357018 6035286791999651000267 := by
  unfold tailWord_357018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3255379055148058666283927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8681010813728156443423805 3255379055148058666283927)
  ·
    refine ⟨4883068582722087999425891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3255379055148058666283927 4883068582722087999425891)
    ·
      refine ⟨7324602874083131999138837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4883068582722087999425891 7324602874083131999138837)
      ·
        refine ⟨343340759722646812459633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7324602874083131999138837 343340759722646812459633)
        ·
          refine ⟨257505569791985109344725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343340759722646812459633 257505569791985109344725)
          ·
            refine ⟨6035286791999651000267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 257505569791985109344725 6035286791999651000267)
            ·
              rfl

theorem cell20_357018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 7].length) (baseStart_357018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357018 prefixEnd_357018 := by exact prefixLift 357018
  have htrace : WordTrace (prefixWord ++ tailWord_357018) baseStart_357018 baseEnd_357018 := by
    simpa [prefixWord, tailWord_357018, baseEnd_357018] using wordTrace_append hprefix tailTrace_357018
  have hstable : (prefixWord ++ tailWord_357018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357018).length < 2 ^ (prefixWord ++ tailWord_357018).sum := by decide
  have hdescent : baseEnd_357018 < baseStart_357018 := by decide
  rcases family_descends (prefixWord ++ tailWord_357018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357039 : List Nat := [1, 1, 2, 1, 2, 7, 1, 5]
def baseStart_357039 : Nat := 118140960795 + 357039 * 2 ^ 59
def prefixEnd_357039 : Nat := 4983230072969 + 3 ^ 40 * 357039 * 2
def baseEnd_357039 : Nat := 54320776118735945769041

theorem tailTrace_357039 : CollatzResearch.WordTrace tailWord_357039 prefixEnd_357039 54320776118735945769041 := by
  unfold tailWord_357039
  simp only [CollatzResearch.WordTrace]
  refine ⟨13022282153516155251650171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8681521435677436834433447 13022282153516155251650171)
  ·
    refine ⟨19533423230274232877475257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13022282153516155251650171 19533423230274232877475257)
    ·
      refine ⟨14650067422705674658106443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19533423230274232877475257 14650067422705674658106443)
      ·
        refine ⟨21975101134058511987159665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14650067422705674658106443 21975101134058511987159665)
        ·
          refine ⟨16481325850543883990369749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21975101134058511987159665 16481325850543883990369749)
          ·
            refine ⟨386281074622122281024291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16481325850543883990369749 386281074622122281024291)
            ·
              refine ⟨579421611933183421536437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386281074622122281024291 579421611933183421536437)
              ·
                refine ⟨54320776118735945769041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 579421611933183421536437 54320776118735945769041)
                ·
                  rfl

theorem cell20_357039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 5].length) (baseStart_357039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357039 prefixEnd_357039 := by exact prefixLift 357039
  have htrace : WordTrace (prefixWord ++ tailWord_357039) baseStart_357039 baseEnd_357039 := by
    simpa [prefixWord, tailWord_357039, baseEnd_357039] using wordTrace_append hprefix tailTrace_357039
  have hstable : (prefixWord ++ tailWord_357039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357039).length < 2 ^ (prefixWord ++ tailWord_357039).sum := by decide
  have hdescent : baseEnd_357039 < baseStart_357039 := by decide
  rcases family_descends (prefixWord ++ tailWord_357039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357053 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_357053 : Nat := 118140960795 + 357053 * 2 ^ 59
def prefixEnd_357053 : Nat := 4983230072969 + 3 ^ 40 * 357053 * 2
def baseEnd_357053 : Nat := 162968718337686010840399

theorem tailTrace_357053 : CollatzResearch.WordTrace tailWord_357053 prefixEnd_357053 162968718337686010840399 := by
  unfold tailWord_357053
  simp only [CollatzResearch.WordTrace]
  refine ⟨13022792775465435642659813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8681861850310290428439875 13022792775465435642659813)
  ·
    refine ⟨2441773645399769182998715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13022792775465435642659813 2441773645399769182998715)
    ·
      refine ⟨3662660468099653774498073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2441773645399769182998715 3662660468099653774498073)
      ·
        refine ⟨2746995351074740330873555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3662660468099653774498073 2746995351074740330873555)
        ·
          refine ⟨4120493026612110496310333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2746995351074740330873555 4120493026612110496310333)
          ·
            refine ⟨1545184884979541436116375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4120493026612110496310333 1545184884979541436116375)
            ·
              refine ⟨2317777327469312154174563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545184884979541436116375 2317777327469312154174563)
              ·
                refine ⟨3476665991203968231261845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317777327469312154174563 3476665991203968231261845)
                ·
                  refine ⟨162968718337686010840399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3476665991203968231261845 162968718337686010840399)
                  ·
                    rfl

theorem cell20_357053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_357053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357053 prefixEnd_357053 := by exact prefixLift 357053
  have htrace : WordTrace (prefixWord ++ tailWord_357053) baseStart_357053 baseEnd_357053 := by
    simpa [prefixWord, tailWord_357053, baseEnd_357053] using wordTrace_append hprefix tailTrace_357053
  have hstable : (prefixWord ++ tailWord_357053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357053).length < 2 ^ (prefixWord ++ tailWord_357053).sum := by decide
  have hdescent : baseEnd_357053 < baseStart_357053 := by decide
  rcases family_descends (prefixWord ++ tailWord_357053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357062 : List Nat := [6, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_357062 : Nat := 118140960795 + 357062 * 2 ^ 59
def prefixEnd_357062 : Nat := 4983230072969 + 3 ^ 40 * 357062 * 2
def baseEnd_357062 : Nat := 162972826182921979540363

theorem tailTrace_357062 : CollatzResearch.WordTrace tailWord_357062 prefixEnd_357062 162972826182921979540363 := by
  unfold tailWord_357062
  simp only [CollatzResearch.WordTrace]
  refine ⟨406972532263525943116795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8682080688288553453158293 406972532263525943116795)
  ·
    refine ⟨610458798395288914675193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 406972532263525943116795 610458798395288914675193)
    ·
      refine ⟨457844098796466686006395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 610458798395288914675193 457844098796466686006395)
      ·
        refine ⟨686766148194700029009593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457844098796466686006395 686766148194700029009593)
        ·
          refine ⟨515074611146025021757195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686766148194700029009593 515074611146025021757195)
          ·
            refine ⟨772611916719037532635793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515074611146025021757195 772611916719037532635793)
            ·
              refine ⟨579458937539278149476845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 772611916719037532635793 579458937539278149476845)
              ·
                refine ⟨217297101577229306053817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 579458937539278149476845 217297101577229306053817)
                ·
                  refine ⟨162972826182921979540363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217297101577229306053817 162972826182921979540363)
                  ·
                    rfl

theorem cell20_357062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_357062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357062 prefixEnd_357062 := by exact prefixLift 357062
  have htrace : WordTrace (prefixWord ++ tailWord_357062) baseStart_357062 baseEnd_357062 := by
    simpa [prefixWord, tailWord_357062, baseEnd_357062] using wordTrace_append hprefix tailTrace_357062
  have hstable : (prefixWord ++ tailWord_357062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357062).length < 2 ^ (prefixWord ++ tailWord_357062).sum := by decide
  have hdescent : baseEnd_357062 < baseStart_357062 := by decide
  rcases family_descends (prefixWord ++ tailWord_357062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357098 : List Nat := [3, 1, 3, 1, 1, 1, 1, 9]
def baseStart_357098 : Nat := 118140960795 + 357098 * 2 ^ 59
def prefixEnd_357098 : Nat := 4983230072969 + 3 ^ 40 * 357098 * 2
def baseEnd_357098 : Nat := 54329752521288618113405

theorem tailTrace_357098 : CollatzResearch.WordTrace tailWord_357098 prefixEnd_357098 54329752521288618113405 := by
  unfold tailWord_357098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3256108515075602082011987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8682956040201605552031965 3256108515075602082011987)
  ·
    refine ⟨4884162772613403123017981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3256108515075602082011987 4884162772613403123017981)
    ·
      refine ⟨1831561039730026171131743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4884162772613403123017981 1831561039730026171131743)
      ·
        refine ⟨2747341559595039256697615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831561039730026171131743 2747341559595039256697615)
        ·
          refine ⟨4121012339392558885046423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747341559595039256697615 4121012339392558885046423)
          ·
            refine ⟨6181518509088838327569635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121012339392558885046423 6181518509088838327569635)
            ·
              refine ⟨9272277763633257491354453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6181518509088838327569635 9272277763633257491354453)
              ·
                refine ⟨54329752521288618113405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9272277763633257491354453 54329752521288618113405)
                ·
                  rfl

theorem cell20_357098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_357098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357098 prefixEnd_357098 := by exact prefixLift 357098
  have htrace : WordTrace (prefixWord ++ tailWord_357098) baseStart_357098 baseEnd_357098 := by
    simpa [prefixWord, tailWord_357098, baseEnd_357098] using wordTrace_append hprefix tailTrace_357098
  have hstable : (prefixWord ++ tailWord_357098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357098).length < 2 ^ (prefixWord ++ tailWord_357098).sum := by decide
  have hdescent : baseEnd_357098 < baseStart_357098 := by decide
  rcases family_descends (prefixWord ++ tailWord_357098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357201 : List Nat := [1, 2, 2, 1, 6, 1, 1, 4, 2]
def baseStart_357201 : Nat := 118140960795 + 357201 * 2 ^ 59
def prefixEnd_357201 : Nat := 4983230072969 + 3 ^ 40 * 357201 * 2
def baseEnd_357201 : Nat := 163036269570455273906461

theorem tailTrace_357201 : CollatzResearch.WordTrace tailWord_357201 prefixEnd_357201 163036269570455273906461 := by
  unfold tailWord_357201
  simp only [CollatzResearch.WordTrace]
  refine ⟨13028190778929256919047457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8685460519286171279364971 13028190778929256919047457)
  ·
    refine ⟨9771143084196942689285593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13028190778929256919047457 9771143084196942689285593)
    ·
      refine ⟨7328357313147707016964195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9771143084196942689285593 7328357313147707016964195)
      ·
        refine ⟨10992535969721560525446293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7328357313147707016964195 10992535969721560525446293)
        ·
          refine ⟨515275123580698149630295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10992535969721560525446293 515275123580698149630295)
          ·
            refine ⟨772912685371047224445443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515275123580698149630295 772912685371047224445443)
            ·
              refine ⟨1159369028056570836668165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772912685371047224445443 1159369028056570836668165)
              ·
                refine ⟨217381692760607031875281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1159369028056570836668165 217381692760607031875281)
                ·
                  refine ⟨163036269570455273906461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217381692760607031875281 163036269570455273906461)
                  ·
                    rfl

theorem cell20_357201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_357201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357201 prefixEnd_357201 := by exact prefixLift 357201
  have htrace : WordTrace (prefixWord ++ tailWord_357201) baseStart_357201 baseEnd_357201 := by
    simpa [prefixWord, tailWord_357201, baseEnd_357201] using wordTrace_append hprefix tailTrace_357201
  have hstable : (prefixWord ++ tailWord_357201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357201).length < 2 ^ (prefixWord ++ tailWord_357201).sum := by decide
  have hdescent : baseEnd_357201 < baseStart_357201 := by decide
  rcases family_descends (prefixWord ++ tailWord_357201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357205 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_357205 : Nat := 118140960795 + 357205 * 2 ^ 59
def prefixEnd_357205 : Nat := 4983230072969 + 3 ^ 40 * 357205 * 2
def baseEnd_357205 : Nat := 163038095279449037773111

theorem tailTrace_357205 : CollatzResearch.WordTrace tailWord_357205 prefixEnd_357205 163038095279449037773111 := by
  unfold tailWord_357205
  simp only [CollatzResearch.WordTrace]
  refine ⟨13028336670914765602193069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8685557780609843734795379 13028336670914765602193069)
  ·
    refine ⟨4885626251593037100822401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13028336670914765602193069 4885626251593037100822401)
    ·
      refine ⟨3664219688694777825616801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4885626251593037100822401 3664219688694777825616801)
      ·
        refine ⟨2748164766521083369212601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3664219688694777825616801 2748164766521083369212601)
        ·
          refine ⟨2061123574890812526909451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2748164766521083369212601 2061123574890812526909451)
          ·
            refine ⟨3091685362336218790364177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061123574890812526909451 3091685362336218790364177)
            ·
              refine ⟨2318764021752164092773133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3091685362336218790364177 2318764021752164092773133)
              ·
                refine ⟨869536508157061534789925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2318764021752164092773133 869536508157061534789925)
                ·
                  refine ⟨163038095279449037773111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 869536508157061534789925 163038095279449037773111)
                  ·
                    rfl

theorem cell20_357205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_357205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357205 prefixEnd_357205 := by exact prefixLift 357205
  have htrace : WordTrace (prefixWord ++ tailWord_357205) baseStart_357205 baseEnd_357205 := by
    simpa [prefixWord, tailWord_357205, baseEnd_357205] using wordTrace_append hprefix tailTrace_357205
  have hstable : (prefixWord ++ tailWord_357205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357205).length < 2 ^ (prefixWord ++ tailWord_357205).sum := by decide
  have hdescent : baseEnd_357205 < baseStart_357205 := by decide
  rcases family_descends (prefixWord ++ tailWord_357205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357246 : List Nat := [4, 2, 3, 1, 2, 1, 7]
def baseStart_357246 : Nat := 118140960795 + 357246 * 2 ^ 59
def prefixEnd_357246 : Nat := 4983230072969 + 3 ^ 40 * 357246 * 2
def baseEnd_357246 : Nat := 18117423199626124156253

theorem tailTrace_357246 : CollatzResearch.WordTrace tailWord_357246 prefixEnd_357246 18117423199626124156253 := by
  unfold tailWord_357246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1628729007970778700554449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8686554709177486402957061 1628729007970778700554449)
  ·
    refine ⟨1221546755978084025415837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1628729007970778700554449 1221546755978084025415837)
    ·
      refine ⟨458080033491781509530939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1221546755978084025415837 458080033491781509530939)
      ·
        refine ⟨687120050237672264296409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458080033491781509530939 687120050237672264296409)
        ·
          refine ⟨515340037678254198222307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 687120050237672264296409 515340037678254198222307)
          ·
            refine ⟨773010056517381297333461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515340037678254198222307 773010056517381297333461)
            ·
              refine ⟨18117423199626124156253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 773010056517381297333461 18117423199626124156253)
              ·
                rfl

theorem cell20_357246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 7].length) (baseStart_357246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357246 prefixEnd_357246 := by exact prefixLift 357246
  have htrace : WordTrace (prefixWord ++ tailWord_357246) baseStart_357246 baseEnd_357246 := by
    simpa [prefixWord, tailWord_357246, baseEnd_357246] using wordTrace_append hprefix tailTrace_357246
  have hstable : (prefixWord ++ tailWord_357246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357246).length < 2 ^ (prefixWord ++ tailWord_357246).sum := by decide
  have hdescent : baseEnd_357246 < baseStart_357246 := by decide
  rcases family_descends (prefixWord ++ tailWord_357246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357253 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 3]
def baseStart_357253 : Nat := 118140960795 + 357253 * 2 ^ 59
def prefixEnd_357253 : Nat := 4983230072969 + 3 ^ 40 * 357253 * 2
def baseEnd_357253 : Nat := 163060003787374204172915

theorem tailTrace_357253 : CollatzResearch.WordTrace tailWord_357253 prefixEnd_357253 163060003787374204172915 := by
  unfold tailWord_357253
  simp only [CollatzResearch.WordTrace]
  refine ⟨13030087374740869799940413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8686724916493913199960275 13030087374740869799940413)
  ·
    refine ⟨4886282765527826174977655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13030087374740869799940413 4886282765527826174977655)
    ·
      refine ⟨7329424148291739262466483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4886282765527826174977655 7329424148291739262466483)
      ·
        refine ⟨10994136222437608893699725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7329424148291739262466483 10994136222437608893699725)
        ·
          refine ⟨4122801083414103335137397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10994136222437608893699725 4122801083414103335137397)
          ·
            refine ⟨386512601570072187669131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4122801083414103335137397 386512601570072187669131)
            ·
              refine ⟨579768902355108281503697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386512601570072187669131 579768902355108281503697)
              ·
                refine ⟨434826676766331211127773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579768902355108281503697 434826676766331211127773)
                ·
                  refine ⟨163060003787374204172915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434826676766331211127773 163060003787374204172915)
                  ·
                    rfl

theorem cell20_357253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_357253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357253 prefixEnd_357253 := by exact prefixLift 357253
  have htrace : WordTrace (prefixWord ++ tailWord_357253) baseStart_357253 baseEnd_357253 := by
    simpa [prefixWord, tailWord_357253, baseEnd_357253] using wordTrace_append hprefix tailTrace_357253
  have hstable : (prefixWord ++ tailWord_357253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357253).length < 2 ^ (prefixWord ++ tailWord_357253).sum := by decide
  have hdescent : baseEnd_357253 < baseStart_357253 := by decide
  rcases family_descends (prefixWord ++ tailWord_357253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357260 : List Nat := [2, 2, 1, 2, 1, 2, 4, 4, 2]
def baseStart_357260 : Nat := 118140960795 + 357260 * 2 ^ 59
def prefixEnd_357260 : Nat := 4983230072969 + 3 ^ 40 * 357260 * 2
def baseEnd_357260 : Nat := 163063198778113290939553

theorem tailTrace_357260 : CollatzResearch.WordTrace tailWord_357260 prefixEnd_357260 163063198778113290939553 := by
  unfold tailWord_357260
  simp only [CollatzResearch.WordTrace]
  refine ⟨6515171342857754997722617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8686895123810339996963489 6515171342857754997722617)
  ·
    refine ⟨4886378507143316248291963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6515171342857754997722617 4886378507143316248291963)
    ·
      refine ⟨7329567760714974372437945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4886378507143316248291963 7329567760714974372437945)
      ·
        refine ⟨5497175820536230779328459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7329567760714974372437945 5497175820536230779328459)
        ·
          refine ⟨8245763730804346168992689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497175820536230779328459 8245763730804346168992689)
          ·
            refine ⟨6184322798103259626744517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8245763730804346168992689 6184322798103259626744517)
            ·
              refine ⟨1159560524644361180014597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6184322798103259626744517 1159560524644361180014597)
              ·
                refine ⟨217417598370817721252737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1159560524644361180014597 217417598370817721252737)
                ·
                  refine ⟨163063198778113290939553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217417598370817721252737 163063198778113290939553)
                  ·
                    rfl

theorem cell20_357260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_357260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357260 prefixEnd_357260 := by exact prefixLift 357260
  have htrace : WordTrace (prefixWord ++ tailWord_357260) baseStart_357260 baseEnd_357260 := by
    simpa [prefixWord, tailWord_357260, baseEnd_357260] using wordTrace_append hprefix tailTrace_357260
  have hstable : (prefixWord ++ tailWord_357260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357260).length < 2 ^ (prefixWord ++ tailWord_357260).sum := by decide
  have hdescent : baseEnd_357260 < baseStart_357260 := by decide
  rcases family_descends (prefixWord ++ tailWord_357260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357319 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 4]
def baseStart_357319 : Nat := 118140960795 + 357319 * 2 ^ 59
def prefixEnd_357319 : Nat := 4983230072969 + 3 ^ 40 * 357319 * 2
def baseEnd_357319 : Nat := 163090127985771307972645

theorem tailTrace_357319 : CollatzResearch.WordTrace tailWord_357319 prefixEnd_357319 163090127985771307972645 := by
  unfold tailWord_357319
  simp only [CollatzResearch.WordTrace]
  refine ⟨13032494592501763071843011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8688329728334508714562007 13032494592501763071843011)
  ·
    refine ⟨19548741888752644607764517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13032494592501763071843011 19548741888752644607764517)
    ·
      refine ⟨3665389104141120863955847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19548741888752644607764517 3665389104141120863955847)
      ·
        refine ⟨5498083656211681295933771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665389104141120863955847 5498083656211681295933771)
        ·
          refine ⟨8247125484317521943900657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5498083656211681295933771 8247125484317521943900657)
          ·
            refine ⟨6185344113238141457925493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8247125484317521943900657 6185344113238141457925493)
            ·
              refine ⟨579876010616075761680515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6185344113238141457925493 579876010616075761680515)
              ·
                refine ⟨869814015924113642520773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579876010616075761680515 869814015924113642520773)
                ·
                  refine ⟨163090127985771307972645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 869814015924113642520773 163090127985771307972645)
                  ·
                    rfl

theorem cell20_357319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_357319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357319 prefixEnd_357319 := by exact prefixLift 357319
  have htrace : WordTrace (prefixWord ++ tailWord_357319) baseStart_357319 baseEnd_357319 := by
    simpa [prefixWord, tailWord_357319, baseEnd_357319] using wordTrace_append hprefix tailTrace_357319
  have hstable : (prefixWord ++ tailWord_357319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357319).length < 2 ^ (prefixWord ++ tailWord_357319).sum := by decide
  have hdescent : baseEnd_357319 < baseStart_357319 := by decide
  rcases family_descends (prefixWord ++ tailWord_357319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357326 : List Nat := [4, 1, 1, 1, 2, 3, 1, 7]
def baseStart_357326 : Nat := 118140960795 + 357326 * 2 ^ 59
def prefixEnd_357326 : Nat := 4983230072969 + 3 ^ 40 * 357326 * 2
def baseEnd_357326 : Nat := 54364440992170131579761

theorem tailTrace_357326 : CollatzResearch.WordTrace tailWord_357326 prefixEnd_357326 54364440992170131579761 := by
  unfold tailWord_357326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629093737934550408418479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8688499935650935511565221 1629093737934550408418479)
  ·
    refine ⟨2443640606901825612627719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1629093737934550408418479 2443640606901825612627719)
    ·
      refine ⟨3665460910352738418941579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443640606901825612627719 3665460910352738418941579)
      ·
        refine ⟨5498191365529107628412369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665460910352738418941579 5498191365529107628412369)
        ·
          refine ⟨4123643524146830721309277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5498191365529107628412369 4123643524146830721309277)
          ·
            refine ⟨1546366321555061520490979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4123643524146830721309277 1546366321555061520490979)
            ·
              refine ⟨2319549482332592280736469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546366321555061520490979 2319549482332592280736469)
              ·
                refine ⟨54364440992170131579761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2319549482332592280736469 54364440992170131579761)
                ·
                  rfl

theorem cell20_357326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_357326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357326 prefixEnd_357326 := by exact prefixLift 357326
  have htrace : WordTrace (prefixWord ++ tailWord_357326) baseStart_357326 baseEnd_357326 := by
    simpa [prefixWord, tailWord_357326, baseEnd_357326] using wordTrace_append hprefix tailTrace_357326
  have hstable : (prefixWord ++ tailWord_357326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357326).length < 2 ^ (prefixWord ++ tailWord_357326).sum := by decide
  have hdescent : baseEnd_357326 < baseStart_357326 := by decide
  rcases family_descends (prefixWord ++ tailWord_357326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357388 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 3]
def baseStart_357388 : Nat := 118140960795 + 357388 * 2 ^ 59
def prefixEnd_357388 : Nat := 4983230072969 + 3 ^ 40 * 357388 * 2
def baseEnd_357388 : Nat := 163121621465913734672363

theorem tailTrace_357388 : CollatzResearch.WordTrace tailWord_357388 prefixEnd_357388 163121621465913734672363 := by
  unfold tailWord_357388
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517505614625893928052409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8690007486167858570736545 6517505614625893928052409)
  ·
    refine ⟨4888129210969420446039307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6517505614625893928052409 4888129210969420446039307)
    ·
      refine ⟨7332193816454130669058961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4888129210969420446039307 7332193816454130669058961)
      ·
        refine ⟨5499145362340598001794221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7332193816454130669058961 5499145362340598001794221)
        ·
          refine ⟨2062179510877724250672833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5499145362340598001794221 2062179510877724250672833)
          ·
            refine ⟨1546634633158293188004625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2062179510877724250672833 1546634633158293188004625)
            ·
              refine ⟨1159975974868719891003469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546634633158293188004625 1159975974868719891003469)
              ·
                refine ⟨434990990575769959126301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1159975974868719891003469 434990990575769959126301)
                ·
                  refine ⟨163121621465913734672363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434990990575769959126301 163121621465913734672363)
                  ·
                    rfl

theorem cell20_357388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_357388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357388 prefixEnd_357388 := by exact prefixLift 357388
  have htrace : WordTrace (prefixWord ++ tailWord_357388) baseStart_357388 baseEnd_357388 := by
    simpa [prefixWord, tailWord_357388, baseEnd_357388] using wordTrace_append hprefix tailTrace_357388
  have hstable : (prefixWord ++ tailWord_357388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357388).length < 2 ^ (prefixWord ++ tailWord_357388).sum := by decide
  have hdescent : baseEnd_357388 < baseStart_357388 := by decide
  rcases family_descends (prefixWord ++ tailWord_357388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357394 : List Nat := [3, 2, 5, 1, 1, 1, 3, 4]
def baseStart_357394 : Nat := 118140960795 + 357394 * 2 ^ 59
def prefixEnd_357394 : Nat := 4983230072969 + 3 ^ 40 * 357394 * 2
def baseEnd_357394 : Nat := 54374786676468126824113

theorem tailTrace_357394 : CollatzResearch.WordTrace tailWord_357394 prefixEnd_357394 54374786676468126824113 := by
  unfold tailWord_357394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3258807516807512720205809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8690153378153367253882157 3258807516807512720205809)
  ·
    refine ⟨2444105637605634540154357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3258807516807512720205809 2444105637605634540154357)
    ·
      refine ⟨229134903525528238139471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2444105637605634540154357 229134903525528238139471)
      ·
        refine ⟨343702355288292357209207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229134903525528238139471 343702355288292357209207)
        ·
          refine ⟨515553532932438535813811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343702355288292357209207 515553532932438535813811)
          ·
            refine ⟨773330299398657803720717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515553532932438535813811 773330299398657803720717)
            ·
              refine ⟨289998862274496676395269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 773330299398657803720717 289998862274496676395269)
              ·
                refine ⟨54374786676468126824113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289998862274496676395269 54374786676468126824113)
                ·
                  rfl

theorem cell20_357394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_357394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357394 prefixEnd_357394 := by exact prefixLift 357394
  have htrace : WordTrace (prefixWord ++ tailWord_357394) baseStart_357394 baseEnd_357394 := by
    simpa [prefixWord, tailWord_357394, baseEnd_357394] using wordTrace_append hprefix tailTrace_357394
  have hstable : (prefixWord ++ tailWord_357394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357394).length < 2 ^ (prefixWord ++ tailWord_357394).sum := by decide
  have hdescent : baseEnd_357394 < baseStart_357394 := by decide
  rcases family_descends (prefixWord ++ tailWord_357394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357408 : List Nat := [2, 1, 1, 7, 1, 1, 2, 3, 2]
def baseStart_357408 : Nat := 118140960795 + 357408 * 2 ^ 59
def prefixEnd_357408 : Nat := 4983230072969 + 3 ^ 40 * 357408 * 2
def baseEnd_357408 : Nat := 163130750010882554005615

theorem tailTrace_357408 : CollatzResearch.WordTrace tailWord_357408 prefixEnd_357408 163130750010882554005615 := by
  unfold tailWord_357408
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517870344589665635916439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8690493792786220847888585 6517870344589665635916439)
  ·
    refine ⟨9776805516884498453874659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6517870344589665635916439 9776805516884498453874659)
    ·
      refine ⟨14665208275326747680811989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9776805516884498453874659 14665208275326747680811989)
      ·
        refine ⟨343715818952970648769031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14665208275326747680811989 343715818952970648769031)
        ·
          refine ⟨515573728429455973153547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343715818952970648769031 515573728429455973153547)
          ·
            refine ⟨773360592644183959730321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515573728429455973153547 773360592644183959730321)
            ·
              refine ⟨580020444483137969797741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773360592644183959730321 580020444483137969797741)
              ·
                refine ⟨217507666681176738674153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 580020444483137969797741 217507666681176738674153)
                ·
                  refine ⟨163130750010882554005615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217507666681176738674153 163130750010882554005615)
                  ·
                    rfl

theorem cell20_357408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_357408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357408 prefixEnd_357408 := by exact prefixLift 357408
  have htrace : WordTrace (prefixWord ++ tailWord_357408) baseStart_357408 baseEnd_357408 := by
    simpa [prefixWord, tailWord_357408, baseEnd_357408] using wordTrace_append hprefix tailTrace_357408
  have hstable : (prefixWord ++ tailWord_357408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357408).length < 2 ^ (prefixWord ++ tailWord_357408).sum := by decide
  have hdescent : baseEnd_357408 < baseStart_357408 := by decide
  rcases family_descends (prefixWord ++ tailWord_357408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357433 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_357433 : Nat := 118140960795 + 357433 * 2 ^ 59
def prefixEnd_357433 : Nat := 4983230072969 + 3 ^ 40 * 357433 * 2
def baseEnd_357433 : Nat := 163142160692093578172179

theorem tailTrace_357433 : CollatzResearch.WordTrace tailWord_357433 prefixEnd_357433 163142160692093578172179 := by
  unfold tailWord_357433
  simp only [CollatzResearch.WordTrace]
  refine ⟨13036652514088760541492953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8691101676059173694328635 13036652514088760541492953)
  ·
    refine ⟨9777489385566570406119715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13036652514088760541492953 9777489385566570406119715)
    ·
      refine ⟨14666234078349855609179573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9777489385566570406119715 14666234078349855609179573)
      ·
        refine ⟨1374959444845298963360585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14666234078349855609179573 1374959444845298963360585)
        ·
          refine ⟨1031219583633974222520439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1374959444845298963360585 1031219583633974222520439)
          ·
            refine ⟨1546829375450961333780659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031219583633974222520439 1546829375450961333780659)
            ·
              refine ⟨2320244063176442000670989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546829375450961333780659 2320244063176442000670989)
              ·
                refine ⟨870091523691165750251621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2320244063176442000670989 870091523691165750251621)
                ·
                  refine ⟨163142160692093578172179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 870091523691165750251621 163142160692093578172179)
                  ·
                    rfl

theorem cell20_357433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_357433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357433 prefixEnd_357433 := by exact prefixLift 357433
  have htrace : WordTrace (prefixWord ++ tailWord_357433) baseStart_357433 baseEnd_357433 := by
    simpa [prefixWord, tailWord_357433, baseEnd_357433] using wordTrace_append hprefix tailTrace_357433
  have hstable : (prefixWord ++ tailWord_357433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357433).length < 2 ^ (prefixWord ++ tailWord_357433).sum := by decide
  have hdescent : baseEnd_357433 < baseStart_357433 := by decide
  rcases family_descends (prefixWord ++ tailWord_357433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357540 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 3]
def baseStart_357540 : Nat := 118140960795 + 357540 * 2 ^ 59
def prefixEnd_357540 : Nat := 4983230072969 + 3 ^ 40 * 357540 * 2
def baseEnd_357540 : Nat := 163190998407676761605075

theorem tailTrace_357540 : CollatzResearch.WordTrace tailWord_357540 prefixEnd_357540 163190998407676761605075 := by
  unfold tailWord_357540
  simp only [CollatzResearch.WordTrace]
  refine ⟨6520277562350558907819037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8693703416467411877092049 6520277562350558907819037)
  ·
    refine ⟨2445104085881459590432139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6520277562350558907819037 2445104085881459590432139)
    ·
      refine ⟨3667656128822189385648209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2445104085881459590432139 3667656128822189385648209)
      ·
        refine ⟨2750742096616642039236157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3667656128822189385648209 2750742096616642039236157)
        ·
          refine ⟨1031528286231240764713559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2750742096616642039236157 1031528286231240764713559)
          ·
            refine ⟨1547292429346861147070339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031528286231240764713559 1547292429346861147070339)
            ·
              refine ⟨2320938644020291720605509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547292429346861147070339 2320938644020291720605509)
              ·
                refine ⟨435175995753804697613533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2320938644020291720605509 435175995753804697613533)
                ·
                  refine ⟨163190998407676761605075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435175995753804697613533 163190998407676761605075)
                  ·
                    rfl

theorem cell20_357540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_357540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357540 prefixEnd_357540 := by exact prefixLift 357540
  have htrace : WordTrace (prefixWord ++ tailWord_357540) baseStart_357540 baseEnd_357540 := by
    simpa [prefixWord, tailWord_357540, baseEnd_357540] using wordTrace_append hprefix tailTrace_357540
  have hstable : (prefixWord ++ tailWord_357540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357540).length < 2 ^ (prefixWord ++ tailWord_357540).sum := by decide
  have hdescent : baseEnd_357540 < baseStart_357540 := by decide
  rcases family_descends (prefixWord ++ tailWord_357540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357543 : List Nat := [1, 1, 6, 2, 1, 2, 1, 4, 2]
def baseStart_357543 : Nat := 118140960795 + 357543 * 2 ^ 59
def prefixEnd_357543 : Nat := 4983230072969 + 3 ^ 40 * 357543 * 2
def baseEnd_357543 : Nat := 163192367689422084505063

theorem tailTrace_357543 : CollatzResearch.WordTrace tailWord_357543 prefixEnd_357543 163192367689422084505063 := by
  unfold tailWord_357543
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040664543690249327997283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8693776362460166218664855 13040664543690249327997283)
  ·
    refine ⟨19560996815535373991995925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13040664543690249327997283 19560996815535373991995925)
    ·
      refine ⟨916921725728220655874809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19560996815535373991995925 916921725728220655874809)
      ·
        refine ⟨687691294296165491906107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 916921725728220655874809 687691294296165491906107)
        ·
          refine ⟨1031536941444248237859161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687691294296165491906107 1031536941444248237859161)
          ·
            refine ⟨773652706083186178394371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031536941444248237859161 773652706083186178394371)
            ·
              refine ⟨1160479059124779267591557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773652706083186178394371 1160479059124779267591557)
              ·
                refine ⟨217589823585896112673417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1160479059124779267591557 217589823585896112673417)
                ·
                  refine ⟨163192367689422084505063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217589823585896112673417 163192367689422084505063)
                  ·
                    rfl

theorem cell20_357543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 2].length) (baseStart_357543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357543 prefixEnd_357543 := by exact prefixLift 357543
  have htrace : WordTrace (prefixWord ++ tailWord_357543) baseStart_357543 baseEnd_357543 := by
    simpa [prefixWord, tailWord_357543, baseEnd_357543] using wordTrace_append hprefix tailTrace_357543
  have hstable : (prefixWord ++ tailWord_357543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357543).length < 2 ^ (prefixWord ++ tailWord_357543).sum := by decide
  have hdescent : baseEnd_357543 < baseStart_357543 := by decide
  rcases family_descends (prefixWord ++ tailWord_357543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357554 : List Nat := [3, 2, 1, 1, 1, 4, 3, 5]
def baseStart_357554 : Nat := 118140960795 + 357554 * 2 ^ 59
def prefixEnd_357554 : Nat := 4983230072969 + 3 ^ 40 * 357554 * 2
def baseEnd_357554 : Nat := 54399129463051645046117

theorem tailTrace_357554 : CollatzResearch.WordTrace tailWord_357554 prefixEnd_357554 54399129463051645046117 := by
  unfold tailWord_357554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260266436662599551661929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8694043831100265471098477 3260266436662599551661929)
  ·
    refine ⟨2445199827496949663746447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3260266436662599551661929 2445199827496949663746447)
    ·
      refine ⟨3667799741245424495619671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2445199827496949663746447 3667799741245424495619671)
      ·
        refine ⟨5501699611868136743429507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3667799741245424495619671 5501699611868136743429507)
        ·
          refine ⟨8252549417802205115144261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501699611868136743429507 8252549417802205115144261)
          ·
            refine ⟨1547353015837913459089549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8252549417802205115144261 1547353015837913459089549)
            ·
              refine ⟨580257380939217547158581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1547353015837913459089549 580257380939217547158581)
              ·
                refine ⟨54399129463051645046117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 580257380939217547158581 54399129463051645046117)
                ·
                  rfl

theorem cell20_357554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_357554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357554 prefixEnd_357554 := by exact prefixLift 357554
  have htrace : WordTrace (prefixWord ++ tailWord_357554) baseStart_357554 baseEnd_357554 := by
    simpa [prefixWord, tailWord_357554, baseEnd_357554] using wordTrace_append hprefix tailTrace_357554
  have hstable : (prefixWord ++ tailWord_357554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357554).length < 2 ^ (prefixWord ++ tailWord_357554).sum := by decide
  have hdescent : baseEnd_357554 < baseStart_357554 := by decide
  rcases family_descends (prefixWord ++ tailWord_357554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357575 : List Nat := [1, 1, 4, 1, 1, 1, 1, 10]
def baseStart_357575 : Nat := 118140960795 + 357575 * 2 ^ 59
def prefixEnd_357575 : Nat := 4983230072969 + 3 ^ 40 * 357575 * 2
def baseEnd_357575 : Nat := 54402324453790731812755

theorem tailTrace_357575 : CollatzResearch.WordTrace tailWord_357575 prefixEnd_357575 54402324453790731812755 := by
  unfold tailWord_357575
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041831679574318793162179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8694554453049545862108119 13041831679574318793162179)
  ·
    refine ⟨19562747519361478189743269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13041831679574318793162179 19562747519361478189743269)
    ·
      refine ⟨3668015159880277160576863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19562747519361478189743269 3668015159880277160576863)
      ·
        refine ⟨5502022739820415740865295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3668015159880277160576863 5502022739820415740865295)
        ·
          refine ⟨8253034109730623611297943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5502022739820415740865295 8253034109730623611297943)
          ·
            refine ⟨12379551164595935416946915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8253034109730623611297943 12379551164595935416946915)
            ·
              refine ⟨18569326746893903125420373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12379551164595935416946915 18569326746893903125420373)
              ·
                refine ⟨54402324453790731812755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18569326746893903125420373 54402324453790731812755)
                ·
                  rfl

theorem cell20_357575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_357575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357575 prefixEnd_357575 := by exact prefixLift 357575
  have htrace : WordTrace (prefixWord ++ tailWord_357575) baseStart_357575 baseEnd_357575 := by
    simpa [prefixWord, tailWord_357575, baseEnd_357575] using wordTrace_append hprefix tailTrace_357575
  have hstable : (prefixWord ++ tailWord_357575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357575).length < 2 ^ (prefixWord ++ tailWord_357575).sum := by decide
  have hdescent : baseEnd_357575 < baseStart_357575 := by decide
  rcases family_descends (prefixWord ++ tailWord_357575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357592 : List Nat := [2, 1, 2, 2, 5, 1, 7]
def baseStart_357592 : Nat := 118140960795 + 357592 * 2 ^ 59
def prefixEnd_357592 : Nat := 4983230072969 + 3 ^ 40 * 357592 * 2
def baseEnd_357592 : Nat := 18134970291621743541281

theorem tailTrace_357592 : CollatzResearch.WordTrace tailWord_357592 prefixEnd_357592 18134970291621743541281 := by
  unfold tailWord_357592
  simp only [CollatzResearch.WordTrace]
  refine ⟨6521225860256365348265515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8694967813675153797687353 6521225860256365348265515)
  ·
    refine ⟨9781838790384548022398273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6521225860256365348265515 9781838790384548022398273)
    ·
      refine ⟨7336379092788411016798705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9781838790384548022398273 7336379092788411016798705)
      ·
        refine ⟨5502284319591308262599029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7336379092788411016798705 5502284319591308262599029)
        ·
          refine ⟨515839154961685149618659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5502284319591308262599029 515839154961685149618659)
          ·
            refine ⟨773758732442527724427989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515839154961685149618659 773758732442527724427989)
            ·
              refine ⟨18134970291621743541281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 773758732442527724427989 18134970291621743541281)
              ·
                rfl

theorem cell20_357592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 7].length) (baseStart_357592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357592 prefixEnd_357592 := by exact prefixLift 357592
  have htrace : WordTrace (prefixWord ++ tailWord_357592) baseStart_357592 baseEnd_357592 := by
    simpa [prefixWord, tailWord_357592, baseEnd_357592] using wordTrace_append hprefix tailTrace_357592
  have hstable : (prefixWord ++ tailWord_357592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357592).length < 2 ^ (prefixWord ++ tailWord_357592).sum := by decide
  have hdescent : baseEnd_357592 < baseStart_357592 := by decide
  rcases family_descends (prefixWord ++ tailWord_357592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357668 : List Nat := [2, 3, 1, 3, 1, 1, 4, 5]
def baseStart_357668 : Nat := 118140960795 + 357668 * 2 ^ 59
def prefixEnd_357668 : Nat := 4983230072969 + 3 ^ 40 * 357668 * 2
def baseEnd_357668 : Nat := 54416473698492401779295

theorem tailTrace_357668 : CollatzResearch.WordTrace tailWord_357668 prefixEnd_357668 54416473698492401779295 := by
  unfold tailWord_357668
  simp only [CollatzResearch.WordTrace]
  refine ⟨6522611834118697838148829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8696815778824930450865105 6522611834118697838148829)
  ·
    refine ⟨2445979437794511689305811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6522611834118697838148829 2445979437794511689305811)
    ·
      refine ⟨3668969156691767533958717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2445979437794511689305811 3668969156691767533958717)
      ·
        refine ⟨1375863433759412825234519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3668969156691767533958717 1375863433759412825234519)
        ·
          refine ⟨2063795150639119237851779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375863433759412825234519 2063795150639119237851779)
          ·
            refine ⟨3095692725958678856777669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2063795150639119237851779 3095692725958678856777669)
            ·
              refine ⟨580442386117252285645813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3095692725958678856777669 580442386117252285645813)
              ·
                refine ⟨54416473698492401779295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 580442386117252285645813 54416473698492401779295)
                ·
                  rfl

theorem cell20_357668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_357668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357668 prefixEnd_357668 := by exact prefixLift 357668
  have htrace : WordTrace (prefixWord ++ tailWord_357668) baseStart_357668 baseEnd_357668 := by
    simpa [prefixWord, tailWord_357668, baseEnd_357668] using wordTrace_append hprefix tailTrace_357668
  have hstable : (prefixWord ++ tailWord_357668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357668).length < 2 ^ (prefixWord ++ tailWord_357668).sum := by decide
  have hdescent : baseEnd_357668 < baseStart_357668 := by decide
  rcases family_descends (prefixWord ++ tailWord_357668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357699 : List Nat := [1, 1, 1, 3, 1, 3, 1, 7, 2]
def baseStart_357699 : Nat := 118140960795 + 357699 * 2 ^ 59
def prefixEnd_357699 : Nat := 4983230072969 + 3 ^ 40 * 357699 * 2
def baseEnd_357699 : Nat := 163263570340178875304425

theorem tailTrace_357699 : CollatzResearch.WordTrace tailWord_357699 prefixEnd_357699 163263570340178875304425 := by
  unfold tailWord_357699
  simp only [CollatzResearch.WordTrace]
  refine ⟨13046354331125087970676151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8697569554083391980450767 13046354331125087970676151)
  ·
    refine ⟨19569531496687631956014227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13046354331125087970676151 19569531496687631956014227)
    ·
      refine ⟨29354297245031447934021341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19569531496687631956014227 29354297245031447934021341)
      ·
        refine ⟨11007861466886792975258003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29354297245031447934021341 11007861466886792975258003)
        ·
          refine ⟨16511792200330189462887005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11007861466886792975258003 16511792200330189462887005)
          ·
            refine ⟨6191922075123821048582627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16511792200330189462887005 6191922075123821048582627)
            ·
              refine ⟨9287883112685731572873941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191922075123821048582627 9287883112685731572873941)
              ·
                refine ⟨217684760453571833739233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9287883112685731572873941 217684760453571833739233)
                ·
                  refine ⟨163263570340178875304425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217684760453571833739233 163263570340178875304425)
                  ·
                    rfl

theorem cell20_357699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 2].length) (baseStart_357699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357699 prefixEnd_357699 := by exact prefixLift 357699
  have htrace : WordTrace (prefixWord ++ tailWord_357699) baseStart_357699 baseEnd_357699 := by
    simpa [prefixWord, tailWord_357699, baseEnd_357699] using wordTrace_append hprefix tailTrace_357699
  have hstable : (prefixWord ++ tailWord_357699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357699).length < 2 ^ (prefixWord ++ tailWord_357699).sum := by decide
  have hdescent : baseEnd_357699 < baseStart_357699 := by decide
  rcases family_descends (prefixWord ++ tailWord_357699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357702 : List Nat := [6, 1, 1, 3, 1, 8]
def baseStart_357702 : Nat := 118140960795 + 357702 * 2 ^ 59
def prefixEnd_357702 : Nat := 4983230072969 + 3 ^ 40 * 357702 * 2
def baseEnd_357702 : Nat := 6046849615626822155719

theorem tailTrace_357702 : CollatzResearch.WordTrace tailWord_357702 prefixEnd_357702 6046849615626822155719 := by
  unfold tailWord_357702
  simp only [CollatzResearch.WordTrace]
  refine ⟨407701992191069358844855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8697642500076146322023573 407701992191069358844855)
  ·
    refine ⟨611552988286604038267283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 407701992191069358844855 611552988286604038267283)
    ·
      refine ⟨917329482429906057400925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611552988286604038267283 917329482429906057400925)
      ·
        refine ⟨343998555911214771525347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 917329482429906057400925 343998555911214771525347)
        ·
          refine ⟨515997833866822157288021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343998555911214771525347 515997833866822157288021)
          ·
            refine ⟨6046849615626822155719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 515997833866822157288021 6046849615626822155719)
            ·
              rfl

theorem cell20_357702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 8].length) (baseStart_357702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357702 prefixEnd_357702 := by exact prefixLift 357702
  have htrace : WordTrace (prefixWord ++ tailWord_357702) baseStart_357702 baseEnd_357702 := by
    simpa [prefixWord, tailWord_357702, baseEnd_357702] using wordTrace_append hprefix tailTrace_357702
  have hstable : (prefixWord ++ tailWord_357702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357702).length < 2 ^ (prefixWord ++ tailWord_357702).sum := by decide
  have hdescent : baseEnd_357702 < baseStart_357702 := by decide
  rcases family_descends (prefixWord ++ tailWord_357702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357716 : List Nat := [2, 4, 1, 1, 2, 1, 3, 4, 2]
def baseStart_357716 : Nat := 118140960795 + 357716 * 2 ^ 59
def prefixEnd_357716 : Nat := 4983230072969 + 3 ^ 40 * 357716 * 2
def baseEnd_357716 : Nat := 163271329603402371737689

theorem tailTrace_357716 : CollatzResearch.WordTrace tailWord_357716 prefixEnd_357716 163271329603402371737689 := by
  unfold tailWord_357716
  simp only [CollatzResearch.WordTrace]
  refine ⟨6523487186031749937022501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8697982914708999916030001 6523487186031749937022501)
  ·
    refine ⟨1223153847380953113191719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6523487186031749937022501 1223153847380953113191719)
    ·
      refine ⟨1834730771071429669787579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1223153847380953113191719 1834730771071429669787579)
      ·
        refine ⟨2752096156607144504681369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1834730771071429669787579 2752096156607144504681369)
        ·
          refine ⟨2064072117455358378511027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2752096156607144504681369 2064072117455358378511027)
          ·
            refine ⟨3096108176183037567766541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064072117455358378511027 3096108176183037567766541)
            ·
              refine ⟨1161040566068639087912453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3096108176183037567766541 1161040566068639087912453)
              ·
                refine ⟨217695106137869828983585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1161040566068639087912453 217695106137869828983585)
                ·
                  refine ⟨163271329603402371737689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217695106137869828983585 163271329603402371737689)
                  ·
                    rfl

theorem cell20_357716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_357716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357716 prefixEnd_357716 := by exact prefixLift 357716
  have htrace : WordTrace (prefixWord ++ tailWord_357716) baseStart_357716 baseEnd_357716 := by
    simpa [prefixWord, tailWord_357716, baseEnd_357716] using wordTrace_append hprefix tailTrace_357716
  have hstable : (prefixWord ++ tailWord_357716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357716).length < 2 ^ (prefixWord ++ tailWord_357716).sum := by decide
  have hdescent : baseEnd_357716 < baseStart_357716 := by decide
  rcases family_descends (prefixWord ++ tailWord_357716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357720 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_357720 : Nat := 118140960795 + 357720 * 2 ^ 59
def prefixEnd_357720 : Nat := 4983230072969 + 3 ^ 40 * 357720 * 2
def baseEnd_357720 : Nat := 163273155312396135604339

theorem tailTrace_357720 : CollatzResearch.WordTrace tailWord_357720 prefixEnd_357720 163273155312396135604339 := by
  unfold tailWord_357720
  simp only [CollatzResearch.WordTrace]
  refine ⟨6523560132024504278595307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8698080176032672371460409 6523560132024504278595307)
  ·
    refine ⟨9785340198036756417892961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6523560132024504278595307 9785340198036756417892961)
    ·
      refine ⟨7339005148527567313419721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9785340198036756417892961 7339005148527567313419721)
      ·
        refine ⟨5504253861395675485064791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7339005148527567313419721 5504253861395675485064791)
        ·
          refine ⟨8256380792093513227597187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5504253861395675485064791 8256380792093513227597187)
          ·
            refine ⟨12384571188140269841395781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8256380792093513227597187 12384571188140269841395781)
            ·
              refine ⟨2322107097776300595261709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12384571188140269841395781 2322107097776300595261709)
              ·
                refine ⟨870790161666112723223141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2322107097776300595261709 870790161666112723223141)
                ·
                  refine ⟨163273155312396135604339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 870790161666112723223141 163273155312396135604339)
                  ·
                    rfl

theorem cell20_357720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_357720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357720 prefixEnd_357720 := by exact prefixLift 357720
  have htrace : WordTrace (prefixWord ++ tailWord_357720) baseStart_357720 baseEnd_357720 := by
    simpa [prefixWord, tailWord_357720, baseEnd_357720] using wordTrace_append hprefix tailTrace_357720
  have hstable : (prefixWord ++ tailWord_357720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357720).length < 2 ^ (prefixWord ++ tailWord_357720).sum := by decide
  have hdescent : baseEnd_357720 < baseStart_357720 := by decide
  rcases family_descends (prefixWord ++ tailWord_357720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357730 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_357730 : Nat := 118140960795 + 357730 * 2 ^ 59
def prefixEnd_357730 : Nat := 4983230072969 + 3 ^ 40 * 357730 * 2
def baseEnd_357730 : Nat := 163277719584880545270965

theorem tailTrace_357730 : CollatzResearch.WordTrace tailWord_357730 prefixEnd_357730 163277719584880545270965 := by
  unfold tailWord_357730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3261871248503195066263661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8698323329341853510036429 3261871248503195066263661)
  ·
    refine ⟨1223201718188698149848873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3261871248503195066263661 1223201718188698149848873)
    ·
      refine ⟨917401288641523612386655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1223201718188698149848873 917401288641523612386655)
      ·
        refine ⟨1376101932962285418579983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917401288641523612386655 1376101932962285418579983)
        ·
          refine ⟨2064152899443428127869975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376101932962285418579983 2064152899443428127869975)
          ·
            refine ⟨3096229349165142191804963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064152899443428127869975 3096229349165142191804963)
            ·
              refine ⟨4644344023747713287707445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096229349165142191804963 4644344023747713287707445)
              ·
                refine ⟨435407252226348120722573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4644344023747713287707445 435407252226348120722573)
                ·
                  refine ⟨163277719584880545270965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435407252226348120722573 163277719584880545270965)
                  ·
                    rfl

theorem cell20_357730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_357730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357730 prefixEnd_357730 := by exact prefixLift 357730
  have htrace : WordTrace (prefixWord ++ tailWord_357730) baseStart_357730 baseEnd_357730 := by
    simpa [prefixWord, tailWord_357730, baseEnd_357730] using wordTrace_append hprefix tailTrace_357730
  have hstable : (prefixWord ++ tailWord_357730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357730).length < 2 ^ (prefixWord ++ tailWord_357730).sum := by decide
  have hdescent : baseEnd_357730 < baseStart_357730 := by decide
  rcases family_descends (prefixWord ++ tailWord_357730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357744 : List Nat := [2, 1, 1, 1, 4, 2, 5, 4]
def baseStart_357744 : Nat := 118140960795 + 357744 * 2 ^ 59
def prefixEnd_357744 : Nat := 4983230072969 + 3 ^ 40 * 357744 * 2
def baseEnd_357744 : Nat := 54428036522119572934747

theorem tailTrace_357744 : CollatzResearch.WordTrace tailWord_357744 prefixEnd_357744 54428036522119572934747 := by
  unfold tailWord_357744
  simp only [CollatzResearch.WordTrace]
  refine ⟨6523997807981030328032143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8698663743974707104042857 6523997807981030328032143)
  ·
    refine ⟨9785996711971545492048215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6523997807981030328032143 9785996711971545492048215)
    ·
      refine ⟨14678995067957318238072323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9785996711971545492048215 14678995067957318238072323)
      ·
        refine ⟨22018492601935977357108485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14678995067957318238072323 22018492601935977357108485)
        ·
          refine ⟨4128467362862995754457841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22018492601935977357108485 4128467362862995754457841)
          ·
            refine ⟨3096350522147246815843381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4128467362862995754457841 3096350522147246815843381)
            ·
              refine ⟨290282861451304388985317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3096350522147246815843381 290282861451304388985317)
              ·
                refine ⟨54428036522119572934747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290282861451304388985317 54428036522119572934747)
                ·
                  rfl

theorem cell20_357744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_357744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357744 prefixEnd_357744 := by exact prefixLift 357744
  have htrace : WordTrace (prefixWord ++ tailWord_357744) baseStart_357744 baseEnd_357744 := by
    simpa [prefixWord, tailWord_357744, baseEnd_357744] using wordTrace_append hprefix tailTrace_357744
  have hstable : (prefixWord ++ tailWord_357744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357744).length < 2 ^ (prefixWord ++ tailWord_357744).sum := by decide
  have hdescent : baseEnd_357744 < baseStart_357744 := by decide
  rcases family_descends (prefixWord ++ tailWord_357744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357768 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 3]
def baseStart_357768 : Nat := 118140960795 + 357768 * 2 ^ 59
def prefixEnd_357768 : Nat := 4983230072969 + 3 ^ 40 * 357768 * 2
def baseEnd_357768 : Nat := 163295063820321302004143

theorem tailTrace_357768 : CollatzResearch.WordTrace tailWord_357768 prefixEnd_357768 163295063820321302004143 := by
  unfold tailWord_357768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6524435483937556377468979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8699247311916741836625305 6524435483937556377468979)
  ·
    refine ⟨9786653225906334566203469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6524435483937556377468979 9786653225906334566203469)
    ·
      refine ⟨3669994959714875462326301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9786653225906334566203469 3669994959714875462326301)
      ·
        refine ⟨1376248109893078298372363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3669994959714875462326301 1376248109893078298372363)
        ·
          refine ⟨2064372164839617447558545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376248109893078298372363 2064372164839617447558545)
          ·
            refine ⟨1548279123629713085668909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2064372164839617447558545 1548279123629713085668909)
            ·
              refine ⟨580604671361142407125841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1548279123629713085668909 580604671361142407125841)
              ·
                refine ⟨435453503520856805344381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580604671361142407125841 435453503520856805344381)
                ·
                  refine ⟨163295063820321302004143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435453503520856805344381 163295063820321302004143)
                  ·
                    rfl

theorem cell20_357768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_357768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357768 prefixEnd_357768 := by exact prefixLift 357768
  have htrace : WordTrace (prefixWord ++ tailWord_357768) baseStart_357768 baseEnd_357768 := by
    simpa [prefixWord, tailWord_357768, baseEnd_357768] using wordTrace_append hprefix tailTrace_357768
  have hstable : (prefixWord ++ tailWord_357768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357768).length < 2 ^ (prefixWord ++ tailWord_357768).sum := by decide
  have hdescent : baseEnd_357768 < baseStart_357768 := by decide
  rcases family_descends (prefixWord ++ tailWord_357768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357885 : List Nat := [1, 4, 1, 1, 1, 6, 2, 2, 2]
def baseStart_357885 : Nat := 118140960795 + 357885 * 2 ^ 59
def prefixEnd_357885 : Nat := 4983230072969 + 3 ^ 40 * 357885 * 2
def baseEnd_357885 : Nat := 163348465808388895103665

theorem tailTrace_357885 : CollatzResearch.WordTrace tailWord_357885 prefixEnd_357885 163348465808388895103665 := by
  unfold tailWord_357885
  simp only [CollatzResearch.WordTrace]
  refine ⟨13053138308451241736947109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8702092205634161157964739 13053138308451241736947109)
  ·
    refine ⟨2447463432834607825677583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13053138308451241736947109 2447463432834607825677583)
    ·
      refine ⟨3671195149251911738516375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2447463432834607825677583 3671195149251911738516375)
      ·
        refine ⟨5506792723877867607774563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3671195149251911738516375 5506792723877867607774563)
        ·
          refine ⟨8260189085816801411661845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506792723877867607774563 8260189085816801411661845)
          ·
            refine ⟨387196363397662566171649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8260189085816801411661845 387196363397662566171649)
            ·
              refine ⟨290397272548246924628737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387196363397662566171649 290397272548246924628737)
              ·
                refine ⟨217797954411185193471553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290397272548246924628737 217797954411185193471553)
                ·
                  refine ⟨163348465808388895103665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217797954411185193471553 163348465808388895103665)
                  ·
                    rfl

theorem cell20_357885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_357885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357885 prefixEnd_357885 := by exact prefixLift 357885
  have htrace : WordTrace (prefixWord ++ tailWord_357885) baseStart_357885 baseEnd_357885 := by
    simpa [prefixWord, tailWord_357885, baseEnd_357885] using wordTrace_append hprefix tailTrace_357885
  have hstable : (prefixWord ++ tailWord_357885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357885).length < 2 ^ (prefixWord ++ tailWord_357885).sum := by decide
  have hdescent : baseEnd_357885 < baseStart_357885 := by decide
  rcases family_descends (prefixWord ++ tailWord_357885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357892 : List Nat := [2, 3, 2, 3, 3, 1, 1, 5]
def baseStart_357892 : Nat := 118140960795 + 357892 * 2 ^ 59
def prefixEnd_357892 : Nat := 4983230072969 + 3 ^ 40 * 357892 * 2
def baseEnd_357892 : Nat := 54450553599709327290101

theorem tailTrace_357892 : CollatzResearch.WordTrace tailWord_357892 prefixEnd_357892 54450553599709327290101 := by
  unfold tailWord_357892
  simp only [CollatzResearch.WordTrace]
  refine ⟨6526696809712940966225965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8702262412950587954967953 6526696809712940966225965)
  ·
    refine ⟨2447511303642352862334737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6526696809712940966225965 2447511303642352862334737)
    ·
      refine ⟨1835633477731764646751053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2447511303642352862334737 1835633477731764646751053)
      ·
        refine ⟨688362554149411742531645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1835633477731764646751053 688362554149411742531645)
        ·
          refine ⟨258135957806029403449367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 688362554149411742531645 258135957806029403449367)
          ·
            refine ⟨387203936709044105174051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258135957806029403449367 387203936709044105174051)
            ·
              refine ⟨580805905063566157761077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387203936709044105174051 580805905063566157761077)
              ·
                refine ⟨54450553599709327290101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 580805905063566157761077 54450553599709327290101)
                ·
                  rfl

theorem cell20_357892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_357892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357892 prefixEnd_357892 := by exact prefixLift 357892
  have htrace : WordTrace (prefixWord ++ tailWord_357892) baseStart_357892 baseEnd_357892 := by
    simpa [prefixWord, tailWord_357892, baseEnd_357892] using wordTrace_append hprefix tailTrace_357892
  have hstable : (prefixWord ++ tailWord_357892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357892).length < 2 ^ (prefixWord ++ tailWord_357892).sum := by decide
  have hdescent : baseEnd_357892 < baseStart_357892 := by decide
  rcases family_descends (prefixWord ++ tailWord_357892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357934 : List Nat := [4, 1, 3, 1, 2, 2, 7]
def baseStart_357934 : Nat := 118140960795 + 357934 * 2 ^ 59
def prefixEnd_357934 : Nat := 4983230072969 + 3 ^ 40 * 357934 * 2
def baseEnd_357934 : Nat := 18152314527062500274459

theorem tailTrace_357934 : CollatzResearch.WordTrace tailWord_357934 prefixEnd_357934 18152314527062500274459 := by
  unfold tailWord_357934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631865685659215388185107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8703283656849148736987237 1631865685659215388185107)
  ·
    refine ⟨2447798528488823082277661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1631865685659215388185107 2447798528488823082277661)
    ·
      refine ⟨917924448183308655854123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2447798528488823082277661 917924448183308655854123)
      ·
        refine ⟨1376886672274962983781185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917924448183308655854123 1376886672274962983781185)
        ·
          refine ⟨1032665004206222237835889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1376886672274962983781185 1032665004206222237835889)
          ·
            refine ⟨774498753154666678376917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1032665004206222237835889 774498753154666678376917)
            ·
              refine ⟨18152314527062500274459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 774498753154666678376917 18152314527062500274459)
              ·
                rfl

theorem cell20_357934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 7].length) (baseStart_357934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357934 prefixEnd_357934 := by exact prefixLift 357934
  have htrace : WordTrace (prefixWord ++ tailWord_357934) baseStart_357934 baseEnd_357934 := by
    simpa [prefixWord, tailWord_357934, baseEnd_357934] using wordTrace_append hprefix tailTrace_357934
  have hstable : (prefixWord ++ tailWord_357934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357934).length < 2 ^ (prefixWord ++ tailWord_357934).sum := by decide
  have hdescent : baseEnd_357934 < baseStart_357934 := by decide
  rcases family_descends (prefixWord ++ tailWord_357934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357941 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 5]
def baseStart_357941 : Nat := 118140960795 + 357941 * 2 ^ 59
def prefixEnd_357941 : Nat := 4983230072969 + 3 ^ 40 * 357941 * 2
def baseEnd_357941 : Nat := 163374025734301589236769

theorem tailTrace_357941 : CollatzResearch.WordTrace tailWord_357941 prefixEnd_357941 163374025734301589236769 := by
  unfold tailWord_357941
  simp only [CollatzResearch.WordTrace]
  refine ⟨13055180796248363300985677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8703453864165575533990451 13055180796248363300985677)
  ·
    refine ⟨4895692798593136237869629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13055180796248363300985677 4895692798593136237869629)
    ·
      refine ⟨1835884799472426089201111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4895692798593136237869629 1835884799472426089201111)
      ·
        refine ⟨2753827199208639133801667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835884799472426089201111 2753827199208639133801667)
        ·
          refine ⟨4130740798812958700702501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2753827199208639133801667 4130740798812958700702501)
          ·
            refine ⟨774513899777429756381719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4130740798812958700702501 774513899777429756381719)
            ·
              refine ⟨1161770849666144634572579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774513899777429756381719 1161770849666144634572579)
              ·
                refine ⟨1742656274499216951858869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161770849666144634572579 1742656274499216951858869)
                ·
                  refine ⟨163374025734301589236769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1742656274499216951858869 163374025734301589236769)
                  ·
                    rfl

theorem cell20_357941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_357941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357941 prefixEnd_357941 := by exact prefixLift 357941
  have htrace : WordTrace (prefixWord ++ tailWord_357941) baseStart_357941 baseEnd_357941 := by
    simpa [prefixWord, tailWord_357941, baseEnd_357941] using wordTrace_append hprefix tailTrace_357941
  have hstable : (prefixWord ++ tailWord_357941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357941).length < 2 ^ (prefixWord ++ tailWord_357941).sum := by decide
  have hdescent : baseEnd_357941 < baseStart_357941 := by decide
  rcases family_descends (prefixWord ++ tailWord_357941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357974 : List Nat := [5, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_357974 : Nat := 118140960795 + 357974 * 2 ^ 59
def prefixEnd_357974 : Nat := 4983230072969 + 3 ^ 40 * 357974 * 2
def baseEnd_357974 : Nat := 163389087833500141136635

theorem tailTrace_357974 : CollatzResearch.WordTrace tailWord_357974 prefixEnd_357974 163389087833500141136635 := by
  unfold tailWord_357974
  simp only [CollatzResearch.WordTrace]
  refine ⟨816024025320550621058561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8704256270085873291291317 816024025320550621058561)
  ·
    refine ⟨612018018990412965793921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 816024025320550621058561 612018018990412965793921)
    ·
      refine ⟨459013514242809724345441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 612018018990412965793921 459013514242809724345441)
      ·
        refine ⟨344260135682107293259081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459013514242809724345441 344260135682107293259081)
        ·
          refine ⟨258195101761580469944311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344260135682107293259081 258195101761580469944311)
          ·
            refine ⟨387292652642370704916467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258195101761580469944311 387292652642370704916467)
            ·
              refine ⟨580938978963556057374701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387292652642370704916467 580938978963556057374701)
              ·
                refine ⟨217852117111333521515513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 580938978963556057374701 217852117111333521515513)
                ·
                  refine ⟨163389087833500141136635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217852117111333521515513 163389087833500141136635)
                  ·
                    rfl

theorem cell20_357974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_357974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_357974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_357974 prefixEnd_357974 := by exact prefixLift 357974
  have htrace : WordTrace (prefixWord ++ tailWord_357974) baseStart_357974 baseEnd_357974 := by
    simpa [prefixWord, tailWord_357974, baseEnd_357974] using wordTrace_append hprefix tailTrace_357974
  have hstable : (prefixWord ++ tailWord_357974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357974).length < 2 ^ (prefixWord ++ tailWord_357974).sum := by decide
  have hdescent : baseEnd_357974 < baseStart_357974 := by decide
  rcases family_descends (prefixWord ++ tailWord_357974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358013 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 3]
def baseStart_358013 : Nat := 118140960795 + 358013 * 2 ^ 59
def prefixEnd_358013 : Nat := 4983230072969 + 3 ^ 40 * 358013 * 2
def baseEnd_358013 : Nat := 163406888496189338836475

theorem tailTrace_358013 : CollatzResearch.WordTrace tailWord_358013 prefixEnd_358013 163406888496189338836475 := by
  unfold tailWord_358013
  simp only [CollatzResearch.WordTrace]
  refine ⟨13057806851987519597606693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8705204567991679731737795 13057806851987519597606693)
  ·
    refine ⟨2448338784747659924551255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13057806851987519597606693 2448338784747659924551255)
    ·
      refine ⟨3672508177121489886826883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2448338784747659924551255 3672508177121489886826883)
      ·
        refine ⟨5508762265682234830240325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3672508177121489886826883 5508762265682234830240325)
        ·
          refine ⟨1032892924815419030670061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5508762265682234830240325 1032892924815419030670061)
          ·
            refine ⟨387334846805782136501273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1032892924815419030670061 387334846805782136501273)
            ·
              refine ⟨290501135104336602375955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387334846805782136501273 290501135104336602375955)
              ·
                refine ⟨435751702656504903563933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290501135104336602375955 435751702656504903563933)
                ·
                  refine ⟨163406888496189338836475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435751702656504903563933 163406888496189338836475)
                  ·
                    rfl

theorem cell20_358013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_358013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358013 prefixEnd_358013 := by exact prefixLift 358013
  have htrace : WordTrace (prefixWord ++ tailWord_358013) baseStart_358013 baseEnd_358013 := by
    simpa [prefixWord, tailWord_358013, baseEnd_358013] using wordTrace_append hprefix tailTrace_358013
  have hstable : (prefixWord ++ tailWord_358013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358013).length < 2 ^ (prefixWord ++ tailWord_358013).sum := by decide
  have hdescent : baseEnd_358013 < baseStart_358013 := by decide
  rcases family_descends (prefixWord ++ tailWord_358013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358117 : List Nat := [1, 3, 1, 4, 1, 1, 1, 6, 2]
def baseStart_358117 : Nat := 118140960795 + 358117 * 2 ^ 59
def prefixEnd_358117 : Nat := 4983230072969 + 3 ^ 40 * 358117 * 2
def baseEnd_358117 : Nat := 163454356930027199369383

theorem tailTrace_358117 : CollatzResearch.WordTrace tailWord_358117 prefixEnd_358117 163454356930027199369383 := by
  unfold tailWord_358117
  simp only [CollatzResearch.WordTrace]
  refine ⟨13061600043610745359392605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8707733362407163572928403 13061600043610745359392605)
  ·
    refine ⟨4898100016354029509772227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13061600043610745359392605 4898100016354029509772227)
    ·
      refine ⟨7347150024531044264658341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4898100016354029509772227 7347150024531044264658341)
      ·
        refine ⟨1377590629599570799623439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7347150024531044264658341 1377590629599570799623439)
        ·
          refine ⟨2066385944399356199435159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377590629599570799623439 2066385944399356199435159)
          ·
            refine ⟨3099578916599034299152739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066385944399356199435159 3099578916599034299152739)
            ·
              refine ⟨4649368374898551448729109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3099578916599034299152739 4649368374898551448729109)
              ·
                refine ⟨217939142573369599159177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4649368374898551448729109 217939142573369599159177)
                ·
                  refine ⟨163454356930027199369383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217939142573369599159177 163454356930027199369383)
                  ·
                    rfl

theorem cell20_358117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_358117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358117 prefixEnd_358117 := by exact prefixLift 358117
  have htrace : WordTrace (prefixWord ++ tailWord_358117) baseStart_358117 baseEnd_358117 := by
    simpa [prefixWord, tailWord_358117, baseEnd_358117] using wordTrace_append hprefix tailTrace_358117
  have hstable : (prefixWord ++ tailWord_358117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358117).length < 2 ^ (prefixWord ++ tailWord_358117).sum := by decide
  have hdescent : baseEnd_358117 < baseStart_358117 := by decide
  rcases family_descends (prefixWord ++ tailWord_358117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358151 : List Nat := [1, 1, 4, 4, 2, 2, 1, 3, 2]
def baseStart_358151 : Nat := 118140960795 + 358151 * 2 ^ 59
def prefixEnd_358151 : Nat := 4983230072969 + 3 ^ 40 * 358151 * 2
def baseEnd_358151 : Nat := 163469875456474192235911

theorem tailTrace_358151 : CollatzResearch.WordTrace tailWord_358151 prefixEnd_358151 163469875456474192235911 := by
  unfold tailWord_358151
  simp only [CollatzResearch.WordTrace]
  refine ⟨13062840125487569166130307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8708560083658379444086871 13062840125487569166130307)
  ·
    refine ⟨19594260188231353749195461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13062840125487569166130307 19594260188231353749195461)
    ·
      refine ⟨3673923785293378827974149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19594260188231353749195461 3673923785293378827974149)
      ·
        refine ⟨688860709742508530245153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3673923785293378827974149 688860709742508530245153)
        ·
          refine ⟨516645532306881397683865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688860709742508530245153 516645532306881397683865)
          ·
            refine ⟨387484149230161048262899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516645532306881397683865 387484149230161048262899)
            ·
              refine ⟨581226223845241572394349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387484149230161048262899 581226223845241572394349)
              ·
                refine ⟨217959833941965589647881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 581226223845241572394349 217959833941965589647881)
                ·
                  refine ⟨163469875456474192235911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217959833941965589647881 163469875456474192235911)
                  ·
                    rfl

theorem cell20_358151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 2].length) (baseStart_358151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358151 prefixEnd_358151 := by exact prefixLift 358151
  have htrace : WordTrace (prefixWord ++ tailWord_358151) baseStart_358151 baseEnd_358151 := by
    simpa [prefixWord, tailWord_358151, baseEnd_358151] using wordTrace_append hprefix tailTrace_358151
  have hstable : (prefixWord ++ tailWord_358151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358151).length < 2 ^ (prefixWord ++ tailWord_358151).sum := by decide
  have hdescent : baseEnd_358151 < baseStart_358151 := by decide
  rcases family_descends (prefixWord ++ tailWord_358151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358152 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_358152 : Nat := 118140960795 + 358152 * 2 ^ 59
def prefixEnd_358152 : Nat := 4983230072969 + 3 ^ 40 * 358152 * 2
def baseEnd_358152 : Nat := 163470331883722633202573

theorem tailTrace_358152 : CollatzResearch.WordTrace tailWord_358152 prefixEnd_358152 163470331883722633202573 := by
  unfold tailWord_358152
  simp only [CollatzResearch.WordTrace]
  refine ⟨6531438299241973168458355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8708584398989297557944473 6531438299241973168458355)
  ·
    refine ⟨9797157448862959752687533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6531438299241973168458355 9797157448862959752687533)
    ·
      refine ⟨3673934043323609907257825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9797157448862959752687533 3673934043323609907257825)
      ·
        refine ⟨2755450532492707430443369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3673934043323609907257825 2755450532492707430443369)
        ·
          refine ⟨2066587899369530572832527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2755450532492707430443369 2066587899369530572832527)
          ·
            refine ⟨3099881849054295859248791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066587899369530572832527 3099881849054295859248791)
            ·
              refine ⟨4649822773581443788873187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3099881849054295859248791 4649822773581443788873187)
              ·
                refine ⟨6974734160372165683309781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649822773581443788873187 6974734160372165683309781)
                ·
                  refine ⟨163470331883722633202573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6974734160372165683309781 163470331883722633202573)
                  ·
                    rfl

theorem cell20_358152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_358152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358152 prefixEnd_358152 := by exact prefixLift 358152
  have htrace : WordTrace (prefixWord ++ tailWord_358152) baseStart_358152 baseEnd_358152 := by
    simpa [prefixWord, tailWord_358152, baseEnd_358152] using wordTrace_append hprefix tailTrace_358152
  have hstable : (prefixWord ++ tailWord_358152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358152).length < 2 ^ (prefixWord ++ tailWord_358152).sum := by decide
  have hdescent : baseEnd_358152 < baseStart_358152 := by decide
  rcases family_descends (prefixWord ++ tailWord_358152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358155 : List Nat := [1, 1, 1, 1, 5, 1, 5, 3, 2]
def baseStart_358155 : Nat := 118140960795 + 358155 * 2 ^ 59
def prefixEnd_358155 : Nat := 4983230072969 + 3 ^ 40 * 358155 * 2
def baseEnd_358155 : Nat := 163471701165467956102561

theorem tailTrace_358155 : CollatzResearch.WordTrace tailWord_358155 prefixEnd_358155 163471701165467956102561 := by
  unfold tailWord_358155
  simp only [CollatzResearch.WordTrace]
  refine ⟨13062986017473077849275919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8708657344982051899517279 13062986017473077849275919)
  ·
    refine ⟨19594479026209616773913879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13062986017473077849275919 19594479026209616773913879)
    ·
      refine ⟨29391718539314425160870819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19594479026209616773913879 29391718539314425160870819)
      ·
        refine ⟨44087577808971637741306229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29391718539314425160870819 44087577808971637741306229)
        ·
          refine ⟨4133210419591091038247459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44087577808971637741306229 4133210419591091038247459)
          ·
            refine ⟨6199815629386636557371189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4133210419591091038247459 6199815629386636557371189)
            ·
              refine ⟨581232715254997177253549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6199815629386636557371189 581232715254997177253549)
              ·
                refine ⟨217962268220623941470081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 581232715254997177253549 217962268220623941470081)
                ·
                  refine ⟨163471701165467956102561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217962268220623941470081 163471701165467956102561)
                  ·
                    rfl

theorem cell20_358155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 2].length) (baseStart_358155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358155 prefixEnd_358155 := by exact prefixLift 358155
  have htrace : WordTrace (prefixWord ++ tailWord_358155) baseStart_358155 baseEnd_358155 := by
    simpa [prefixWord, tailWord_358155, baseEnd_358155] using wordTrace_append hprefix tailTrace_358155
  have hstable : (prefixWord ++ tailWord_358155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358155).length < 2 ^ (prefixWord ++ tailWord_358155).sum := by decide
  have hdescent : baseEnd_358155 < baseStart_358155 := by decide
  rcases family_descends (prefixWord ++ tailWord_358155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358162 : List Nat := [3, 2, 4, 1, 1, 1, 8]
def baseStart_358162 : Nat := 118140960795 + 358162 * 2 ^ 59
def prefixEnd_358162 : Nat := 4983230072969 + 3 ^ 40 * 358162 * 2
def baseEnd_358162 : Nat := 18163877350689671429911

theorem tailTrace_358162 : CollatzResearch.WordTrace tailWord_358162 prefixEnd_358162 18163877350689671429911 := by
  unfold tailWord_358162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3265810332111929511195185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8708827552298478696520493 3265810332111929511195185)
  ·
    refine ⟨2449357749083947133396389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3265810332111929511195185 2449357749083947133396389)
    ·
      refine ⟨459254577953240087511823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2449357749083947133396389 459254577953240087511823)
      ·
        refine ⟨688881866929860131267735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459254577953240087511823 688881866929860131267735)
        ·
          refine ⟨1033322800394790196901603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688881866929860131267735 1033322800394790196901603)
          ·
            refine ⟨1549984200592185295352405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033322800394790196901603 1549984200592185295352405)
            ·
              refine ⟨18163877350689671429911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1549984200592185295352405 18163877350689671429911)
              ·
                rfl

theorem cell20_358162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 8].length) (baseStart_358162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358162 prefixEnd_358162 := by exact prefixLift 358162
  have htrace : WordTrace (prefixWord ++ tailWord_358162) baseStart_358162 baseEnd_358162 := by
    simpa [prefixWord, tailWord_358162, baseEnd_358162] using wordTrace_append hprefix tailTrace_358162
  have hstable : (prefixWord ++ tailWord_358162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358162).length < 2 ^ (prefixWord ++ tailWord_358162).sum := by decide
  have hdescent : baseEnd_358162 < baseStart_358162 := by decide
  rcases family_descends (prefixWord ++ tailWord_358162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358172 : List Nat := [2, 2, 3, 1, 1, 2, 5, 2, 2]
def baseStart_358172 : Nat := 118140960795 + 358172 * 2 ^ 59
def prefixEnd_358172 : Nat := 4983230072969 + 3 ^ 40 * 358172 * 2
def baseEnd_358172 : Nat := 163479460428691452535825

theorem tailTrace_358172 : CollatzResearch.WordTrace tailWord_358172 prefixEnd_358172 163479460428691452535825 := by
  unfold tailWord_358172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6531803029205744876322385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8709070705607659835096513 6531803029205744876322385)
  ·
    refine ⟨4898852271904308657241789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6531803029205744876322385 4898852271904308657241789)
    ·
      refine ⟨1837069601964115746465671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4898852271904308657241789 1837069601964115746465671)
      ·
        refine ⟨2755604402946173619698507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837069601964115746465671 2755604402946173619698507)
        ·
          refine ⟨4133406604419260429547761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2755604402946173619698507 4133406604419260429547761)
          ·
            refine ⟨3100054953314445322160821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4133406604419260429547761 3100054953314445322160821)
            ·
              refine ⟨290630151873229248952577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3100054953314445322160821 290630151873229248952577)
              ·
                refine ⟨217972613904921936714433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290630151873229248952577 217972613904921936714433)
                ·
                  refine ⟨163479460428691452535825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217972613904921936714433 163479460428691452535825)
                  ·
                    rfl

theorem cell20_358172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_358172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358172 prefixEnd_358172 := by exact prefixLift 358172
  have htrace : WordTrace (prefixWord ++ tailWord_358172) baseStart_358172 baseEnd_358172 := by
    simpa [prefixWord, tailWord_358172, baseEnd_358172] using wordTrace_append hprefix tailTrace_358172
  have hstable : (prefixWord ++ tailWord_358172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358172).length < 2 ^ (prefixWord ++ tailWord_358172).sum := by decide
  have hdescent : baseEnd_358172 < baseStart_358172 := by decide
  rcases family_descends (prefixWord ++ tailWord_358172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358252 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_358252 : Nat := 118140960795 + 358252 * 2 ^ 59
def prefixEnd_358252 : Nat := 4983230072969 + 3 ^ 40 * 358252 * 2
def baseEnd_358252 : Nat := 163515974608566729868831

theorem tailTrace_358252 : CollatzResearch.WordTrace tailWord_358252 prefixEnd_358252 163515974608566729868831 := by
  unfold tailWord_358252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6533261949060831707778505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8711015932081108943704673 6533261949060831707778505)
  ·
    refine ⟨4899946461795623780833879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6533261949060831707778505 4899946461795623780833879)
    ·
      refine ⟨7349919692693435671250819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4899946461795623780833879 7349919692693435671250819)
      ·
        refine ⟨11024879539040153506876229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7349919692693435671250819 11024879539040153506876229)
        ·
          refine ⟨2067164913570028782539293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11024879539040153506876229 2067164913570028782539293)
          ·
            refine ⟨775186842588760793452235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2067164913570028782539293 775186842588760793452235)
            ·
              refine ⟨1162780263883141190178353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775186842588760793452235 1162780263883141190178353)
              ·
                refine ⟨872085197912355892633765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162780263883141190178353 872085197912355892633765)
                ·
                  refine ⟨163515974608566729868831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 872085197912355892633765 163515974608566729868831)
                  ·
                    rfl

theorem cell20_358252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_358252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358252 prefixEnd_358252 := by exact prefixLift 358252
  have htrace : WordTrace (prefixWord ++ tailWord_358252) baseStart_358252 baseEnd_358252 := by
    simpa [prefixWord, tailWord_358252, baseEnd_358252] using wordTrace_append hprefix tailTrace_358252
  have hstable : (prefixWord ++ tailWord_358252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358252).length < 2 ^ (prefixWord ++ tailWord_358252).sum := by decide
  have hdescent : baseEnd_358252 < baseStart_358252 := by decide
  rcases family_descends (prefixWord ++ tailWord_358252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358279 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 3]
def baseStart_358279 : Nat := 118140960795 + 358279 * 2 ^ 59
def prefixEnd_358279 : Nat := 4983230072969 + 3 ^ 40 * 358279 * 2
def baseEnd_358279 : Nat := 163528298144274635968721

theorem tailTrace_358279 : CollatzResearch.WordTrace tailWord_358279 prefixEnd_358279 163528298144274635968721 := by
  unfold tailWord_358279
  simp only [CollatzResearch.WordTrace]
  refine ⟨13067508669023847026789891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8711672446015898017859927 13067508669023847026789891)
  ·
    refine ⟨19601263003535770540184837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13067508669023847026789891 19601263003535770540184837)
    ·
      refine ⟨3675236813162956976284657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19601263003535770540184837 3675236813162956976284657)
      ·
        refine ⟨2756427609872217732213493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3675236813162956976284657 2756427609872217732213493)
        ·
          refine ⟨258415088425520412395015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2756427609872217732213493 258415088425520412395015)
          ·
            refine ⟨387622632638280618592523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258415088425520412395015 387622632638280618592523)
            ·
              refine ⟨581433948957420927888785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387622632638280618592523 581433948957420927888785)
              ·
                refine ⟨436075461718065695916589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581433948957420927888785 436075461718065695916589)
                ·
                  refine ⟨163528298144274635968721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436075461718065695916589 163528298144274635968721)
                  ·
                    rfl

theorem cell20_358279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 3].length) (baseStart_358279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358279 prefixEnd_358279 := by exact prefixLift 358279
  have htrace : WordTrace (prefixWord ++ tailWord_358279) baseStart_358279 baseEnd_358279 := by
    simpa [prefixWord, tailWord_358279, baseEnd_358279] using wordTrace_append hprefix tailTrace_358279
  have hstable : (prefixWord ++ tailWord_358279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358279).length < 2 ^ (prefixWord ++ tailWord_358279).sum := by decide
  have hdescent : baseEnd_358279 < baseStart_358279 := by decide
  rcases family_descends (prefixWord ++ tailWord_358279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358286 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_358286 : Nat := 118140960795 + 358286 * 2 ^ 59
def prefixEnd_358286 : Nat := 4983230072969 + 3 ^ 40 * 358286 * 2
def baseEnd_358286 : Nat := 163531493135013722735359

theorem tailTrace_358286 : CollatzResearch.WordTrace tailWord_358286 prefixEnd_358286 163531493135013722735359 := by
  unfold tailWord_358286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1633470497499810902786839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8711842653332324814863141 1633470497499810902786839)
  ·
    refine ⟨2450205746249716354180259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1633470497499810902786839 2450205746249716354180259)
    ·
      refine ⟨3675308619374574531270389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2450205746249716354180259 3675308619374574531270389)
      ·
        refine ⟨344560183066366362306599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3675308619374574531270389 344560183066366362306599)
        ·
          refine ⟨516840274599549543459899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344560183066366362306599 516840274599549543459899)
          ·
            refine ⟨775260411899324315189849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516840274599549543459899 775260411899324315189849)
            ·
              refine ⟨581445308924493236392387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775260411899324315189849 581445308924493236392387)
              ·
                refine ⟨872167963386739854588581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581445308924493236392387 872167963386739854588581)
                ·
                  refine ⟨163531493135013722735359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 872167963386739854588581 163531493135013722735359)
                  ·
                    rfl

theorem cell20_358286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_358286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358286 prefixEnd_358286 := by exact prefixLift 358286
  have htrace : WordTrace (prefixWord ++ tailWord_358286) baseStart_358286 baseEnd_358286 := by
    simpa [prefixWord, tailWord_358286, baseEnd_358286] using wordTrace_append hprefix tailTrace_358286
  have hstable : (prefixWord ++ tailWord_358286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358286).length < 2 ^ (prefixWord ++ tailWord_358286).sum := by decide
  have hdescent : baseEnd_358286 < baseStart_358286 := by decide
  rcases family_descends (prefixWord ++ tailWord_358286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358390 : List Nat := [5, 1, 1, 1, 5, 7]
def baseStart_358390 : Nat := 118140960795 + 358390 * 2 ^ 59
def prefixEnd_358390 : Nat := 4983230072969 + 3 ^ 40 * 358390 * 2
def baseEnd_358390 : Nat := 6058480058105614195121

theorem tailTrace_358390 : CollatzResearch.WordTrace tailWord_358390 prefixEnd_358390 6058480058105614195121 := by
  unfold tailWord_358390
  simp only [CollatzResearch.WordTrace]
  refine ⟨816972323226357061505039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8714371447747808656053749 816972323226357061505039)
  ·
    refine ⟨1225458484839535592257559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 816972323226357061505039 1225458484839535592257559)
    ·
      refine ⟨1838187727259303388386339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1225458484839535592257559 1838187727259303388386339)
      ·
        refine ⟨2757281590888955082579509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838187727259303388386339 2757281590888955082579509)
        ·
          refine ⟨258495149145839538991829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2757281590888955082579509 258495149145839538991829)
          ·
            refine ⟨6058480058105614195121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 258495149145839538991829 6058480058105614195121)
            ·
              rfl

theorem cell20_358390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 7].length) (baseStart_358390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358390 prefixEnd_358390 := by exact prefixLift 358390
  have htrace : WordTrace (prefixWord ++ tailWord_358390) baseStart_358390 baseEnd_358390 := by
    simpa [prefixWord, tailWord_358390, baseEnd_358390] using wordTrace_append hprefix tailTrace_358390
  have hstable : (prefixWord ++ tailWord_358390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358390).length < 2 ^ (prefixWord ++ tailWord_358390).sum := by decide
  have hdescent : baseEnd_358390 < baseStart_358390 := by decide
  rcases family_descends (prefixWord ++ tailWord_358390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358428 : List Nat := [2, 2, 3, 1, 3, 2, 3, 4]
def baseStart_358428 : Nat := 118140960795 + 358428 * 2 ^ 59
def prefixEnd_358428 : Nat := 4983230072969 + 3 ^ 40 * 358428 * 2
def baseEnd_358428 : Nat := 54532101934764113333815

theorem tailTrace_358428 : CollatzResearch.WordTrace tailWord_358428 prefixEnd_358428 54532101934764113333815 := by
  unfold tailWord_358428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6536471572742022736981969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8715295430322696982642625 6536471572742022736981969)
  ·
    refine ⟨4902353679556517052736477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6536471572742022736981969 4902353679556517052736477)
    ·
      refine ⟨1838382629833693894776179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4902353679556517052736477 1838382629833693894776179)
      ·
        refine ⟨2757573944750540842164269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838382629833693894776179 2757573944750540842164269)
        ·
          refine ⟨1034090229281452815811601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2757573944750540842164269 1034090229281452815811601)
          ·
            refine ⟨775567671961089611858701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034090229281452815811601 775567671961089611858701)
            ·
              refine ⟨290837876985408604447013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 775567671961089611858701 290837876985408604447013)
              ·
                refine ⟨54532101934764113333815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290837876985408604447013 54532101934764113333815)
                ·
                  rfl

theorem cell20_358428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_358428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358428 prefixEnd_358428 := by exact prefixLift 358428
  have htrace : WordTrace (prefixWord ++ tailWord_358428) baseStart_358428 baseEnd_358428 := by
    simpa [prefixWord, tailWord_358428, baseEnd_358428] using wordTrace_append hprefix tailTrace_358428
  have hstable : (prefixWord ++ tailWord_358428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358428).length < 2 ^ (prefixWord ++ tailWord_358428).sum := by decide
  have hdescent : baseEnd_358428 < baseStart_358428 := by decide
  rcases family_descends (prefixWord ++ tailWord_358428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358452 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 5]
def baseStart_358452 : Nat := 118140960795 + 358452 * 2 ^ 59
def prefixEnd_358452 : Nat := 4983230072969 + 3 ^ 40 * 358452 * 2
def baseEnd_358452 : Nat := 163607260058254923201347

theorem tailTrace_358452 : CollatzResearch.WordTrace tailWord_358452 prefixEnd_358452 163607260058254923201347 := by
  unfold tailWord_358452
  simp only [CollatzResearch.WordTrace]
  refine ⟨6536909248698548786418805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8715878998264731715225073 6536909248698548786418805)
  ·
    refine ⟨612835242065488948726763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6536909248698548786418805 612835242065488948726763)
    ·
      refine ⟨919252863098233423090145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612835242065488948726763 919252863098233423090145)
      ·
        refine ⟨689439647323675067317609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 919252863098233423090145 689439647323675067317609)
        ·
          refine ⟨517079735492756300488207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689439647323675067317609 517079735492756300488207)
          ·
            refine ⟨775619603239134450732311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517079735492756300488207 775619603239134450732311)
            ·
              refine ⟨1163429404858701676098467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775619603239134450732311 1163429404858701676098467)
              ·
                refine ⟨1745144107288052514147701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163429404858701676098467 1745144107288052514147701)
                ·
                  refine ⟨163607260058254923201347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1745144107288052514147701 163607260058254923201347)
                  ·
                    rfl

theorem cell20_358452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_358452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358452 prefixEnd_358452 := by exact prefixLift 358452
  have htrace : WordTrace (prefixWord ++ tailWord_358452) baseStart_358452 baseEnd_358452 := by
    simpa [prefixWord, tailWord_358452, baseEnd_358452] using wordTrace_append hprefix tailTrace_358452
  have hstable : (prefixWord ++ tailWord_358452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358452).length < 2 ^ (prefixWord ++ tailWord_358452).sum := by decide
  have hdescent : baseEnd_358452 < baseStart_358452 := by decide
  rcases family_descends (prefixWord ++ tailWord_358452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358463 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_358463 : Nat := 118140960795 + 358463 * 2 ^ 59
def prefixEnd_358463 : Nat := 4983230072969 + 3 ^ 40 * 358463 * 2
def baseEnd_358463 : Nat := 163612280757987773834635

theorem tailTrace_358463 : CollatzResearch.WordTrace tailWord_358463 prefixEnd_358463 163612280757987773834635 := by
  unfold tailWord_358463
  simp only [CollatzResearch.WordTrace]
  refine ⟨13074219700357246451488043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8716146466904830967658695 13074219700357246451488043)
  ·
    refine ⟨19611329550535869677232065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13074219700357246451488043 19611329550535869677232065)
    ·
      refine ⟨14708497162901902257924049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19611329550535869677232065 14708497162901902257924049)
      ·
        refine ⟨11031372872176426693443037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14708497162901902257924049 11031372872176426693443037)
        ·
          refine ⟨4136764827066160010041139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11031372872176426693443037 4136764827066160010041139)
          ·
            refine ⟨6205147240599240015061709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4136764827066160010041139 6205147240599240015061709)
            ·
              refine ⟨2326930215224715005648141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6205147240599240015061709 2326930215224715005648141)
              ·
                refine ⟨872598830709268127118053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2326930215224715005648141 872598830709268127118053)
                ·
                  refine ⟨163612280757987773834635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 872598830709268127118053 163612280757987773834635)
                  ·
                    rfl

theorem cell20_358463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_358463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358463 prefixEnd_358463 := by exact prefixLift 358463
  have htrace : WordTrace (prefixWord ++ tailWord_358463) baseStart_358463 baseEnd_358463 := by
    simpa [prefixWord, tailWord_358463, baseEnd_358463] using wordTrace_append hprefix tailTrace_358463
  have hstable : (prefixWord ++ tailWord_358463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358463).length < 2 ^ (prefixWord ++ tailWord_358463).sum := by decide
  have hdescent : baseEnd_358463 < baseStart_358463 := by decide
  rcases family_descends (prefixWord ++ tailWord_358463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358473 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 3]
def baseStart_358473 : Nat := 118140960795 + 358473 * 2 ^ 59
def prefixEnd_358473 : Nat := 4983230072969 + 3 ^ 40 * 358473 * 2
def baseEnd_358473 : Nat := 163616845030472183501261

theorem tailTrace_358473 : CollatzResearch.WordTrace tailWord_358473 prefixEnd_358473 163616845030472183501261 := by
  unfold tailWord_358473
  simp only [CollatzResearch.WordTrace]
  refine ⟨13074584430321018159352073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8716389620214012106234715 13074584430321018159352073)
  ·
    refine ⟨9805938322740763619514055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13074584430321018159352073 9805938322740763619514055)
    ·
      refine ⟨14708907484111145429271083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9805938322740763619514055 14708907484111145429271083)
      ·
        refine ⟨22063361226166718143906625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14708907484111145429271083 22063361226166718143906625)
        ·
          refine ⟨16547520919625038607929969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22063361226166718143906625 16547520919625038607929969)
          ·
            refine ⟨12410640689718778955947477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16547520919625038607929969 12410640689718778955947477)
            ·
              refine ⟨290874391165283881780019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12410640689718778955947477 290874391165283881780019)
              ·
                refine ⟨436311586747925822670029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290874391165283881780019 436311586747925822670029)
                ·
                  refine ⟨163616845030472183501261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436311586747925822670029 163616845030472183501261)
                  ·
                    rfl

theorem cell20_358473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_358473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358473 prefixEnd_358473 := by exact prefixLift 358473
  have htrace : WordTrace (prefixWord ++ tailWord_358473) baseStart_358473 baseEnd_358473 := by
    simpa [prefixWord, tailWord_358473, baseEnd_358473] using wordTrace_append hprefix tailTrace_358473
  have hstable : (prefixWord ++ tailWord_358473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358473).length < 2 ^ (prefixWord ++ tailWord_358473).sum := by decide
  have hdescent : baseEnd_358473 < baseStart_358473 := by decide
  rcases family_descends (prefixWord ++ tailWord_358473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358487 : List Nat := [1, 1, 3, 2, 2, 1, 6, 4]
def baseStart_358487 : Nat := 118140960795 + 358487 * 2 ^ 59
def prefixEnd_358487 : Nat := 4983230072969 + 3 ^ 40 * 358487 * 2
def baseEnd_358487 : Nat := 54541078337316785678179

theorem tailTrace_358487 : CollatzResearch.WordTrace tailWord_358487 prefixEnd_358487 54541078337316785678179 := by
  unfold tailWord_358487
  simp only [CollatzResearch.WordTrace]
  refine ⟨13075095052270298550361715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8716730034846865700241143 13075095052270298550361715)
  ·
    refine ⟨19612642578405447825542573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13075095052270298550361715 19612642578405447825542573)
    ·
      refine ⟨7354740966902042934578465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19612642578405447825542573 7354740966902042934578465)
      ·
        refine ⟨5516055725176532200933849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7354740966902042934578465 5516055725176532200933849)
        ·
          refine ⟨4137041793882399150700387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5516055725176532200933849 4137041793882399150700387)
          ·
            refine ⟨6205562690823598726050581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137041793882399150700387 6205562690823598726050581)
            ·
              refine ⟨290885751132356190283621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6205562690823598726050581 290885751132356190283621)
              ·
                refine ⟨54541078337316785678179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290885751132356190283621 54541078337316785678179)
                ·
                  rfl

theorem cell20_358487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 4].length) (baseStart_358487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358487 prefixEnd_358487 := by exact prefixLift 358487
  have htrace : WordTrace (prefixWord ++ tailWord_358487) baseStart_358487 baseEnd_358487 := by
    simpa [prefixWord, tailWord_358487, baseEnd_358487] using wordTrace_append hprefix tailTrace_358487
  have hstable : (prefixWord ++ tailWord_358487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358487).length < 2 ^ (prefixWord ++ tailWord_358487).sum := by decide
  have hdescent : baseEnd_358487 < baseStart_358487 := by decide
  rcases family_descends (prefixWord ++ tailWord_358487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358493 : List Nat := [1, 4, 4, 1, 1, 3, 1, 3, 2]
def baseStart_358493 : Nat := 118140960795 + 358493 * 2 ^ 59
def prefixEnd_358493 : Nat := 4983230072969 + 3 ^ 40 * 358493 * 2
def baseEnd_358493 : Nat := 163625973575441002834513

theorem tailTrace_358493 : CollatzResearch.WordTrace tailWord_358493 prefixEnd_358493 163625973575441002834513 := by
  unfold tailWord_358493
  simp only [CollatzResearch.WordTrace]
  refine ⟨13075313890248561575080133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8716875926832374383386755 13075313890248561575080133)
  ·
    refine ⟨2451621354421605295327525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13075313890248561575080133 2451621354421605295327525)
    ·
      refine ⟨459679003954050992873911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2451621354421605295327525 459679003954050992873911)
      ·
        refine ⟨689518505931076489310867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459679003954050992873911 689518505931076489310867)
        ·
          refine ⟨1034277758896614733966301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689518505931076489310867 1034277758896614733966301)
          ·
            refine ⟨387854159586230525237363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1034277758896614733966301 387854159586230525237363)
            ·
              refine ⟨581781239379345787856045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387854159586230525237363 581781239379345787856045)
              ·
                refine ⟨218167964767254670446017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 581781239379345787856045 218167964767254670446017)
                ·
                  refine ⟨163625973575441002834513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218167964767254670446017 163625973575441002834513)
                  ·
                    rfl

theorem cell20_358493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_358493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358493 prefixEnd_358493 := by exact prefixLift 358493
  have htrace : WordTrace (prefixWord ++ tailWord_358493) baseStart_358493 baseEnd_358493 := by
    simpa [prefixWord, tailWord_358493, baseEnd_358493] using wordTrace_append hprefix tailTrace_358493
  have hstable : (prefixWord ++ tailWord_358493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358493).length < 2 ^ (prefixWord ++ tailWord_358493).sum := by decide
  have hdescent : baseEnd_358493 < baseStart_358493 := by decide
  rcases family_descends (prefixWord ++ tailWord_358493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358508 : List Nat := [2, 2, 1, 1, 3, 3, 8]
def baseStart_358508 : Nat := 118140960795 + 358508 * 2 ^ 59
def prefixEnd_358508 : Nat := 4983230072969 + 3 ^ 40 * 358508 * 2
def baseEnd_358508 : Nat := 18181424442685290814939

theorem tailTrace_358508 : CollatzResearch.WordTrace tailWord_358508 prefixEnd_358508 18181424442685290814939 := by
  unfold tailWord_358508
  simp only [CollatzResearch.WordTrace]
  refine ⟨6537930492597109568438089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8717240656796146091250785 6537930492597109568438089)
  ·
    refine ⟨4903447869447832176328567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6537930492597109568438089 4903447869447832176328567)
    ·
      refine ⟨7355171804171748264492851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4903447869447832176328567 7355171804171748264492851)
      ·
        refine ⟨11032757706257622396739277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7355171804171748264492851 11032757706257622396739277)
        ·
          refine ⟨4137284139846608398777229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11032757706257622396739277 4137284139846608398777229)
          ·
            refine ⟨1551481552442478149541461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4137284139846608398777229 1551481552442478149541461)
            ·
              refine ⟨18181424442685290814939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1551481552442478149541461 18181424442685290814939)
              ·
                rfl

theorem cell20_358508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 8].length) (baseStart_358508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358508 prefixEnd_358508 := by exact prefixLift 358508
  have htrace : WordTrace (prefixWord ++ tailWord_358508) baseStart_358508 baseEnd_358508 := by
    simpa [prefixWord, tailWord_358508, baseEnd_358508] using wordTrace_append hprefix tailTrace_358508
  have hstable : (prefixWord ++ tailWord_358508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358508).length < 2 ^ (prefixWord ++ tailWord_358508).sum := by decide
  have hdescent : baseEnd_358508 < baseStart_358508 := by decide
  rcases family_descends (prefixWord ++ tailWord_358508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358514 : List Nat := [3, 2, 1, 2, 2, 3, 3, 2, 2]
def baseStart_358514 : Nat := 118140960795 + 358514 * 2 ^ 59
def prefixEnd_358514 : Nat := 4983230072969 + 3 ^ 40 * 358514 * 2
def baseEnd_358514 : Nat := 163635558547658263134427

theorem tailTrace_358514 : CollatzResearch.WordTrace tailWord_358514 prefixEnd_358514 163635558547658263134427 := by
  unfold tailWord_358514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269019955793120540398649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8717386548781654774396397 3269019955793120540398649)
  ·
    refine ⟨2451764966844840405298987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3269019955793120540398649 2451764966844840405298987)
    ·
      refine ⟨3677647450267260607948481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2451764966844840405298987 3677647450267260607948481)
      ·
        refine ⟨2758235587700445455961361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3677647450267260607948481 2758235587700445455961361)
        ·
          refine ⟨2068676690775334091971021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2758235587700445455961361 2068676690775334091971021)
          ·
            refine ⟨775753759040750284489133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2068676690775334091971021 775753759040750284489133)
            ·
              refine ⟨290907659640281356683425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 775753759040750284489133 290907659640281356683425)
              ·
                refine ⟨218180744730211017512569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290907659640281356683425 218180744730211017512569)
                ·
                  refine ⟨163635558547658263134427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218180744730211017512569 163635558547658263134427)
                  ·
                    rfl

theorem cell20_358514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_358514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358514 prefixEnd_358514 := by exact prefixLift 358514
  have htrace : WordTrace (prefixWord ++ tailWord_358514) baseStart_358514 baseEnd_358514 := by
    simpa [prefixWord, tailWord_358514, baseEnd_358514] using wordTrace_append hprefix tailTrace_358514
  have hstable : (prefixWord ++ tailWord_358514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358514).length < 2 ^ (prefixWord ++ tailWord_358514).sum := by decide
  have hdescent : baseEnd_358514 < baseStart_358514 := by decide
  rcases family_descends (prefixWord ++ tailWord_358514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358525 : List Nat := [1, 4, 1, 1, 3, 3, 2, 5]
def baseStart_358525 : Nat := 118140960795 + 358525 * 2 ^ 59
def prefixEnd_358525 : Nat := 4983230072969 + 3 ^ 40 * 358525 * 2
def baseEnd_358525 : Nat := 54546859749130371255905

theorem tailTrace_358525 : CollatzResearch.WordTrace tailWord_358525 prefixEnd_358525 54546859749130371255905 := by
  unfold tailWord_358525
  simp only [CollatzResearch.WordTrace]
  refine ⟨13076481026132631040245029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8717654017421754026830019 13076481026132631040245029)
  ·
    refine ⟨2451840192399868320045943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13076481026132631040245029 2451840192399868320045943)
    ·
      refine ⟨3677760288599802480068915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2451840192399868320045943 3677760288599802480068915)
      ·
        refine ⟨5516640432899703720103373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677760288599802480068915 5516640432899703720103373)
        ·
          refine ⟨2068740162337388895038765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5516640432899703720103373 2068740162337388895038765)
          ·
            refine ⟨775777560876520835639537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2068740162337388895038765 775777560876520835639537)
            ·
              refine ⟨581833170657390626729653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775777560876520835639537 581833170657390626729653)
              ·
                refine ⟨54546859749130371255905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 581833170657390626729653 54546859749130371255905)
                ·
                  rfl

theorem cell20_358525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_358525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358525 prefixEnd_358525 := by exact prefixLift 358525
  have htrace : WordTrace (prefixWord ++ tailWord_358525) baseStart_358525 baseEnd_358525 := by
    simpa [prefixWord, tailWord_358525, baseEnd_358525] using wordTrace_append hprefix tailTrace_358525
  have hstable : (prefixWord ++ tailWord_358525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358525).length < 2 ^ (prefixWord ++ tailWord_358525).sum := by decide
  have hdescent : baseEnd_358525 < baseStart_358525 := by decide
  rcases family_descends (prefixWord ++ tailWord_358525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358553 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_358553 : Nat := 118140960795 + 358553 * 2 ^ 59
def prefixEnd_358553 : Nat := 4983230072969 + 3 ^ 40 * 358553 * 2
def baseEnd_358553 : Nat := 163653359210347460834267

theorem tailTrace_358553 : CollatzResearch.WordTrace tailWord_358553 prefixEnd_358553 163653359210347460834267 := by
  unfold tailWord_358553
  simp only [CollatzResearch.WordTrace]
  refine ⟨13077502270031191822264313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8718334846687461214842875 13077502270031191822264313)
  ·
    refine ⟨9808126702523393866698235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13077502270031191822264313 9808126702523393866698235)
    ·
      refine ⟨14712190053785090800047353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9808126702523393866698235 14712190053785090800047353)
      ·
        refine ⟨11034142540338818100035515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14712190053785090800047353 11034142540338818100035515)
        ·
          refine ⟨16551213810508227150053273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11034142540338818100035515 16551213810508227150053273)
          ·
            refine ⟨12413410357881170362539955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16551213810508227150053273 12413410357881170362539955)
            ·
              refine ⟨18620115536821755543809933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12413410357881170362539955 18620115536821755543809933)
              ·
                refine ⟨6982543326308158328928725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18620115536821755543809933 6982543326308158328928725)
                ·
                  refine ⟨163653359210347460834267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6982543326308158328928725 163653359210347460834267)
                  ·
                    rfl

theorem cell20_358553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_358553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358553 prefixEnd_358553 := by exact prefixLift 358553
  have htrace : WordTrace (prefixWord ++ tailWord_358553) baseStart_358553 baseEnd_358553 := by
    simpa [prefixWord, tailWord_358553, baseEnd_358553] using wordTrace_append hprefix tailTrace_358553
  have hstable : (prefixWord ++ tailWord_358553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358553).length < 2 ^ (prefixWord ++ tailWord_358553).sum := by decide
  have hdescent : baseEnd_358553 < baseStart_358553 := by decide
  rcases family_descends (prefixWord ++ tailWord_358553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358591 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_358591 : Nat := 118140960795 + 358591 * 2 ^ 59
def prefixEnd_358591 : Nat := 4983230072969 + 3 ^ 40 * 358591 * 2
def baseEnd_358591 : Nat := 163670703445788217567445

theorem tailTrace_358591 : CollatzResearch.WordTrace tailWord_358591 prefixEnd_358591 163670703445788217567445 := by
  unfold tailWord_358591
  simp only [CollatzResearch.WordTrace]
  refine ⟨13078888243893524312147627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8719258829262349541431751 13078888243893524312147627)
  ·
    refine ⟨19618332365840286468221441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13078888243893524312147627 19618332365840286468221441)
    ·
      refine ⟨14713749274380214851166081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19618332365840286468221441 14713749274380214851166081)
      ·
        refine ⟨11035311955785161138374561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14713749274380214851166081 11035311955785161138374561)
        ·
          refine ⟨8276483966838870853780921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11035311955785161138374561 8276483966838870853780921)
          ·
            refine ⟨6207362975129153140335691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8276483966838870853780921 6207362975129153140335691)
            ·
              refine ⟨9311044462693729710503537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6207362975129153140335691 9311044462693729710503537)
              ·
                refine ⟨6983283347020297282877653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9311044462693729710503537 6983283347020297282877653)
                ·
                  refine ⟨163670703445788217567445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6983283347020297282877653 163670703445788217567445)
                  ·
                    rfl

theorem cell20_358591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_358591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358591 prefixEnd_358591 := by exact prefixLift 358591
  have htrace : WordTrace (prefixWord ++ tailWord_358591) baseStart_358591 baseEnd_358591 := by
    simpa [prefixWord, tailWord_358591, baseEnd_358591] using wordTrace_append hprefix tailTrace_358591
  have hstable : (prefixWord ++ tailWord_358591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358591).length < 2 ^ (prefixWord ++ tailWord_358591).sum := by decide
  have hdescent : baseEnd_358591 < baseStart_358591 := by decide
  rcases family_descends (prefixWord ++ tailWord_358591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358632 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_358632 : Nat := 118140960795 + 358632 * 2 ^ 59
def prefixEnd_358632 : Nat := 4983230072969 + 3 ^ 40 * 358632 * 2
def baseEnd_358632 : Nat := 163689416962974297200611

theorem tailTrace_358632 : CollatzResearch.WordTrace tailWord_358632 prefixEnd_358632 163689416962974297200611 := by
  unfold tailWord_358632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6540191818372494157195075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8720255757829992209593433 6540191818372494157195075)
  ·
    refine ⟨9810287727558741235792613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6540191818372494157195075 9810287727558741235792613)
    ·
      refine ⟨1839428948917263981711115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9810287727558741235792613 1839428948917263981711115)
      ·
        refine ⟨2759143423375895972566673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839428948917263981711115 2759143423375895972566673)
        ·
          refine ⟨2069357567531921979425005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2759143423375895972566673 2069357567531921979425005)
          ·
            refine ⟨776009087824470742284377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2069357567531921979425005 776009087824470742284377)
            ·
              refine ⟨582006815868353056713283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776009087824470742284377 582006815868353056713283)
              ·
                refine ⟨873010223802529585069925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582006815868353056713283 873010223802529585069925)
                ·
                  refine ⟨163689416962974297200611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 873010223802529585069925 163689416962974297200611)
                  ·
                    rfl

theorem cell20_358632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_358632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358632 prefixEnd_358632 := by exact prefixLift 358632
  have htrace : WordTrace (prefixWord ++ tailWord_358632) baseStart_358632 baseEnd_358632 := by
    simpa [prefixWord, tailWord_358632, baseEnd_358632] using wordTrace_append hprefix tailTrace_358632
  have hstable : (prefixWord ++ tailWord_358632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358632).length < 2 ^ (prefixWord ++ tailWord_358632).sum := by decide
  have hdescent : baseEnd_358632 < baseStart_358632 := by decide
  rcases family_descends (prefixWord ++ tailWord_358632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358642 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_358642 : Nat := 118140960795 + 358642 * 2 ^ 59
def prefixEnd_358642 : Nat := 4983230072969 + 3 ^ 40 * 358642 * 2
def baseEnd_358642 : Nat := 163693981235458706867237

theorem tailTrace_358642 : CollatzResearch.WordTrace tailWord_358642 prefixEnd_358642 163693981235458706867237 := by
  unfold tailWord_358642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3270187091677190005563545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8720498911139173348169453 3270187091677190005563545)
  ·
    refine ⟨2452640318757892504172659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3270187091677190005563545 2452640318757892504172659)
    ·
      refine ⟨3678960478136838756258989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2452640318757892504172659 3678960478136838756258989)
      ·
        refine ⟨1379610179301314533597121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3678960478136838756258989 1379610179301314533597121)
        ·
          refine ⟨1034707634475985900197841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1379610179301314533597121 1034707634475985900197841)
          ·
            refine ⟨776030725856989425148381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034707634475985900197841 776030725856989425148381)
            ·
              refine ⟨291011522196371034430643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776030725856989425148381 291011522196371034430643)
              ·
                refine ⟨436517283294556551645965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291011522196371034430643 436517283294556551645965)
                ·
                  refine ⟨163693981235458706867237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436517283294556551645965 163693981235458706867237)
                  ·
                    rfl

theorem cell20_358642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_358642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358642 prefixEnd_358642 := by exact prefixLift 358642
  have htrace : WordTrace (prefixWord ++ tailWord_358642) baseStart_358642 baseEnd_358642 := by
    simpa [prefixWord, tailWord_358642, baseEnd_358642] using wordTrace_append hprefix tailTrace_358642
  have hstable : (prefixWord ++ tailWord_358642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358642).length < 2 ^ (prefixWord ++ tailWord_358642).sum := by decide
  have hdescent : baseEnd_358642 < baseStart_358642 := by decide
  rcases family_descends (prefixWord ++ tailWord_358642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358667 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_358667 : Nat := 118140960795 + 358667 * 2 ^ 59
def prefixEnd_358667 : Nat := 4983230072969 + 3 ^ 40 * 358667 * 2
def baseEnd_358667 : Nat := 163705391916669731033801

theorem tailTrace_358667 : CollatzResearch.WordTrace tailWord_358667 prefixEnd_358667 163705391916669731033801 := by
  unfold tailWord_358667
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081660191618189291914255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8721106794412126194609503 13081660191618189291914255)
  ·
    refine ⟨19622490287427283937871383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13081660191618189291914255 19622490287427283937871383)
    ·
      refine ⟨29433735431140925906807075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19622490287427283937871383 29433735431140925906807075)
      ·
        refine ⟨44150603146711388860210613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29433735431140925906807075 44150603146711388860210613)
        ·
          refine ⟨4139119045004192705644745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44150603146711388860210613 4139119045004192705644745)
          ·
            refine ⟨3104339283753144529233559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4139119045004192705644745 3104339283753144529233559)
            ·
              refine ⟨4656508925629716793850339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104339283753144529233559 4656508925629716793850339)
              ·
                refine ⟨6984763388444575190775509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4656508925629716793850339 6984763388444575190775509)
                ·
                  refine ⟨163705391916669731033801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6984763388444575190775509 163705391916669731033801)
                  ·
                    rfl

theorem cell20_358667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_358667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358667 prefixEnd_358667 := by exact prefixLift 358667
  have htrace : WordTrace (prefixWord ++ tailWord_358667) baseStart_358667 baseEnd_358667 := by
    simpa [prefixWord, tailWord_358667, baseEnd_358667] using wordTrace_append hprefix tailTrace_358667
  have hstable : (prefixWord ++ tailWord_358667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358667).length < 2 ^ (prefixWord ++ tailWord_358667).sum := by decide
  have hdescent : baseEnd_358667 < baseStart_358667 := by decide
  rcases family_descends (prefixWord ++ tailWord_358667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358684 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 3]
def baseStart_358684 : Nat := 118140960795 + 358684 * 2 ^ 59
def prefixEnd_358684 : Nat := 4983230072969 + 3 ^ 40 * 358684 * 2
def baseEnd_358684 : Nat := 163713151179893227467065

theorem tailTrace_358684 : CollatzResearch.WordTrace tailWord_358684 prefixEnd_358684 163713151179893227467065 := by
  unfold tailWord_358684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6541140116278300597641553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8721520155037734130188737 6541140116278300597641553)
  ·
    refine ⟨4905855087208725448231165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6541140116278300597641553 4905855087208725448231165)
    ·
      refine ⟨1839695657703272043086687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4905855087208725448231165 1839695657703272043086687)
      ·
        refine ⟨2759543486554908064630031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839695657703272043086687 2759543486554908064630031)
        ·
          refine ⟨4139315229832362096945047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759543486554908064630031 4139315229832362096945047)
          ·
            refine ⟨6208972844748543145417571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139315229832362096945047 6208972844748543145417571)
            ·
              refine ⟨9313459267122814718126357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208972844748543145417571 9313459267122814718126357)
              ·
                refine ⟨436568403146381939912173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9313459267122814718126357 436568403146381939912173)
                ·
                  refine ⟨163713151179893227467065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436568403146381939912173 163713151179893227467065)
                  ·
                    rfl

theorem cell20_358684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_358684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358684 prefixEnd_358684 := by exact prefixLift 358684
  have htrace : WordTrace (prefixWord ++ tailWord_358684) baseStart_358684 baseEnd_358684 := by
    simpa [prefixWord, tailWord_358684, baseEnd_358684] using wordTrace_append hprefix tailTrace_358684
  have hstable : (prefixWord ++ tailWord_358684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358684).length < 2 ^ (prefixWord ++ tailWord_358684).sum := by decide
  have hdescent : baseEnd_358684 < baseStart_358684 := by decide
  rcases family_descends (prefixWord ++ tailWord_358684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358815 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 3]
def baseStart_358815 : Nat := 118140960795 + 358815 * 2 ^ 59
def prefixEnd_358815 : Nat := 4983230072969 + 3 ^ 40 * 358815 * 2
def baseEnd_358815 : Nat := 163772943149438994099863

theorem tailTrace_358815 : CollatzResearch.WordTrace tailWord_358815 prefixEnd_358815 163772943149438994099863 := by
  unfold tailWord_358815
  simp only [CollatzResearch.WordTrace]
  refine ⟨13087058195082010568301899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8724705463388007045534599 13087058195082010568301899)
  ·
    refine ⟨19630587292623015852452849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13087058195082010568301899 19630587292623015852452849)
    ·
      refine ⟨14722940469467261889339637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19630587292623015852452849 14722940469467261889339637)
      ·
        refine ⟨1380275669012555802125591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14722940469467261889339637 1380275669012555802125591)
        ·
          refine ⟨2070413503518833703188387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380275669012555802125591 2070413503518833703188387)
          ·
            refine ⟨3105620255278250554782581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070413503518833703188387 3105620255278250554782581)
            ·
              refine ⟨291151898932335989510867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3105620255278250554782581 291151898932335989510867)
              ·
                refine ⟨436727848398503984266301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291151898932335989510867 436727848398503984266301)
                ·
                  refine ⟨163772943149438994099863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436727848398503984266301 163772943149438994099863)
                  ·
                    rfl

theorem cell20_358815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 3].length) (baseStart_358815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358815 prefixEnd_358815 := by exact prefixLift 358815
  have htrace : WordTrace (prefixWord ++ tailWord_358815) baseStart_358815 baseEnd_358815 := by
    simpa [prefixWord, tailWord_358815, baseEnd_358815] using wordTrace_append hprefix tailTrace_358815
  have hstable : (prefixWord ++ tailWord_358815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358815).length < 2 ^ (prefixWord ++ tailWord_358815).sum := by decide
  have hdescent : baseEnd_358815 < baseStart_358815 := by decide
  rcases family_descends (prefixWord ++ tailWord_358815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358839 : List Nat := [1, 1, 3, 1, 3, 5, 1, 3, 2]
def baseStart_358839 : Nat := 118140960795 + 358839 * 2 ^ 59
def prefixEnd_358839 : Nat := 4983230072969 + 3 ^ 40 * 358839 * 2
def baseEnd_358839 : Nat := 163783897403401577299765

theorem tailTrace_358839 : CollatzResearch.WordTrace tailWord_358839 prefixEnd_358839 163783897403401577299765 := by
  unfold tailWord_358839
  simp only [CollatzResearch.WordTrace]
  refine ⟨13087933546995062667175571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8725289031330041778117047 13087933546995062667175571)
  ·
    refine ⟨19631900320492594000763357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13087933546995062667175571 19631900320492594000763357)
    ·
      refine ⟨7361962620184722750286259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19631900320492594000763357 7361962620184722750286259)
      ·
        refine ⟨11042943930277084125429389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7361962620184722750286259 11042943930277084125429389)
        ·
          refine ⟨4141103973853906547036021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11042943930277084125429389 4141103973853906547036021)
          ·
            refine ⟨388228497548803738784627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4141103973853906547036021 388228497548803738784627)
            ·
              refine ⟨582342746323205608176941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388228497548803738784627 582342746323205608176941)
              ·
                refine ⟨218378529871202103066353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 582342746323205608176941 218378529871202103066353)
                ·
                  refine ⟨163783897403401577299765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218378529871202103066353 163783897403401577299765)
                  ·
                    rfl

theorem cell20_358839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 2].length) (baseStart_358839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358839 prefixEnd_358839 := by exact prefixLift 358839
  have htrace : WordTrace (prefixWord ++ tailWord_358839) baseStart_358839 baseEnd_358839 := by
    simpa [prefixWord, tailWord_358839, baseEnd_358839] using wordTrace_append hprefix tailTrace_358839
  have hstable : (prefixWord ++ tailWord_358839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358839).length < 2 ^ (prefixWord ++ tailWord_358839).sum := by decide
  have hdescent : baseEnd_358839 < baseStart_358839 := by decide
  rcases family_descends (prefixWord ++ tailWord_358839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358857 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_358857 : Nat := 118140960795 + 358857 * 2 ^ 59
def prefixEnd_358857 : Nat := 4983230072969 + 3 ^ 40 * 358857 * 2
def baseEnd_358857 : Nat := 163792113093873514699691

theorem tailTrace_358857 : CollatzResearch.WordTrace tailWord_358857 prefixEnd_358857 163792113093873514699691 := by
  unfold tailWord_358857
  simp only [CollatzResearch.WordTrace]
  refine ⟨13088590060929851741330825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8725726707286567827553883 13088590060929851741330825)
  ·
    refine ⟨9816442545697388805998119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13088590060929851741330825 9816442545697388805998119)
    ·
      refine ⟨14724663818546083208997179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9816442545697388805998119 14724663818546083208997179)
      ·
        refine ⟨22086995727819124813495769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14724663818546083208997179 22086995727819124813495769)
        ·
          refine ⟨16565246795864343610121827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22086995727819124813495769 16565246795864343610121827)
          ·
            refine ⟨24847870193796515415182741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16565246795864343610121827 24847870193796515415182741)
            ·
              refine ⟨1164743915334211660086691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24847870193796515415182741 1164743915334211660086691)
              ·
                refine ⟨1747115873001317490130037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164743915334211660086691 1747115873001317490130037)
                ·
                  refine ⟨163792113093873514699691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1747115873001317490130037 163792113093873514699691)
                  ·
                    rfl

theorem cell20_358857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_358857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358857 prefixEnd_358857 := by exact prefixLift 358857
  have htrace : WordTrace (prefixWord ++ tailWord_358857) baseStart_358857 baseEnd_358857 := by
    simpa [prefixWord, tailWord_358857, baseEnd_358857] using wordTrace_append hprefix tailTrace_358857
  have hstable : (prefixWord ++ tailWord_358857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358857).length < 2 ^ (prefixWord ++ tailWord_358857).sum := by decide
  have hdescent : baseEnd_358857 < baseStart_358857 := by decide
  rcases family_descends (prefixWord ++ tailWord_358857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358866 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 3]
def baseStart_358866 : Nat := 118140960795 + 358866 * 2 ^ 59
def prefixEnd_358866 : Nat := 4983230072969 + 3 ^ 40 * 358866 * 2
def baseEnd_358866 : Nat := 163796220939109483399655

theorem tailTrace_358866 : CollatzResearch.WordTrace tailWord_358866 prefixEnd_358866 163796220939109483399655 := by
  unfold tailWord_358866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272229579474311569602113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8725945545264830852272301 3272229579474311569602113)
  ·
    refine ⟨2454172184605733677201585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3272229579474311569602113 2454172184605733677201585)
    ·
      refine ⟨1840629138454300257901189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2454172184605733677201585 1840629138454300257901189)
      ·
        refine ⟨345117963460181298356473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1840629138454300257901189 345117963460181298356473)
        ·
          refine ⟨258838472595135973767355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345117963460181298356473 258838472595135973767355)
          ·
            refine ⟨388257708892703960651033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258838472595135973767355 388257708892703960651033)
            ·
              refine ⟨291193281669527970488275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388257708892703960651033 291193281669527970488275)
              ·
                refine ⟨436789922504291955732413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291193281669527970488275 436789922504291955732413)
                ·
                  refine ⟨163796220939109483399655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436789922504291955732413 163796220939109483399655)
                  ·
                    rfl

theorem cell20_358866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_358866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358866 prefixEnd_358866 := by exact prefixLift 358866
  have htrace : WordTrace (prefixWord ++ tailWord_358866) baseStart_358866 baseEnd_358866 := by
    simpa [prefixWord, tailWord_358866, baseEnd_358866] using wordTrace_append hprefix tailTrace_358866
  have hstable : (prefixWord ++ tailWord_358866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358866).length < 2 ^ (prefixWord ++ tailWord_358866).sum := by decide
  have hdescent : baseEnd_358866 < baseStart_358866 := by decide
  rcases family_descends (prefixWord ++ tailWord_358866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358874 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_358874 : Nat := 118140960795 + 358874 * 2 ^ 59
def prefixEnd_358874 : Nat := 4983230072969 + 3 ^ 40 * 358874 * 2
def baseEnd_358874 : Nat := 163799872357097011132955

theorem tailTrace_358874 : CollatzResearch.WordTrace tailWord_358874 prefixEnd_358874 163799872357097011132955 := by
  unfold tailWord_358874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272302525467065911174919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8726140067912175763133117 3272302525467065911174919)
  ·
    refine ⟨4908453788200598866762379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3272302525467065911174919 4908453788200598866762379)
    ·
      refine ⟨7362680682300898300143569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4908453788200598866762379 7362680682300898300143569)
      ·
        refine ⟨5522010511725673725107677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7362680682300898300143569 5522010511725673725107677)
        ·
          refine ⟨2070753941897127646915379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5522010511725673725107677 2070753941897127646915379)
          ·
            refine ⟨3106130912845691470373069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070753941897127646915379 3106130912845691470373069)
            ·
              refine ⟨1164799092317134301389901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3106130912845691470373069 1164799092317134301389901)
              ·
                refine ⟨436799659618925363021213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1164799092317134301389901 436799659618925363021213)
                ·
                  refine ⟨163799872357097011132955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436799659618925363021213 163799872357097011132955)
                  ·
                    rfl

theorem cell20_358874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_358874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358874 prefixEnd_358874 := by exact prefixLift 358874
  have htrace : WordTrace (prefixWord ++ tailWord_358874) baseStart_358874 baseEnd_358874 := by
    simpa [prefixWord, tailWord_358874, baseEnd_358874] using wordTrace_append hprefix tailTrace_358874
  have hstable : (prefixWord ++ tailWord_358874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358874).length < 2 ^ (prefixWord ++ tailWord_358874).sum := by decide
  have hdescent : baseEnd_358874 < baseStart_358874 := by decide
  rcases family_descends (prefixWord ++ tailWord_358874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358888 : List Nat := [2, 1, 4, 1, 1, 3, 2, 6]
def baseStart_358888 : Nat := 118140960795 + 358888 * 2 ^ 59
def prefixEnd_358888 : Nat := 4983230072969 + 3 ^ 40 * 358888 * 2
def baseEnd_358888 : Nat := 54602087446191728222077

theorem tailTrace_358888 : CollatzResearch.WordTrace tailWord_358888 prefixEnd_358888 54602087446191728222077 := by
  unfold tailWord_358888
  simp only [CollatzResearch.WordTrace]
  refine ⟨6544860361908772017854659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8726480482545029357139545 6544860361908772017854659)
  ·
    refine ⟨9817290542863158026781989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6544860361908772017854659 9817290542863158026781989)
    ·
      refine ⟨1840741976786842130021623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9817290542863158026781989 1840741976786842130021623)
      ·
        refine ⟨2761112965180263195032435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840741976786842130021623 2761112965180263195032435)
        ·
          refine ⟨4141669447770394792548653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2761112965180263195032435 4141669447770394792548653)
          ·
            refine ⟨1553126042913898047205745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4141669447770394792548653 1553126042913898047205745)
            ·
              refine ⟨1164844532185423535404309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553126042913898047205745 1164844532185423535404309)
              ·
                refine ⟨54602087446191728222077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1164844532185423535404309 54602087446191728222077)
                ·
                  rfl

theorem cell20_358888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_358888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358888 prefixEnd_358888 := by exact prefixLift 358888
  have htrace : WordTrace (prefixWord ++ tailWord_358888) baseStart_358888 baseEnd_358888 := by
    simpa [prefixWord, tailWord_358888, baseEnd_358888] using wordTrace_append hprefix tailTrace_358888
  have hstable : (prefixWord ++ tailWord_358888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358888).length < 2 ^ (prefixWord ++ tailWord_358888).sum := by decide
  have hdescent : baseEnd_358888 < baseStart_358888 := by decide
  rcases family_descends (prefixWord ++ tailWord_358888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358918 : List Nat := [6, 2, 1, 1, 1, 3, 1, 5]
def baseStart_358918 : Nat := 118140960795 + 358918 * 2 ^ 59
def prefixEnd_358918 : Nat := 4983230072969 + 3 ^ 40 * 358918 * 2
def baseEnd_358918 : Nat := 54606651718676137888703

theorem tailTrace_358918 : CollatzResearch.WordTrace tailWord_358918 prefixEnd_358918 54606651718676137888703 := by
  unfold tailWord_358918
  simp only [CollatzResearch.WordTrace]
  refine ⟨409087966053401848728169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8727209942472572772867605 409087966053401848728169)
  ·
    refine ⟨306815974540051386546127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 409087966053401848728169 306815974540051386546127)
    ·
      refine ⟨460223961810077079819191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306815974540051386546127 460223961810077079819191)
      ·
        refine ⟨690335942715115619728787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460223961810077079819191 690335942715115619728787)
        ·
          refine ⟨1035503914072673429593181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690335942715115619728787 1035503914072673429593181)
          ·
            refine ⟨388313967777252536097443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1035503914072673429593181 388313967777252536097443)
            ·
              refine ⟨582470951665878804146165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388313967777252536097443 582470951665878804146165)
              ·
                refine ⟨54606651718676137888703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 582470951665878804146165 54606651718676137888703)
                ·
                  rfl

theorem cell20_358918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_358918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358918 prefixEnd_358918 := by exact prefixLift 358918
  have htrace : WordTrace (prefixWord ++ tailWord_358918) baseStart_358918 baseEnd_358918 := by
    simpa [prefixWord, tailWord_358918, baseEnd_358918] using wordTrace_append hprefix tailTrace_358918
  have hstable : (prefixWord ++ tailWord_358918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358918).length < 2 ^ (prefixWord ++ tailWord_358918).sum := by decide
  have hdescent : baseEnd_358918 < baseStart_358918 := by decide
  rcases family_descends (prefixWord ++ tailWord_358918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358980 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 3]
def baseStart_358980 : Nat := 118140960795 + 358980 * 2 ^ 59
def prefixEnd_358980 : Nat := 4983230072969 + 3 ^ 40 * 358980 * 2
def baseEnd_358980 : Nat := 163848253645431753599189

theorem tailTrace_358980 : CollatzResearch.WordTrace tailWord_358980 prefixEnd_358980 163848253645431753599189 := by
  unfold tailWord_358980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6546538119742121874029197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8728717492989495832038929 6546538119742121874029197)
  ·
    refine ⟨2454951794903295702760949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6546538119742121874029197 2454951794903295702760949)
    ·
      refine ⟨230151730772183972133839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2454951794903295702760949 230151730772183972133839)
      ·
        refine ⟨345227596158275958200759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230151730772183972133839 345227596158275958200759)
        ·
          refine ⟨517841394237413937301139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345227596158275958200759 517841394237413937301139)
          ·
            refine ⟨776762091356120905951709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517841394237413937301139 776762091356120905951709)
            ·
              refine ⟨291285784258545339731891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776762091356120905951709 291285784258545339731891)
              ·
                refine ⟨436928676387818009597837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291285784258545339731891 436928676387818009597837)
                ·
                  refine ⟨163848253645431753599189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436928676387818009597837 163848253645431753599189)
                  ·
                    rfl

theorem cell20_358980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_358980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_358980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_358980 prefixEnd_358980 := by exact prefixLift 358980
  have htrace : WordTrace (prefixWord ++ tailWord_358980) baseStart_358980 baseEnd_358980 := by
    simpa [prefixWord, tailWord_358980, baseEnd_358980] using wordTrace_append hprefix tailTrace_358980
  have hstable : (prefixWord ++ tailWord_358980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358980).length < 2 ^ (prefixWord ++ tailWord_358980).sum := by decide
  have hdescent : baseEnd_358980 < baseStart_358980 := by decide
  rcases family_descends (prefixWord ++ tailWord_358980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359009 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_359009 : Nat := 118140960795 + 359009 * 2 ^ 59
def prefixEnd_359009 : Nat := 4983230072969 + 3 ^ 40 * 359009 * 2
def baseEnd_359009 : Nat := 163861490035636541632403

theorem tailTrace_359009 : CollatzResearch.WordTrace tailWord_359009 prefixEnd_359009 163861490035636541632403 := by
  unfold tailWord_359009
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094133956379181700864081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8729422637586121133909387 13094133956379181700864081)
  ·
    refine ⟨9820600467284386275648061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13094133956379181700864081 9820600467284386275648061)
    ·
      refine ⟨3682725175231644853368023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9820600467284386275648061 3682725175231644853368023)
      ·
        refine ⟨5524087762847467280052035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682725175231644853368023 5524087762847467280052035)
        ·
          refine ⟨8286131644271200920078053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5524087762847467280052035 8286131644271200920078053)
          ·
            refine ⟨1553649683300850172514635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8286131644271200920078053 1553649683300850172514635)
            ·
              refine ⟨2330474524951275258771953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553649683300850172514635 2330474524951275258771953)
              ·
                refine ⟨1747855893713456444078965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2330474524951275258771953 1747855893713456444078965)
                ·
                  refine ⟨163861490035636541632403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1747855893713456444078965 163861490035636541632403)
                  ·
                    rfl

theorem cell20_359009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_359009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359009 prefixEnd_359009 := by exact prefixLift 359009
  have htrace : WordTrace (prefixWord ++ tailWord_359009) baseStart_359009 baseEnd_359009 := by
    simpa [prefixWord, tailWord_359009, baseEnd_359009] using wordTrace_append hprefix tailTrace_359009
  have hstable : (prefixWord ++ tailWord_359009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359009).length < 2 ^ (prefixWord ++ tailWord_359009).sum := by decide
  have hdescent : baseEnd_359009 < baseStart_359009 := by decide
  rcases family_descends (prefixWord ++ tailWord_359009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359023 : List Nat := [1, 1, 2, 1, 3, 2, 10]
def baseStart_359023 : Nat := 118140960795 + 359023 * 2 ^ 59
def prefixEnd_359023 : Nat := 4983230072969 + 3 ^ 40 * 359023 * 2
def baseEnd_359023 : Nat := 18207542224123857240631

theorem tailTrace_359023 : CollatzResearch.WordTrace tailWord_359023 prefixEnd_359023 18207542224123857240631 := by
  unfold tailWord_359023
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094644578328462091873723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8729763052218974727915815 13094644578328462091873723)
  ·
    refine ⟨19641966867492693137810585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13094644578328462091873723 19641966867492693137810585)
    ·
      refine ⟨14731475150619519853357939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19641966867492693137810585 14731475150619519853357939)
      ·
        refine ⟨22097212725929279780036909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14731475150619519853357939 22097212725929279780036909)
        ·
          refine ⟨8286454772223479917513841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22097212725929279780036909 8286454772223479917513841)
          ·
            refine ⟨6214841079167609938135381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8286454772223479917513841 6214841079167609938135381)
            ·
              refine ⟨18207542224123857240631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6214841079167609938135381 18207542224123857240631)
              ·
                rfl

theorem cell20_359023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 10].length) (baseStart_359023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_359023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_359023 prefixEnd_359023 := by exact prefixLift 359023
  have htrace : WordTrace (prefixWord ++ tailWord_359023) baseStart_359023 baseEnd_359023 := by
    simpa [prefixWord, tailWord_359023, baseEnd_359023] using wordTrace_append hprefix tailTrace_359023
  have hstable : (prefixWord ++ tailWord_359023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359023).length < 2 ^ (prefixWord ++ tailWord_359023).sum := by decide
  have hdescent : baseEnd_359023 < baseStart_359023 := by decide
  rcases family_descends (prefixWord ++ tailWord_359023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
